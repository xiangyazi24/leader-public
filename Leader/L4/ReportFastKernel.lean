import Leader.L4.ReportAdaptiveBlock
import Leader.L4.ShortTwoPublicationClock

namespace L4.ReportFastKernel
open Height ReportAdaptiveFibre

variable {X Y J : Type} {n : Nat}

def cap : Nat := 2^22
def denominator : Nat := 2^(cap+1)
def block (t W n : Nat) : Nat := 8192*t*W*n
def coefficient (t W : Nat) : Nat := 8192*t*W*denominator

/-- The exact abstract inputs still required from the report's literal
steering/front program. The phase state and its rank are proof-only.
`closed` includes ordinary labels with zero driver preimages: on a wrong
side one may restart the observer at the real endpoint, retaining the
authentic latch. `idle`/diminution concern DRIVER steps only, and spacing
is required only along mapped driver words, not wrong ordinary words. -/
structure PaperKernel (step : Y→Fin n→Y) (steer : Y→Fin n→Fin n)
    (Q : Y→Prop) (finish : Y→Bool)
    (rank : Y→Nat) (mark : Y→Fin n→Nat) (t w W : Nat) : Prop where
  closed : ∀ y e,Q y→Q (step y e)
  fibre_two : ∀ y e,Q y→fibre steer y e≤2
  rank_bound : ∀ y,Q y→rank y≤2048*t*W
  idle : ∀ y e,Q y→finish y≠true→rank (step y (steer y e))≤rank y
  nominate : ∀ y,Q y→finish y≠true→
    ∃ a d, steer y d=a ∧ rank (step y a)<rank y
  mark_sum : ∀ y,Q y→(List.ofFn (mark y)).sum≤10
  separation : ∀ y,Q y→∀ v, v.length=block t W n→
    let u:=mapWord step steer y v
    3*t*w*choices step steer y u≤3*t*w*5+reward step mark y u

/-- Positive success count on ORIGINAL iid raw labels from the six
deterministic ingredients of the bounded likelihood proof. -/
theorem paper_block_success
    (step : Y→Fin n→Y) (steer : Y→Fin n→Fin n)
    (Q : Y→Prop) (finish : Y→Bool) (rank : Y→Nat) (mark : Y→Fin n→Nat) {t w W : Nat}
    (T : 0<t) (Wp : 0<W) (wp : 0<w) (N : 0<n) (R : W≤11*w)
    (K : PaperKernel step steer Q finish rank mark t w W)
    (sticky : ∀ y e,finish y=true→finish (step y e)=true)
    (x : Y) (G : Q x) :
    n^(block t W n)≤denominator*successCount step finish x (block t W n) := by
  let H := block t W n
  have M := driver_nominated_mean step steer Q (fun y=>finish y=true) rank
    K.closed K.idle K.nominate x G
  have B : IIDExpectedHittingTimeAtMost (driverStep step steer) (fun y=>finish y=true)
      x (2048*t*W*n) := by
    intro v
    exact Nat.le_trans (M v) (Nat.mul_le_mul_right _
      (by rw [Nat.mul_comm _ n]; exact Nat.mul_le_mul_left n (K.rank_bound x G)))
  have L := miss_from_mean (driverStep step steer) finish
    (fun y e=>sticky y (steer y e)) x (2048*t*W*n) H B
  have A : H=4*(2048*t*W*n) := by
    unfold H block
    change (4*2048)*t*W*n=4*(2048*t*W*n)
    ac_rfl
  have Hlate : 4*missCount (driverStep step steer) finish x H≤n^H := by
    apply Nat.le_of_mul_le_mul_left _
      (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide : 0<2048) T) Wp) N)
    calc
      (2048*t*W*n)*(4*missCount (driverStep step steer) finish x H) =
          H*missCount (driverStep step steer) finish x H := by rw [A]; ac_rfl
      _ ≤ _ := L
  have mass := total_driver_reward step steer mark Q K.closed K.fibre_two 10 K.mark_sum H x G
  have O := cap_overflow_count step steer mark x H (3*t*w) 5 cap 20 (K.separation x G) mass
  have Hcap := paper_cap_quarter T wp N R
    (fun u=>if cap<choices step steer x (mapWord step steer x u) then 1 else 0) O
  exact block_success_from_quarters step steer finish Q K.closed K.fibre_two x G H cap Hlate Hcap

private theorem run_project_on_good
    (next : Y→Fin n→Y) (real : X→Fin n→X) (project : Y→X)
    (Q : Y→Prop) (stay : ∀ y e,Q y→Q (next y e))
    (comm : ∀ y e,Q y→project (next y e)=real (project y) e)
    (x : Y) (G : Q x) (u : List (Fin n)) :
    project (runWord next x u)=runWord real (project x) u := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih =>
    change project (runWord next (next x e) u)=runWord real (real (project x) e) u
    rw [ih _ (stay x e G),comm x e G]

/-- An auxiliary monitor may certify fewer events than ordinary
publication; it may not manufacture a hit or change the sampled tape. -/
theorem block_project
    (next : Y→Fin n→Y) (real : X→Fin n→X) (project : Y→X)
    (Q : Y→Prop) (stay : ∀ y e,Q y→Q (next y e))
    (comm : ∀ y e,Q y→project (next y e)=real (project y) e)
    (finish : Y→Bool) (done : X→Bool)
    (sound : ∀ y,Q y→finish y=true→done (project y)=true)
    (x : Y) (G : Q x) (H : Nat) :
    successCount next finish x H ≤ successCount real done (project x) H := by
  unfold successCount
  apply wordSum_mono
  intro u
  cases E : finish (runWord next x u)
  · simp
  · have H := sound _ (runWord_of_closed next Q stay x u G) E
    have R := run_project_on_good next real project Q stay comm x G u
    rw [R] at H
    simp [H]

/-- Exact consumer. All mathematical scheduler work is factored into the
checked kernel. The remaining obligations are the literal report's proof
observer, actual old-pair projection, phase nomination and event counts. -/
theorem paper_uniform_publication [DecidableEq J]
    (real : X→Fin n→X) (classify : X→Fin n→Option J)
    (Good : X→Prop) (closed : ∀ x e,Good x→Good (real x e)) {t w W : Nat}
    (T : 0<t) (Wp : 0<W) (wp : 0<w) (N : 0<n) (R : W≤11*w)
    (next : J→Y→Fin n→Y) (steer : J→Y→Fin n→Fin n)
    (Q : J→Y→Prop) (finish : J→Y→Bool) (rank : J→Y→Nat)
    (mark : J→Y→Fin n→Nat) (project : J→Y→X×Bool) (init : J→X→Y)
    (K : ∀ j, PaperKernel (next j) (steer j) (Q j) (finish j) (rank j) (mark j) t w W)
    (sticky : ∀ j y e,finish j y=true→finish j (next j y e)=true)
    (initQ : ∀ j x,Good x→Q j (init j x))
    (initP : ∀ j x,Good x→project j (init j x)=(x,false))
    (comm : ∀ j y e,Q j y→project j (next j y e)=
      ShortTwoPublicationClock.phase real classify j (project j y) e)
    (sound : ∀ j y,Q j y→finish j y=true→(project j y).2=true) :
    ShortTwoPublicationClock.UniformPublicationMean real classify Good (coefficient t W*n) := by
  intro j x G
  let real' := ShortTwoPublicationClock.phase real classify j
  let gd := fun y : X×Bool=>Good y.1
  let done := fun y : X×Bool=>y.2
  have succCount (p : X×Bool) (P : gd p) :
      n^(block t W n)≤denominator*successCount real' done p (block t W n) := by
    rcases p with ⟨y,f⟩
    cases f
    · have A := paper_block_success (next j) (steer j) (Q j) (finish j) (rank j) (mark j)
        T Wp wp N R (K j) (sticky j) (init j y) (initQ j y P)
      have B := block_project (next j) real' (project j) (Q j) (K j).closed (comm j)
        (finish j) done (sound j) (init j y) (initQ j y P) (block t W n)
      rw [initP j y P] at B
      exact Nat.le_trans A (Nat.mul_le_mul_left _ B)
    · have carry (z : X×Bool) (e : Fin n) (H : done z=true) : done (real' z e)=true := by
        change z.2=true at H
        change (z.2 || decide (classify z.1 e=some j))=true
        simp [H]
      have E : successCount real' done (y,true) (block t W n)=n^(block t W n) := by
        unfold successCount
        rw [←wordSum_const_one (n:=n) (block t W n)]
        apply wordSum_congr_fun
        intro u
        rw [runWord_of_closed real' (fun z=>done z=true) carry (y,true) u rfl]
        rfl
      rw [E]
      exact Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide))
  have Wpos : 0<block t W n := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) T) Wp) N
  have B := fixed_block_mean real' done gd (fun z e h=>closed z.1 e h)
    (fun z e h=>by
      change z.2=true at h
      change (z.2 || decide (classify z.1 e=some j))=true
      simp [h])
    denominator (block t W n) Wpos succCount (x,false) G
  have Eq : denominator*block t W n=coefficient t W*n := by
    unfold block coefficient
    generalize denominator=d
    ac_rfl
  rw [Eq] at B
  exact B

theorem coefficient_le_of_exp (t W S : Nat) (Esize : cap+14≤S) :
    coefficient t W ≤ 2^S*t*W := by
  have E : coefficient t W = 2^(cap+14)*t*W := by
    unfold coefficient denominator
    rw [show cap+14=13+(cap+1) by omega,Nat.pow_add 2 13 (cap+1),
      show 2^13=8192 by decide]
    generalize 2^(cap+1)=d
    ac_rfl
  rw [E]
  have P := Nat.pow_le_pow_right (n:=2) (i:=cap+14) (j:=S) (by decide) Esize
  exact Nat.mul_le_mul_right W (Nat.mul_le_mul_right t P)

theorem exponent_le_deployed : cap+14≤2^22+14 := Nat.le_refl _

end L4.ReportFastKernel
