import Leader.Core.Basic
import Leader.L4.Height.CapRepair
import Leader.L4.Height.LeaderBridge
import Leader.L4.Height.Physical
import Leader.L4.Height.G9Core

/-! Raw-edge composition for the padded ordered pair rule. The charts remember
a fixed layout, custody evidence and publication history. -/
namespace L4.Height.G9Spine
open Classical
open L4.Compiler.Native

/-- The same physical site is the sole positive readout on every continuation. -/
def Permanent {X : Type} {n : Nat} (next : X → Fin n → X)
    (read : X → Fin n → Bool) (x : X) : Prop :=
  ∃ v : Fin n, ∀ w : List (Fin n), ∀ j, read (runWord next x w) j = decide (j = v)

theorem permanent_closed {X : Type} {n : Nat} (next : X → Fin n → X)
    (read : X → Fin n → Bool) (x : X) (e : Fin n) :
    Permanent next read x → Permanent next read (next x e) := by
  rintro ⟨v, h⟩
  exact ⟨v, fun w j => h (e :: w) j⟩

def custodyCoeff (geometryCoeff : Nat) : Nat := geometryCoeff

def timeCoeff (geometryCoeff bL patrol : Nat) : Nat :=
  custodyCoeff geometryCoeff + 2^(5*bL+65) + 7 + (2049 + patrol)

/-- Packed deployments no longer run the observer or modular public row. -/
def compactTimeCoeff (g bL patrol : Nat) : Nat :=
  max (g + 2^(5*bL+65)) (2049+patrol)

/-- Fixed-layout charts may have different header counts at the same n.
The level map is the coherent increment count measured from a stopped epoch. -/
structure G9Data (S : Type) (n : Nat) where
  row : S × S → S × S
  leader : S → Bool
  reference : S → Bool
  cust : (Fin n → S) → Prop
  marked : (Fin n → S) → Prop
  Chart : Type
  State : Chart → Type
  m : Chart → Nat
  hm : ∀ j, 0 < m j
  r : Nat
  width : Chart → Nat
  clock : ∀ j, Recover.Chain.ClockChain (State j) n (m j) (heightMod r) (modulus r) (hm j)
  raw : ∀ j, State j → Fin n → S
  opening : ∀ j, State j → Nat
  level : ∀ j, State j → List (Fin n) → Fin (m j) → Nat

variable {S : Type} {n : Nat}

def G9Data.next (D : G9Data S n) (hn : 0 < n) :
    (Fin n → S) → Fin n → (Fin n → S) :=
  PopulationProtocol.step ⟨S, Bool, (fun a b => D.row (a,b)), D.leader⟩ ⟨hn⟩

def G9Data.display (D : G9Data S n) (hn : 0 < n) :=
  Permanent (D.next hn) (fun x i => D.reference (x i))

def G9Data.elected (D : G9Data S n) (hn : 0 < n) :=
  Permanent (D.next hn) (fun x i => D.leader (x i))

def G9Data.scale (D : G9Data S n) (bL : Nat) := 2^(5*bL+34)*n*D.r
def G9Data.block (D : G9Data S n) (j : D.Chart) := 2^21*n*D.width j

def G9Data.deadline (D : G9Data S n) (bL : Nat) (j : D.Chart) :=
  physicalDeadline (D.scale bL) (D.m j)

/-- The crossing from cap to cap+1 publishes the phase-zero display. -/
def G9Data.miss (D : G9Data S n) (j : D.Chart) (z : D.State j) (u : List (Fin n)) : Prop :=
  ∃ i, D.level j z u i ≤ D.opening j z + 32*(2^19 * D.m j)

noncomputable def failureCount {k : Nat} (F : List (Fin k) → Prop) (t : Nat) :=
  wordSum (fun u => if F u then 1 else 0) t

/-- Physical conformance and quantitative obligations for both production
branches. Chart obligations concern only custody epochs. The marked predicate
includes the certificate that subsequent public steps are ordinary. -/
structure G9Interfaces (D : G9Data S n) (hn : 0 < n) (geometryCoeff bL patrol : Nat) : Prop where
  bounded : n ≤ 2^32 → ∀ x, IIDExpectedHittingTimeAtMost (D.next hn) (D.elected hn) x
    ((2049+patrol)*n^2)
  custody : 2^32 < n → ∀ x, IIDExpectedHittingTimeAtMost (D.next hn) D.cust x
    (custodyCoeff geometryCoeff*n^2)
  liftCustody : 2^32 < n → ∀ x, D.cust x → ∃ j z, D.raw j z = x ∧
    Recover.StageTwo.WellFormed (modulus D.r) ((D.clock j).cfg z)
  rawStep : ∀ j z e, D.raw j ((D.clock j).next z e) = D.next hn (D.raw j z) e
  parameters : ∀ j : D.Chart, Recover.StageTwo.ClockParams (modulus D.r) ∧
    D.m j / 2 < modulus D.r / 2 ∧ 0 < D.block j ∧
    4*(2^(5*bL+1)*D.block j) ≤ D.scale bL ∧ D.m j * D.r ≤ n
  service : ∀ j i z, n^(D.block j) ≤ 2^(5*bL+1) *
    RawService.publicationMass (D.clock j).next ((D.clock j).served i) z (D.block j)
  displaySplit : ∀ j z, Recover.Chain.LgSet (D.clock j) z → ¬D.display hn (D.raw j z) →
    4 * failureCount (fun w => ¬D.display hn (D.raw j (runWord (D.clock j).next z w)))
        (D.deadline bL j) ≤
      n^(D.deadline bL j) + 4 * failureCount (D.miss j z) (D.deadline bL j)
  missQuarter : ∀ j z, Recover.Chain.LgSet (D.clock j) z → ¬D.display hn (D.raw j z) →
    4 * failureCount (D.miss j z) (D.deadline bL j) ≤ n^(D.deadline bL j)
  observer : 2^32 < n → ∀ x, D.display hn x →
    IIDExpectedHittingTimeAtMost (D.next hn) D.marked x (5*n^2 + 7*n)
  publicSuffix : 2^32 < n → ∀ x, D.marked x →
    IIDExpectedHittingTimeAtMost (D.next hn) (D.elected hn) x ((2049+patrol)*n^2)

/-- Only the chart obligations used by the direct packed readout. -/
structure PackedDisplayInputs (D : G9Data S n) (hn : 0 < n) (bL : Nat) : Prop where
  liftCustody : 2^32 < n → ∀ x, D.cust x → ∃ j z, D.raw j z = x ∧
    Recover.StageTwo.WellFormed (modulus D.r) ((D.clock j).cfg z)
  rawStep : ∀ j z e, D.raw j ((D.clock j).next z e) = D.next hn (D.raw j z) e
  parameters : ∀ j : D.Chart, Recover.StageTwo.ClockParams (modulus D.r) ∧
    D.m j / 2 < modulus D.r / 2 ∧ 0 < D.block j ∧
    4*(2^(5*bL+1)*D.block j) ≤ D.scale bL ∧ D.m j * D.r ≤ n
  service : ∀ j i z, n^(D.block j) ≤ 2^(5*bL+1) *
    RawService.publicationMass (D.clock j).next ((D.clock j).served i) z (D.block j)
  displaySplit : ∀ j z, Recover.Chain.LgSet (D.clock j) z → ¬D.display hn (D.raw j z) →
    4 * failureCount (fun w => ¬D.display hn (D.raw j (runWord (D.clock j).next z w)))
        (D.deadline bL j) ≤
      n^(D.deadline bL j) + 4 * failureCount (D.miss j z) (D.deadline bL j)
  missQuarter : ∀ j z, Recover.Chain.LgSet (D.clock j) z → ¬D.display hn (D.raw j z) →
    4 * failureCount (D.miss j z) (D.deadline bL j) ≤ n^(D.deadline bL j)

/-- First hit the intermediate stage, with early success also permitted. -/
private theorem addStages {X : Type} (next : X → Fin n → X) (hn : 0 < n)
    {A P : X → Prop} {x : X} {a b : Nat}
    (h : IIDExpectedHittingTimeAtMost next A x a)
    (k : ∀ y, A y → IIDExpectedHittingTimeAtMost next P y b) :
    IIDExpectedHittingTimeAtMost next P x (a+b) := by
  refine iid_stage_le next hn x A P a b ?_ k
  intro t
  have ha := h t
  rw [iidHitCost_eq_costNumerator] at ha ⊢
  exact Nat.le_trans (L3.Prob.costNumerator_target_mono next A _ (fun _ hy => Or.inl hy) x t) ha

/-- Any deterministic projection commuting with the same raw letters preserves
every finite-horizon cost for a target on the projected state. -/
theorem projection_cost {X Y : Type} (f : X → Y) (a : X → Fin n → X) (b : Y → Fin n → Y)
    (h : ∀ x e, f (a x e) = b (f x) e) (P : Y → Prop) (t : Nat) (x : X) :
    iidHitCost a (fun z => P (f z)) t x = iidHitCost b P t (f x) := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    by_cases hp : P (f x)
    · simp only [iidHitCost, if_pos hp]
    · simp only [iidHitCost, if_neg hp, ih, h]

/-- The verified seventeen-scale repair still fits the paper coefficient. -/
private theorem chart_budget (bL n r m : Nat) (width : m*r ≤ n) :
    17*(2^(5*bL+34)*n*r)*m + 2*physicalDeadline (2^(5*bL+34)*n*r) m
      ≤ 2^(5*bL+65)*n^2 := by
  rw [twice_physicalDeadline]
  let L := 2^(5*bL+34)*n*r
  change 17*L*m + 2^30*L*m ≤ _
  have c : 17+2^30 ≤ 2^31 := by decide
  have h := Nat.mul_le_mul_right m (Nat.mul_le_mul_right L c)
  rw [Nat.add_mul, Nat.add_mul] at h
  refine Nat.le_trans h ?_
  have pr : 2^31 * 2^(5*bL+34) = 2^(5*bL+65) := by
    rw [← Nat.pow_add, show 31+(5*bL+34) = 5*bL+65 by omega]
  calc
    2^31*L*m = (2^31*2^(5*bL+34)) * n * (m*r) := by dsimp [L]; ac_rfl
    _ ≤ (2^31*2^(5*bL+34)) * n * n := Nat.mul_le_mul_left _ width
    _ = 2^(5*bL+65)*n^2 := by rw [pr, Nat.pow_two, Nat.mul_assoc]

theorem custody_to_display_core (D : G9Data S n) (hn : 0 < n) {bL : Nat}
    (H : PackedDisplayInputs D hn bL) (hp : 2^32 < n) (x : Fin n → S) (hx : D.cust x) :
    IIDExpectedHittingTimeAtMost (D.next hn) (D.display hn) x (2^(5*bL+65)*n^2) := by
  obtain ⟨j,z,rfl,hz⟩ := H.liftCustody hp x hx
  let C := D.clock j
  let R := fun y => D.display hn (D.raw j y)
  obtain ⟨hM,hd,hH,hs,hw⟩ := H.parameters j
  have hdpos : 1 ≤ 2^(5*bL+1) := Nat.two_pow_pos _
  have hpos := Nat.mul_pos hdpos hH
  have hL : 1 ≤ D.scale bL := by omega
  have hmom i := RawService.publication_moment_of_block C.next (C.served i)
    (D.block j) (2^(5*bL+1)) (D.scale bL) hH hdpos hs (H.service j i)
  have rep := clock_repair C hM hd hL (D.hm j) hmom z hz
  have hR : ∀ y e, R y → R (C.next y e) := by
    intro y e hy
    change D.display hn (D.raw j ((D.clock j).next y e))
    rw [H.rawStep]
    exact permanent_closed _ _ _ _ hy
  have trial (y : D.State j) (hy : Recover.Chain.LgSet C y) (hr : ¬ R y) :
      2 * wordSum (fun w => if R (runWord C.next y w) then 0 else 1)
        (D.deadline bL j) ≤ n^(D.deadline bL j) := by
    have s := H.displaySplit j y hy hr
    have q := H.missQuarter j y hy hr
    have hh : 2*failureCount (fun w => ¬R (runWord C.next y w)) (D.deadline bL j)
        ≤ n^(D.deadline bL j) := by
      change 4*failureCount (fun w => ¬R (runWord C.next y w)) _ ≤ _ at s
      omega
    have compare :
        wordSum (fun w => if R (runWord C.next y w) then 0 else 1) (D.deadline bL j) =
          failureCount (fun w => ¬R (runWord C.next y w)) (D.deadline bL j) := by
      unfold failureCount
      apply wordSum_congr_fun
      intro w
      by_cases hc : R (runWord C.next y w) <;> simp [hc]
    rw [compare]
    exact hh
  have finish := addStages C.next hn rep (fun y hy =>
    restart_mean C.next R (Recover.Chain.LgSet C) hR (Recover.Chain.lg_closed C hM)
      trial y hy)
  have small := expected_bound_mono C.next R z finish (chart_budget bL n D.r (D.m j) hw)
  intro t
  rw [← projection_cost (D.raw j) C.next (D.next hn) (H.rawStep j)]
  exact small t

theorem custody_to_display (D : G9Data S n) (hn : 0 < n) {g bL p : Nat}
    (H : G9Interfaces D hn g bL p) (hp : 2^32 < n) (x : Fin n → S) (hx : D.cust x) :
    IIDExpectedHittingTimeAtMost (D.next hn) (D.display hn) x (2^(5*bL+65)*n^2) :=
  custody_to_display_core D hn
    ⟨H.liftCustody,H.rawStep,H.parameters,H.service,H.displaySplit,H.missQuarter⟩ hp x hx

theorem packed_reference_expected (D : G9Data S n) (hn : 0 < n) {g bL : Nat}
    (H : PackedDisplayInputs D hn bL) (hp : 2^32 < n) (x : Fin n → S)
    (hc : IIDExpectedHittingTimeAtMost (D.next hn) D.cust x (g*n^2)) :
    IIDExpectedHittingTimeAtMost (D.next hn) (D.display hn) x ((g+2^(5*bL+65))*n^2) := by
  rw [Nat.add_mul]
  exact addStages (D.next hn) hn hc (custody_to_display_core D hn H hp)

/-- First entrance into the fixed-winner class from every Cartesian start. -/
theorem physical_expected (D : G9Data S n) (hfour : 4 ≤ n) {g bL p : Nat}
    (H : G9Interfaces D (by omega) g bL p) (x : Fin n → S) :
    UniformFirstHit.ExpectedHittingTimeAtMost (D.next (by omega)) (D.elected (by omega)) x
      ((timeCoeff g bL p * n^2 : Nat) : Rat) := by
  have hn : 0 < n := by omega
  apply (iid_expected_iff_leader _ _ hn _ _).1
  by_cases hb : n ≤ 2^32
  · exact expected_bound_mono _ _ _ (H.bounded hb x)
      (Nat.mul_le_mul_right (n^2) (Nat.le_add_left (2049+p) (custodyCoeff g+2^(5*bL+65)+7)))
  · have hp := Nat.lt_of_not_ge hb
    have suffix (y) (hy : D.display hn y) := addStages (D.next hn) hn
      (expected_bound_mono _ _ _ (H.observer hp y hy) (observer n hfour)) (H.publicSuffix hp)
    have pack := addStages (D.next hn) hn (H.custody hp x) (fun y hy =>
      addStages (D.next hn) hn (custody_to_display D hn H hp y hy) suffix)
    have eqn : custodyCoeff g*n^2 + (2^(5*bL+65)*n^2 + (7*n^2+(2049+p)*n^2)) =
        timeCoeff g bL p * n^2 := by simp only [timeCoeff, Nat.add_mul]; ac_rfl
    rw [← eqn]
    exact pack

/-- Use the same deployed map and public readout at every size of one advice band. -/
def G9Data.withProtocol (D : G9Data S n) (row : S × S → S × S) (leader : S → Bool) :
    G9Data S n := { D with row := row, leader := leader }

/-- The pair map and the site alphabet are chosen using only the advice.
The preliminary and patrol coefficients are fixed before the circumference. -/
theorem all_sizes_expected (Site : Nat → Type)
    (row : ∀ s, Site s × Site s → Site s × Site s)
    (leader : ∀ s, Site s → Bool) (g patrol : Nat)
    (model : ∀ n, G9Data (Site (ceilingLogTwo (ceilingLogTwo n))) n)
    (interfaces : ∀ n (h : 4 ≤ n),
      let s := ceilingLogTwo (ceilingLogTwo n)
      G9Interfaces ((model n).withProtocol (row s) (leader s)) (by omega) g (2^32) patrol)
    (n : Nat) (h : 4 ≤ n) (x : Fin n → Site (ceilingLogTwo (ceilingLogTwo n))) :
    let s := ceilingLogTwo (ceilingLogTwo n)
    let step := PopulationProtocol.step ⟨Site s, Bool, (fun a b => row s (a,b)), leader s⟩
      (⟨by omega⟩ : DirectedRing n)
    UniformFirstHit.ExpectedHittingTimeAtMost step
      (Permanent step (fun y i => leader s (y i))) x
      ((timeCoeff g (2^32) patrol * n^2 : Nat) : Rat) := by
  exact physical_expected _ h (interfaces n h) x

end L4.Height.G9Spine

