import Leader.L4.TripleRenewal

/-! Dyadic root-rank absorption on the quiet entrance class.
The affine local-block estimate is a separate paper input, not a
consequence of the uniform whole-ring first-retirement estimate. -/
namespace L4.RankBlockContraction
open TaggedTail RankRenewal RankPhysical TripleRenewal Classical

/-- Exact numerator form of the block contraction. A block with scale
L uses B*n*L marks. This is not included in ConcreteBoundedRank. -/
def ConcreteRankBlock : Prop :=
  ∀ c : Nat, 12≤c → ∃ B C₀ : Nat, 0<B ∧ 0<C₀ ∧
    ∀ {p n : Nat} (x : Config p c n) (L : Nat),
      2≤p → 4≤n → (¬ p ∣ n) → QuietEntrance x → 1≤L → L≤n →
      4*L*endpointSum step rank (B*n*L) x ≤
        (L*rank x+4*C₀*n)*n^(B*n*L)

/-- Global quadratic root-rank entrance from the quiet class. -/
def ConcreteRankOneMean : Prop :=
  ∀ c : Nat, 12≤c → ∃ A : Nat, ∀ {p n : Nat} (x : Config p c n),
    2≤p → 4≤n → (¬ p ∣ n) → QuietEntrance x →
    IIDExpectedHittingTimeAtMost step (fun y => rank y=1) x (A*n^2)

private theorem sSucc {n : Nat} (f : Fin (n+1) → Nat) :
    sumEdge f = f 0 + sumEdge (fun i : Fin n => f i.succ) := by
  simp [sumEdge,List.ofFn_succ]

private theorem sMono {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i≤g i) :
    sumEdge f≤sumEdge g := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sSucc,sSucc]; exact Nat.add_le_add (h _) (ih (fun i => h i.succ))

private theorem sMul {n : Nat} (a : Nat) (f : Fin n → Nat) :
    sumEdge (fun e => a*f e)=a*sumEdge f := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sSucc,sSucc f,ih,Nat.mul_add]

private theorem sConst (n a : Nat) : sumEdge (fun _ : Fin n => a)=n*a := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sSucc,ih,Nat.succ_mul,Nat.add_comm]

private theorem sPick {n : Nat} (i : Fin n) :
    sumEdge (fun e => if e=i then 1 else 0)=1 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [sSucc]
      simp [show (fun i : Fin n => if i.succ=(0 : Fin (n+1)) then 1 else 0) =
        (fun _ => 0) from funext (fun i => by simp [Fin.succ_ne_zero]),sConst]
    · rw [sSucc,if_neg (Ne.symm (Fin.succ_ne_zero j))]
      simpa using ih j

/-- Literal rank never exceeds the number of sites. -/
theorem rank_le_size {p c n : Nat} (x : Config p c n) : rank x≤n := by
  unfold rank
  have h := sMono (f := fun e => (x e).mark.toNat) (g := fun _ : Fin n => 1)
    (fun i => by cases (x i).mark <;> decide)
  simpa only [sConst,Nat.mul_one] using h

/-- A quiet configuration retains at least one marked identity. -/
theorem quiet_rank_pos {p c n : Nat} {x : Config p c n} (hx : QuietEntrance x) :
    0<rank x := by
  obtain ⟨i,hi⟩ := hx.2.2.1
  have h := sMono (f := fun e => if e=i then 1 else 0)
    (g := fun e => (x e).mark.toNat) (fun e => by
      by_cases he : e=i
      · subst e; simp [hi]
      · simp [he])
  rw [sPick] at h
  exact h

private theorem survival_threshold {α : Type} {n : Nat} (next : α → Fin n → α)
    (R : α → Nat) (r t : Nat) (x : α) :
    r*survival next (fun y => r/2<R y) t x ≤ 2*endpointSum next R t x := by
  induction t generalizing x with
  | zero =>
    by_cases h : r/2<R x
    · simp [survival,weightedSurvival,endpointSum,h]; omega
    · simp [survival,weightedSurvival,endpointSum,h]
  | succ t ih =>
    by_cases h : r/2<R x
    · simp only [survival,weightedSurvival,h,if_true,endpointSum,←sMul]
      exact sMono (fun e => ih (next x e))
    · simp [survival,weightedSurvival,h]

/-- A block with L*r ≥ 8*C₀*n fails to halve rank with probability at
most three quarters. Exact cleared-denominator form. -/
theorem halfBlock_of_affine {α : Type} {n : Nat} (next : α → Fin n → α)
    (R : α → Nat) (x : α) (r L C₀ t : Nat)
    (hr : 0<r) (hL : 0<L) (hR : R x≤r) (hscale : 8*C₀*n≤L*r)
    (affine : 4*L*endpointSum next R t x ≤ (L*R x+4*C₀*n)*n^t) :
    4*survival next (fun y => r/2<R y) t x ≤ 3*n^t := by
  let S := survival next (fun y => r/2<R y) t x
  let E := endpointSum next R t x
  change 4*S≤3*n^t
  have h := Nat.mul_le_mul_left (2*L) (survival_threshold next R r t x)
  have hQ : 2*L*r*S≤4*L*E := by
    change (2*L)*(r*S) ≤ (2*L)*(2*E) at h
    calc
      _ = (2*L)*(r*S) := by ac_rfl
      _ ≤ (2*L)*(2*E) := h
      _ = _ := by ac_rfl
  have h' : 2*L*r*S≤(L*r+4*C₀*n)*n^t :=
    Nat.le_trans (Nat.le_trans hQ affine)
      (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.mul_le_mul_left _ hR) _))
  have hs : 2*(L*r+4*C₀*n)≤3*(L*r) := by
    have hh : 2*(4*C₀*n)=8*C₀*n := by ac_rfl
    rw [Nat.mul_add,hh]; omega
  apply Nat.le_of_mul_le_mul_left _ (Nat.mul_pos hL hr)
  calc
    _ = 2*(2*L*r*S) := by ac_rfl
    _ ≤ 2*((L*r+4*C₀*n)*n^t) := Nat.mul_le_mul_left _ h'
    _ = (2*(L*r+4*C₀*n))*n^t := by ac_rfl
    _ ≤ (3*(L*r))*n^t := Nat.mul_le_mul_right _ hs
    _ = _ := by ac_rfl

/-- Restartable halving in a fixed slab, from the exact common-block
survival bound. Stopping at rank ≤r/2 is irreversible in the slab. -/
theorem halfMean {α : Type} {n : Nat} (next : α → Fin n → α)
    (R : α → Nat) (r H : Nat) (hH : 0<H)
    (mono : ∀ x e, R (next x e)≤R x)
    (block : ∀ x, r/2<R x →
      4*survival next (fun y => r/2<R y) H x≤3*n^H)
    (x : α) : IIDExpectedHittingTimeAtMost next (fun y => R y≤r/2) x (4*H) := by
  let flag (y : α) := if R y≤r/2 then 0 else 1
  have hflag (y : α) : flag y≤1 := by unfold flag; split <;> omega
  have monoFlag (y : α) (e : Fin n) : flag (next y e)≤flag y := by
    by_cases hy : R y≤r/2
    · have hh := Nat.le_trans (mono y e) hy
      simp [flag,hy,hh]
    · simpa [flag,hy] using hflag (next y e)
  have hzero : ∀ y, flag y=0 → R y≤r/2 := by
    intro y hy
    by_cases h : R y≤r/2
    · exact h
    · simp [flag,h] at hy
  have htrial (y : α) (hy : 0<flag y) :
      4*survival next (fun z => flag y≤flag z) H y≤(4-1)*n^H := by
    have hlt : r/2<R y := by
      by_cases h : R y≤r/2
      · simp [flag,h] at hy
      · omega
    have hFy : flag y=1 := by have := hflag y; omega
    have hfun : (fun z => flag y≤flag z) = (fun z => r/2<R z) := by
      funext z; apply propext
      by_cases hz : R z≤r/2 <;> simp [flag,hFy,hz] <;> omega
    rw [hfun]
    exact block y hlt
  simpa [Nat.mul_comm] using
    expected_of_rank_trial_certificate (next := next) flag (fun y => R y≤r/2)
      hzero monoFlag H 4 1 hH (by decide) htrial x (hflag x)

private def quietStage {p c n : Nat} (x : Config p c n)
    (hp : 2≤p) (hc : 12≤c) (hn : 4≤n) (hnd : ¬p∣n) (hx : QuietEntrance x)
    (ready : Config p c n → Prop) : Stage step x where
  State := Config p c n
  start := x
  next := step
  project := id
  ready := ready
  reachable := QuietEntrance
  projInit := rfl
  projStep := fun _ _ => rfl
  reachStart := hx
  reachStep := fun y e hy => quiet_step y e hp hc hn hnd hy

/-- Exact one-slab dyadic contraction on physical marks. -/
theorem physical_half_mean {p c n : Nat} (x : Config p c n)
    (hp : 2≤p) (hc : 12≤c) (hn : 4≤n) (hnd : ¬p∣n) (hx : QuietEntrance x)
    (B C₀ r L : Nat) (hB : 0<B) (hr : 0<r) (hL : 0<L) 
    (hR : rank x≤r) (hscale : 8*C₀*n≤L*r)
    (blocks : ∀ y : Config p c n, QuietEntrance y →
      4*L*endpointSum step rank (B*n*L) y ≤
        (L*rank y+4*C₀*n)*n^(B*n*L)) :
    IIDExpectedHittingTimeAtMost step (fun y => rank y≤r/2) x (4*(B*n*L)) := by
  let S := {y : Config p c n // QuietEntrance y ∧ rank y≤r}
  let lift (y : S) (e : Fin n) : S :=
    ⟨step y.val e,quiet_step y.val e hp hc hn hnd y.property.1,
      Nat.le_trans (rank_step_le hn y.val e y.property.1.1) y.property.2⟩
  let start : S := ⟨x,hx,hR⟩
  have hh := halfMean lift (fun y => rank y.val) r (B*n*L)
    (Nat.mul_pos (Nat.mul_pos hB (by omega)) hL)
    (fun y e => rank_step_le hn y.val e y.property.1.1) (fun y _ => by
      rw [equal_survival_of_projection step lift (fun z => r/2<rank z)
        (fun z : S => z.val) (fun _ _ => rfl)]
      exact halfBlock_of_affine step rank y.val r L C₀ (B*n*L) hr hL y.property.2 hscale
        (blocks y.val y.property.1)) start
  intro t
  have h := EntranceCover.iidHitCost_le_of_projection step lift
    (fun y => rank y≤r/2) (fun y : S => rank y.val≤r/2)
    (fun y : S => y.val) (fun _ _ => rfl) (fun _ h => h) t start
  exact Nat.le_trans h (hh t)

/-- At most r whole-ring first-retirement trials pay for all remaining
rank changes when the current rank is ≤r. In the dyadic proof r will
be an absolute cutoff, not the initial rank n. -/
theorem small_rank_cost {p c n : Nat} (hp : 2≤p) (hc : 12≤c) (hn : 4≤n) (hnd : ¬p∣n)
    (A : Nat) (retire : ∀ y : Config p c n, QuietEntrance y → 2≤rank y →
      IIDExpectedHittingTimeAtMost step (fun z => rank z<rank y) y (A*n^2))
    (r : Nat) (x : Config p c n) (hx : QuietEntrance x) (hxR : rank x≤r) :
    IIDExpectedHittingTimeAtMost step (fun y => rank y=1) x ((A*n^2)*r) := by
  induction r generalizing x with
  | zero => have h := quiet_rank_pos hx; omega
  | succ r ih =>
    by_cases he : rank x=1
    · intro t; rw [iidHitCost_of_target step (fun y => rank y=1) x he]; exact Nat.zero_le _
    · have h2 : 2≤rank x := by have h := quiet_rank_pos hx; omega
      let s := quietStage x hp hc hn hnd hx (fun z => rank z<rank x)
      have hh := expected_with_preparation s (fun z => rank z=1) (A*n^2) ((A*n^2)*r)
        (retire x hx h2) (fun y hy hReady _ => ih y hy (by change rank y<rank x at hReady; omega))
      refine expected_mono hh ?_
      rw [Nat.mul_succ,Nat.add_comm]
      exact Nat.le_refl _

private theorem pow2_pos (j : Nat) : 0 < (2 : Nat)^j := Nat.pow_pos (by decide)

private theorem div_half (n j : Nat) :
    n/2^(j+1) = (n/2^j)/2 := by rw [Nat.pow_succ,Nat.div_div_eq_div_mul]

private theorem dyadic_budget (n j : Nat) :
    (n/2^(j+1)+1)+(n-n/2^j+j) ≤ n-n/2^(j+1)+(j+1) := by
  have hj := Nat.div_le_self n (2^j)
  have hk := Nat.div_le_self n (2^(j+1))
  have h := Nat.mul_div_le (n/2^j) 2
  rw [div_half]
  rw [div_half] at hk
  omega

private theorem scale_ge (n M j : Nat) :
    M*n ≤ (n/2^(j+1)+1)*(M*2^(j+1)) := by
  have hh : n≤(n/2^(j+1)+1)*2^(j+1) := by
    have h := Nat.mod_add_div n (2^(j+1))
    have hh := Nat.mod_lt n (pow2_pos (j+1))
    rw [Nat.add_mul,Nat.one_mul]
    rw [Nat.mul_comm (n/2^(j+1)) (2^(j+1))]
    omega
  calc
    _ ≤ M*((n/2^(j+1)+1)*2^(j+1)) := Nat.mul_le_mul_left M hh
    _ = _ := by ac_rfl

private theorem pow2_ge (n : Nat) : n≤(2:Nat)^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h := pow2_pos n
    rw [Nat.pow_succ]
    omega

/-- Dyadic absorption with an explicit paper-style coefficient. The
scales are L_j=floor(n/2^j)+1, with rank caps (8*C₀)*2^j.
Starting at j=n is safe and the summable cost still follows from exact
integer telescoping; the many vacuous large caps cost nothing in reality. -/
theorem rankOne_mean_of_local_data {p c n : Nat} (x : Config p c n)
    (hp : 2≤p) (hc : 12≤c) (hn : 4≤n) (hnd : ¬p∣n) (hx : QuietEntrance x)
    (A B C₀ : Nat) (hB : 0<B) (hC : 0<C₀)
    (retire : ∀ y : Config p c n, QuietEntrance y → 2≤rank y →
      IIDExpectedHittingTimeAtMost step (fun z => rank z<rank y) y (A*n^2))
    (blocks : ∀ (y : Config p c n) (L : Nat), QuietEntrance y → 1≤L → L≤n →
      4*L*endpointSum step rank (B*n*L) y ≤ (L*rank y+4*C₀*n)*n^(B*n*L)) :
    IIDExpectedHittingTimeAtMost step (fun y => rank y=1) x ((8*B+8*C₀*A)*n^2) := by
  let M := 8*C₀
  let q := (A*n^2)*M
  let b := 4*B*n
  have hM : 0<M := by dsimp [M]; omega
  have stages (j : Nat) (z : Config p c n) (hz : QuietEntrance z) (hr : rank z≤M*2^j) :
      IIDExpectedHittingTimeAtMost step (fun y => rank y=1) z (b*(n-n/2^j+j)+q) := by
    induction j generalizing z with
    | zero =>
      simp only [Nat.pow_zero,Nat.div_one,Nat.sub_self,Nat.add_zero,Nat.mul_zero,Nat.zero_add] at *
      exact small_rank_cost hp hc hn hnd A retire M z hz (by simpa using hr)
    | succ j ih =>
      let r := M*2^(j+1)
      let L := n/2^(j+1)+1
      have hL : 0<L := Nat.succ_pos _
      have hLn : L ≤ n := by
        have hp2 : 1 < (2:Nat)^(j+1) := by
          have hpos := pow2_pos j
          rw [Nat.pow_succ]; omega
        have hh := Nat.div_lt_self (by omega : 0<n) hp2
        dsimp [L]
        omega
      have hR : 0<r := Nat.mul_pos hM (pow2_pos (j+1))
      have hs : 8*C₀*n≤L*r := scale_ge n M j
      have half := physical_half_mean z hp hc hn hnd hz B C₀ r L hB hR hL hr hs
        (fun y hy => blocks y L hy hL hLn)
      let s := quietStage z hp hc hn hnd hz (fun y => rank y≤r/2)
      have he : r/2=M*2^j := by
        dsimp [r]
        rw [Nat.pow_succ,←Nat.mul_assoc,Nat.mul_div_left _ (by decide)]
      have recomp := expected_with_preparation s (fun y => rank y=1) (4*(B*n*L))
        (b*(n-n/2^j+j)+q) half (fun y hy hr' _ =>
          ih y hy (by change rank y≤r/2 at hr'; rwa [he] at hr'))
      refine expected_mono recomp ?_
      have hbudget := Nat.mul_le_mul_left b (dyadic_budget n j)
      rw [Nat.mul_add] at hbudget
      calc
        _ = (b*L+b*(n-n/2^j+j))+q := by
          have h : 4*(B*n*L)=b*L := by dsimp [b]; ac_rfl
          rw [h,Nat.add_assoc]
        _ ≤ b*(n-n/2^(j+1)+(j+1))+q := Nat.add_le_add_right hbudget _
  have hxR : rank x≤M*2^n :=
    Nat.le_trans (rank_le_size x) (Nat.le_trans (pow2_ge n) (Nat.le_mul_of_pos_left _ hM))
  refine expected_mono (stages n x hx hxR) ?_
  have hbnd : n-n/2^n+n≤2*n := by
    rw [Nat.two_mul]; exact Nat.add_le_add_right (Nat.sub_le ..) _
  calc
    _ ≤ b*(2*n)+q := Nat.add_le_add_right (Nat.mul_le_mul_left _ hbnd) _
    _ = (8*B+8*C₀*A)*n^2 := by
      dsimp [b,q,M]
      rw [Nat.pow_two,Nat.add_mul]
      have he : 4*B*n*(2*n) = (4*2)*B*(n*n) := by ac_rfl
      rw [he,show (4:Nat)*2=8 by decide]
      congr 1
      ac_rfl

/-- The exact all-rank endpoint, conditional on the distinct global
first-retirement and local block interfaces. -/
theorem rankOne_mean_of_boundedRank_and_block
    (retirement : ConcreteBoundedRank) (blocks : ConcreteRankBlock) : ConcreteRankOneMean := by
  intro c hc
  obtain ⟨A,retire⟩ := retirement c hc
  obtain ⟨B,C₀,hB,hC,block⟩ := blocks c hc
  refine ⟨8*B+8*C₀*A,?_⟩
  intro p n x hp hn hnd hx
  exact rankOne_mean_of_local_data x hp hc hn hnd hx A B C₀ hB hC
    (fun y hy hr => retire y hp hn hnd hy hr)
    (fun y L hy hL hLn => block y L hp hn hnd hy hL hLn)

private theorem eMono {α : Type} {n : Nat} (next : α → Fin n → α)
    (f g : α → Nat) (h : ∀ x, f x≤g x) (t : Nat) (x : α) :
    endpointSum next f t x≤endpointSum next g t x := by
  induction t generalizing x with
  | zero => exact h x
  | succ t ih => exact sMono (fun e => ih _)

private theorem sAdd {n : Nat} (f g : Fin n → Nat) :
    sumEdge (fun e => f e+g e)=sumEdge f+sumEdge g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sSucc,sSucc f,sSucc g,ih]; omega

private theorem eAdd {α : Type} {n : Nat} (next : α → Fin n → α)
    (f g : α → Nat) (t : Nat) (x : α) :
    endpointSum next (fun y => f y+g y) t x=endpointSum next f t x+endpointSum next g t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih => simp only [endpointSum,ih,sAdd]

private theorem eMul {α : Type} {n : Nat} (next : α → Fin n → α)
    (f : α → Nat) (a t : Nat) (x : α) :
    endpointSum next (fun y => a*f y) t x=a*endpointSum next f t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih => simp only [endpointSum,ih,sMul]

private theorem eConst {α : Type} {n : Nat} (next : α → Fin n → α)
    (a t : Nat) (x : α) : endpointSum next (fun _ => a) t x=a*n^t := by
  induction t generalizing x with
  | zero => simp [endpointSum]
  | succ t ih =>
    simp only [endpointSum,ih,sConst,Nat.pow_succ]
    ac_rfl

private theorem eList {α : Type} {n : Nat} (next : α → Fin n → α)
    (events : List (α → Nat)) (t : Nat) (x : α) :
    endpointSum next (fun y => (events.map (fun f => f y)).sum) t x =
      (events.map (fun f => endpointSum next f t x)).sum := by
  induction events with
  | nil => simp [eConst]
  | cons f fs ih => simp [eAdd,ih]

/-- Exact local-group averaging. Each short group succeeds with
probability at least 12/25; the total number of successes is charged
at most seven times to rank losses. The history-dependent marks may
correlate every event. H bounds how many cyclic starts were not short.
The states may retain lineage/initial groups in a proof observer. -/
theorem one_block_of_group_rewards {α : Type} {n : Nat} (next : α → Fin n → α)
    (R : α → Nat) (x : α) (H T : Nat) (events : List (α → Nat))
    (many : R x ≤ events.length + H)
    (success : ∀ f ∈ events, 12*n^T ≤ 25*endpointSum next f T x)
    (incidence : ∀ y, 7*R y + (events.map (fun f => f y)).sum ≤ 7*R x) :
    175*endpointSum next R T x ≤ (163*R x+12*H)*n^T := by
  let N := n^T
  let E := endpointSum next R T x
  let Z := (events.map (fun f => endpointSum next f T x)).sum
  have lower (fs : List (α → Nat)) (hs : ∀ f ∈ fs, 12*N≤25*endpointSum next f T x) :
      (12*fs.length)*N≤25*(fs.map (fun f => endpointSum next f T x)).sum := by
    induction fs with
    | nil => simp
    | cons f fs ih =>
      have h₁ := hs f (List.mem_cons_self ..)
      have h₂ := ih (fun g hg => hs g (List.mem_cons_of_mem _ hg))
      simp only [List.length_cons,List.map_cons,List.sum_cons,Nat.mul_add,Nat.mul_one]
      rw [Nat.add_mul]
      omega
  have hu := eMono next (fun y => 7*R y + (events.map (fun f => f y)).sum)
      (fun _ => 7*R x) incidence T x
  rw [eAdd,eMul,eList,eConst] at hu
  change 7*E+Z≤(7*R x)*N at hu
  have hU := Nat.mul_le_mul_left 25 hu
  have hL : (12*events.length)*N≤25*Z := lower events success
  have hm : (12*R x)*N ≤ (12*events.length)*N+(12*H)*N := by
    have hh := Nat.mul_le_mul_right N (Nat.mul_le_mul_left 12 many)
    rwa [Nat.mul_add 12,Nat.add_mul] at hh
  have he : 25*(7*E)=175*E := by rw [←Nat.mul_assoc]
  have hR : 25*((7*R x)*N)=(175*R x)*N := by rw [←Nat.mul_assoc,←Nat.mul_assoc]
  rw [Nat.mul_add,he,hR] at hU
  have hNum : (175*R x)*N = (163*R x)*N+(12*R x)*N := by
    rw [←Nat.add_mul,←Nat.add_mul]
  change 175*E≤(163*R x+12*H)*N
  rw [Nat.add_mul]
  omega

private theorem eComp {α : Type} {n : Nat} (next : α → Fin n → α)
    (f : α → Nat) (t u : Nat) (x : α) :
    endpointSum next f (t+u) x =
      endpointSum next (fun y => endpointSum next f u y) t x := by
  induction t generalizing x with
  | zero => simp [endpointSum]
  | succ t ih =>
    rw [show t+1+u=(t+u)+1 by omega]
    simp only [endpointSum,ih]

/-- Exact affine iteration with no probabilistic approximation and
no independence assumption beyond a fresh raw mark at each step. -/
theorem iterated_group_blocks {α : Type} {n : Nat} (next : α → Fin n → α)
    (R : α → Nat) (T H : Nat)
    (one : ∀ z, 175*endpointSum next R T z≤(163*R z+12*H)*n^T)
    (j : Nat) (x : α) :
    175^j*endpointSum next R (j*T) x + 163^j*H*n^(j*T) ≤
      163^j*R x*n^(j*T) + 175^j*H*n^(j*T) := by
  induction j with
  | zero => simp [endpointSum]
  | succ j ih =>
    let W := endpointSum next R (j*T) x
    let N := n^(j*T)
    let P := n^T
    have h := eMono next (fun y => 175*endpointSum next R T y)
      (fun y => P*(163*R y+12*H)) (fun z => by simpa only [Nat.mul_comm P] using one z)
      (j*T) x
    rw [eMul,←eComp,eMul,eAdd,eMul,eConst,←Nat.succ_mul] at h
    change 175*endpointSum next R ((j+1)*T) x≤P*(163*W+12*H*N) at h
    have hNP : n^((j+1)*T)=N*P := by
      rw [Nat.succ_mul,Nat.pow_add]
    have hcoeff : 163*(175^j*H*N)*P+175^j*P*(12*H*N)=175^(j+1)*H*(N*P) := by
      calc
        _ = ((163+12)*175^j)*(H*(N*P)) := by rw [Nat.add_mul,Nat.add_mul]; ac_rfl
        _ = _ := by rw [Nat.pow_succ]; ac_rfl
    rw [hNP]
    calc
      _ ≤ 175^j*(P*(163*W+12*H*N))+163^(j+1)*H*(N*P) := by
        rw [Nat.pow_succ 175, Nat.mul_assoc]
        exact Nat.add_le_add_right (Nat.mul_le_mul_left _ h) _
      _ = (163*P)*(175^j*W+163^j*H*N) + 175^j*P*(12*H*N) := by
        rw [Nat.pow_succ 163]
        simp only [Nat.mul_add]
        ac_rfl
      _ ≤ (163*P)*(163^j*R x*N+175^j*H*N) + 175^j*P*(12*H*N) :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ ih) _
      _ = 163^(j+1)*R x*(N*P) + (163*(175^j*H*N)*P+175^j*P*(12*H*N)) := by
        rw [Nat.pow_succ 163]
        simp only [Nat.mul_add]
        ac_rfl
      _ = _ := by rw [hcoeff]

/-- Thirty-two batches make the remaining coefficient at most 1/4.
With H*L≤C₀*n this is the exact affine Halving interface at scale L. -/
theorem affine_of_group_blocks {α : Type} {n : Nat} (next : α → Fin n → α)
    (R : α → Nat) (T H L C₀ : Nat)
    (one : ∀ z, 175*endpointSum next R T z≤(163*R z+12*H)*n^T)
    (hHL : H*L≤C₀*n) (x : α) :
    4*L*endpointSum next R (32*T) x≤(L*R x+4*C₀*n)*n^(32*T) := by
  let d := (175:Nat)^32
  let a := (163:Nat)^32
  let E := endpointSum next R (32*T) x
  let N := n^(32*T)
  have hh := iterated_group_blocks next R T H one 32 x
  change d*E+a*H*N≤a*R x*N+d*H*N at hh
  have h₁ : d*E≤a*R x*N+d*H*N := Nat.le_trans (Nat.le_add_right ..) hh
  have hnum : 4*a≤d := by decide
  have hpos : 0<d := by decide
  have hA : 4*a*R x*N≤d*R x*N := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hnum)
  have hH : 4*L*H≤4*C₀*n := by
    calc
      _ = 4*(H*L) := by ac_rfl
      _ ≤ 4*(C₀*n) := Nat.mul_le_mul_left 4 hHL
      _ = _ := (Nat.mul_assoc ..).symm
  apply Nat.le_of_mul_le_mul_left _ hpos
  change d*(4*L*E)≤d*((L*R x+4*C₀*n)*N)
  calc
    _ = (4*L)*(d*E) := by ac_rfl
    _ ≤ (4*L)*(a*R x*N+d*H*N) := Nat.mul_le_mul_left _ h₁
    _ = L*(4*a*R x*N)+(d*N)*(4*L*H) := by rw [Nat.mul_add]; ac_rfl
    _ ≤ L*(d*R x*N)+(d*N)*(4*C₀*n) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hA) (Nat.mul_le_mul_left _ hH)
    _ = _ := by rw [Nat.add_mul,Nat.mul_add]; ac_rfl

private theorem eProjection {α β : Type} {n : Nat} (next : α → Fin n → α)
    (lift : β → Fin n → β) (f : α → Nat) (proj : β → α)
    (h : ∀ z e, proj (lift z e)=next (proj z) e) (T : Nat) (x : β) :
    endpointSum lift (fun z => f (proj z)) T x = endpointSum next f T (proj x) := by
  induction T generalizing x with
  | zero => rfl
  | succ T ih =>
    simp only [endpointSum,ih,h]

/-- Physical origin monitor for a list of successful short seven-groups.
Use reachable observer states as State, so incidence is only required
on states reachable by the original common marks. -/
structure GroupRewardCertificate {p c n : Nat} (x : Config p c n) (H T : Nat) where
  State : Type
  start : State
  next : State → Fin n → State
  project : State → Config p c n
  initial : project start=x
  projects : ∀ z e, project (next z e)=step (project z) e
  events : List (State → Nat)
  many : rank x≤events.length+H
  success : ∀ f ∈ events, 12*n^T ≤ 25*endpointSum next f T start
  incidence : ∀ y, 7*rank (project y)+(events.map (fun f => f y)).sum≤7*rank x

/-- Remaining local seven-group interface after finite-word averaging
and iteration. H is any common bound on the number of long windows,
with H*L≤C₀*n. The empty list covers low ranks when H dominates rank.
The literal group trial and group-origin facts are not asserted here. -/
def ConcreteSevenGroups : Prop :=
  ∀ c : Nat, 12≤c → ∃ B C₀ : Nat, 0<B ∧ 0<C₀ ∧
    ∀ (n L : Nat), 4≤n → 1≤L → L≤n →
    ∃ H : Nat, H*L≤C₀*n ∧
      ∀ {p : Nat} (x : Config p c n), 2≤p → (¬p∣n) → QuietEntrance x →
        Nonempty (GroupRewardCertificate x H (B*n*L))

/-- Compile the paper's local-group schema into its affine physical
block law. The horizon has a single global coefficient 32*B. -/
theorem rank_block_of_seven_data (data : ConcreteSevenGroups) : ConcreteRankBlock := by
  intro c hc
  obtain ⟨B,C₀,hB,hC,h⟩ := data c hc
  refine ⟨32*B,C₀,by omega,hC,?_⟩
  intro p n x L hp hn hnd hx hL hLn
  obtain ⟨H,hHL,group⟩ := h n L hn hL hLn
  let S := { y : Config p c n // QuietEntrance y }
  let lift (y : S) (e : Fin n) : S :=
    ⟨step y.val e,quiet_step y.val e hp hc hn hnd y.property⟩
  let start : S := ⟨x,hx⟩
  have one (y : S) : 175*endpointSum lift (fun z => rank z.val) (B*n*L) y≤
      (163*rank y.val+12*H)*n^(B*n*L) := by
    obtain ⟨o⟩ := group y.val hp hnd y.property
    have hg := one_block_of_group_rewards o.next (fun z => rank (o.project z))
      o.start H (B*n*L) o.events (by rw [o.initial]; exact o.many) o.success
      (fun z => by simpa only [o.initial] using o.incidence z)
    rw [eProjection step o.next rank o.project o.projects,o.initial] at hg
    rw [eProjection step lift rank (fun z : S => z.val) (fun _ _ => rfl)]
    exact hg
  have hh := affine_of_group_blocks lift (fun z => rank z.val) (B*n*L) H L C₀ one hHL start
  rw [eProjection step lift rank (fun z : S => z.val) (fun _ _ => rfl)] at hh
  simpa only [start,Nat.mul_assoc] using hh

/-- Integer version of the paper's short-span cutoff. -/
def shortSpanCutoff (n L : Nat) : Nat := max 1 (min L (n/5))

/-- Valid cutoff and scale conversion, including all small n. The
strict separation premise only applies when there can be seven roots. -/
theorem shortSpanCutoff_bounds (n L : Nat) (hn : 4≤n) (hL : 1≤L) (hLn : L≤n) :
    let D := shortSpanCutoff n L
    0<D ∧ D+1≤2*L ∧ (5≤n → 2*D+2<n) ∧ L≤10*D := by
  let D := shortSpanCutoff n L
  have hD : 1≤D := Nat.le_max_left _ _
  have hDL : D≤L := Nat.max_le.mpr ⟨hL,Nat.min_le_left ..⟩
  refine ⟨hD,by omega,?_,?_⟩
  · intro h5
    have hh : D≤n/5 := Nat.max_le.mpr ⟨by omega,Nat.min_le_right ..⟩
    omega
  · by_cases h5 : n≤4
    · omega
    · by_cases hl : L≤n/5
      · have h : D=L := by unfold D shortSpanCutoff; rw [Nat.min_eq_left hl,Nat.max_eq_right hL]
        omega
      · have hp : 1≤n/5 := by omega
        have h : D=n/5 := by
          unfold D shortSpanCutoff
          rw [Nat.min_eq_right (by omega),Nat.max_eq_right hp]
        omega

/-- If the six-gap spans total 6n, the number of long starts is bounded
by the floor of 6n/D. No stochastic information enters the count. -/
theorem countLong_le (D n : Nat) (hD : 0<D) (spans : List Nat)
    (htotal : spans.sum≤6*n) : (spans.filter (fun s => D<s)).length ≤ 6*n/D := by
  have aux : ∀ fs : List Nat, (fs.filter (fun s => D<s)).length*D≤fs.sum := by
    intro fs
    induction fs with
    | nil => simp
    | cons a fs ih =>
      by_cases ha : D<a
      · simp only [List.filter_cons,show decide (D<a)=true from decide_eq_true ha,if_true,List.length_cons,
          List.sum_cons,Nat.add_mul,Nat.one_mul]
        omega
      · simp only [List.filter_cons,show decide (D<a)=false from decide_eq_false ha, Bool.false_eq_true,if_false,List.sum_cons]
        omega
  exact (Nat.le_div_iff_mul_le hD).mpr (Nat.le_trans (aux _) htotal)

/-- Common offset H=floor(6n/D) lands within the published 60n/L budget. -/
theorem shortSpanOffset_budget (n L : Nat) (hn : 4≤n) (hL : 1≤L) (hLn : L≤n) :
    (6*n / shortSpanCutoff n L)*L ≤ 60*n := by
  let D := shortSpanCutoff n L
  have hl : L≤10*D := (shortSpanCutoff_bounds n L hn hL hLn).2.2.2
  have hdiv : (6*n/D)*D ≤ 6*n := by rw [Nat.mul_comm]; exact Nat.mul_div_le _ _
  change (6*n/D)*L ≤ 60*n
  calc
    _ ≤ (6*n/D)*(10*D) := Nat.mul_le_mul_left _ hl
    _ = 10*((6*n/D)*D) := by ac_rfl
    _ ≤ 10*(6*n) := Nat.mul_le_mul_left _ hdiv
    _ = _ := (Nat.mul_assoc 10 6 n).symm

end L4.RankBlockContraction

#print axioms L4.RankBlockContraction.halfBlock_of_affine
#print axioms L4.RankBlockContraction.physical_half_mean
#print axioms L4.RankBlockContraction.rankOne_mean_of_boundedRank_and_block

#print axioms L4.RankBlockContraction.one_block_of_group_rewards

#print axioms L4.RankBlockContraction.affine_of_group_blocks

#print axioms L4.RankBlockContraction.rank_block_of_seven_data

#print axioms L4.RankBlockContraction.shortSpanOffset_budget
