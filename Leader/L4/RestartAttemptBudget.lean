import Leader.L4.RankAttempt
import Leader.L4.RankRace

namespace L4.RestartAttemptBudget
open RankPhysical RankRenewal TaggedTail

/-- Paper restart budget, in units of n². The 9, 8, 4096
and final failure-charge inputs are not asserted by this arithmetic. -/
def B (c : Nat) : Nat := 4170+16*c
def A (c : Nat) : Nat := (21*B c+19)/20

theorem stageSum (c : Nat) :
    9+8*(2*c+1)+19+19+4096+19 = B c := by unfold B; omega

theorem calibration (c : Nat) : 0<A c ∧ B c≤A c ∧ 21*B c≤20*A c := by
  unfold A B
  omega

theorem c12 : B 12=4362 ∧ A 12=4581 := by decide

private noncomputable def indicator {α : Type} (test : α → Prop) (x : α) : Nat :=
  open Classical in if test x then 1 else 0

/-- Given a paper Bn² mean and an ε≤11/1000 failed endpoint
budget, the existing attempt fields require no extra timeout charge.
Keeping both hypotheses explicit is important: neither is just arithmetic. -/
structure Observer {p c n : Nat} (x : Config p c n) where
  State : Type
  start : State
  next : State → Fin n → State
  project : State → Config p c n
  done : State → Prop
  failed : State → Prop
  initial : project start = x
  projectStep : ∀ y e, project (next y e) = step (project y) e
  quiet : ∀ y, QuietEntrance (project y)
  doneAbsorbs : ∀ y e, done y → done (next y e)
  terminalFailure : ∀ y, rank x ≤ rank (project y) → done y → failed y
  mean : IIDExpectedHittingTimeAtMost next done start (B c*n^2)
  failure : ∀ t, 1000*endpointSum next (indicator failed) t start ≤ 11*n^t

def Observer.toRestartTrial {p c n : Nat} {x : Config p c n} (o : Observer x) :
    RestartTrial x (A c*n^2) where
  State := o.State
  start := o.start
  next := o.next
  project := o.project
  done := o.done
  failed := o.failed
  initial := o.initial
  projectStep := o.projectStep
  quiet := o.quiet
  doneAbsorbs := o.doneAbsorbs
  terminalFailure := o.terminalFailure
  mean := fun t => Nat.le_trans (o.mean t)
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (calibration c).2.1))
  failureMass := by
    have h := o.failure (4*(A c*n^2))
    change 4*endpointSum o.next (indicator o.failed) (4*(A c*n^2)) o.start ≤ n^(4*(A c*n^2))
    omega

theorem concreteRestartTrial_of_observers
    (h : ∀ {p c n : Nat} (x : Config p c n), 2≤p → 12≤c → 4≤n →
      (¬p ∣ n) → QuietEntrance x → 2≤rank x → Nonempty (Observer x)) :
    ConcreteRestartTrial := by
  intro c hc
  refine ⟨A c,(calibration c).1,?_⟩
  intro p n x hp hn hnd hQ hR
  obtain ⟨o⟩ := h x hp hc hn hnd hQ hR
  exact ⟨o.toRestartTrial⟩

/-- Stronger paper timeout convention: the timeout component at
4 A n² contributes at most 5/21 on the actual finite raw-word cost. -/
theorem Observer.timeout {p c n : Nat} {x : Config p c n} (o : Observer x)
    (hn : 0<n) :
    let T := 4*(A c*n^2)
    21 * survival o.next (fun z => ¬ o.done z) T o.start ≤ 5*n^T := by
  let U := A c*n^2
  let T := 4*U
  let S := survival o.next (fun z => ¬o.done z) T o.start
  change 21*S ≤ 5*n^T
  have h := Nat.le_trans (horizon_mul_survival_le_cost o.next o.done T o.start) (o.mean T)
  change T*S ≤ B c*n^2*n^T at h
  have h₁ := Nat.mul_le_mul_left 21 h
  have h₂ := Nat.mul_le_mul_right (n^2*n^T) (calibration c).2.2
  have hpos : 0<T := Nat.mul_pos (by decide) (Nat.mul_pos (calibration c).1 (Nat.pow_pos hn))
  apply Nat.le_of_mul_le_mul_left _ hpos
  calc
    T*(21*S) = 21*(T*S) := by ac_rfl
    _ ≤ 21*(B c*n^2*n^T) := h₁
    _ = (21*B c)*(n^2*n^T) := by ac_rfl
    _ ≤ (20*A c)*(n^2*n^T) := h₂
    _ = T*(5*n^T) := by
      change (20*A c)*(n^2*n^T) = (4*(A c*n^2))*(5*n^T)
      calc
        _ = ((4*5)*A c)*(n^2*n^T) := rfl
        _ = _ := by ac_rfl

/-- Strict quarter follows even if the premature-birth estimate is
relaxed to exactly 11/1000 and timeout is additionally charged. -/
theorem union_below_quarter (mass late failed : Nat) (hm : 0 < mass)
    (hl : 21*late≤5*mass) (hf : 1000*failed≤11*mass) :
    4*(late+failed)<mass := by omega


private theorem geom100 (M : Nat) (mass : Nat → Nat)
    (h : ∀ h', 0<h' → 100^h' * mass h'≤M)
    (first k : Nat) (hf : 0<first) :
    99*100^first*RankRace.gapSum mass first k ≤ 100*M := by
  induction k generalizing first with
  | zero => simp [RankRace.gapSum]
  | succ k ih =>
    have ht := ih (first+1) (by omega)
    have hRest :
        99*100^first*RankRace.gapSum mass (first+1) k ≤ M := by
      apply Nat.le_of_mul_le_mul_left _ (by decide : 0<100)
      calc
        _ = 99*100^(first+1)*RankRace.gapSum mass (first+1) k := by
          rw [Nat.pow_succ]
          ac_rfl
        _ ≤ _ := ht
    have hb := Nat.mul_le_mul_left 99 (h first hf)
    change 99*100^first*(mass first + RankRace.gapSum mass (first+1) k) ≤ _
    rw [Nat.mul_add]
    have hHead : 99*100^first*mass first≤99*M := by simpa only [Nat.mul_assoc] using hb
    omega

/-- Finite integer union bound, including the entire distinct-gap sum.
The premise is about the *sum* of the two cause numerators per gap;
their probability laws need not be independent. The paper's sharper
per-gap estimate implies this convenient rational envelope. -/
theorem failed_bound_of_distinct_gap_union (M K failed : Nat)
    (early slow : Nat → Nat)
    (perGap : ∀ h, 0<h → 100^h*(early h+slow h)≤M)
    (covered : failed≤RankRace.gapSum (fun h => early h+slow h) 1 K) :
    1000*failed≤11*M := by
  have g := geom100 M (fun h => early h+slow h) perGap 1 K (by decide)
  rw [Nat.pow_one] at g
  have hg : 99*RankRace.gapSum (fun h => early h+slow h) 1 K ≤ M := by
    apply Nat.le_of_mul_le_mul_left _ (by decide : 0<100)
    simpa only [Nat.mul_left_comm, Nat.mul_assoc] using g
  omega

end L4.RestartAttemptBudget

#print axioms L4.RestartAttemptBudget.stageSum
#print axioms L4.RestartAttemptBudget.calibration
#print axioms L4.RestartAttemptBudget.concreteRestartTrial_of_observers
#print axioms L4.RestartAttemptBudget.Observer.timeout
#print axioms L4.RestartAttemptBudget.union_below_quarter

#print axioms L4.RestartAttemptBudget.failed_bound_of_distinct_gap_union
