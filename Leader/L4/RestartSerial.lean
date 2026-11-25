import Leader.L4.TripleRenewal
import Leader.L4.RestartAttemptBudget

namespace L4.RestartSerial
open TaggedTail TripleRenewal Classical

private theorem edge_mono {n : Nat} (f g : Fin n → Nat) (h : ∀ i, f i≤g i) :
    sumEdge f≤sumEdge g := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons]
    exact Nat.add_le_add (h 0) (ih _ _ (fun i => h i.succ))

private theorem edge_add {n : Nat} (f g : Fin n → Nat) :
    sumEdge (fun e => f e+g e) = sumEdge f+sumEdge g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons] at *
    rw [ih]
    omega

private theorem edge_scale {n : Nat} (k : Nat) (f : Fin n → Nat) :
    sumEdge (fun e => k*f e) = k*sumEdge f := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons] at *
    rw [ih,Nat.mul_add]

private theorem edge_const (n a : Nat) : sumEdge (fun _ : Fin n => a) = n*a := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons] at *
    rw [ih,Nat.succ_mul,Nat.add_comm]

/-- The continuation runs on the same raw labels, on the actual successor
state, not an independent restart. Before ready, the auxiliary stage
takes one corresponding raw mark; ready may hold already at time zero. -/
theorem stage_cost {α β : Type} {n : Nat} (next : α → Fin n → α)
    (localNext : β → Fin n → β) (project : β → α) (done : α → Prop)
    (ready valid : β → Prop)
    (align : ∀ b e, valid b → ¬ready b →
      project (localNext b e) = next (project b) e)
    (keep : ∀ b e, valid b → ¬ready b → valid (localNext b e))
    (B : Nat)
    (after : ∀ b, valid b → ready b →
      IIDExpectedHittingTimeAtMost next done (project b) B) :
    ∀ t b, valid b →
      iidHitCost next done t (project b) ≤ iidHitCost localNext ready t b + B*n^t := by
  intro t
  induction t with
  | zero => intro b _; simp [iidHitCost]
  | succ t ih =>
    intro b hv
    by_cases hd : done (project b)
    · rw [iidHitCost_of_target _ _ _ hd]; exact Nat.zero_le _
    by_cases hr : ready b
    · rw [iidHitCost_of_target _ _ _ hr,Nat.zero_add]
      exact after b hv hr (t+1)
    rw [iidHitCost,if_neg hd,iidHitCost,if_neg hr]
    have h := edge_mono
      (fun e => iidHitCost next done t (next (project b) e))
      (fun e => iidHitCost localNext ready t (localNext b e)+B*n^t)
      (fun e => by rw [←align b e hv hr]; exact ih _ (keep b e hv hr))
    rw [edge_add,show sumEdge (fun _ : Fin n => B*n^t) = B*n^(t+1) by
      rw [edge_scale,edge_const,Nat.pow_succ']] at h
    change n^(t+1)+sumEdge _ ≤ n^(t+1)+sumEdge _+B*n^(t+1)
    omega

/-- Add per-entry clock bounds, at arbitrary observed phase exits. An
early global stop shortens the bound even if the local phase is not ready. -/
theorem stage_mean {α β : Type} {n : Nat} (next : α → Fin n → α)
    (localNext : β → Fin n → β) (project : β → α) (done : α → Prop)
    (ready valid : β → Prop)
    (align : ∀ b e, valid b → ¬ready b →
      project (localNext b e) = next (project b) e)
    (keep : ∀ b e, valid b → ¬ready b → valid (localNext b e))
    (A B : Nat) (b : β) (hv : valid b)
    (before : IIDExpectedHittingTimeAtMost localNext ready b A)
    (after : ∀ b, valid b → ready b →
      IIDExpectedHittingTimeAtMost next done (project b) B) :
    IIDExpectedHittingTimeAtMost next done (project b) (A+B) := by
  intro t
  have h := stage_cost next localNext project done ready valid align keep B after t b hv
  rw [Nat.add_mul]
  exact Nat.le_trans h (Nat.add_le_add_right (before t) _)

/-- Dominance of first-hit costs on a common raw alphabet. The
comparison may stop the physical observer earlier but cannot route
a comparison hit to a still-active physical stage. -/
theorem cost_dominated {α β : Type} {n : Nat}
    (next : α → Fin n → α) (other : β → Fin n → β)
    (done : α → Prop) (hit : β → Prop) (rel : α → β → Prop)
    (exit : ∀ x y, rel x y → hit y → done x)
    (align : ∀ x y e, rel x y → ¬ done x → ¬hit y → rel (next x e) (other y e)) :
    ∀ t x y, rel x y → iidHitCost next done t x ≤ iidHitCost other hit t y := by
  intro t
  induction t with
  | zero => intro x y _; exact Nat.le_refl _
  | succ t ih =>
    intro x y h
    by_cases hd : done x
    · rw [iidHitCost_of_target _ _ _ hd]; exact Nat.zero_le _
    have hb : ¬hit y := fun h' => hd (exit x y h h')
    rw [iidHitCost,if_neg hd,iidHitCost,if_neg hb]
    apply Nat.add_le_add_left
    exact edge_mono _ _ (fun e => ih _ _ (align x y e h hd hb))

/-- When each active state can leave its current numerical stage in
bounded mean, and the phase exit is defined as reaching a lower rank,
sum the stage budgets with no independence or extra handoff mark. -/
theorem ranked_stage_mean {α : Type} {n : Nat} (next : α → Fin n → α)
    (level : α → Nat) (cost : Nat → Nat)
    (stage : ∀ x, 0<level x →
      IIDExpectedHittingTimeAtMost next (fun y => level y<level x) x (cost (level x))) :
    ∀ x, IIDExpectedHittingTimeAtMost next (fun y => level y=0) x
      ((List.range (level x)).map (fun j => cost (j+1))).sum := by
  let B := fun k => ((List.range k).map (fun j => cost (j+1))).sum
  have hNext (k : Nat) : B (k+1)=cost (k+1)+B k := by
    simp [B,List.range_succ,List.map_append,Nat.add_comm]
  have hMono : ∀ {a b : Nat}, a≤b → B a≤B b := by
    intro a b hab
    induction hab with
    | refl => exact Nat.le_refl _
    | step _ ih => rw [hNext]; omega
  have go : ∀ k x, level x=k →
      IIDExpectedHittingTimeAtMost next (fun y => level y=0) x (B k) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro x hx
      cases k with
      | zero =>
        intro t
        rw [iidHitCost_of_target next _ x hx]
        exact Nat.zero_le _
      | succ k =>
        let ready := fun y => level y<k+1
        have hs : IIDExpectedHittingTimeAtMost next ready x (cost (k+1)) := by
          simpa only [ready,hx] using stage x (by omega)
        have h := stage_mean next next id (fun y => level y=0) ready (fun _ => True)
          (fun _ _ _ _ => rfl) (fun _ _ _ _ => trivial)
          (cost (k+1)) (B k) x trivial hs
          (by intro y _ hy
              change level y<k+1 at hy
              exact expected_mono (ih (level y) hy y rfl) (hMono (by omega)))
        rw [hNext]
        exact h
  intro x
  exact go (level x) x rfl

/-- The checked 17 n² drain can replace the paper's sharper 9 n²
without changing any other threshold or requiring a new failure law. -/
def verifiedBudget (c : Nat) : Nat := 4178+16*c

theorem verifiedBudget_sum (c : Nat) :
    17+8*(2*c+1)+19+19+4096+19=verifiedBudget c := by
  unfold verifiedBudget
  omega

def verifiedAttempt (c : Nat) : Nat := (21*verifiedBudget c+19)/20

theorem verifiedAttempt_calibrate (c : Nat) :
    0<verifiedAttempt c ∧ verifiedBudget c≤verifiedAttempt c ∧
    21*verifiedBudget c≤20*verifiedAttempt c := by
  unfold verifiedAttempt verifiedBudget
  omega

open RankPhysical in
/-- The audited restart-calibration has room for the conservative drain.
The physical projection and failure bit are retained verbatim. -/
structure VerifiedObserver {p c n : Nat} (x : Config p c n) where
  State : Type
  start : State
  next : State → Fin n → State
  project : State → Config p c n
  done : State → Prop
  failed : State → Prop
  initial : project start=x
  projectStep : ∀ y e, project (next y e)=step (project y) e
  quiet : ∀ y, QuietEntrance (project y)
  doneAbsorbs : ∀ y e, done y → done (next y e)
  terminalFailure : ∀ y, rank x≤rank (project y) → done y → failed y
  mean : IIDExpectedHittingTimeAtMost next done start (verifiedBudget c*n^2)
  failure : ∀ t, 1000*RankRenewal.endpointSum next
    (fun x => if failed x then 1 else 0) t start ≤ 11*n^t

noncomputable def VerifiedObserver.toRestartTrial {p c n : Nat} {x : Config p c n} (o : VerifiedObserver x) :
    RankPhysical.RestartTrial x (verifiedAttempt c*n^2) where
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
  mean := expected_mono o.mean (Nat.mul_le_mul_right _ (verifiedAttempt_calibrate c).2.1)
  failureMass := by
    have h := o.failure (4*(verifiedAttempt c*n^2))
    change 4*RankRenewal.endpointSum o.next (fun x => if o.failed x then 1 else 0)
      (4*(verifiedAttempt c*n^2)) o.start ≤ n^(4*(verifiedAttempt c*n^2))
    omega

def RootIndependentRestartTrial : Prop :=
  ∀ c : Nat, 12≤c → ∃ K : Nat, 0<K ∧
    ∀ {p n : Nat} (x : Config p c n), 2≤p → 4≤n → QuietEntrance x →
      2≤RankPhysical.rank x → Nonempty (RankPhysical.RestartTrial x (K*n^2))

theorem concreteRestartTrial_of_verified_observers
    (h : ∀ {p c n : Nat} (x : Config p c n), 2≤p → 12≤c → 4≤n →
      QuietEntrance x → 2≤RankPhysical.rank x → Nonempty (VerifiedObserver x)) :
    RootIndependentRestartTrial := by
  intro c hc
  refine ⟨verifiedAttempt c,(verifiedAttempt_calibrate c).1,?_⟩
  intro p n x hp hn hq hr
  obtain ⟨o⟩ := h x hp hc hn hq hr
  exact ⟨o.toRestartTrial⟩

end L4.RestartSerial
