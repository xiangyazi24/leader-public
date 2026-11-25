import Leader.L4.ScoredTapeRenewal
import Leader.L4.SequentialMarkClock

namespace L4.MonitorRawBridge

set_option autoImplicit false

variable {X M : Type} {n : Nat}

/-- The previously private H2Ready recursion, now exportable. -/
theorem iid_cost_eq_height
    (next : X → Fin n → X) (P : X → Prop) :
    ∀ (t : Nat) (x : X),
      L4.iidHitCost next P t x =
        L4.Height.iidHitCost next P t x := fun t x => L4.ScoredTapeRenewal.height_cost next P t x

theorem height_iff_row
    (next : X → Fin n → X) (P : X → Prop)
    (x : X) (B : Nat) :
    L4.Height.IIDExpectedHittingTimeAtMost next P x B ↔
      L4.IIDExpectedHittingTimeAtMost next P x B := by
  constructor
  · intro h t
    rw [iid_cost_eq_height next P t x]
    exact h t
  · intro h t
    rw [← iid_cost_eq_height next P t x]
    exact h t

/-- No suspension, conditioning, or loss from the product alphabet. -/
theorem cost_project_le
    (rawNext : X → Fin n → X)
    (monitorNext : M → Fin n → M)
    (project : M → X) (done : M → Prop) (P : X → Prop)
    (Inv : M → Prop)
    (step_project : ∀ z e,
      project (monitorNext z e) = rawNext (project z) e)
    (inv_closed : ∀ z e, Inv z → Inv (monitorNext z e))
    (done_sound : ∀ z, Inv z → done z → P (project z)) :
    ∀ (t : Nat) (z : M), Inv z →
      L4.iidHitCost rawNext P t (project z) ≤
        L4.Height.iidHitCost monitorNext done t z := by
  intro t
  induction t with
  | zero =>
      intro z hz
      exact Nat.le_refl _
  | succ t ih =>
      intro z hz
      classical
      by_cases hp : P (project z)
      · have hzero :
            L4.iidHitCost rawNext P (t+1) (project z)=0 := by
          simp [L4.iidHitCost, hp]
        rw [hzero]
        exact Nat.zero_le _
      · have hd : ¬ done z := fun d => hp (done_sound z hz d)
        simp only [L4.iidHitCost, L4.Height.iidHitCost,
          if_neg hp, if_neg hd]
        apply Nat.add_le_add_left
        apply FiniteUniformStoppingTree.ofFn_sum_le
        intro e
        rw [← step_project z e]
        exact ih (monitorNext z e) (inv_closed z e hz)

/-- Exact same original Fin n tape and bound B, with no extra n. -/
theorem expected_project
    (rawNext : X → Fin n → X)
    (monitorNext : M → Fin n → M)
    (project : M → X) (done : M → Prop) (P : X → Prop)
    (Inv : M → Prop)
    (step_project : ∀ z e,
      project (monitorNext z e) = rawNext (project z) e)
    (inv_closed : ∀ z e, Inv z → Inv (monitorNext z e))
    (done_sound : ∀ z, Inv z → done z → P (project z))
    (start : M) (hstart : Inv start) (B : Nat)
    (bound : L4.Height.IIDExpectedHittingTimeAtMost
      monitorNext done start B) :
    L4.IIDExpectedHittingTimeAtMost
      rawNext P (project start) B := by
  intro t
  exact Nat.le_trans
    (cost_project_le rawNext monitorNext project done P Inv
      step_project inv_closed done_sound t start hstart)
    (bound t)

end L4.MonitorRawBridge

namespace L4.MonitorRawBridge

variable {X M : Type} {n : Nat}

/-- Suffix a single actual physical mark without restarting the run. -/
theorem run_snoc (f : M → Fin n → M) (z : M)
    (w : List (Fin n)) (e : Fin n) :
    L4.SequentialMarkClock.run f z (w ++ [e]) =
      f (L4.SequentialMarkClock.run f z w) e := by
  induction w generalizing z with
  | nil => rfl
  | cons a w ih =>
      change
        L4.SequentialMarkClock.run f (f z a) (w ++ [e]) =
          f (L4.SequentialMarkClock.run f (f z a) w) e
      exact ih (f z a)

theorem run_project
    (rawNext : X → Fin n → X)
    (monitorNext : M → Fin n → M) (project : M → X)
    (h : ∀ z e, project (monitorNext z e) =
      rawNext (project z) e) (z : M) (w : List (Fin n)) :
    project (L4.SequentialMarkClock.run monitorNext z w) =
      L4.SequentialMarkClock.run rawNext (project z) w := by
  induction w generalizing z with
  | nil => rfl
  | cons e w ih =>
      change
        project (L4.SequentialMarkClock.run
          monitorNext (monitorNext z e) w) =
        L4.SequentialMarkClock.run rawNext (rawNext (project z) e) w
      rw [ih (monitorNext z e), h z e]

/-- Restrict source states to the actual finite future of the seed. -/
def ReachFrom (monitorNext : M → Fin n → M)
    (start z : M) : Prop :=
  ∃ w : List (Fin n),
    L4.SequentialMarkClock.run monitorNext start w = z

theorem reachable_closed
    (monitorNext : M → Fin n → M) (start : M) :
    ∀ z e, ReachFrom monitorNext start z →
      ReachFrom monitorNext start (monitorNext z e) := by
  rintro z e ⟨w,hw⟩
  refine ⟨w ++ [e], ?_⟩
  rw [run_snoc, hw]

theorem reachable_sound
    (rawNext : X → Fin n → X)
    (monitorNext : M → Fin n → M)
    (project : M → X) (done : M → Prop) (P : X → Prop)
    (h : ∀ z e, project (monitorNext z e) =
      rawNext (project z) e)
    (start : M)
    (word_sound : ∀ w : List (Fin n),
      done (L4.SequentialMarkClock.run monitorNext start w) →
      P (L4.SequentialMarkClock.run rawNext (project start) w)) :
    ∀ z, ReachFrom monitorNext start z →
      done z → P (project z) := by
  intro z hz hd
  rcases hz with ⟨w,rfl⟩
  rw [run_project rawNext monitorNext project h start w]
  exact word_sound w hd

/-- The useful one-line monitor producer: no extra factor n. -/
theorem expected_of_monitor_words
    (rawNext : X → Fin n → X)
    (monitorNext : M → Fin n → M)
    (project : M → X) (done : M → Prop) (P : X → Prop)
    (h : ∀ z e, project (monitorNext z e) =
      rawNext (project z) e)
    (start : M)
    (word_sound : ∀ w : List (Fin n),
      done (L4.SequentialMarkClock.run monitorNext start w) →
      P (L4.SequentialMarkClock.run rawNext (project start) w))
    (B : Nat)
    (bound : L4.Height.IIDExpectedHittingTimeAtMost
      monitorNext done start B) :
    L4.IIDExpectedHittingTimeAtMost
      rawNext P (project start) B := by
  exact expected_project rawNext monitorNext project done P
    (ReachFrom monitorNext start) h
    (reachable_closed monitorNext start)
    (reachable_sound rawNext monitorNext project done P h start word_sound)
    start ⟨[], rfl⟩ B bound

end L4.MonitorRawBridge

namespace L4.MonitorRawBridge

variable {X M : Type} {n : Nat}

def AnchoredFinished
    (rawNext : X → Fin n → X)
    (monitorNext : M → Fin n → M)
    (project : M → X) (done : M → Prop)
    (start : M) (y : X) : Prop :=
  ∃ w : List (Fin n),
    L4.SequentialMarkClock.run rawNext (project start) w = y ∧
    done (L4.SequentialMarkClock.run monitorNext start w)

theorem anchored_closed
    (rawNext : X → Fin n → X)
    (monitorNext : M → Fin n → M)
    (project : M → X) (done : M → Prop)
    (start : M)
    (done_closed : ∀ z e, done z → done (monitorNext z e)) :
    ∀ y e, AnchoredFinished rawNext monitorNext project done start y →
      AnchoredFinished rawNext monitorNext project done start
        (rawNext y e) := by
  rintro y e ⟨w,hy,hd⟩
  refine ⟨w ++ [e], ?_, ?_⟩
  · rw [run_snoc, hy]
  · rw [run_snoc]
    exact done_closed _ e hd

theorem expected_anchored
    (rawNext : X → Fin n → X)
    (monitorNext : M → Fin n → M)
    (project : M → X) (done : M → Prop)
    (step_project : ∀ z e, project (monitorNext z e) =
      rawNext (project z) e)
    (start : M) (B : Nat)
    (bound : L4.Height.IIDExpectedHittingTimeAtMost
      monitorNext done start B) :
    L4.IIDExpectedHittingTimeAtMost rawNext
      (AnchoredFinished rawNext monitorNext project done start)
      (project start) B := by
  apply expected_of_monitor_words rawNext monitorNext project
    done (AnchoredFinished rawNext monitorNext project done start)
    step_project start _ B bound
  intro w hd
  exact ⟨w,rfl,hd⟩

theorem anchored_sound
    (rawNext : X → Fin n → X)
    (monitorNext : M → Fin n → M)
    (project : M → X) (done : M → Prop)
    (start : M) (P : X → Prop)
    (word_sound : ∀ w : List (Fin n),
      done (L4.SequentialMarkClock.run monitorNext start w) →
      P (L4.SequentialMarkClock.run rawNext (project start) w)) :
    ∀ y, AnchoredFinished rawNext monitorNext project done start y →
      P y := by
  rintro y ⟨w,hy,hd⟩
  rw [←hy]
  exact word_sound w hd

end L4.MonitorRawBridge

namespace L4.MonitorRawBridge
end L4.MonitorRawBridge
