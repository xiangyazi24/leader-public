import Leader.L4.GGStage
import Leader.L4.GGPause
import Leader.L4.EntranceCover

/-!
# Conditional literal preparation bound
All scheduling estimates are proved. The remaining deterministic
certificate is to realize a particular fixed-sink exclusion comparison
and its path family on the literal preparation monitor.
-/

namespace L4.GGStage

/-- The remaining physical/DAG obligation. Every decision to suspend is
pre-mark. The ghost stock cap creates at most s+1 resident reservations.
The family represents the virtual exclusion DAG of depth at most 4s+2,
not a scheduler-selected successful continuation. -/
structure PredictableDrainCertificate {p c n : Nat} (x : Config p c n)
    (b : Fin n) (a : Heads) where
  State : Type
  start : State
  project : State → Obs p c n
  next : State → Fin n → State
  done : State → Prop
  good : State → Prop
  keepGood : ∀ q e, good q → good (next q e)
  goodStart : good start
  projectStart : project start = init x a
  projectStep : ∀ q e, project (next q e) = advance b (project q) e
  sound : ∀ q, done q → Drained b (project q)
  paths : State → List (List (Fin n))
  paused : State → Prop
  credit : State → Nat
  L : Nat
  span_bound : L ≤ 4*(a.k-a.i)+2
  bounded_paths : ∀ q ∈ paths start, q.length ≤ L
  count_paths : (paths start).length ≤ 2^(L+1)
  initialCredit : credit start ≤ a.k-a.i+1
  keepCredit : ∀ q e, good q → ¬ done q → credit (next q e) ≤ credit q
  active : ∀ q, good q → ¬ done q → ¬ paused q →
    ¬ GGTiming.finished (paths q) ∧
      ∀ e, paths (next q e) = GGTiming.advance (paths q) e
  suspended : ∀ q, good q → ¬ done q → paused q →
    (∃ e : Fin n, credit (next q e)+1 ≤ credit q) ∧
      ∀ e, paths (next q e) = paths q

/-- Only the projection and finite exclusion certificate are premises;
the common-clock maximum and predictable pause cost are not. -/
theorem preparation_mean_of_predictable_certificate {p c n : Nat} (x : Config p c n)
    (b : Fin n) (a : Heads) (C : PredictableDrainCertificate x b a) :
    IIDExpectedHittingTimeAtMost (advance b) (Drained b) (init x a)
      (17*n*(a.k-a.i+1)) := by
  intro t
  let s := a.k-a.i
  have hs : 0 < n := Nat.zero_lt_of_lt b.isLt
  have hproj := EntranceCover.iidHitCost_le_of_projection
    (advance b) C.next (Drained b) C.done C.project C.projectStep C.sound t C.start
  rw [C.projectStart] at hproj
  have hCost := GGPause.hittingTime_with_pauses C.next C.done C.paths C.credit C.paused C.good
    C.keepGood C.keepCredit C.active C.suspended t C.start C.goodStart
  have hPaths := GGTiming.pathClock_expected hs (C.paths C.start) C.L C.bounded_paths C.count_paths t
  have hfact : 4*n*(C.L+1)+n*C.credit C.start ≤ 17*n*(s+1) := by
    have h₁ : C.L ≤ 4*s+2 := C.span_bound
    have h₂ : C.credit C.start ≤ s+1 := C.initialCredit
    calc
      _ = n*(4*(C.L+1)+C.credit C.start) := by
        simp only [Nat.mul_add]; ac_rfl
      _ ≤ n*(17*(s+1)) := Nat.mul_le_mul_left n (by omega)
      _ = _ := by ac_rfl
  apply Nat.le_trans _ (Nat.mul_le_mul_right (n^t) hfact)
  rw [Nat.add_mul]
  exact Nat.le_trans hproj (Nat.le_trans hCost (Nat.add_le_add_right hPaths _))

theorem stageCover_step {p c n : Nat} (hn : 4 ≤ n) (b e : Fin n) (s : Obs p c n)
    (h : MCOV s.config ∧ COV s.config) :
    MCOV (advance b s e).config ∧ COV (advance b s e).config := by
  have h' := EntranceCover.cover_closed hn s.config e h
  unfold advance
  split
  · exact h
  · dsimp only
    split <;> exact h'

theorem stageCover_run {p c n : Nat} (hn : 4 ≤ n) (b : Fin n) (s : Obs p c n)
    (h : MCOV s.config ∧ COV s.config) (w : List (Fin n)) :
    MCOV (GGTiming.runMarks (advance b) s w).config ∧
      COV (GGTiming.runMarks (advance b) s w).config := by
  induction w generalizing s with
  | nil => exact h
  | cons e w ih => exact ih (advance b s e) (stageCover_step hn b e s h)

/-- The remaining literal no-injection closure after the first emptied cut.
At every nonterminal endpoint, j is still fixed and the retained interval
is empty. On each nonterminal advance of i, its vacated site is an empty
nonleader immediately after the selected mark. -/
def LiteralDrainedPersistence {p c n : Nat} (x : Config p c n)
    (b : Fin n) (a : Heads) : Prop :=
  ∀ (u v : List (Fin n)), InitialCut x b a →
    let y := observe x b a u
    let z := observe x b a (u++v)
    y.stopped = false → Drained b y → z.stopped = false →
    z.heads.j = y.heads.j ∧ Drained b z ∧
      ∀ e : Fin n, let z' := advance b z e
        z'.stopped = false → z.heads.i < z'.heads.i →
          (z'.config (liftedSite b z.heads.i)).stock = false ∧
            (z'.config (liftedSite b z.heads.i)).leader = false

end L4.GGStage

