import Leader.L4.Height.LeaderBridge
import Leader.Core.FiniteUniformStoppingTree

namespace L4.SequentialMarkClock

set_option autoImplicit false

open L4.Height

variable {X A J : Type} {n : Nat}

/-- A physical state, its current phase's private observer, and the phases
not yet completed (in prescribed order). -/
structure State (X A J : Type) where
  raw : X
  aux : A
  todo : List J

def start (fresh : A) (js : List J) (x : X) : State X A J :=
  ⟨x, fresh, js⟩

def finished (z : State X A J) : Prop := z.todo = []

/-- Every phase uses the same physical mark. When the current observer
reaches its goal the observer for the next phase starts at the actual
physical endpoint of this same mark, without resampling. -/
noncomputable def step (advance : X → Fin n → X)
    (phase : J → X × A → Fin n → X × A)
    (goal : J → X × A → Prop) (fresh : A)
    (z : State X A J) (e : Fin n) : State X A J := by
  classical
  exact match z.todo with
  | [] => ⟨advance z.raw e, fresh, []⟩
  | j :: js =>
    let w := phase j (z.raw, z.aux) e
    if goal j w then ⟨w.1, fresh, js⟩ else ⟨w.1, w.2, j :: js⟩

theorem step_raw (advance : X → Fin n → X)
    (phase : J → X × A → Fin n → X × A)
    (goal : J → X × A → Prop) (fresh : A)
    (physical : ∀ j w e, (phase j w e).1 = advance w.1 e)
    (z : State X A J) (e : Fin n) :
    (step advance phase goal fresh z e).raw = advance z.raw e := by
  classical
  cases z with
  | mk x a todo =>
    cases todo with
    | nil => rfl
    | cons j js =>
      simp only [step]
      split <;> exact physical j (x,a) e

private theorem cost_from_phase
    (advance : X → Fin n → X)
    (phase : J → X × A → Fin n → X × A)
    (goal : J → X × A → Prop) (fresh : A)
    (ok : X → Prop)
    (physical : ∀ j w e, (phase j w e).1 = advance w.1 e)
    (closed : ∀ x e, ok x → ok (advance x e))
    (j : J) (js : List J) (K : Nat)
    (rest : ∀ x, ok x → IIDExpectedHittingTimeAtMost
      (step advance phase goal fresh) finished (start fresh js x) K)
    (t : Nat) (w : X × A) (hw : ok w.1) (ng : ¬goal j w) :
    iidHitCost (step advance phase goal fresh) finished t ⟨w.1, w.2, j :: js⟩ ≤
      iidHitCost (phase j) (goal j) t w + K * n^t := by
  classical
  let next := step advance phase goal fresh
  induction t generalizing w with
  | zero => simp [iidHitCost]
  | succ t ih =>
    have live : ¬finished (⟨w.1, w.2, j :: js⟩ : State X A J) := by
      simp [finished]
    rw [show iidHitCost (step advance phase goal fresh) finished (t+1)
      (⟨w.1, w.2, j :: js⟩ : State X A J) =
      n^(t+1) + (List.ofFn (fun e : Fin n =>
        iidHitCost next finished t (next ⟨w.1,w.2,j::js⟩ e))).sum by
          simp only [next,iidHitCost,if_neg live]]
    rw [show iidHitCost (phase j) (goal j) (t+1) w =
      n^(t+1) + (List.ofFn (fun e : Fin n =>
        iidHitCost (phase j) (goal j) t (phase j w e))).sum by
          simp only [iidHitCost,if_neg ng]]
    have S : (List.ofFn (fun e : Fin n =>
        iidHitCost next finished t (next ⟨w.1,w.2,j::js⟩ e))).sum ≤
        (List.ofFn (fun e : Fin n =>
          iidHitCost (phase j) (goal j) t (phase j w e) + K*n^t)).sum := by
      apply FiniteUniformStoppingTree.ofFn_sum_le
      intro e
      have Hok : ok (phase j w e).1 := by rw [physical]; exact closed _ _ hw
      by_cases hit : goal j (phase j w e)
      · have U := rest (phase j w e).1 Hok t
        have E : next ⟨w.1,w.2,j::js⟩ e = start fresh js (phase j w e).1 := by
          simp only [next, step, if_pos hit, start]
        rw [E, iidHitCost_of_target _ _ _ hit, Nat.zero_add]
        exact U
      · have E : next ⟨w.1,w.2,j::js⟩ e =
            ⟨(phase j w e).1,(phase j w e).2,j::js⟩ := by
          simp only [next, step, if_neg hit]
        rw [E]
        exact ih _ Hok hit
    have addConst {f : Fin n → Nat} (b : Nat) :
        (List.ofFn (fun e : Fin n => f e + b)).sum =
          (List.ofFn f).sum + n*b := by
      rw [FiniteUniformStoppingTree.ofFn_sum_add,
        FiniteUniformStoppingTree.ofFn_sum_const]
    rw [addConst, ←Nat.mul_assoc, Nat.mul_comm n K, Nat.mul_assoc, ←Nat.pow_succ'] at S
    simpa only [Nat.add_assoc] using Nat.add_le_add_left S (n^(t+1))

theorem expected
    (advance : X → Fin n → X)
    (phase : J → X × A → Fin n → X × A)
    (goal : J → X × A → Prop) (fresh : A)
    (ok : X → Prop)
    (physical : ∀ j w e, (phase j w e).1 = advance w.1 e)
    (closed : ∀ x e, ok x → ok (advance x e))
    (K : Nat)
    (initial : ∀ j x, ok x → ¬goal j (x,fresh))
    (budget : ∀ j x, ok x → IIDExpectedHittingTimeAtMost
      (phase j) (goal j) (x,fresh) K)
    (js : List J) (x : X) (hx : ok x) :
    IIDExpectedHittingTimeAtMost (step advance phase goal fresh) finished
      (start fresh js x) (js.length*K) := by
  induction js generalizing x with
  | nil =>
    intro t
    rw [iidHitCost_of_target _ _ _ (show finished (start (J:=J) fresh [] x) from rfl)]
    exact Nat.zero_le _
  | cons j js ih =>
    intro t
    calc
      _ ≤ iidHitCost (phase j) (goal j) t (x,fresh) + js.length*K*n^t :=
        cost_from_phase advance phase goal fresh ok physical closed j js _
          ih t (x,fresh) hx (initial j x hx)
      _ ≤ K*n^t + js.length*K*n^t :=
        Nat.add_le_add_right (budget j x hx t) _
      _ = _ := by simp [Nat.succ_mul, Nat.add_mul, Nat.add_comm]

/-- Run one marked tape in chronological order. -/
def run {Z : Type} (stepZ : Z → Fin n → Z) (z : Z) : List (Fin n) → Z
  | [] => z
  | e :: w => run stepZ (stepZ z e) w

theorem run_raw (advance : X → Fin n → X)
    (phase : J → X × A → Fin n → X × A)
    (goal : J → X × A → Prop) (fresh : A)
    (physical : ∀ j w e, (phase j w e).1 = advance w.1 e)
    (z : State X A J) (w : List (Fin n)) :
    (run (step advance phase goal fresh) z w).raw = run advance z.raw w := by
  induction w generalizing z with
  | nil => rfl
  | cons e w ih =>
    simp only [run, ih, step_raw advance phase goal fresh physical]

/-- Each constituent phase receipt also projects to its literal physical
segment. In particular no tape reordering occurs at a phase boundary. -/
theorem phase_run_raw (advance : X → Fin n → X)
    (phase : J → X × A → Fin n → X × A)
    (physical : ∀ j w e, (phase j w e).1 = advance w.1 e)
    (j : J) (z : X × A) (w : List (Fin n)) :
    (run (phase j) z w).1 = run advance z.1 w := by
  induction w generalizing z with
  | nil => rfl
  | cons e w ih => simp only [run, ih, physical]

/-- Each credited phase has a nonempty segment of the original tape ending
at an actual goal. Unused suffix marks remain in the tape. The next phase
starts at the same cut with a fresh observer. This certifies history, not
simultaneous truth of the old goals at the last endpoint. -/
def Receipts (phase : J → X × A → Fin n → X × A)
    (goal : J → X × A → Prop) (fresh : A) :
    List J → X × A → List (Fin n) → Prop
  | [], _, _ => True
  | j :: js, x, w => ∃ u v : List (Fin n), w = u ++ v ∧ u ≠ [] ∧
      goal j (run (phase j) x u) ∧
      Receipts phase goal fresh js ((run (phase j) x u).1, fresh) v

theorem receipts_of_finished (advance : X → Fin n → X)
    (phase : J → X × A → Fin n → X × A)
    (goal : J → X × A → Prop) (fresh : A)
    (z : State X A J) (w : List (Fin n))
    (done : finished (run (step advance phase goal fresh) z w)) :
    Receipts phase goal fresh z.todo (z.raw,z.aux) w := by
  classical
  induction w generalizing z with
  | nil =>
    have h : z.todo = [] := done
    simp [Receipts,h]
  | cons e w ih =>
    cases z with
    | mk x a todo =>
      cases todo with
      | nil => trivial
      | cons j js =>
        have D : finished
            (run (step advance phase goal fresh)
              (step advance phase goal fresh ⟨x,a,j::js⟩ e) w) := done
        by_cases H : goal j (phase j (x,a) e)
        · rw [show step advance phase goal fresh ⟨x,a,j::js⟩ e =
              ⟨(phase j (x,a) e).1,fresh,js⟩ by simp [step,H]] at D
          exact ⟨[e],w,rfl,by simp,H,ih _ D⟩
        · rw [show step advance phase goal fresh ⟨x,a,j::js⟩ e =
              ⟨(phase j (x,a) e).1,(phase j (x,a) e).2,j::js⟩ by simp [step,H]] at D
          obtain ⟨u,v,E,_,U,V⟩ := ih _ D
          exact ⟨e::u,v,congrArg (List.cons e) E,by simp,U,V⟩

end L4.SequentialMarkClock
