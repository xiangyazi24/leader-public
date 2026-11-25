import Leader.L4.GGTiming

/-!
# Predictable suspension of the exclusion clock
At a physical pre-mark the comparison either reads the mark or waits for
one predictable edge. A reserved pause can be charged at most once.
-/

namespace L4.GGPause
open TaggedTail Classical

private theorem sSucc {n : Nat} (f : Fin (n+1) → Nat) :
    sumEdge f = f 0 + sumEdge (fun j : Fin n => f j.succ) := by
  simp [sumEdge, List.ofFn_succ]

private theorem sConst (n a : Nat) : sumEdge (fun _ : Fin n => a) = n*a := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sSucc, ih, Nat.succ_mul, Nat.add_comm]

private theorem sMono {n : Nat} (f g : Fin n → Nat) (h : ∀ e, f e ≤ g e) :
    sumEdge f ≤ sumEdge g := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    rw [sSucc f, sSucc g]
    exact Nat.add_le_add (h 0) (ih _ _ (fun e => h e.succ))

private theorem sAdd {n : Nat} (f g : Fin n → Nat) :
    sumEdge (fun e => f e + g e) = sumEdge f + sumEdge g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sSucc, sSucc f, sSucc g, ih]; omega

private theorem sSelector {n : Nat} (i : Fin n) (a : Nat) :
    sumEdge (fun e => if e = i then a else 0) = a := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [sSucc]
      have hz : (fun e : Fin n => if e.succ = (0 : Fin (n+1)) then a else 0) =
          (fun _ : Fin n => 0) := by funext e; simp [Fin.succ_ne_zero]
      rw [hz, sConst]
      simp
    · rw [sSucc, if_neg (Ne.symm (Fin.succ_ne_zero j))]
      have hc : (fun e : Fin n => if e.succ = j.succ then a else 0) =
          (fun e : Fin n => if e = j then a else 0) := by funext e; simp
      rw [hc, ih, Nat.zero_add]

private theorem sScale {n : Nat} (a : Nat) (f : Fin n → Nat) :
    sumEdge (fun e => a*f e) = a*sumEdge f := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sSucc,sSucc f,ih,Nat.mul_add]

/-- In a pause a predictable hit spends one full unit of remaining
pause credit. This gives expected charge at most n per reserved pause. -/
theorem pause_credit_oneStep {α : Type} {n : Nat}
    (next : α → Fin n → α) (credit : α → Nat) (x : α) (a : Fin n)
    (h : ∀ e, credit (next x e) ≤ credit x)
    (hh : credit (next x a)+1 ≤ credit x) :
    n + sumEdge (fun e => n*credit (next x e)) ≤ n * (n*credit x) := by
  have hp : ∀ e : Fin n,
      n*credit (next x e) + (if e=a then n else 0) ≤ n*credit x := by
    intro e
    by_cases he : e=a
    · subst e
      simpa [Nat.mul_add] using Nat.mul_le_mul_left n hh
    · simp [he,Nat.mul_le_mul_left n (h e)]
  have hsum := sMono _ _ hp
  rw [sAdd,sSelector,sConst] at hsum
  exact Nat.le_of_eq (Nat.add_comm _ _) |> fun h => Nat.le_trans h hsum

/-- Same-scheduler transfer with predictable pauses. Its hypotheses are
checked before the next edge: active marks drive every path; paused marks
leave the virtual paths untouched, with one nominated edge spending a
pause reserve. No conditioning on the selected edge is used to decide
whether that mark belongs to the active stream. -/
theorem hittingTime_with_pauses {α : Type} {n : Nat}
    (next : α → Fin n → α) (target : α → Prop)
    (paths : α → List (List (Fin n))) (credit : α → Nat) (paused : α → Prop)
    (good : α → Prop)
    (hGood : ∀ x e, good x → good (next x e))
    (hCredit : ∀ x e, good x → ¬ target x → credit (next x e) ≤ credit x)
    (hActive : ∀ x, good x → ¬ target x → ¬ paused x →
      ¬ GGTiming.finished (paths x) ∧
        ∀ e, paths (next x e) = GGTiming.advance (paths x) e)
    (hHold : ∀ x, good x → ¬ target x → paused x →
      (∃ a : Fin n, credit (next x a)+1 ≤ credit x) ∧
        ∀ e, paths (next x e) = paths x) :
    ∀ t x, good x →
      iidHitCost next target t x ≤ iidHitCost GGTiming.advance GGTiming.finished t (paths x) +
        (n*credit x)*n^t := by
  intro t
  induction t with
  | zero => intro x hx; simp [iidHitCost]
  | succ t ih =>
    intro x hx
    by_cases hs : target x
    · simp [iidHitCost_of_target _ _ _ hs]
    · let V := fun y => iidHitCost GGTiming.advance GGTiming.finished t (paths y)
      let D := fun y => n*credit y
      have hsum : sumEdge (fun e => iidHitCost next target t (next x e)) ≤
          sumEdge (fun e => V (next x e)) + sumEdge (fun e => D (next x e)*n^t) := by
        rw [← sAdd]
        exact sMono _ _ (fun e => ih (next x e) (hGood x e hx))
      have hd : sumEdge (fun e => D (next x e)*n^t) =
          n^t*sumEdge (fun e => D (next x e)) := by
        rw [show (fun e => D (next x e)*n^t) = (fun e => n^t*D (next x e)) from funext (fun e => Nat.mul_comm ..)]
        rw [sScale]
      rw [iidHitCost,if_neg hs]
      change n^(t+1)+sumEdge (fun e => iidHitCost next target t (next x e)) ≤ _
      have hb : n^(t+1)+sumEdge (fun e => iidHitCost next target t (next x e)) ≤
          n^(t+1)+sumEdge (fun e => V (next x e))+n^t*sumEdge (fun e => D (next x e)) := by
        rw [← hd, Nat.add_assoc]; exact Nat.add_le_add_left hsum _
      refine Nat.le_trans hb ?_
      by_cases hP : paused x
      · obtain ⟨⟨a,ha⟩,hV⟩ := hHold x hx hs hP
        have he : (fun e => V (next x e)) = fun _ : Fin n => V x :=
          funext (fun e => by simp [V,hV e])
        have hp := pause_credit_oneStep next credit x a (fun e => hCredit x e hx hs) ha
        have hpaid := Nat.mul_le_mul_left (n^t) hp
        change n^t*(n+sumEdge (fun e => D (next x e))) ≤ n^t*(n*D x) at hpaid
        have hvBound : n*V x ≤ iidHitCost GGTiming.advance GGTiming.finished (t+1) (paths x) := by
          rw [iidHitCost_succ_eq]
          exact Nat.mul_le_mul_left _ (Nat.le_add_right ..)
        rw [he,sConst]
        calc
          _ = n*V x + n^t*(n + sumEdge (fun e => D (next x e))) := by
            rw [Nat.pow_succ,Nat.mul_add]; ac_rfl
          _ ≤ _ := by
            rw [Nat.pow_succ]
            exact Nat.add_le_add hvBound (by simpa only [D,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hpaid)
      · obtain ⟨hFin,hV⟩ := hActive x hx hs hP
        have he : (fun e => V (next x e)) =
            fun e => iidHitCost GGTiming.advance GGTiming.finished t (GGTiming.advance (paths x) e) :=
          funext (fun e => by simp [V,hV e])
        have hc : sumEdge (fun e => D (next x e)) ≤ n*D x := by
          rw [← sConst]
          exact sMono _ _ (fun e => Nat.mul_le_mul_left _ (hCredit x e hx hs))
        rw [iidHitCost,if_neg hFin,he]
        change _ ≤ n^(t+1)+sumEdge (fun e => iidHitCost GGTiming.advance GGTiming.finished t
          (GGTiming.advance (paths x) e)) + (n*credit x)*n^(t+1)
        apply Nat.add_le_add_left
        rw [Nat.pow_succ]
        simpa only [D,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using (Nat.mul_le_mul_left (n^t) hc)

end L4.GGPause

#print axioms L4.GGPause.pause_credit_oneStep
#print axioms L4.GGPause.hittingTime_with_pauses
