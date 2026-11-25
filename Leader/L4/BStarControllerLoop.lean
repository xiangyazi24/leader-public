import Leader.L4.BStarResetSchedule

/-! Assembly after the separating return. Bounds count completed
attempts, not individual nondoor marks. No per-op physical service
theorem is postulated as a global instance. -/
namespace L4.BStarControllerLoop

structure Service {X : Type} {n : Nat} (step : X → Fin n → X)
    (Inv : X → Prop) (pc : X → Nat) (budget : Nat) : Prop where
  range : ∀ x, Inv x → pc x<413
  attempt : ∀ x, Inv x → pc x≠0 →
    ∃ w : List (Fin n), w.length≤budget ∧
      let y := BStarResetSchedule.run step x w
      Inv y ∧ (pc y=0 ∨ pc x<pc y)

inductive Attempts {X : Type} {n : Nat} (step : X → Fin n → X) (Inv : X → Prop)
    (pc : X → Nat) (budget : Nat) : X → X → Nat → List (Fin n) → Prop
  | stop {x} (I : Inv x) (R : pc x=0) : Attempts step Inv pc budget x x 0 []
  | next {x z : X} {k w v} (live : pc x≠0) (B : w.length≤budget)
      (I : Inv (BStarResetSchedule.run step x w))
      (advance : pc (BStarResetSchedule.run step x w)=0 ∨ pc x<pc (BStarResetSchedule.run step x w))
      (tail : Attempts step Inv pc budget (BStarResetSchedule.run step x w) z k v) :
      Attempts step Inv pc budget x z (k+1) (w++v)

def remaining (op : Nat) := if op=0 then 0 else 413-op

theorem charge {a b : Nat} (A : a<413) (live : a≠0)
    (progress : b=0 ∨ a<b) : remaining b<remaining a := by
  by_cases E : b=0
  · simp [remaining,E,live]; omega
  · simp [remaining,E,live]
    omega

theorem to_reset {X : Type} {n : Nat} {step : X → Fin n → X}
    {Inv : X → Prop} {pc : X → Nat} {budget : Nat}
    (S : Service step Inv pc budget) (x : X) (I : Inv x) :
    ∃ k w, k≤remaining (pc x) ∧ w.length≤budget*k ∧
      Attempts step Inv pc budget x (BStarResetSchedule.run step x w) k w ∧
      Inv (BStarResetSchedule.run step x w) ∧ pc (BStarResetSchedule.run step x w)=0 := by
  classical
  have loop (r : Nat) : ∀ x, remaining (pc x)=r → Inv x →
      ∃ k w, k≤r ∧ w.length≤budget*k ∧
        Attempts step Inv pc budget x (BStarResetSchedule.run step x w) k w ∧
        Inv (BStarResetSchedule.run step x w) ∧ pc (BStarResetSchedule.run step x w)=0 := by
    induction r using Nat.strongRecOn with
    | ind r ih =>
      intro x E I
      by_cases L : pc x=0
      · exact ⟨0,[],Nat.zero_le _,Nat.zero_le _,.stop I L,I,L⟩
      obtain ⟨w,W,J,H⟩ := S.attempt x I L
      have D := charge (S.range x I) L H
      rw [E] at D
      obtain ⟨k,v,K,V,T,I',R⟩ := ih _ D _ rfl J
      refine ⟨k+1,w++v,by omega,?_,?_⟩
      · rw [List.length_append,Nat.mul_succ]
        omega
      · rw [BStarResetSchedule.run_append]
        exact ⟨.next L W J H T,I',R⟩
  exact loop _ x rfl I

/-- Starting at any legal PC, at most 412 attempts are required.
This is sharper than 413 and automatically improves for a late PC.
Any fault/restart that really schedules zero satisfies the same terminal
alternative; a failed attempt that stays at the same PC does not. -/
theorem absolute_budget {X : Type} {n : Nat} {step : X → Fin n → X}
    {Inv : X → Prop} {pc : X → Nat} {budget : Nat}
    (S : Service step Inv pc budget) (x : X) (I : Inv x) :
    ∃ k w, k≤412 ∧ w.length≤budget*412 ∧
      Attempts step Inv pc budget x (BStarResetSchedule.run step x w) k w ∧
      Inv (BStarResetSchedule.run step x w) ∧ pc (BStarResetSchedule.run step x w)=0 := by
  obtain ⟨k,w,K,W,T,J,R⟩ := to_reset S x I
  have H : remaining (pc x)≤412 := by
    unfold remaining
    split <;> omega
  exact ⟨k,w,Nat.le_trans K H,Nat.le_trans W (Nat.mul_le_mul_left _ (Nat.le_trans K H)),T,J,R⟩

/-- Qualitative residual navigation. A finite per-op forcing word
suffices; the 412 bound is on controller attempts only, not marks. -/
inductive FiniteAttempts {X : Type} {n : Nat} (step : X → Fin n → X)
    (Inv : X → Prop) (pc : X → Nat) : X → X → Nat → List (Fin n) → Prop
  | stop {x} (I : Inv x) (R : pc x=0) : FiniteAttempts step Inv pc x x 0 []
  | next {x z : X} {k w v} (live : pc x≠0)
      (I : Inv (BStarResetSchedule.run step x w))
      (advance : pc (BStarResetSchedule.run step x w)=0 ∨
        pc x<pc (BStarResetSchedule.run step x w))
      (tail : FiniteAttempts step Inv pc (BStarResetSchedule.run step x w) z k v) :
      FiniteAttempts step Inv pc x z (k+1) (w++v)

theorem finite_to_reset {X : Type} {n : Nat} {step : X → Fin n → X}
    {Inv : X → Prop} {pc : X → Nat}
    (range : ∀ x, Inv x → pc x<413)
    (attempt : ∀ x, Inv x → pc x≠0 →
      ∃ w : List (Fin n), let y := BStarResetSchedule.run step x w
        Inv y ∧ (pc y=0 ∨ pc x<pc y))
    (x : X) (I : Inv x) :
    ∃ k w, k≤remaining (pc x) ∧ k≤412 ∧
      FiniteAttempts step Inv pc x (BStarResetSchedule.run step x w) k w ∧
      Inv (BStarResetSchedule.run step x w) ∧ pc (BStarResetSchedule.run step x w)=0 := by
  classical
  have loop (r : Nat) : ∀ x, remaining (pc x)=r → Inv x →
      ∃ k w, k≤r ∧ FiniteAttempts step Inv pc x (BStarResetSchedule.run step x w) k w ∧
        Inv (BStarResetSchedule.run step x w) ∧ pc (BStarResetSchedule.run step x w)=0 := by
    induction r using Nat.strongRecOn with
    | ind r ih =>
      intro x E I
      by_cases L : pc x=0
      · exact ⟨0,[],Nat.zero_le _,.stop I L,I,L⟩
      obtain ⟨w,J,H⟩ := attempt x I L
      have D := charge (range x I) L H
      rw [E] at D
      obtain ⟨k,v,K,T,I',R⟩ := ih _ D _ rfl J
      refine ⟨k+1,w++v,by omega,?_⟩
      rw [BStarResetSchedule.run_append]
      exact ⟨.next L J H T,I',R⟩
  obtain ⟨k,w,U,T,H,E⟩ := loop _ x rfl I
  have B : remaining (pc x)≤412 := by unfold remaining; split <;> omega
  exact ⟨k,w,U,Nat.le_trans U B,T,H,E⟩

end L4.BStarControllerLoop
