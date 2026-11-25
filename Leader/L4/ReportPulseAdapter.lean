import Leader.L4.ReportPulseWait

namespace L4.ReportPulseWait

/-- Transfer the exact finite-word mean through a clock factor of the
original process. The proof does not change or condition its alphabet. -/
theorem factor_cost {X : Type} {n J : Nat} (a b : Fin n) {raw : X → Fin n → X}
    (C : X → Prop) (stay : ∀ x e, C x → C (raw x e))
    (obs : X → State)
    (comm : ∀ x e, C x → obs (raw x e)=step J a b e (obs x))
    (t : Nat) (x : X) (A : C x) :
    iidHitCost raw (fun y => (obs y).hit=true) t x =
      iidHitCost (fun y e=>step J a b e y) (fun y => y.hit=true) t (obs x) := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    by_cases H : (obs x).hit=true
    · simp [iidHitCost,H]
    · simp only [iidHitCost,if_neg H]
      congr 2
      apply congrArg List.ofFn
      funext e
      rw [ih _ (stay x e A),comm _ _ A]

/-- Count only actual paint events as hits via an absorbing observer bit. -/
def monitor {X : Type} {n : Nat} (raw : X → Fin n → X)
    (paints : X → Fin n → Bool) (x : X × Bool) (e : Fin n) : X × Bool :=
  (raw x.1 e,x.2 || paints x.1 e)

theorem original_tape_mean {X : Type} {n J : Nat} (P : 0<J) (a b : Fin n) (D : a≠b)
    (raw : X → Fin n → X) (paints : X → Fin n → Bool)
    (C : X → Prop) (stay : ∀ x e, C x → C (raw x e))
    (phaseOf : X→Phase) (countOf : X→Nat)
    (comm : ∀ x e h, C x →
      (⟨phaseOf (raw x e),countOf (raw x e),h || paints x e⟩ : State) =
      step J a b e ⟨phaseOf x,countOf x,h⟩)
    (x : X) (A : C x) :
    IIDExpectedHittingTimeAtMost (monitor raw paints) (fun y=>y.2=true)
      (x,false) (4*n*2^J) := by
  intro t
  let obs : X×Bool→State := fun y=>⟨phaseOf y.1,countOf y.1,y.2⟩
  rw [show iidHitCost (monitor raw paints) (fun y=>y.2=true) t (x,false) =
    iidHitCost (monitor raw paints) (fun y=>(obs y).hit=true) t (x,false) from rfl,
    factor_cost a b (fun y : X×Bool=>C y.1)
      (fun y e B=>stay y.1 e B) obs (fun y e B=>comm y.1 e y.2 B) t (x,false) A]
  exact arbitrary_clock_mean P a b D (obs (x,false)) t

end L4.ReportPulseWait
