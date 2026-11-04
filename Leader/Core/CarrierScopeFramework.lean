set_option autoImplicit false

namespace CarrierScopeFramework

structure PopulationProtocol where
  Q : Type
  Y : Type
  transition : Q → Q → Q × Q
  output : Q → Y

structure ComplementView (P : PopulationProtocol) {S : Type}
    (view : P.Q → S) where
  T : Type
  outside : P.Q → T
  separate :
    ∀ x y, view x = view y → outside x = outside y → x = y

structure RefinesFamily (P : PopulationProtocol) {S : Type}
    (view : P.Q → S) (selected : P.Q → P.Q → Prop)
    (row : S → S → S × S) : Prop where
  left :
    ∀ l r, selected l r →
      view ((P.transition l r).1) =
        (row (view l) (view r)).1
  right :
    ∀ l r, selected l r →
      view ((P.transition l r).2) =
        (row (view l) (view r)).2

structure Framed (P : PopulationProtocol) {S : Type}
    (view : P.Q → S) (complement : ComplementView P view)
    (selected : P.Q → P.Q → Prop) : Prop where
  left :
    ∀ l r, selected l r →
      complement.outside ((P.transition l r).1) =
        complement.outside l
  right :
    ∀ l r, selected l r →
      complement.outside ((P.transition l r).2) =
        complement.outside r

def DispatchCovered {k : Nat} (P : PopulationProtocol)
    (selected : Fin k → P.Q → P.Q → Prop) : Prop :=
  ∀ l r, ∃ i : Fin k, selected i l r

structure DispatchComplete {k : Nat} (P : PopulationProtocol)
    (selected : Fin k → P.Q → P.Q → Prop) : Prop where
  covered : DispatchCovered P selected
  unique :
    ∀ l r (i j : Fin k),
      selected i l r → selected j l r → i = j

theorem assembled_agrees_of_coverage
    {k : Nat} (P : PopulationProtocol)
    (S : Fin k → Type)
    (view : (i : Fin k) → P.Q → S i)
    (complement : (i : Fin k) → ComplementView P (view i))
    (selected : Fin k → P.Q → P.Q → Prop)
    (row : (i : Fin k) → S i → S i → S i × S i)
    (hrefine :
      ∀ i, RefinesFamily P (view i) (selected i) (row i))
    (hframe :
      ∀ i, Framed P (view i) (complement i) (selected i))
    (hcover : DispatchCovered P selected) :
    ∀ l r, ∃ i : Fin k,
      selected i l r ∧
      view i ((P.transition l r).1) =
        (row i (view i l) (view i r)).1 ∧
      view i ((P.transition l r).2) =
        (row i (view i l) (view i r)).2 ∧
      (complement i).outside ((P.transition l r).1) =
        (complement i).outside l ∧
      (complement i).outside ((P.transition l r).2) =
        (complement i).outside r := by
  intro l r
  cases hcover l r with
  | intro i hi =>
      exact ⟨i, hi,
        (hrefine i).left l r hi,
        (hrefine i).right l r hi,
        (hframe i).left l r hi,
        (hframe i).right l r hi⟩

theorem assembled_agrees
    {k : Nat} (P : PopulationProtocol)
    (S : Fin k → Type)
    (view : (i : Fin k) → P.Q → S i)
    (complement : (i : Fin k) → ComplementView P (view i))
    (selected : Fin k → P.Q → P.Q → Prop)
    (row : (i : Fin k) → S i → S i → S i × S i)
    (hrefine :
      ∀ i, RefinesFamily P (view i) (selected i) (row i))
    (hframe :
      ∀ i, Framed P (view i) (complement i) (selected i))
    (hdispatch : DispatchComplete P selected) :
    ∀ l r, ∃ i : Fin k,
      selected i l r ∧
      view i ((P.transition l r).1) =
        (row i (view i l) (view i r)).1 ∧
      view i ((P.transition l r).2) =
        (row i (view i l) (view i r)).2 ∧
      (complement i).outside ((P.transition l r).1) =
        (complement i).outside l ∧
      (complement i).outside ((P.transition l r).2) =
        (complement i).outside r ∧
      ∀ j : Fin k, selected j l r → j = i := by
  intro l r
  cases hdispatch.covered l r with
  | intro i hi =>
      exact ⟨i, hi,
        (hrefine i).left l r hi,
        (hrefine i).right l r hi,
        (hframe i).left l r hi,
        (hframe i).right l r hi,
        fun j hj => hdispatch.unique l r j i hj hi⟩

structure ScopedCarrier where
  State : Nat → Nat → Type
  all : (psi h : Nat) → List (State psi h)
  complete :
    ∀ psi h (x : State psi h), List.Mem x (all psi h)
  nodup :
    ∀ psi h, (all psi h).Nodup

namespace ScopedCarrier

def count (C : ScopedCarrier) (psi h : Nat) : Nat :=
  (C.all psi h).length

def countAtPopulation (C : ScopedCarrier)
    (psi h : Nat) (_n : Nat) : Nat :=
  C.count psi h

theorem countAtPopulation_independent
    (C : ScopedCarrier) (psi h n m : Nat) :
    C.countAtPopulation psi h n =
      C.countAtPopulation psi h m := by
  rfl

end ScopedCarrier

structure ScopedProtocol (C : ScopedCarrier) where
  Y : Type
  transition :
    (psi h : Nat) →
      C.State psi h → C.State psi h →
        C.State psi h × C.State psi h
  output :
    (psi h : Nat) → C.State psi h → Y

namespace ScopedProtocol

def instantiate (C : ScopedCarrier) (P : ScopedProtocol C)
    (psi h : Nat) : PopulationProtocol where
  Q := C.State psi h
  Y := P.Y
  transition := P.transition psi h
  output := P.output psi h

end ScopedProtocol

structure ExactCostTransfer
    {B A E : Type}
    (erase : B → A)
    (boundedStep : B → E → B)
    (auditStep : A → E → A)
    (boundedTerminal : B → Prop)
    (auditTerminal : A → Prop) : Prop where
  step :
    ∀ b e,
      erase (boundedStep b e) =
        auditStep (erase b) e
  terminal :
    ∀ b,
      boundedTerminal b ↔ auditTerminal (erase b)

theorem audit_step_in_image
    {B A E : Type}
    (erase : B → A)
    (boundedStep : B → E → B)
    (auditStep : A → E → A)
    (boundedTerminal : B → Prop)
    (auditTerminal : A → Prop)
    (T : ExactCostTransfer erase boundedStep auditStep
      boundedTerminal auditTerminal)
    (b : B) (e : E) :
    ∃ b' : B,
      erase b' = auditStep (erase b) e := by
  exact ⟨boundedStep b e, T.step b e⟩

def run {X E : Type}
    (step : X → E → X) (x : X) : List E → X
  | [] => x
  | e :: es => run step (step x e) es

theorem run_transfer
    {B A E : Type}
    (erase : B → A)
    (boundedStep : B → E → B)
    (auditStep : A → E → A)
    (boundedTerminal : B → Prop)
    (auditTerminal : A → Prop)
    (T : ExactCostTransfer erase boundedStep auditStep
      boundedTerminal auditTerminal)
    (b : B) (events : List E) :
    erase (run boundedStep b events) =
      run auditStep (erase b) events := by
  induction events generalizing b with
  | nil => rfl
  | cons e es ih =>
      change
        erase (run boundedStep (boundedStep b e) es) =
          run auditStep (auditStep (erase b) e) es
      rw [← T.step b e]
      exact ih (boundedStep b e)

theorem terminal_run_iff
    {B A E : Type}
    (erase : B → A)
    (boundedStep : B → E → B)
    (auditStep : A → E → A)
    (boundedTerminal : B → Prop)
    (auditTerminal : A → Prop)
    (T : ExactCostTransfer erase boundedStep auditStep
      boundedTerminal auditTerminal)
    (b : B) (events : List E) :
    boundedTerminal (run boundedStep b events) ↔
      auditTerminal (run auditStep (erase b) events) := by
  have hrun := run_transfer erase boundedStep auditStep
    boundedTerminal auditTerminal T b events
  rw [← hrun]
  exact T.terminal (run boundedStep b events)

end CarrierScopeFramework

#print axioms CarrierScopeFramework.assembled_agrees_of_coverage
#print axioms CarrierScopeFramework.assembled_agrees
#print axioms CarrierScopeFramework.ScopedCarrier.countAtPopulation_independent
#print axioms CarrierScopeFramework.audit_step_in_image
#print axioms CarrierScopeFramework.run_transfer
#print axioms CarrierScopeFramework.terminal_run_iff
