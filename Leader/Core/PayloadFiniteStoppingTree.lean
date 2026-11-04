import Leader.Core.FiniteUniformStoppingTree

/-!
# Payload-carrying finite stopping trees and first-terminal bind

Unlike `FiniteUniformStoppingTree.StopNode`, both terminal constructors below
retain their concrete endpoint payload.  The `firstTerminalBindMass` fold
starts a continuation at that endpoint immediately.  Scheduler choices left
unused from the first local budget are counted only after the continuation;
they are therefore padding after overall success, not physical interactions
inserted between two protocol stages.
-/

namespace PayloadFiniteStoppingTree

set_option autoImplicit false

open FiniteUniformStoppingTree

/-- Active, successful, and failed nodes with separate payload types. -/
inductive PayloadNode (A S F : Type) where
  | active : A -> PayloadNode A S F
  | success : S -> PayloadNode A S F
  | failure : F -> PayloadNode A S F

/-- Extend an active transition by absorbing both payload terminals. -/
def stepNode {A S F : Type} {n : Nat}
    (step : A -> Fin n -> PayloadNode A S F) :
    PayloadNode A S F -> Fin n -> PayloadNode A S F
  | .active a, e => step a e
  | s@(.success _), _ => s
  | f@(.failure _), _ => f

/-- Exact successful terminal mass at a fixed local horizon. -/
def successMass {A S F : Type} {n : Nat}
    (step : A -> Fin n -> PayloadNode A S F) :
    PayloadNode A S F -> Nat -> Nat
  | .active _, 0 => 0
  | .success _, 0 => 1
  | .failure _, 0 => 0
  | x, T + 1 =>
      (List.ofFn (fun e : Fin n =>
        successMass step (stepNode step x e) T)).sum

/-- Exact failed terminal mass at a fixed local horizon. -/
def failureMass {A S F : Type} {n : Nat}
    (step : A -> Fin n -> PayloadNode A S F) :
    PayloadNode A S F -> Nat -> Nat
  | .active _, 0 => 0
  | .success _, 0 => 0
  | .failure _, 0 => 1
  | x, T + 1 =>
      (List.ofFn (fun e : Fin n =>
        failureMass step (stepNode step x e) T)).sum

@[simp] theorem successMass_success {A S F : Type} {n : Nat}
    (step : A -> Fin n -> PayloadNode A S F) (s : S) :
    forall T, successMass step (.success s) T = n ^ T := by
  intro T
  induction T with
  | zero => rfl
  | succ T ih =>
      simp only [successMass, stepNode]
      rw [show (List.ofFn (fun _ : Fin n =>
        successMass step (.success s) T)).sum =
          n * successMass step (.success s) T by
            exact ofFn_sum_const n _]
      rw [ih]
      simp [Nat.pow_succ, Nat.mul_comm]

@[simp] theorem successMass_failure {A S F : Type} {n : Nat}
    (step : A -> Fin n -> PayloadNode A S F) (f : F) :
    forall T, successMass step (.failure f) T = 0 := by
  intro T
  induction T with
  | zero => rfl
  | succ T ih =>
      simp only [successMass, stepNode, ih]
      rw [ofFn_sum_const]
      simp

@[simp] theorem failureMass_success {A S F : Type} {n : Nat}
    (step : A -> Fin n -> PayloadNode A S F) (s : S) :
    forall T, failureMass step (.success s) T = 0 := by
  intro T
  induction T with
  | zero => rfl
  | succ T ih =>
      simp only [failureMass, stepNode, ih]
      rw [ofFn_sum_const]
      simp

@[simp] theorem failureMass_failure {A S F : Type} {n : Nat}
    (step : A -> Fin n -> PayloadNode A S F) (f : F) :
    forall T, failureMass step (.failure f) T = n ^ T := by
  intro T
  induction T with
  | zero => rfl
  | succ T ih =>
      simp only [failureMass, stepNode]
      rw [show (List.ofFn (fun _ : Fin n =>
        failureMass step (.failure f) T)).sum =
          n * failureMass step (.failure f) T by
            exact ofFn_sum_const n _]
      rw [ih]
      simp [Nat.pow_succ, Nat.mul_comm]

/-- Forget terminal payloads, retaining the active payload used by the
existing stopped-tree analytic library. -/
def PayloadNode.erase {A S F : Type} :
    PayloadNode A S F -> StopNode A
  | .active a => .active a
  | .success _ => .success
  | .failure _ => .failure

def eraseStep {A S F : Type} {n : Nat}
    (step : A -> Fin n -> PayloadNode A S F) : A -> Fin n -> StopNode A :=
  fun a e => (step a e).erase

/-- Payload retention changes no scalar successful scheduler mass. -/
theorem successMass_eq_successCount {A S F : Type} {n : Nat}
    (step : A -> Fin n -> PayloadNode A S F) :
    forall (x : PayloadNode A S F) T,
      successMass step x T =
        successCount (eraseStep step) x.erase T := by
  intro x T
  induction T generalizing x with
  | zero => cases x <;> rfl
  | succ T ih =>
      cases x with
      | active a =>
          simp only [successMass, successCount, treeWeight, stepNode,
            PayloadNode.erase, eraseStep]
          exact ofFn_sum_eq _ _ (fun e => ih (step a e))
      | success s =>
          rw [successMass_success]
          simp [successCount, PayloadNode.erase, treeWeight_success,
            successWeight]
      | failure f =>
          rw [successMass_failure]
          simp [successCount, PayloadNode.erase, treeWeight_failure,
            successWeight]

/-- Payload retention changes no scalar failed scheduler mass. -/
theorem failureMass_eq_failureCount {A S F : Type} {n : Nat}
    (step : A -> Fin n -> PayloadNode A S F) :
    forall (x : PayloadNode A S F) T,
      failureMass step x T =
        failureCount (eraseStep step) x.erase T := by
  intro x T
  induction T generalizing x with
  | zero => cases x <;> rfl
  | succ T ih =>
      cases x with
      | active a =>
          simp only [failureMass, failureCount, treeWeight, stepNode,
            PayloadNode.erase, eraseStep]
          exact ofFn_sum_eq _ _ (fun e => ih (step a e))
      | success s =>
          rw [failureMass_success]
          simp [failureCount, PayloadNode.erase, treeWeight_success,
            failureWeight]
      | failure f =>
          rw [failureMass_failure]
          simp [failureCount, PayloadNode.erase, treeWeight_failure,
            failureWeight]

/-- A successful prefix of length `a` admits every length-`b` suffix.
This is the payload-tree form of persistent hit padding. -/
theorem successMass_mul_pow_le_add {A S F : Type} {n : Nat}
    (step : A -> Fin n -> PayloadNode A S F) :
    forall (x : PayloadNode A S F) a b,
      successMass step x a * n ^ b <= successMass step x (a + b) := by
  intro x a b
  induction a generalizing x with
  | zero =>
      cases x with
      | active z => simp [successMass]
      | success s => simp
      | failure f => simp
  | succ a ih =>
      cases x with
      | success s => simp [Nat.pow_add]
      | failure f => simp
      | active z =>
          simp only [successMass]
          have hpoint : forall e : Fin n,
              successMass step (step z e) a * n ^ b <=
                successMass step (step z e) (a + b) := by
            intro e
            exact ih (step z e)
          have hsum := ofFn_sum_le
            (fun e : Fin n => successMass step (step z e) a * n ^ b)
            (fun e : Fin n => successMass step (step z e) (a + b))
            hpoint
          calc
            (List.ofFn (fun e : Fin n =>
                successMass step (step z e) a)).sum * n ^ b =
                (List.ofFn (fun e : Fin n =>
                  successMass step (step z e) a * n ^ b)).sum := by
              rw [Nat.mul_comm
                    (List.ofFn (fun e : Fin n =>
                      successMass step (step z e) a)).sum (n ^ b),
                <- ofFn_sum_mul_left]
              apply ofFn_sum_eq
              intro e
              exact Nat.mul_comm _ _
            _ <= (List.ofFn (fun e : Fin n =>
                successMass step (step z e) (a + b))).sum := hsum
            _ = successMass step (.active z) (a + 1 + b) := by
              rw [show a + 1 + b = (a + b) + 1 by omega]
              rfl

#print axioms successMass_mul_pow_le_add

/-- Start the endpoint-dependent continuation immediately at the first
successful terminal.  `continuation s` already counts the fixed second-stage
words.  The `n^remaining` factor is unused first-stage budget placed after the
continuation. -/
def firstTerminalBindMass {A S F : Type} {n : Nat}
    (step : A -> Fin n -> PayloadNode A S F)
    (continuation : S -> Nat) : PayloadNode A S F -> Nat -> Nat
  | .active _, 0 => 0
  | .active a, T + 1 =>
      (List.ofFn (fun e : Fin n =>
        firstTerminalBindMass step continuation (step a e) T)).sum
  | .success s, remaining => n ^ remaining * continuation s
  | .failure _, _ => 0

/-- State-uniform continuation estimates multiply against the exact weighted
first-terminal mass.  This is the denominator-cleared strong-Markov/bind
principle needed by sequential finite protocol trials. -/
theorem successMass_mul_le_firstTerminalBindMass
    {A S F : Type} {n continuationScale continuationHorizon : Nat}
    (step : A -> Fin n -> PayloadNode A S F)
    (continuation : S -> Nat)
    (hcontinuation : forall s,
      n ^ continuationHorizon <= continuationScale * continuation s) :
    forall (x : PayloadNode A S F) T,
      n ^ continuationHorizon * successMass step x T <=
        continuationScale *
          firstTerminalBindMass step continuation x T := by
  intro x T
  induction T generalizing x with
  | zero =>
      cases x with
      | active a => simp [successMass, firstTerminalBindMass]
      | success s => simpa [successMass, firstTerminalBindMass] using
          hcontinuation s
      | failure f => simp [successMass, firstTerminalBindMass]
  | succ T ih =>
      cases x with
      | active a =>
          simp only [successMass, firstTerminalBindMass]
          calc
            n ^ continuationHorizon *
                (List.ofFn (fun e : Fin n =>
                  successMass step (step a e) T)).sum =
                (List.ofFn (fun e : Fin n =>
                  n ^ continuationHorizon *
                    successMass step (step a e) T)).sum := by
                      rw [ofFn_sum_mul_left]
            _ <= (List.ofFn (fun e : Fin n =>
                  continuationScale * firstTerminalBindMass step
                    continuation (step a e) T)).sum :=
              ofFn_sum_le _ _ (fun e => ih (step a e))
            _ = continuationScale *
                (List.ofFn (fun e : Fin n =>
                  firstTerminalBindMass step continuation
                    (step a e) T)).sum :=
              ofFn_sum_mul_left _ _
      | success s =>
          rw [successMass_success]
          simp only [firstTerminalBindMass]
          have hscaled := Nat.mul_le_mul_left (n ^ (T + 1))
            (hcontinuation s)
          simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hscaled
      | failure f => simp [successMass_failure, firstTerminalBindMass]

#print axioms successMass_mul_le_firstTerminalBindMass

/-! ## One-total-horizon continuation bind -/

/-- Start an endpoint-dependent continuation with exactly the scheduler
horizon remaining when the first stage succeeds.  Unlike
`firstTerminalBindMass`, no separate fixed continuation horizon is padded
after the first stage. -/
def remainingHorizonTerminalBindMass {A S F : Type} {n : Nat}
    (step : A -> Fin n -> PayloadNode A S F)
    (continuation : S -> Nat -> Nat) :
    PayloadNode A S F -> Nat -> Nat
  | _, 0 => 0
  | .active a, T + 1 =>
      (List.ofFn (fun e : Fin n =>
        remainingHorizonTerminalBindMass step continuation (step a e) T)).sum
  | .success s, T + 1 => continuation s (T + 1)
  | .failure _, _ + 1 => 0

/-- A continuation estimate uniform in both endpoint and remaining horizon
survives the exact first-terminal fold at the same total denominator. -/
theorem remainingHorizonTerminalBindMass_le
    {A S F : Type} {n continuationBudget : Nat}
    (step : A -> Fin n -> PayloadNode A S F)
    (continuation : S -> Nat -> Nat)
    (hcontinuation : forall endpoint T,
      continuation endpoint T <= n ^ T * continuationBudget) :
    forall (node : PayloadNode A S F) T,
      remainingHorizonTerminalBindMass step continuation node T <=
        n ^ T * continuationBudget := by
  intro node T
  induction T generalizing node with
  | zero => simp [remainingHorizonTerminalBindMass]
  | succ T ih =>
      cases node with
      | active state =>
          simp only [remainingHorizonTerminalBindMass]
          calc
            (List.ofFn (fun edge : Fin n =>
                remainingHorizonTerminalBindMass step continuation
                  (step state edge) T)).sum <=
              (List.ofFn (fun _ : Fin n =>
                n ^ T * continuationBudget)).sum :=
              ofFn_sum_le _ _ (fun edge => ih (step state edge))
            _ = n * (n ^ T * continuationBudget) :=
              ofFn_sum_const n _
            _ = n ^ (T + 1) * continuationBudget := by
              rw [Nat.pow_succ]
              ac_rfl
      | success endpoint =>
          exact hcontinuation endpoint (T + 1)
      | failure endpoint =>
          simp [remainingHorizonTerminalBindMass]

/-- Same-total-horizon cost of a first stopped stage followed immediately by
an endpoint-dependent continuation. -/
def remainingHorizonSequentialCostNumerator {A S F : Type} {n : Nat}
    (step : A -> Fin n -> PayloadNode A S F)
    (continuation : S -> Nat -> Nat)
    (node : PayloadNode A S F) (T : Nat) : Nat :=
  truncatedActiveCostNumerator (eraseStep step) node.erase T +
    remainingHorizonTerminalBindMass step continuation node T

/-- Additive stage composition at one common raw horizon. -/
theorem remainingHorizonSequentialCostNumerator_le
    {A S F : Type} {n firstBudget continuationBudget : Nat}
    (step : A -> Fin n -> PayloadNode A S F)
    (continuation : S -> Nat -> Nat)
    (node : PayloadNode A S F)
    (hfirst : forall T,
      truncatedActiveCostNumerator (eraseStep step) node.erase T <=
        n ^ T * firstBudget)
    (hcontinuation : forall endpoint T,
      continuation endpoint T <= n ^ T * continuationBudget) :
    forall T,
      remainingHorizonSequentialCostNumerator step continuation node T <=
        n ^ T * (firstBudget + continuationBudget) := by
  intro T
  unfold remainingHorizonSequentialCostNumerator
  exact Nat.le_trans
    (Nat.add_le_add (hfirst T)
      (remainingHorizonTerminalBindMass_le
        step continuation hcontinuation node T))
    (by rw [Nat.mul_add]; exact Nat.le_refl _)

end PayloadFiniteStoppingTree
