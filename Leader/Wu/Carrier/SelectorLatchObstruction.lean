import Leader.Wu.Safety.CorrectedFormulation

/-!
# Pair-local selector/latch obstruction

This file records the smallest disjoint-copy obstruction behind a proposed
select-then-serve overlay.  The quotient is deliberately stronger than the
positive-gap physical carrier: one interaction sees two adjacent virtual
roots directly.

If a row can create a token on an idle pair, two disjoint copies of that row
create two tokens.  Likewise, every one-row admission and every two-row
prepare/admit path can be replayed on two disjoint identical token/idle views.
The final section evaluates concrete total rows used by the finite checker.
-/

namespace PPLLSelectorLatchLocality

open PPLLResearchFormulation

set_option autoImplicit false
set_option warningAsError true

theorem ringFour : DirectedRing 4 := ⟨by omega⟩

@[simp] theorem ringFour_right_zero :
    ringFour.rightNeighbor (0 : Fin 4) = 1 := by
  apply Fin.ext
  decide

@[simp] theorem ringFour_right_one :
    ringFour.rightNeighbor (1 : Fin 4) = 2 := by
  apply Fin.ext
  decide

@[simp] theorem ringFour_right_two :
    ringFour.rightNeighbor (2 : Fin 4) = 3 := by
  apply Fin.ext
  decide

@[simp] theorem ringFour_right_three :
    ringFour.rightNeighbor (3 : Fin 4) = 0 := by
  apply Fin.ext
  decide

def repeatedPair {Q : Type} (left right : Q) : Fin 4 → Q :=
  fun i => if i = 0 ∨ i = 2 then left else right

@[simp] theorem repeatedPair_zero {Q : Type} (left right : Q) :
    repeatedPair left right 0 = left := by
  simp [repeatedPair]

@[simp] theorem repeatedPair_one {Q : Type} (left right : Q) :
    repeatedPair left right 1 = right := by
  simp [repeatedPair]

@[simp] theorem repeatedPair_two {Q : Type} (left right : Q) :
    repeatedPair left right 2 = left := by
  simp [repeatedPair]

@[simp] theorem repeatedPair_three {Q : Type} (left right : Q) :
    repeatedPair left right 3 = right := by
  simp [repeatedPair]

/-- Two disjoint copies of the same ordered local view execute the same row.
This is the exact four-root kernel used by both the birth and admission
counterexamples. -/
theorem disjoint_pair_row_replicates {Q : Type}
    (T : Q → Q → Q × Q) (left right outLeft outRight : Q)
    (hrow : T left right = (outLeft, outRight)) :
    runLocalSchedule ringFour T (repeatedPair left right) [0, 2] =
      repeatedPair outLeft outRight := by
  funext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;>
    simp [runLocalSchedule, localStep, hrow]

/-- Any direct nontrivial idle/idle birth row is reproducible at two disjoint
locations.  Keeping the idle/idle row framed instead leaves the uniform idle
configuration fixed. -/
theorem idle_birth_replicates {Q : Type}
    (T : Q → Q → Q × Q) (idle born : Q)
    (hbirth : T idle idle = (born, idle)) :
    runLocalSchedule ringFour T (fun _ => idle) [0, 2] =
      repeatedPair born idle := by
  have huniform : (fun _ : Fin 4 => idle) = repeatedPair idle idle := by
    funext i
    simp [repeatedPair]
  rw [huniform]
  exact disjoint_pair_row_replicates T idle idle born idle hbirth

/-- A one-row latch enabled by the local token/idle view cannot distinguish a
singleton token from two separated tokens with the same view. -/
theorem one_row_admission_replicates {Q : Type}
    (T : Q → Q → Q × Q) (idle token latch : Q)
    (hadmit : T token idle = (latch, idle)) :
    runLocalSchedule ringFour T (repeatedPair token idle) [0, 2] =
      repeatedPair latch idle :=
  disjoint_pair_row_replicates T token idle latch idle hadmit

/-- Adding a bounded prepare state does not help: the two-step local history
also has two disjoint copies. -/
theorem two_row_admission_replicates {Q : Type}
    (T : Q → Q → Q × Q) (idle token prepared latch : Q)
    (hprepare : T token idle = (prepared, idle))
    (hadmit : T prepared idle = (latch, idle)) :
    runLocalSchedule ringFour T (repeatedPair token idle) [0, 0, 2, 2] =
      repeatedPair latch idle := by
  simp only [runLocalSchedule]
  funext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;>
    simp [localStep, repeatedPair, hprepare, hadmit]

/-! ## Concrete total rows -/

inductive SelectorState
  | empty
  | token
  | prepared
  | latch
  deriving DecidableEq, Repr

/-- Total moving/coalescing row.  All omitted cases frame. -/
def coalesceRow : SelectorState → SelectorState →
    SelectorState × SelectorState
  | .token, .empty => (.empty, .token)
  | .token, .token => (.token, .empty)
  | left, right => (left, right)

/-- Total one-row admission candidate.  Adjacent latches coalesce, but
separated latches are immobile. -/
def admitRow : SelectorState → SelectorState →
    SelectorState × SelectorState
  | .token, .token => (.token, .empty)
  | .token, .empty => (.latch, .empty)
  | .latch, .latch => (.latch, .empty)
  | left, right => (left, right)

/-- Total two-row prepare/admit candidate. -/
def twoRow : SelectorState → SelectorState →
    SelectorState × SelectorState
  | .token, .token => (.token, .empty)
  | .token, .empty => (.prepared, .empty)
  | .prepared, .empty => (.latch, .empty)
  | .latch, .latch => (.latch, .empty)
  | left, right => (left, right)

def allTokens : Fin 4 → SelectorState := fun _ => .token

/-- The concrete one-row table reaches two separated latches in four
interactions. -/
theorem admitRow_double_latch :
    runLocalSchedule ringFour admitRow allTokens [0, 0, 2, 2] =
      repeatedPair .latch .empty := by
  funext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;>
    decide

/-- The concrete two-row table reaches the same bad state in six
interactions. -/
theorem twoRow_double_latch :
    runLocalSchedule ringFour twoRow allTokens [0, 0, 0, 2, 2, 2] =
      repeatedPair .latch .empty := by
  funext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;>
    decide

#print axioms disjoint_pair_row_replicates
#print axioms idle_birth_replicates
#print axioms one_row_admission_replicates
#print axioms two_row_admission_replicates
#print axioms admitRow_double_latch
#print axioms twoRow_double_latch

end PPLLSelectorLatchLocality
