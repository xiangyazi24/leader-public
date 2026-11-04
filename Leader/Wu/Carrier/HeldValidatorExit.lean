import Leader.Core.Basic

/-!
# Exact held-validator exit word for the literal PPLL-v2 rows

This file isolates the three local rows used by the parametric obstruction
exit.  They are the literal v2 rewrites

* `F:. , F:deny-keep -> F:deny-keep , E:.`,
* `validate-S , F:deny-keep -> S , E:.`, and
* `E:. , target-hold -> E:. , T`.

`Fires edge before after` includes the untouched left/right context, so the
edge labels are the physical corridor labels.  The theorem proves that

`[ell-1, ..., 1, 0, ell]`

has length exactly `ell+1` and carries the stated all-length family to
`(S,E^ell,T)`.  It does not encode the other v2 table rows or claim that this
small transition relation is the full protocol semantics; the companion
Python cold audit pins and executes the complete literal table.
-/

namespace PPLLV2HeldValidatorExit

set_option autoImplicit false

inductive RootMode where
  | stableSource
  | validateSource
  | targetHold
  | stableTarget
  deriving DecidableEq, Repr

inductive CellMode where
  | empty
  | frozen
  | denyKeep
  deriving DecidableEq, Repr

structure Corridor where
  left : RootMode
  lane : List CellMode
  right : RootMode
  deriving DecidableEq, Repr

/-- The exact local v2 rows needed by the exit word, with arbitrary untouched
lane context. -/
inductive Fires : Nat → Corridor → Corridor → Prop where
  | frozenDeny (pre suffix : List CellMode) :
      Fires (pre.length + 1)
        ⟨.validateSource,
          pre ++ .frozen :: .denyKeep :: suffix,
          .targetHold⟩
        ⟨.validateSource,
          pre ++ .denyKeep :: .empty :: suffix,
          .targetHold⟩
  | sourceConsumesDeny (suffix : List CellMode) :
      Fires 0
        ⟨.validateSource, .denyKeep :: suffix, .targetHold⟩
        ⟨.stableSource, .empty :: suffix, .targetHold⟩
  | heldTargetRetires (pre : List CellMode) :
      Fires (pre.length + 1)
        ⟨.stableSource, pre ++ [.empty], .targetHold⟩
        ⟨.stableSource, pre ++ [.empty], .stableTarget⟩

/-- Execute a concrete physical-edge word in the exact-row relation. -/
inductive Runs : Corridor → List Nat → Corridor → Prop where
  | nil (state : Corridor) : Runs state [] state
  | cons {before middle after : Corridor} {edge : Nat} {word : List Nat}
      (head : Fires edge before middle)
      (tail : Runs middle word after) :
      Runs before (edge :: word) after

theorem Runs.append {first middle last : Corridor} {preword suffix : List Nat}
    (hpreword : Runs first preword middle)
    (hsuffix : Runs middle suffix last) :
    Runs first (preword ++ suffix) last := by
  induction hpreword generalizing last suffix with
  | nil => simpa using hsuffix
  | cons head tail ih =>
      exact Runs.cons head (ih hsuffix)

/-- Reverse sweep: `k` frozen cells followed by the denial are converted to
`k+1` empty cells by the exact word `[k,...,0]`. -/
theorem drainDeny (k : Nat) (suffix : List CellMode) :
    Runs
      ⟨.validateSource,
        List.replicate k .frozen ++ .denyKeep :: suffix,
        .targetHold⟩
      (List.range (k + 1)).reverse
      ⟨.stableSource,
        List.replicate (k + 1) .empty ++ suffix,
        .targetHold⟩ := by
  induction k generalizing suffix with
  | zero =>
      simpa using
        Runs.cons (Fires.sourceConsumesDeny suffix)
          (Runs.nil
            ⟨.stableSource, .empty :: suffix, .targetHold⟩)
  | succ k ih =>
      have htail := ih (.empty :: suffix)
      have hrun :=
        Runs.cons
          (Fires.frozenDeny (List.replicate k .frozen) suffix)
          htail
      simpa [List.range_succ, List.replicate_succ', List.append_assoc] using hrun

/-- The distinguished obstruction state `D_ell`. -/
def heldValidator (ell : Nat) : Corridor :=
  ⟨.validateSource,
    List.replicate (ell - 1) .frozen ++ [.denyKeep],
    .targetHold⟩

/-- The stopped role-terminal endpoint used by the Bellman/block argument. -/
def settled (ell : Nat) : Corridor :=
  ⟨.stableSource, List.replicate ell .empty, .stableTarget⟩

/-- The concrete physical word `[ell-1,...,1,0,ell]`. -/
def exitWord (ell : Nat) : List Nat :=
  (List.range ell).reverse ++ [ell]

@[simp] theorem exitWord_length (ell : Nat) :
    (exitWord ell).length = ell + 1 := by
  simp [exitWord]

/-- Exact parametric exit: the word of length `ell+1` sends `D_ell` to
`(S,E^ell,T)` for every positive corridor length. -/
theorem heldValidator_exitWord (ell : Nat) (hell : 0 < ell) :
    Runs (heldValidator ell) (exitWord ell) (settled ell) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hell)
  have hdrain := drainDeny k ([] : List CellMode)
  have hretire :
      Runs
        ⟨.stableSource, List.replicate (k + 1) .empty, .targetHold⟩
        [k + 1]
        ⟨.stableSource, List.replicate (k + 1) .empty, .stableTarget⟩ := by
    simpa [List.replicate_succ', List.append_assoc] using
      Runs.cons (Fires.heldTargetRetires (List.replicate k .empty))
        (Runs.nil
          ⟨.stableSource, List.replicate k .empty ++ [.empty],
            .stableTarget⟩)
  have hdrain' :
      Runs
        ⟨.validateSource,
          List.replicate k .frozen ++ [.denyKeep],
          .targetHold⟩
        (List.range (k + 1)).reverse
        ⟨.stableSource, List.replicate (k + 1) .empty, .targetHold⟩ := by
    simpa using hdrain
  have hrun := Runs.append hdrain' hretire
  simpa [heldValidator, exitWord, settled, List.append_assoc] using hrun

#print axioms exitWord_length
#print axioms drainDeny
#print axioms heldValidator_exitWord

end PPLLV2HeldValidatorExit
