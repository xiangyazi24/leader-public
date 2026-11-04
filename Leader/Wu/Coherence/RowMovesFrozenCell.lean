import Std
import Leader.Wu.Splice.NeutralRow

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace ZZV31MovesFrozen

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open R2CoherenceV31

private theorem h3 : 0 < 3 := by decide
private theorem h23 : 2 ≤ 3 := by decide
private theorem h02 : 0 < 2 := by decide

/-- Byte-for-byte reconstruction of the private payload in `ZZFrozen45`. -/
private def literalFollower (lab : Fin 3) : R2.Cell 3 3 48 :=
  let seed := WriterProducerRegression.clean h3 (fun _ => false) lab
  let b := seed.base.core.core
  let b' : BoundedAgentState 3 3 := {
    b with
      leader := false
      shield := false
      gen_ws := false
      label := lab
      state := .none
      path := .bot
      bit := false
      path2 := none
      path3 := none
      path4 := none
      path5 := none
      p := false
      p_carry := false
      reset_cmd := false
      echo := false
      write_state := .none
      write := .none
      b_carry := false }
  ⟨⟨⟨b', false⟩, 48⟩, 0⟩

/-- V3.1 analogue of the old frozen cell: identical physical payload,
with the V3.1 control exactly `(.closing,.none)`. -/
def frozenV3Cell (k : Fin 3) : R2CoherenceV31.Cell 3 3 48 :=
  ⟨literalFollower k, ⟨.closing, .none⟩⟩

/-- Old-controller copy, only for the contrast theorem below. -/
private def frozenOldCell (k : Fin 3) : R2Coherence.Cell 3 3 48 :=
  ⟨literalFollower k, ⟨.closing, .none⟩⟩

@[simp] theorem frozenV3Cell_tok (k : Fin 3) :
    (frozenV3Cell k).ctl.tok = .none := by
  rfl

@[simp] theorem frozenV3Cell_mark (k : Fin 3) :
    (frozenV3Cell k).ctl.mark = .closing := by
  rfl

@[simp] theorem frozenV3Cell_label (k : Fin 3) :
    (R2CoherenceV31.raw (frozenV3Cell k)).label = k := by
  rfl

/-! ## Attack check: the six top-level V3.1 token guards are all false. -/

theorem rowV3_six_guards_false (a b : Fin 3) :
    (frozenV3Cell b).ctl.tok ≠ .seek ∧
    (frozenV3Cell a).ctl.tok ≠ .sweep ∧
    (frozenV3Cell b).ctl.tok ≠ .commit ∧
    (frozenV3Cell a).ctl.tok ≠ .release ∧
    (frozenV3Cell b).ctl.tok ≠ .scrubL ∧
    (frozenV3Cell a).ctl.tok ≠ .openR := by
  simp [frozenV3Cell]

/-- With token-free closing/closing controls, `rowV3` reaches exactly the
new passive normalizer. This is the branch that did not exist in the old row. -/
theorem rowV3_eq_normalizePassiveV3 (a b : Fin 3) :
    R2CoherenceV31.rowV3 h3 h02 h23
      (frozenV3Cell a) (frozenV3Cell b) =
    R2CoherenceV31.normalizePassiveV3
      (frozenV3Cell a) (frozenV3Cell b) := by
  simp [R2CoherenceV31.rowV3,
    R2CoherenceV31.ordinaryStageV3, frozenV3Cell]

/-- Exact result on an admitted edge. -/
theorem rowV3_exact_frozen_of_admitted
    (a b : Fin 3)
    (hOK : R2CoherenceV31.passiveEdgeOKV3
      (frozenV3Cell a) (frozenV3Cell b) = true) :
    R2CoherenceV31.rowV3 h3 h02 h23
      (frozenV3Cell a) (frozenV3Cell b) =
    (frozenV3Cell a,
      R2CoherenceV31.startClosing (frozenV3Cell b)) := by
  rw [rowV3_eq_normalizePassiveV3]
  exact R2CoherenceV31.normalizePassiveV3_good_edge
    (frozenV3Cell a) (frozenV3Cell b) hOK

/-- Stronger than requested: every closing/none pair moves.  On an admitted
edge the right token becomes SEEK; on a non-admitted edge the left mark becomes
OPEN. -/
theorem rowV3_moves_frozen (a b : Fin 3) :
    R2CoherenceV31.rowV3 h3 h02 h23
      (frozenV3Cell a) (frozenV3Cell b) ≠
    (frozenV3Cell a, frozenV3Cell b) := by
  rw [rowV3_eq_normalizePassiveV3]
  cases h : R2CoherenceV31.passiveEdgeOKV3
      (frozenV3Cell a) (frozenV3Cell b) with
  | false =>
      rw [R2CoherenceV31.normalizePassiveV3_bad_edge
        (frozenV3Cell a) (frozenV3Cell b) h]
      intro heq
      have hm := congrArg
        (fun q : R2CoherenceV31.Cell 3 3 48 ×
            R2CoherenceV31.Cell 3 3 48 => q.1.ctl.mark) heq
      change R2Coherence.Mark.open = R2Coherence.Mark.closing at hm
      cases hm
  | true =>
      rw [R2CoherenceV31.normalizePassiveV3_good_edge
        (frozenV3Cell a) (frozenV3Cell b) h]
      intro heq
      have ht := congrArg
        (fun q : R2CoherenceV31.Cell 3 3 48 ×
            R2CoherenceV31.Cell 3 3 48 => q.2.ctl.tok) heq
      change R2CoherenceV31.TokenV3.seek =
        R2CoherenceV31.TokenV3.none at ht
      cases ht

/-! ## Attack check: `passiveEdgeOKV3 = atRootB r || successorB l r`. -/

/-- Ordinary successor edge `0 -> 1`: right is not root; successor is true. -/
theorem passive_guard_01 :
    R2CoherenceV31.atRootB (frozenV3Cell 1) = false ∧
    R2CoherenceV31.successorB
      (frozenV3Cell 0) (frozenV3Cell 1) = true := by
  decide +kernel

/-- Ordinary successor edge `1 -> 2`: right is not root; successor is true. -/
theorem passive_guard_12 :
    R2CoherenceV31.atRootB (frozenV3Cell 2) = false ∧
    R2CoherenceV31.successorB
      (frozenV3Cell 1) (frozenV3Cell 2) = true := by
  decide +kernel

/-- Wrap edge `2 -> 0`: successorB is false, but the right endpoint is root. -/
theorem passive_guard_20 :
    R2CoherenceV31.atRootB (frozenV3Cell 0) = true ∧
    R2CoherenceV31.successorB
      (frozenV3Cell 2) (frozenV3Cell 0) = false := by
  decide +kernel

private def next3 (a : Fin 3) : Fin 3 :=
  ⟨(a.val + 1) % 3, Nat.mod_lt _ h3⟩

private theorem fin3_cases (a : Fin 3) :
    a = (0 : Fin 3) ∨ a = 1 ∨ a = 2 := by
  have ha : a.val < 3 := a.isLt
  have hv : a.val = 0 ∨ a.val = 1 ∨ a.val = 2 := by
    omega
  rcases hv with h | h | h
  · left
    apply Fin.ext
    omega
  · right; left
    apply Fin.ext
    omega
  · right; right
    apply Fin.ext
    omega

/-- Every cyclic ruler edge `a -> (a+1) mod 3` is admitted.  This explicitly
covers the wrap via `atRootB`, not via `successorB`. -/
theorem passiveEdgeOKV3_next3 (a : Fin 3) :
    R2CoherenceV31.passiveEdgeOKV3
      (frozenV3Cell a) (frozenV3Cell (next3 a)) = true := by
  rcases fin3_cases a with h | h | h
  all_goals subst a
  all_goals decide +kernel

/-- Requested exact successor-labelled result, including `2 -> 0`. -/
theorem rowV3_exact_frozen_successor (a : Fin 3) :
    R2CoherenceV31.rowV3 h3 h02 h23
      (frozenV3Cell a) (frozenV3Cell (next3 a)) =
    (frozenV3Cell a,
      R2CoherenceV31.startClosing (frozenV3Cell (next3 a))) := by
  exact rowV3_exact_frozen_of_admitted
    a (next3 a) (passiveEdgeOKV3_next3 a)

/-- Requested nonidentity on every cyclic successor-labelled pair. -/
theorem rowV3_moves_frozen_successor (a : Fin 3) :
    R2CoherenceV31.rowV3 h3 h02 h23
      (frozenV3Cell a) (frozenV3Cell (next3 a)) ≠
    (frozenV3Cell a, frozenV3Cell (next3 a)) := by
  exact rowV3_moves_frozen a (next3 a)

/-! ## Old-row contrast: this same shape is exactly the old identity arm. -/

theorem old_row_identity (a b : Fin 3) :
    R2Coherence.row h3 h02 h23
      (frozenOldCell a) (frozenOldCell b) =
    (frozenOldCell a, frozenOldCell b) := by
  simp [R2Coherence.row, R2Coherence.ordinaryStage, frozenOldCell]

#print axioms ZZV31MovesFrozen.rowV3_exact_frozen_successor
#print axioms ZZV31MovesFrozen.rowV3_moves_frozen
#print axioms ZZV31MovesFrozen.old_row_identity

end ZZV31MovesFrozen
