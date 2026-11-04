import Leader.Wu.Coherence.FootprintCoverAnchoring
import Leader.Wu.Coherence.ReachableOpenRProvenance

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

/-!
# Row-fact statements, separated from their consumers

The three row facts below used to be stated inside
`R2CoherenceV31FootprintCover2R`, which made it impossible to import a proof of
one of them back into that file: the proof file imports the consumer.  They are
stated here, in the same namespace, so that

* `R2CoherenceV31RowFacts` can import only the statements and prove them, and
* `R2CoherenceV31FootprintCover2R` can import the proofs and stop carrying the
  corresponding hypotheses in its signatures.

Moving a statement to this file is the first half of discharging it; the second
half is deleting the hypothesis from every signature that threaded it.
-/

namespace R2CoherenceV31FootprintCover2R

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open R2CoherenceV31 R2CoherenceBranches

variable {ψ κ τ : Nat}

/-- Exact former `rowMainClear2` statement.

Outside the `openNoHazard` branch, one pair operation preserves `MainClearV3`
on each side separately.  **Proved** in `R2CoherenceV31RowFacts` as
`rowMainClearFact_holds`; no consumer takes it as a hypothesis any more. -/
def RowMainClearFactV31 (ψ κ τ : Nat) : Prop :=
  ∀ {b : BranchV3} (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
      (l r : Cell ψ κ τ),
    branchAtV3 hψ h2 l r = b →
    b ≠ .openNoHazard →
    (MainClearV3 l →
      MainClearV3 (rowV3 hψ (by decide : 0 < 2) h2 l r).1) ∧
    (MainClearV3 r →
      MainClearV3 (rowV3 hψ (by decide : 0 < 2) h2 l r).2)

/-- Exact former `rowScrubBack2` statement.

Outside the `release` and `scrubL` branches, a `scrubL` token in an output cell
was already present in the corresponding input cell: no branch manufactures one.
Still an unsupplied hypothesis. -/
def RowScrubBackFactV31 (ψ κ τ : Nat) : Prop :=
  ∀ {b : BranchV3} (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
      (l r : Cell ψ κ τ),
    branchAtV3 hψ h2 l r = b →
    b ≠ .release → b ≠ .scrubL →
    ((rowV3 hψ (by decide : 0 < 2) h2 l r).1.ctl.tok = .scrubL →
      l.ctl.tok = .scrubL) ∧
    ((rowV3 hψ (by decide : 0 < 2) h2 l r).2.ctl.tok = .scrubL →
      r.ctl.tok = .scrubL)

/-- Exact former `rowFresh4` statement.

The `FreshnessClearV31` analogue of `RowMainClearFactV31`.
Still an unsupplied hypothesis. -/
def RowFreshFactV31 (ψ κ τ : Nat) : Prop :=
  ∀ {b : BranchV3} (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
      (l r : Cell ψ κ τ),
    branchAtV3 hψ h2 l r = b →
    b ≠ .openNoHazard →
    (R2CoherenceV31MainClearTruth.FreshnessClearV31 l →
      R2CoherenceV31MainClearTruth.FreshnessClearV31
        (rowV3 hψ (by decide : 0 < 2) h2 l r).1) ∧
    (R2CoherenceV31MainClearTruth.FreshnessClearV31 r →
      R2CoherenceV31MainClearTruth.FreshnessClearV31
        (rowV3 hψ (by decide : 0 < 2) h2 l r).2)

end R2CoherenceV31FootprintCover2R
