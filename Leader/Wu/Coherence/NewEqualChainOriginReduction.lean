import Leader.Wu.Coherence.CheckSurvivalSuppress
import Leader.Wu.Coherence.CheckSurvivalCheckCut
import Leader.Wu.Coherence.NewEqualChainOriginSuppress
import Leader.Wu.Coherence.NewEqualChainOriginFrames


set_option autoImplicit false
set_option Elab.async false


namespace R2NewEqualChainOrigin3


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair
open BirthSigMoveDisposalRepair
open R2CoherenceBranches R2NewEqualLocal
open R2NewEqualProvenance


variable {ψ width κ τ : Nat}


/-- Exact CHECK-input alignment still missing for the sanitized ordinary row.
`R2NewEqualProvenance2.Alignment.preCheckResetWall_readyAligned` closes the
reset-wall substage, while `PPrimePreservesReadyAlignment` and
`CleanPreservesReadyAlignment` are intentionally still residual Props. -/
def CheckInputAlignmentRemaining
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ) : Prop :=
  R2CheckSurvivalSuppress.SanitizedR2NewEqualFreshChainOriginCheckInputAlignmentRemaining
      (κ := κ) (τ := τ) hψ hw hle


/-- The suffix obligations are already isolated:
final equal must come from the corresponding through-CHECK equal, final
path/label are accounted for, and responder provenance can force paired-left
survival. -/
def PrivateCutsSuffixRemaining
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ) : Prop :=
  R2NewEqualChainOrigin2.RemainingCheckAndPrivateCutsObligation
    (κ := κ) (τ := τ) hψ hw hle


/-- The ordinary prefix is only used under inactive deletion.  This fact is
not supplied by the current CHECK-survival API, so name it rather than unfold
`R2.row` through the private shell. -/
def SanitizedDeletionInactive (hψ : 0 < ψ) : Prop :=
  ∀ (l r : R2.Cell ψ κ τ),
    let sl := sanitizeReadyPhys l
    let sr := sanitizeReadyPhys r
    let pl := prepareExpiringDisposal hψ sl.base
    let pr := prepareExpiringDisposal hψ sr.base
    let al := normalizeDeletion pl.core.erase
    let ar := normalizeDeletion pr.core.erase
    deletionActive al = false ∧ deletionActive ar = false


/-- Exact remaining CHECK-source/origin bridge after alignment.
The local CHECK algebra is already public in
`R2CoherenceBranches.checkSigCheckL_new_equal_fresh` and
`checkSigCheckR_new_equal_fresh`.  What is not public is the stage-local
transport from the sanitized outer endpoints to the actual `r2CheckInput`,
and then from that CHECK-created fresh component to the final bounded carrier.
This Prop states only those two endpoint consequences plus the label-origin
facts used by the strengthened seam. -/
def CheckInputFreshnessOriginRemaining
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ) : Prop :=
  ∀ (l r : R2.Cell ψ κ τ),
    let sl := sanitizeReadyPhys l
    let sr := sanitizeReadyPhys r
    let pl := prepareExpiringDisposal hψ sl.base
    let pr := prepareExpiringDisposal hψ sr.base
    let al := normalizeDeletion pl.core.erase
    let ar := normalizeDeletion pr.core.erase
    let b := r2CheckInput (κ := κ) hψ hw hle al ar
    let c := r2ThroughCheck (κ := κ) hψ hw hle al ar
    let q := R2.row hψ hw hle sl sr
    R2MainCarrierFrame l r q →
    deletionActive al = false → deletionActive ar = false →
    ReadyAlignedRaw b.1.core → ReadyAlignedRaw b.2.core →
    (c.1.core.state = .equal →
      l.base.core.core.state ≠ .equal →
      R2FreshAtOwnLabel q.1 ∧ c.1.core.label.val = 0) ∧
    (c.2.core.state = .equal →
      r.base.core.core.state ≠ .equal →
      R2FreshAtOwnLabel q.2 ∧
        (c.2.core.label.val = 0 ∨ c.1.core.state = .equal))


/-- Exact target proposition from OpenNoHazardClose, repeated here to avoid an
import cycle when this file is later imported by that close module. -/
def SanitizedR2NewEqualFreshChainOriginNoMainMutation
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ) : Prop :=
  ∀ (l r : R2.Cell ψ κ τ),
    let q := R2.row hψ hw hle (sanitizeReadyPhys l) (sanitizeReadyPhys r)
    R2MainCarrierFrame l r q →
      (q.1.base.core.core.state = .equal →
        l.base.core.core.state ≠ .equal →
        R2FreshAtOwnLabel q.1 ∧ q.1.base.core.core.label.val = 0) ∧
      (q.2.base.core.core.state = .equal →
        r.base.core.core.state ≠ .equal →
        R2FreshAtOwnLabel q.2 ∧
          (q.2.base.core.core.label.val = 0 ∨
            q.1.base.core.core.state = .equal))

theorem sanitizedR2NewEqualFreshChainOriginNoMainMutation_of
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (hAlign : CheckInputAlignmentRemaining (κ := κ) (τ := τ) hψ hw hle)
    (hDel : SanitizedDeletionInactive (κ := κ) (τ := τ) hψ)
    (hSource :
      CheckInputFreshnessOriginRemaining (κ := κ) (τ := τ) hψ hw hle)
    (hSuffix : PrivateCutsSuffixRemaining (κ := κ) (τ := τ) hψ hw hle) :
    SanitizedR2NewEqualFreshChainOriginNoMainMutation
      (κ := κ) (τ := τ) hψ hw hle := by
  unfold SanitizedR2NewEqualFreshChainOriginNoMainMutation
  intro l r
  try dsimp only
  intro hframe

  unfold SanitizedDeletionInactive at hDel
  have hdel := hDel l r
  try dsimp only at hdel

  unfold CheckInputAlignmentRemaining at hAlign
  have ha := hAlign l r hframe hdel.1 hdel.2
  try dsimp only at ha

  unfold CheckInputFreshnessOriginRemaining at hSource
  have hsrc := hSource l r hframe hdel.1 hdel.2 ha.1 ha.2
  try dsimp only at hsrc
  rcases hsrc with ⟨hsrcL, hsrcR⟩

  unfold PrivateCutsSuffixRemaining at hSuffix
  have hs := hSuffix l r hdel.1 hdel.2 hframe
  try dsimp only at hs
  rcases hs with ⟨_ha, hsL, hsR, hsPair⟩

  constructor
  · intro hq hold
    have hq' :
        (R2.row hψ hw hle (sanitizeReadyPhys l) (sanitizeReadyPhys r)).1.base.core.erase.core.state =
          .equal := hq
    rcases hsL hq' with ⟨hc, _hp, hlab⟩
    rcases hsrcL hc hold with ⟨hfresh, hzero⟩
    refine ⟨hfresh, ?_⟩
    exact (congrArg Fin.val hlab).trans hzero
  · intro hq hold
    have hq' :
        (R2.row hψ hw hle (sanitizeReadyPhys l) (sanitizeReadyPhys r)).2.base.core.erase.core.state =
          .equal := hq
    rcases hsR hq' with ⟨hc, _hp, hlab⟩
    rcases hsrcR hc hold with ⟨hfresh, horigin⟩
    refine ⟨hfresh, ?_⟩
    rcases horigin with hzero | hcL
    · exact Or.inl ((congrArg Fin.val hlab).trans hzero)
    · exact Or.inr (hsPair hq' hcL)


end R2NewEqualChainOrigin3
