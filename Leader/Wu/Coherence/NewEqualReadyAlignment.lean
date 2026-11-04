import Leader.Wu.Coherence.NewEqualCheckInput
import Leader.Wu.Birth.CheckChainStages


set_option autoImplicit false
set_option Elab.async false


namespace R2NewEqualProvenance2


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open PPLLWallSweepRepair PPLLWallSweepFinite
open PPLLWallSweepPreCheckResetRepair
open K2BirthLeaderNormalize
open WriterProducerRepair
open R2CoherenceBranches R2NewEqualLocal
open R2NewEqualProvenance


variable {ψ κ τ width : Nat}


/-! ## What the writer/producer frame already closes -/


private def writerMainTriple (u : WCell ψ κ) :
    MainState × BoundedPathInfo ψ × Fin ψ :=
  (u.agent.core.state, u.agent.core.path, u.agent.core.label)


/-- Repackage the accepted writer/producer frame as the exact
three-field equality wanted by the provenance argument. -/
theorem stationaryProducer_mainTriple
    (hψ : 0 < ψ) (l r : WCell ψ κ) :
    let q := stationaryProducerRow hψ l r
    writerMainTriple q.1 = writerMainTriple l ∧
      writerMainTriple q.2 = writerMainTriple r := by
  rcases stationaryProducerMainComparisonFrame (κ := κ) hψ l r with
    ⟨hsL, hpL, hlL, hsR, hpR, hlR⟩
  constructor
  · unfold writerMainTriple
    exact Prod.ext hsL (Prod.ext hpL hlL)
  · unfold writerMainTriple
    exact Prod.ext hsR (Prod.ext hpR hlR)


/-! ## normalizeLeader needs its own stage-local label equality -/


private def expiringMainTriple (u : ExpiringAgentState ψ κ τ) :
    MainState × BoundedPathInfo ψ × Fin ψ :=
  (u.core.core.state, u.core.core.path, u.core.core.label)


/-- `normalizeLeader` changes no main field except label.  Therefore a
stage-local label frame is enough to transport the whole main triple.
The important point is that the *final* R2MainCarrierFrame does not supply
this stage-local equality. -/
theorem normalizeLeader_mainTriple_of_own_label_frame
    (hψ : 0 < ψ) (u : ExpiringAgentState ψ κ τ)
    (hlabel :
      (normalizeLeader hψ u).core.core.label = u.core.core.label) :
    expiringMainTriple (normalizeLeader hψ u) = expiringMainTriple u := by
  unfold expiringMainTriple
  apply Prod.ext
  · unfold normalizeLeader
    split <;> rfl
  · apply Prod.ext
    · unfold normalizeLeader
      split <;> rfl
    · exact hlabel

namespace Alignment


/-- Clearing a comparison carrier cannot leave a malformed CHECK_ready:
its main state is `.none`. -/
private theorem clearAuthorizedComparison_readyAligned
    (u : AuthorizedAgentState ψ) :
    ReadyAlignedRaw (clearAuthorizedComparison u).core := by
  simp [ReadyAlignedRaw, clearAuthorizedComparison, clearComparisonSignal]


/-- `preCheckResetWall` is not the alignment residual.  It either clears a
carrier completely or leaves it unchanged. -/
theorem preCheckResetWall_readyAligned
    (l r : AuthorizedAgentState ψ)
    (hl : ReadyAlignedRaw l.core) (hr : ReadyAlignedRaw r.core) :
    let q := preCheckResetWall l r
    ReadyAlignedRaw q.1.core ∧ ReadyAlignedRaw q.2.core := by
  unfold preCheckResetWall
  dsimp only
  by_cases hs : l.core.leader = true ∨ l.core.reset_cmd = true
  · rw [if_pos hs]
    rw [if_pos (Or.inl hs)]
    exact ⟨clearAuthorizedComparison_readyAligned l,
      clearAuthorizedComparison_readyAligned r⟩
  · rw [if_neg hs]
    by_cases hrst : r.core.reset_cmd = true
    · rw [if_pos (Or.inr hrst)]
      exact ⟨hl, clearAuthorizedComparison_readyAligned r⟩
    · have hn :
          ¬ ((l.core.leader = true ∨ l.core.reset_cmd = true) ∨
            r.core.reset_cmd = true) := by
        intro h
        rcases h with h | h
        · exact hs h
        · exact hrst h
      rw [if_neg hn]
      exact ⟨hl, hr⟩


/-- Exact first residual: P′ may alter the resident label before CHECK.
This Prop is deliberately not asserted for arbitrary states. -/
def PPrimePreservesReadyAlignment
    (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) : Prop :=
  ReadyAlignedRaw l.core → ReadyAlignedRaw r.core →
    let q := authorizedPPsiLeaderResetProbeWall hψ l r
    ReadyAlignedRaw q.1.core ∧ ReadyAlignedRaw q.2.core


/-- Exact second residual: CLEAN_SIG can erase `path` while leaving an old
CHECK_ready state.  This also is not valid on arbitrary states; it requires
cleanup-marker compatibility / canonical-history assumptions. -/
def CleanPreservesReadyAlignment
    (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ) : Prop :=
  ReadyAlignedRaw l.core → ReadyAlignedRaw r.core →
    let q := authorizedCleanSig hψ l r
    ReadyAlignedRaw q.1.core ∧ ReadyAlignedRaw q.2.core


end Alignment

/-!
What remains before the requested final theorem can be stated honestly:


1. P′ alignment: obtain the stable-successor / follower facts from the
   openNoHazard ElectionGeometryV31 context, then use the existing
   `BirthCheckChainR1.pPsiWall_keeps_genView`-style frame.


2. CLEAN alignment: rule out stale `path4/path5 = (-1, …)` cleanup commands
   on a stored CHECK_ready carrier, or strengthen the V3 sanitizer to retire
   them before the ordinary proposal.  This is independent of preCheckResetWall.


3. Post-CHECK survival: export a one-endpoint main-state/path theorem for
   DISAPPEAR -> action-one COMPARE -> SUPPRESS that says a final `.equal`
   with retained nonempty path came from the through-CHECK `.equal`.
   `B6TrafficPairFrame` is not that theorem; its projections are reset/echo.
   `BirthCheckChainR1.afterCheck_keeps_chain` is a usable stronger theorem
   only after its local hypotheses have been derived.


4. Stage-local normalization: prove that the metadata endpoint fed to
   `normalizeLeader` already has the final framed label.  A net
   `R2MainCarrierFrame` does not imply this because an earlier P′ relabel can
   be canceled by normalization.


Only after 1--4 can `checkSigCheckL_new_equal_fresh` and
`checkSigCheckR_new_equal_fresh` be transported to
`SanitizedR2NewEqualFreshAtOwnLabelNoMainMutation`.
-/








end R2NewEqualProvenance2
