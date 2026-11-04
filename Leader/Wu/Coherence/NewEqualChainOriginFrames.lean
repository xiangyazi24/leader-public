import Leader.Wu.Coherence.NewEqualReadyAlignment
import Leader.Wu.Coherence.OpenNoHazardChainOrigin

set_option autoImplicit false
set_option Elab.async false

namespace R2NewEqualChainOrigin

open PPLL PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open BirthCheckPermitRepair
open K2BirthDispatcher K2BirthLeaderNormalize

variable {ψ κ τ : Nat}

/-- On the exact left-CHECK equality case, R1/R2's permit cut keeps the
physical core literally and consumes the moved-carrier authorization. -/
theorem permitFix_equal_frame
    (u : AuthorizedAgentState ψ) (h : u.core.state = .equal) :
    (permitFix u).core = u.core ∧
      (permitFix u).path0Crossed = false := by
  simp [permitFix, h]

/-- Leader normalization cannot change comparison state or the main path.
Only the label is a normalization seam. -/
theorem normalizeLeader_state_path_frame
    (hψ : 0 < ψ) (u : ExpiringAgentState ψ κ τ) :
    (normalizeLeader hψ u).core.core.state = u.core.core.state ∧
      (normalizeLeader hψ u).core.core.path = u.core.core.path := by
  unfold normalizeLeader
  split <;> exact ⟨rfl, rfl⟩

/-- The physical K2 tail is invisible to the three comparison fields needed
for CHECK provenance. -/
theorem finalPhysical_main_frame
    (hψ : 0 < ψ)
    (oldL oldR metaL metaR : ExpiringAgentState ψ κ τ) :
    ((finalPhysical hψ oldL oldR metaL metaR).1.core.core.state =
        metaL.core.core.state ∧
      (finalPhysical hψ oldL oldR metaL metaR).1.core.core.path =
        metaL.core.core.path ∧
      (finalPhysical hψ oldL oldR metaL metaR).1.core.core.label =
        metaL.core.core.label) ∧
    ((finalPhysical hψ oldL oldR metaL metaR).2.core.core.state =
        metaR.core.core.state ∧
      (finalPhysical hψ oldL oldR metaL metaR).2.core.core.path =
        metaR.core.core.path ∧
      (finalPhysical hψ oldL oldR metaL metaR).2.core.core.label =
        metaR.core.core.label) := by
  have h := finalPhysical_nonK2 hψ oldL oldR metaL metaR
  constructor
  · have hs := congrArg
      (fun u : ExpiringAgentState ψ κ τ => u.core.core.state) h.1
    have hp := congrArg
      (fun u : ExpiringAgentState ψ κ τ => u.core.core.path) h.1
    have hl := congrArg
      (fun u : ExpiringAgentState ψ κ τ => u.core.core.label) h.1
    change (finalPhysical hψ oldL oldR metaL metaR).1.core.core.state =
      metaL.core.core.state at hs
    change (finalPhysical hψ oldL oldR metaL metaR).1.core.core.path =
      metaL.core.core.path at hp
    change (finalPhysical hψ oldL oldR metaL metaR).1.core.core.label =
      metaL.core.core.label at hl
    exact ⟨hs, hp, hl⟩
  · have hs := congrArg
      (fun u : ExpiringAgentState ψ κ τ => u.core.core.state) h.2
    have hp := congrArg
      (fun u : ExpiringAgentState ψ κ τ => u.core.core.path) h.2
    have hl := congrArg
      (fun u : ExpiringAgentState ψ κ τ => u.core.core.label) h.2
    change (finalPhysical hψ oldL oldR metaL metaR).2.core.core.state =
      metaR.core.core.state at hs
    change (finalPhysical hψ oldL oldR metaL metaR).2.core.core.path =
      metaR.core.core.path at hp
    change (finalPhysical hψ oldL oldR metaL metaR).2.core.core.label =
      metaR.core.core.label at hl
    exact ⟨hs, hp, hl⟩

/-!
RESIDUAL: export a public R2 CHECK-to-row paired state-survival theorem.
For the ordinary branch, after identifying the public through-CHECK pair `c`,
it must establish at least:

* final right `.equal` newly created on this service -> `c.2.state = .equal`;
* if that right equality is the non-root CHECK-R case, then
  `c.1.state = .equal` -> final left state `.equal`.

The first implication is a no-post-CHECK-creation statement.  The second is
paired survival.  `permitFix` closes fresh CMP restart on the left, but the
current exported API has no arbitrary-state theorem carrying the pair through
DISAPPEAR / action-one COMPARE / SUPPRESS / markLeaderBirth / expiry.

The closest existing theorem is
`BirthCheckChainR1.afterCheck_keeps_chain`, which needs its explicit
nonempty-path, no-fresh-start, reset-free, nonterminal and path2 hypotheses.
The R2-specific writer half is already closed by
`R2NewEqualLocal.stationaryProducerMainComparisonFrame`.

PRE-CHECK RESIDUAL FOR FRESHNESS: the net `R2MainCarrierFrame` does not imply
`R2ActualCheckInputSource`.  P′ relabel is at `Leader/Wu/Protocol/Algorithm.lean:24-44`;
CLEAN path erasure is in `cleanSigCleanApply` in `Leader/Wu/Protocol/Algorithm.lean`.
Those changes can be masked later, so a stage-local ready-alignment premise
or a reachable-state/canonical-history theorem is still required before
`checkSigCheckL_new_equal_fresh` / `checkSigCheckR_new_equal_fresh` can be used.
-/




end R2NewEqualChainOrigin
