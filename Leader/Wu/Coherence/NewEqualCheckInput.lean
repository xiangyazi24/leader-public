import Leader.Wu.Coherence.NewEqualLocal

set_option autoImplicit false
set_option Elab.async false

namespace R2NewEqualProvenance

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair
open BirthShortDoneTerminalEntryCut BirthShortDoneCuts
open R2CoherenceBranches R2NewEqualLocal

variable {ψ width κ τ : Nat}

/-- The actual public boundary immediately before CHECK in the R2 ordinary body. -/
def r2CheckInput
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  doneBeforeCheckEntryWidth hψ hw hle κ l r

/-- The exact public through-CHECK computation used by R2 ordinary. -/
def r2ThroughCheck
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedAgentState ψ) :
    AuthorizedAgentState ψ × AuthorizedAgentState ψ :=
  doneThroughCheckEntryWidth hψ hw hle κ l r

/-- Source-level diagnostic: the SUPPRESS reset kill is a real main-path
mutation, so CHECK-output equality cannot simply be pushed through
`beforeWriteWidth` without ruling this branch out. -/
theorem resetKill_main_path_erasure
    (u : AgentState ψ) (hreset : u.reset_cmd = true) :
    let v := resetKillComparison u
    v.state = .none ∧ v.path = .bot := by
  have h := resetKillComparison_exact u hreset
  exact ⟨h.1, h.2.1⟩

namespace R2NewEqualProvenance

/-- Missing prefix bridge: the actual CHECK input, not the outer pair, must be
aligned and must carry the endpoint source used by the freshness lemma. -/
def R2ActualCheckInputSource
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ) : Prop :=
  ∀ (l r : AuthorizedAgentState ψ),
    let b := r2CheckInput (κ := κ) hψ hw hle l r
    ReadyAlignedRaw b.1.core ∧ ReadyAlignedRaw b.2.core

/-- Missing suffix bridge: a CHECK-created equal that survives as an equal in
the complete R2 row retains the main carrier through the post-CHECK suffix,
writer, birth marking, expiry, normalization, and final physical tail. -/
def R2CheckEqualSurvival : Prop :=
  True

-- `R2CheckEqualSurvival` above is intentionally left only as a marker here:
-- its useful statement must mention the actual bounded/expiring endpoint
-- produced by `R2.row`; writing `True` avoids pretending that the currently
-- missing transport theorem has been proved.
