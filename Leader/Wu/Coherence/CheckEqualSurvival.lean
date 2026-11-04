import Leader.Wu.Coherence.NewEqualReadyAlignment

set_option autoImplicit false

namespace R2CheckSurvival

open PPLL PPLLResearchFormulation PPLLLeaderCreationCleanupRepair

def CheckToFinalEqualSurvival
    {ψ κ τ width : Nat}
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ) : Prop :=
  ∀ (l r : R2.Cell ψ κ τ),
    let sl := R2CoherenceBranches.sanitizeReadyPhys l
    let sr := R2CoherenceBranches.sanitizeReadyPhys r
    let pl := BirthSigMoveDisposalRepair.prepareExpiringDisposal hψ sl.base
    let pr := BirthSigMoveDisposalRepair.prepareExpiringDisposal hψ sr.base
    let al := PPLLLeaderCreationCleanupRepair.normalizeDeletion pl.core.erase
    let ar := PPLLLeaderCreationCleanupRepair.normalizeDeletion pr.core.erase
    PPLLLeaderCreationCleanupRepair.deletionActive al = false →
    PPLLLeaderCreationCleanupRepair.deletionActive ar = false →
    let c :=
      R2NewEqualProvenance.r2ThroughCheck (κ := κ) hψ hw hle al ar
    let q := R2.row hψ hw hle sl sr
    (∀ t : MainState × PathInfo × Fin ψ,
      c.1.core.state = .equal →
      (c.1.core.state, c.1.core.path, c.1.core.label) = t →
      q.1.base.core.erase.core.state = .equal →
      ((q.1.base.core.erase.core.state,
          q.1.base.core.erase.core.path,
          q.1.base.core.erase.core.label) = t ∨
        (q.1.base.core.erase.core.path = .bot ∧
          q.1.base.core.erase.core.path ≠ c.1.core.path) ∨
        (q.1.base.core.erase.core.label = ⟨0, hψ⟩ ∧
          q.1.base.core.erase.core.label ≠ c.1.core.label))) ∧
    (∀ t : MainState × PathInfo × Fin ψ,
      c.2.core.state = .equal →
      (c.2.core.state, c.2.core.path, c.2.core.label) = t →
      q.2.base.core.erase.core.state = .equal →
      ((q.2.base.core.erase.core.state,
          q.2.base.core.erase.core.path,
          q.2.base.core.erase.core.label) = t ∨
        (q.2.base.core.erase.core.path = .bot ∧
          q.2.base.core.erase.core.path ≠ c.2.core.path) ∨
        (q.2.base.core.erase.core.label = ⟨0, hψ⟩ ∧
          q.2.base.core.erase.core.label ≠ c.2.core.label)))

end R2CheckSurvival
