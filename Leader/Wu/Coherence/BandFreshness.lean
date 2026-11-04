import Leader.Wu.Coherence.FootprintBand

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31BandFreshness

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair WriterProducerRepair
open R2CoherenceV31 R2CoherenceV31Closure
open R2CoherenceV31ReachablePlus2
open R2CoherenceV31FootprintBand

variable {n ψ κ τ : Nat}

private theorem prefixPos_self_bandFresh
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n) :
    R2Coherence.prefixPos ring (eraseCfgV3 C) i (raw (C i)).label.val = i := by
  unfold R2Coherence.prefixPos
  change R2Coherence.back ring i
      ((raw (C i)).label.val - (raw (C i)).label.val) = i
  rw [Nat.sub_self]
  apply Fin.ext
  simp [R2Coherence.back, Nat.add_mod, Nat.mod_eq_of_lt i.isLt]

private theorem mainClear_state_none_bandFresh
    (u : Cell ψ κ τ) (h : MainClearV3 u) :
    (raw u).state = .none := by
  unfold MainClearV3 R2CoherenceBranches.MainClear at h
  change u.phys.base.core.core.state = .none
  exact h.1

/-- If both index bands exported by `openRFreshFootprintBand_of_root` are
main-clear, then every owner-containing arithmetic window is intrinsically
fresh.  No resident-bit or control-state hypothesis is needed: a band cell
which could generate an intrinsic-freshness obligation would have
`state = .equal`, while `MainClearV3` gives `state = .none`. -/
theorem openROwnerFresh_of_bands_mainClear
    (ring : DirectedRing n) (C : FC n ψ κ τ) (owner : Fin n)
    (hElection : ElectionGeometryV31 ring C)
    (hRoot : atRootB (C owner) = true)
    (hPred : ∀ d : Fin ψ, 0 < d.val →
      MainClearV3 (C (R2Coherence.back ring owner d.val)))
    (hFwd : ∀ d : Fin ψ,
      MainClearV3 (C (R2Coherence.fwd ring owner d.val))) :
    OpenROwnerFreshV3 ring C owner := by
  unfold OpenROwnerFreshV3 GroupIntrinsicFreshV3 IntrinsicFreshAtV3
  intro j ko hOwner q hEq
  let front := R2Coherence.groupPos ring (eraseCfgV3 C) j q.val
  have hFrontFoot :
      InOpenRFreshFootprintV31 ring C owner front := by
    let k : Fin ((raw (C front)).label.val + 1) :=
      ⟨(raw (C front)).label.val, Nat.lt_succ_self _⟩
    refine ⟨j, ko, q, hOwner, k, ?_⟩
    simpa [front, k] using prefixPos_self_bandFresh ring C front
  have hBand :=
    openRFreshFootprintBand_of_root
      ring C owner front hElection hRoot hFrontFoot
  have hMain : MainClearV3 (C front) := by
    rcases hBand with hPredBand | hFwdBand
    · rcases hPredBand with ⟨d, hd, hpos⟩
      rw [hpos]
      exact hPred d hd
    · rcases hFwdBand with ⟨d, hpos⟩
      rw [hpos]
      exact hFwd d
  have hNone : (raw (C front)).state = .none :=
    mainClear_state_none_bandFresh (C front) hMain
  change (raw (C front)).state = .equal at hEq
  rw [hNone] at hEq
  cases hEq

end R2CoherenceV31BandFreshness
