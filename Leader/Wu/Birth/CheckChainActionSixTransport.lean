import Leader.Wu.Birth.CheckChainStages

set_option autoImplicit false

/-! # DONE-stage transport of the action-6 signal inside an aligned train

After a `less` outcome at label `k` the responder holds the action-6 signal `⟨0, 0, 0, 6⟩`.  On the DONE move
(`BirthGenerationDone.doneCaptureSigMove`: leader preclear, capture Step1, control transfers, leader wall, single-use
control tail) of a pair of aligned followers whose right cell holds that signal and whose left cell holds none:
* `doneCaptureSigMove_signal6`: the signal moves to the left cell and leaves the right cell; above label 0 no state
  changes, at label 0 the left cell enters `toss` (and keeps the signal, ERRATA T29).
-/

namespace BirthCheckChainR1Signal6

open PPLL PPLLWallSweepRepair BirthGenerationDone BirthArrivalCaptureRepair BirthSingleUseReleaseRepair

variable {ψ : Nat}

theorem doneCaptureSigMove_signal6 (hψ : 0 < ψ) (l r : AgentState ψ) (a b c d : Nat)
    (hlp : l.path = .some a b) (hrp : r.path = .some c d)
    (hll : l.leader = false) (hrl : r.leader = false)
    (hlp2 : l.path2 = none) (hrp2 : r.path2 = some ⟨0, 0, 0, 6⟩)
    (hldn : l.state ≠ .done) (hrdep : r.state ≠ .depart) :
    let q := doneCaptureSigMove hψ l r
    q.1.path2 = some ⟨0, 0, 0, 6⟩ ∧ q.2.path2 = none ∧ q.1.path = l.path ∧ q.2.path = r.path ∧
      q.1.label = l.label ∧ q.2.label = r.label ∧ q.2.state = r.state ∧
      (l.label ≠ ⟨0, hψ⟩ → q.1.state = l.state) ∧ (l.label = ⟨0, hψ⟩ → q.1.state = .toss) := by
  intro q
  have hp : sigMoveLeaderPreclear hψ l r = (l, r) := by
    simp [sigMoveLeaderPreclear, incompleteLeftLeaderBoundary, clearIfLeader, hll, hrl]
  have hm : doneTransfers l r = ({ l with path2 := some ⟨0, 0, 0, 6⟩ }, { r with path2 := none }) := by
    simp [doneTransfers, holdDoneStep1, hldn, captureStep1, hlp, hrp, controlTransfers, sigMoveStep2,
      sigMoveStep3, sigMoveStep4, sigMoveStep5, hlp2, hrp2]
  have hw : comparisonLeaderWall { l with path2 := some ⟨0, 0, 0, 6⟩ } { r with path2 := none } =
      ({ l with path2 := some ⟨0, 0, 0, 6⟩ }, { r with path2 := none }) := by
    simp [comparisonLeaderWall, hll, hrl]
  have hq : q = singleUseControlTail hψ { l with path2 := some ⟨0, 0, 0, 6⟩ } { r with path2 := none } := by
    show doneCaptureSigMove hψ l r = _
    unfold doneCaptureSigMove
    rw [hp]; dsimp only; rw [hm]; dsimp only; rw [hw]
  rw [hq]
  by_cases h0 : l.label = ⟨0, hψ⟩
  · by_cases hterm : l.label = ⟨ψ - 1, by omega⟩
    · -- label 0 is also the terminal only when psi = 1
      simp [singleUseControlTail, singleUseApplyControl, h0, hrdep, hlp, hrp] at hterm ⊢
    · simp [singleUseControlTail, singleUseApplyControl, h0, hrdep, hlp, hrp]
  · simp [singleUseControlTail, singleUseApplyControl, h0, hrdep, hlp, hrp]

end BirthCheckChainR1Signal6
