import Leader.Wu.Authorization.ProvenanceMarks

/-!
# Exact GoodEq / wrong-stamp ready CHECK cut

This is only the original `checkSourceAuth` stage. Its right verdict uses the
input physical bit and path payload, before WRITE can change the physical bit.
It makes no full-interaction, population-run, or generator-reachability claim.
The stated own-path and token premises are the entire entrance: CLEAN records,
writer fields, leaders, resets and other raw payloads are unrestricted.

Source-level entrance example: psi=4, j=0, left state equal, right CHECK_ready,
own paths at labels 0 and 1, both path2 empty, both path marks 0, left control
mark 0 and right control mark 1. Other fields may be chosen arbitrarily.
-/

namespace PPLLAuthCheckGoodEqBadReady

open PPLL PPLLBirthPatch PPLLBirthPatchM2
open PPLLFableDesignR1 PPLLAuthF
open PPLLAuthF.AuthState

set_option autoImplicit false

/-- The selected original AuthF+MCC configuration. -/
def cfg : PPLLAuthF.Cfg :=
  { retire := true, markClean := true, claimCheck := true }

variable {ψ j bl br : Nat}

/-- At this CHECK cut, the certified equal predecessor consumes the
wrong-stamp ready responder exactly by CHECK_BIT.  No other field changes. -/
theorem checkSource_goodEq_badReady_exact
    (hp : ψ > 0) (hj : j + 2 < ψ)
    (l r : AuthState ψ)
    (hll : l.core.label.val = j)
    (hrl : r.core.label.val = j + 1)
    (hlp : l.core.path = .some j bl)
    (hrp : r.core.path = .some (j + 1) br)
    (hls : l.core.state = .equal)
    (hrs : r.core.state = .CHECK_ready)
    (hlt : l.core.path2 = none)
    (hrt : r.core.path2 = none)
    (hpm : l.path_mark = r.path_mark)
    (hlcm : l.ctrl_mark = l.path_mark)
    (hrcm : r.ctrl_mark ≠ r.path_mark) :
    checkSourceAuth hp cfg l r =
      (l, { r with core :=
        { r.core with state := checkBit r.core.bit br } }) := by
  have hj1 : j + 1 ≠ 0 := by omega
  have hjlt : j < ψ - 1 := by omega
  have hrnt :
      r.core.label ≠ (⟨ψ - 1, by omega⟩ : Fin ψ) := by
    intro h
    have hv : r.core.label.val = ψ - 1 := by
      simpa using congrArg Fin.val h
    rw [hrl] at hv
    omega

  have hv : validateCheck l r = (l, r) := by
    have hlbad : headBad l = false := by
      simp [headBad, hlcm]
    have hrbad : headBad r = false := by
      simp [headBad, isHead, hrl, hj1]
    simp [validateCheck, hlbad, hrbad, verdict, AuthState.st, hrs]

  have hreadyL : readyAuth l = l := by
    simp [readyAuth, checkSigSetReadyGuarded, controlPending,
      checkSigSetReady, AuthState.st, waveState, hls, hlp]

  have hreadyR : readyAuth r = r := by
    have hu : {r.core with state := .CHECK_ready} = r.core := by rw [← hrs]
    simp [readyAuth, checkSigSetReadyGuarded, controlPending,
      checkSigSetReady, AuthState.st, waveState, hrs, hrp, hrl, hrt, hu]
    all_goals rw [← hrp, ← hrt, ← hrs]

  have hcheckL : checkSigCheckL hp l.core = l.core := by
    cases j with
    | zero =>
        simp [checkSigCheckL, hlp, hls]
    | succ j =>
        simp [checkSigCheckL, hlp]

  have hcert : certPred l r = true := by
    simp [certPred, hlp, hrp, AuthState.st, hls, hlcm, hpm,
      aligned, hll, hrl]

  have hcheckR :
      checkSigCheckR hp l.core r.core =
        { r.core with state := checkBit r.core.bit br } := by
    simp [checkSigCheckR, hrp, hll, hls, hrs, hjlt]

  simp [checkSourceAuth, cfg, hv, hreadyL, hreadyR, hrs,
    hcheckL, hcert, hcheckR, issue, AuthState.st, AuthState.withCore, hls, hrcm, hrnt]

/-- The CHECK-only field frame used by a later full-row proof. The left GoodEq
cell is retained; right label, path, leader and reset fields are preserved;
both tokens stay empty and the right control stamp remains different from
its path stamp. The verdict uses the CHECK input bit, with no assertion about
a subsequent WRITE bit or production of this entrance. -/
theorem checkSource_goodEq_badReady_facts
    (hp : ψ > 0) (hj : j + 2 < ψ)
    (l r : AuthState ψ)
    (hll : l.core.label.val = j)
    (hrl : r.core.label.val = j + 1)
    (hlp : l.core.path = .some j bl)
    (hrp : r.core.path = .some (j + 1) br)
    (hls : l.core.state = .equal)
    (hrs : r.core.state = .CHECK_ready)
    (hlt : l.core.path2 = none)
    (hrt : r.core.path2 = none)
    (hpm : l.path_mark = r.path_mark)
    (hlcm : l.ctrl_mark = l.path_mark)
    (hrcm : r.ctrl_mark ≠ r.path_mark) :
    let q := checkSourceAuth hp cfg l r
    q.1 = l ∧
    q.1.core.label.val = j ∧
    q.1.core.path = .some j bl ∧
    q.1.core.state = .equal ∧
    q.1.core.path2 = none ∧
    q.1.ctrl_mark = q.1.path_mark ∧
    q.2.core.label = r.core.label ∧
    q.2.core.path = .some (j + 1) br ∧
    q.2.core.leader = r.core.leader ∧
    q.2.core.reset_cmd = r.core.reset_cmd ∧
    q.2.core.state = checkBit r.core.bit br ∧
    q.2.core.path2 = none ∧
    q.2.ctrl_mark = r.ctrl_mark ∧
    q.2.path_mark = r.path_mark ∧
    q.2.ctrl_mark ≠ q.2.path_mark := by
  dsimp only
  rw [checkSource_goodEq_badReady_exact
    (hp := hp) (hj := hj) (l := l) (r := r)
    (hll := hll) (hrl := hrl) (hlp := hlp) (hrp := hrp)
    (hls := hls) (hrs := hrs) (hlt := hlt) (hrt := hrt)
    (hpm := hpm) (hlcm := hlcm) (hrcm := hrcm)]
  simp [hll, hlp, hrp, hls, hlt, hlcm, hrt, hrcm]

#print axioms checkSource_goodEq_badReady_exact
#print axioms checkSource_goodEq_badReady_facts

end PPLLAuthCheckGoodEqBadReady
