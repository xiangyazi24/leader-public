import Leader.Wu.Authorization.ProvenanceMarks

/-!
# Exact CHECK recovery of a wrong-stamp verdict

This module concerns only the original `checkSourceAuth` stage at a
nonterminal responder (`j + 2 < psi`). Validation demotes an old wrong-stamp
verdict, readiness stamps the lineage, and CHECK recomputes the verdict from
the input physical bit. This bit is not a later WRITE output bit.

Unused token sidecars and other raw fields are arbitrary. Equal keeps those
sidecars; larger/less issues a line-scoped A4/A6 token. No full-row, population
run, or entrance-producer result is asserted.

Source-level satisfiable entrance: psi = 4, j = 0, own paths at labels 0 and 1,
left equal and right larger (or equal/less), both tokens empty, both path marks
0, left control mark 0, right control mark 1. Other fields are arbitrary.
-/

namespace PPLLAuthCheckGoodEqBadVerdict

open PPLL PPLLBirthPatch PPLLBirthPatchM2
open PPLLFableDesignR1 PPLLAuthF
open PPLLAuthF.AuthState

set_option autoImplicit false

/-- The selected original AuthF+MCC configuration. -/
def cfg : PPLLAuthF.Cfg :=
  { retire := true, markClean := true, claimCheck := true }

variable {ψ j bl br : Nat}

/-- Exact responder after the second CHECK service.  The equal branch deliberately
keeps the old token sidecars; only A4/A6 issuance stamps them as line-local. -/
private def outRight (r : AuthState ψ) (br : Nat) : AuthState ψ :=
  let v := checkBit r.core.bit br
  if v = .larger then
    { r with
      core := { r.core with state := v, path2 := some ⟨0, 0, 0, 4⟩ }
      ctrl_mark := r.path_mark
      path2_scope := .line
      path2_mark := r.path_mark }
  else if v = .less then
    { r with
      core := { r.core with state := v, path2 := some ⟨0, 0, 0, 6⟩ }
      ctrl_mark := r.path_mark
      path2_scope := .line
      path2_mark := r.path_mark }
  else
    { r with core := { r.core with state := v }, ctrl_mark := r.path_mark }

private theorem outRight_label (r : AuthState ψ) (br : Nat) :
    (outRight r br).core.label = r.core.label := by
  unfold outRight
  dsimp only
  split
  · rfl
  · split <;> rfl

private theorem issue_rearmed_exact
    (r : AuthState ψ) (br : Nat) (hrt : r.core.path2 = none) :
    issue ({ r with
      core := { r.core with state := checkBit r.core.bit br }
      ctrl_mark := r.path_mark } : AuthState ψ) =
      outRight r br := by
  unfold outRight issue
  dsimp only
  rw [hrt]
  by_cases h4 : checkBit r.core.bit br = .larger
  · simp [h4, checkSigSetResult, AuthState.st]
  · by_cases h6 : checkBit r.core.bit br = .less
    · simp [h4, h6, checkSigSetResult, AuthState.st]
    · simp [h4, h6, checkSigSetResult, AuthState.st]

/-- A wrong-stamp non-head verdict is demoted, re-readied with the correct stamp,
checked against the input physical bit, and immediately issued if the result is
larger/less.  The predecessor is unchanged and terminal birth is inactive. -/
theorem checkSource_goodEq_badVerdict_exact
    (hp : ψ > 0) (hj : j + 2 < ψ)
    (l r : AuthState ψ)
    (hll : l.core.label.val = j)
    (hrl : r.core.label.val = j + 1)
    (hlp : l.core.path = .some j bl)
    (hrp : r.core.path = .some (j + 1) br)
    (hls : l.core.state = .equal)
    (hrs : r.core.state = .equal ∨
      r.core.state = .larger ∨ r.core.state = .less)
    (hlt : l.core.path2 = none)
    (hrt : r.core.path2 = none)
    (hpm : l.path_mark = r.path_mark)
    (hlcm : l.ctrl_mark = l.path_mark)
    (hrcm : r.ctrl_mark ≠ r.path_mark) :
    checkSourceAuth hp cfg l r = (l, outRight r br) := by
  have hj1 : j + 1 ≠ 0 := by omega
  have hjlt : j < ψ - 1 := by omega
  have hrnt :
      r.core.label ≠ (⟨ψ - 1, by omega⟩ : Fin ψ) := by
    intro h
    have hv : r.core.label.val = ψ - 1 := by
      simpa using congrArg Fin.val h
    rw [hrl] at hv
    omega

  have hlbad : headBad l = false := by
    simp [headBad, hlcm]
  have hheadR : isHead r = false := by
    simp [isHead, hrl, hj1]
  have hrbad : headBad r = false := by
    simp [headBad, hheadR]
  have halR : aligned r.core = true := by
    simp [aligned, hrp, hrl]
  have hverR : verdict r = true := by
    rcases hrs with hrs | hrs | hrs <;>
      simp [verdict, AuthState.st, hrs]
  have hcert0 : certPred l r = true := by
    simp [certPred, hlp, hrp, AuthState.st, hls, hlcm, hpm,
      aligned, hll, hrl]
  have hdemote :
      demote r = { r with core := { r.core with state := .none } } := by
    rcases hrs with hrs | hrs | hrs <;>
      simp [demote, AuthState.st, hrs, hrt]
  have hv :
      validateCheck l r =
        (l, { r with core := { r.core with state := .none } }) := by
    simp [validateCheck, hlbad, hrbad, hheadR, halR, hverR,
      hcert0, hrcm, hdemote]

  have hreadyL : readyAuth l = l := by
    simp [readyAuth, checkSigSetReadyGuarded, controlPending,
      checkSigSetReady, AuthState.st, waveState, hls, hlp]
  have hreadyR :
      readyAuth ({ r with core := { r.core with state := .none } } : AuthState ψ) =
        { r with
          core := { r.core with state := .CHECK_ready }
          ctrl_mark := r.path_mark } := by
    simp [readyAuth, checkSigSetReadyGuarded, controlPending,
      checkSigSetReady, AuthState.st, waveState, hrp, hrl]

  have hcheckL : checkSigCheckL hp l.core = l.core := by
    cases j with
    | zero =>
        simp [checkSigCheckL, hlp, hls]
    | succ j =>
        simp [checkSigCheckL, hlp]

  have hcert :
      certPred l
        ({ r with
          core := { r.core with state := .CHECK_ready }
          ctrl_mark := r.path_mark } : AuthState ψ) = true := by
    simp [certPred, hlp, hrp, AuthState.st, hls, hlcm, hpm,
      aligned, hll, hrl]

  have hcheckR :
      checkSigCheckR hp l.core
        ({ r.core with state := .CHECK_ready }) =
        { r.core with state := checkBit r.core.bit br } := by
    simp [checkSigCheckR, hrp, hll, hls, hjlt]

  have hissueL : issue l = l := by
    simp [issue, AuthState.st, hls]
  have hissueR :
      issue ({ r with
        core := { r.core with state := checkBit r.core.bit br }
        ctrl_mark := r.path_mark } : AuthState ψ) =
        outRight r br :=
    issue_rearmed_exact r br hrt

  simp [checkSourceAuth, cfg, hv, hreadyL, hreadyR, hcheckL,
    hcert, hcheckR, hissueL, hissueR, AuthState.withCore, AuthState.st,
    outRight_label, hrnt]

/-- The CHECK-only field and canonical-token interface. The right label, path,
leader and reset fields are preserved, and the verdict uses the CHECK input bit.
The equal branch keeps old token sidecars; A4/A6 issuance writes line scope and
the path mark. This supplies an internal cut, not a full-row recovery theorem. -/
theorem checkSource_goodEq_badVerdict_facts
    (hp : ψ > 0) (hj : j + 2 < ψ)
    (l r : AuthState ψ)
    (hll : l.core.label.val = j)
    (hrl : r.core.label.val = j + 1)
    (hlp : l.core.path = .some j bl)
    (hrp : r.core.path = .some (j + 1) br)
    (hls : l.core.state = .equal)
    (hrs : r.core.state = .equal ∨
      r.core.state = .larger ∨ r.core.state = .less)
    (hlt : l.core.path2 = none)
    (hrt : r.core.path2 = none)
    (hpm : l.path_mark = r.path_mark)
    (hlcm : l.ctrl_mark = l.path_mark)
    (hrcm : r.ctrl_mark ≠ r.path_mark) :
    let q := checkSourceAuth hp cfg l r
    let v := checkBit r.core.bit br
    q.1 = l ∧
    q.1.core.state = .equal ∧
    q.1.core.path = .some j bl ∧
    q.2.core.label.val = j + 1 ∧
    q.2.core.path = .some (j + 1) br ∧
    q.2.path_mark = r.path_mark ∧
    q.2.ctrl_mark = q.2.path_mark ∧
    q.2.core.state = v ∧
    q.2.core.leader = r.core.leader ∧
    q.2.core.reset_cmd = r.core.reset_cmd ∧
    (v = .larger →
      q.2.core.path2 = some ⟨0, 0, 0, 4⟩ ∧
      q.2.path2_scope = .line ∧ q.2.path2_mark = q.2.path_mark) ∧
    (v = .less →
      q.2.core.path2 = some ⟨0, 0, 0, 6⟩ ∧
      q.2.path2_scope = .line ∧ q.2.path2_mark = q.2.path_mark) ∧
    (v = .equal →
      q.2.core.path2 = none ∧
      q.2.path2_scope = r.path2_scope ∧ q.2.path2_mark = r.path2_mark) := by
  dsimp only
  rw [checkSource_goodEq_badVerdict_exact
    (hp := hp) (hj := hj) (l := l) (r := r)
    (hll := hll) (hrl := hrl) (hlp := hlp) (hrp := hrp)
    (hls := hls) (hrs := hrs) (hlt := hlt) (hrt := hrt)
    (hpm := hpm) (hlcm := hlcm) (hrcm := hrcm)]
  by_cases h4 : checkBit r.core.bit br = .larger
  · simp [outRight, h4, hls, hlp, hrl, hrp]
  · by_cases h6 : checkBit r.core.bit br = .less
    · simp [outRight, h4, h6, hls, hlp, hrl, hrp]
    · simp [outRight, h4, h6, hls, hlp, hrl, hrp, hrt]

#print axioms checkSource_goodEq_badVerdict_exact
#print axioms checkSource_goodEq_badVerdict_facts

end PPLLAuthCheckGoodEqBadVerdict
