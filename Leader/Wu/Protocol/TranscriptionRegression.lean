import Leader.Wu.Protocol.Algorithm

/-!
# Executable regressions for non-literal transcription choices

Wu's Algorithms 1–20 contain several malformed assignments, missing token
consumptions, impossible guards, and reads from optional `⊥` payloads.  The
executable transition in `Leader.Wu.Protocol.Algorithm` is total only because it selects
explicit interpretations for those lines.  This module pins the selected Lean
behavior with small exact regressions.

These theorems belong to the **formalization audit**, not the thesis source
lane: checking an interpretation does not turn the corresponding printed line
into `SOURCE-VERIFIED`.  The page-level status of each line is recorded in
`FORMALIZATION_AUDIT.md` and `ERRATA.md`.
-/

namespace PPLLTranscriptionAudit

open PPLL

/-- A neutral two-label agent used only to isolate one ambiguous pseudocode
assignment at a time.  All optional carriers are absent and all control tokens
are inactive unless a regression overrides the relevant field. -/
def auditState (label : Fin 2) : AgentState 2 :=
  { leader := false, probe := false, phase := false, bit := false,
    wait := true, state := .none, path := .bot, reset := false,
    carry := false, count := 0, label, h_field := false, path2 := none,
    path3 := none, path4 := none, path5 := none, p := false,
    p_carry := false, reset_cmd := false, echo := false, signal_B := 0,
    bullet := 0, shield := true, write_state := .none, write := .none,
    last := false, last_set := false, last_unset := false,
    b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }

/-! ## Algorithm 3: inferred assignments and single-use carry

Printed lines 22–23 and 27–28 use equality signs where state updates are
required.  The print also never clears `l.carry` after lines 10–18 consume it.
The Lean transition reads the equalities as assignments and the carry as a
single-use token.
-/

private def waitCarryL : AgentState 2 := { auditState 0 with carry := true }
private def waitCarryR : AgentState 2 := { auditState 1 with h_field := true }

/-- The interpreted WAIT consumes the initiator carry that increments the
terminal counter.  This extra clearing assignment is absent from Algorithm 3. -/
theorem wait_interpreted_consumes_carry :
    (wait (by omega : 2 > 0) 10 waitCarryL waitCarryR).1.carry = false := by
  rfl

private def waitResetL : AgentState 2 := { auditState 0 with reset := true }
private def waitResetR : AgentState 2 := { auditState 0 with h_field := true }

/-- Lean reads Algorithm 3 lines 22–23 as the assignments
`l.reset ← 0` and `r.h ← 0`, rather than literal equality expressions. -/
theorem wait_interprets_plain_reset_equalities_as_updates :
    let q := wait (by omega : 2 > 0) 10 waitResetL waitResetR
    q.1.reset = false ∧ q.2.h_field = false := by
  decide

private def waitDoneL : AgentState 2 := auditState 0
private def waitDoneR : AgentState 2 := { auditState 0 with wait := false }

/-- Lean likewise reads Algorithm 3 lines 27–28 as assignments propagating the
finished-wait marker left while resetting the responder marker. -/
theorem wait_interprets_plain_wait_equalities_as_updates :
    let q := wait (by omega : 2 > 0) 10 waitDoneL waitDoneR
    q.1.wait = false ∧ q.2.wait = true := by
  decide

/-! ## Algorithm 5: asymmetric printed bit source

Algorithm 5 line 13 sends a backward clean command from `l.path5`, but prints
its polarity as `1 - r.path5[2]`.  The Lean correction uses the bit of the
initiator token actually being checked.  The following pair gives both sides a
`path5`, with opposite bits, so the two readings are observably different.
-/

private def cleanLine13L : AgentState 2 :=
  { auditState 0 with path5 := some (1, 1) }

private def cleanLine13R : AgentState 2 :=
  { auditState 1 with path := .some 1 0, path5 := some (0, 0) }

/-- The implemented line-13 correction complements `l.path5[2]=1`, producing
clean-command polarity zero. -/
theorem cleanSig_line13_uses_initiator_path5_bit :
    (cleanSigStep4 cleanLine13L cleanLine13R).1.path4 = some (-1, 0) := by
  rfl

/-- The same execution is not the literal printed computation from
`r.path5[2]=0`, which would produce polarity one. -/
theorem cleanSig_line13_not_literal_responder_path5_bit :
    (cleanSigStep4 cleanLine13L cleanLine13R).1.path4 ≠ some (-1, 1) := by
  decide

/-- A total auxiliary reading of the literal Algorithm 5 line 13.  It uses
the responder's `path5` bit exactly as printed and no-ops when that unguarded
field is absent.  This definition exists only to compare source and repair
lanes; it is not the executable protocol. -/
def printedCleanSigStep4 (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  match l.path5, r.path, r.path5 with
  | some (p5Label, _), .some rLabel _, some (_, printedBit) =>
    if p5Label ≠ (-1 : Int) then
      let l := if p5Label ≠ Int.ofNat rLabel - 1 then
        { l with path4 := some ((-1 : Int), 1 - printedBit) }
      else l
      ({ l with path5 := none }, r)
    else (l, r)
  | _, _, _ => (l, r)

/-- CLEAN_SIG with only line 13 changed back to its printed opposite-endpoint
bit.  All other stages and their sequential order are shared with `cleanSig`,
so a behavioral difference isolates that source line. -/
def cleanSigWithPrintedLine13 (hψ : ψ > 0) (l r : AgentState ψ) :
    AgentState ψ × AgentState ψ :=
  let l := cleanSigGenConnect l
  let r := cleanSigGenConnect r
  let (l, r) := cleanSigStep3 l r
  let (l, r) := printedCleanSigStep4 l r
  let (l, r) := cleanSigStep5 hψ l r
  let (l, r) := cleanSigStep6 hψ l r
  (cleanSigCleanApply l, cleanSigCleanApply r)

/-- The printed line-13 polarity can die at label zero one interaction before
reaching the signal whose connection failed.  With the symmetric Lean repair,
the returned phase-one command crosses that boundary and clears the source;
with the literal responder bit, phase zero is consumed and the source survives.
The first interaction also proves the two clean-command polarities differ. -/
theorem cleanSig_line13_literal_command_dies_before_source :
    let source : AgentState 2 := { auditState 0 with path := .some 0 0 }
    let detector : AgentState 2 :=
      { auditState 1 with path5 := some (0, 0) }
    let target : AgentState 2 := { auditState 0 with path := .some 0 0 }
    let repairedDetector :=
      (cleanSig (by omega : 2 > 0) detector target).1
    let printedDetector :=
      (cleanSigWithPrintedLine13 (by omega : 2 > 0) detector target).1
    repairedDetector.path4 = some (-1, 1) ∧
      printedDetector.path4 = some (-1, 0) ∧
      (cleanSig (by omega : 2 > 0) source repairedDetector).1.path = .bot ∧
      (cleanSig (by omega : 2 > 0) source printedDetector).1.path = .some 0 0 := by
  decide

/-! ## Algorithms 8 and 13: repaired tuple/terminal operations -/

private def terminalCompareR : AgentState 2 :=
  { auditState 1 with path2 := some ⟨0, 0, 0, 1⟩ }

/-- Algorithm 8 prints the unreachable guard `r.label = ψ`.  Lean uses the
terminal in-domain label `ψ-1`, so equal terminal bits select action 3. -/
theorem compareBit_interprets_terminal_guard_at_psi_pred :
    (compareBitUpdateR (by omega : 2 > 0) terminalCompareR).path2 =
      some ⟨0, 0, 0, 3⟩ := by
  rfl

private def disappearCarryL : AgentState 2 :=
  { auditState 0 with p_carry := true }

private def disappearCarryR : AgentState 2 :=
  { auditState 1 with p := true }

/-- As for WAIT, the Lean DISAPPEAR transition consumes `l.p_carry`; the
clearing assignment is not printed in Algorithm 13. -/
theorem disappear_interpreted_consumes_carry :
    (disappear (by omega : 2 > 0) disappearCarryL disappearCarryR).1.p_carry =
      false := by
  rfl

private def disappearStartRState : AgentState 2 :=
  { auditState 0 with state := .toss }

/-- Algorithm 13 line 3 assigns a four-tuple to `r.path2[4]`, which is only one
component.  Lean interprets it as a whole-`path2` assignment with action 5. -/
theorem disappear_interprets_line3_as_whole_path2_write :
    (disappear (by omega : 2 > 0) (auditState 1)
      disappearStartRState).2.path2 = some ⟨0, 0, 0, 5⟩ := by
  rfl

/-! ## Algorithms 15–17: plain equalities and moving control tokens -/

private def signalAssignL : AgentState 2 :=
  { auditState 0 with leader := true }

private def signalAssignR : AgentState 2 := auditState 1

/-- Algorithm 15 line 17 is printed with `=`.  Lean reads it as assignment;
on a non-barrier leader edge it writes the propagated absence signal to one. -/
theorem eliminateLeaders_interprets_line17_as_assignment :
    (eliminateLeaders (by omega : 2 > 0)
      signalAssignL signalAssignR).2.signal_B = 1 := by
  rfl

private def migrateL : AgentState 2 := auditState 0
private def migrateR : AgentState 2 := { auditState 1 with leader := true }

/-- Algorithm 16 lines 2–3 are also printed with equality signs.  Lean reads
them as assignments that migrate a nonzero-label responder leader left. -/
theorem writeSeq_interprets_leader_equalities_as_assignments :
    let q := writeSeq (by omega : 2 > 0) migrateL migrateR
    q.1.leader = true ∧ q.2.leader = false := by
  decide

private def lastSetR : AgentState 2 :=
  { auditState 1 with last_set := true }

/-- Algorithm 17 propagates `last_set` but prints no source clearing.  Lean
chooses movement semantics: the responder token is consumed as the initiator
receives its successor. -/
theorem groupInfo_interpreted_consumes_last_set :
    let q := groupInfo (by omega : 2 > 0) (auditState 0) lastSetR
    q.1.last_set = true ∧ q.2.last_set = false ∧ q.2.last = true := by
  decide

/-! ## Algorithm 20: `last`-guard correction

Printed line 7 places an assignment `l.last ← 1` inside a guard.  Printed line
17 tests `l.label = 1`, although `GROUP_INFO` computes `last` for this role.
Lean tests `last = 1` at both sites.  Opposite-label/marker examples below make
that second correction observable.
-/

private def checkLastTrue : AgentState 2 :=
  { auditState 0 with
      path3 := some { label := 0, bit := 0, flag := 1 }
      write_state := .depart, write := .move, last := true }

private def checkLastFalse : AgentState 2 :=
  { checkLastTrue with last := false }

/-- Lean reads Algorithm 20 line 7's assignment-in-guard as a test: a matching
path is cleared when `last=true`, while the otherwise identical `last=false`
state is unchanged by this helper. -/
theorem moveWsig_line7_interprets_last_assignment_as_test :
    (moveWsigCheckLast checkLastTrue).path3 = none ∧
    (moveWsigCheckLast checkLastTrue).write = .none ∧
    (moveWsigCheckLast checkLastTrue).write_state = .none ∧
    moveWsigCheckLast checkLastFalse = checkLastFalse := by
  decide

private def transferLastL : AgentState 2 :=
  { auditState 0 with
      path3 := some { label := 1, bit := 0, flag := 1 }
      write_state := .depart, last := true }

private def transferLabelL : AgentState 2 :=
  { auditState 1 with
      path3 := some { label := 0, bit := 0, flag := 1 }
      write_state := .depart, last := false }

/-- Lean emits `ws_echo` when `last=true` even though the source agent's label is
zero, contradicting a literal `label=1` guard. -/
theorem moveWsig_line17_uses_last_not_label :
    (moveWsig (by omega : 2 > 0)
      transferLastL (auditState 1)).1.ws_echo = true := by
  decide

/-- Conversely, label one alone does not emit `ws_echo` when `last=false`. -/
theorem moveWsig_line17_does_not_use_label :
    (moveWsig (by omega : 2 > 0)
      transferLabelL (auditState 0)).1.ws_echo = false := by
  decide

/-! ## Adjacent prose regressions

The pseudocode defects are not confined to assignment glyphs.  Two nearby
explanatory claims are exact statements that fail under the same sequential
semantics used by the printed top-level algorithm.
-/

private def genSigTwoL : AgentState 2 := { auditState 0 with wait := false }
private def genSigTwoR : AgentState 2 := auditState 1

/-- For `ψ=2`, one interaction executes Algorithm 4 lines 2, 4, 6, 9, and 13
sequentially and completes both sub-signals.  Thus the prose claim on printed
p.20 / PDF p.33 that generation takes *exactly* `2ψ` interactions is not true
for the executable sequential reading (one is not four). -/
theorem genSig_two_labels_completes_in_one_interaction :
    let q := genSig (by omega : 2 > 0) 10 genSigTwoL genSigTwoR
    q.1.path = .some 0 0 ∧ q.2.path = .some 1 0 ∧
      q.1.state = .depart ∧ q.2.state = .depart := by
  decide

/-- The denominator identity used in the DISAPPEAR prose is not an arithmetic
identity in independent `n` and `ψ`: already `ψ=2, n=5` gives
`2^(2^ψ)=16 ≠ 5`.  An exact probability equality with `1/n` therefore requires
an additional parameter equation, not merely asymptotic `ψ=Θ(log log n)`. -/
theorem disappear_probability_denominator_ne_example :
    2 ^ (2 ^ 2) ≠ (5 : Nat) := by
  decide

private def checkLessState : AgentState 2 :=
  { auditState 0 with state := .less }

/-- A `.less` CHECK result means the group bit is smaller than the signal bit
and selects action 6.  Algorithm 11 line 12's comment repeats `ID(G)>ID(S)`
from the preceding `.larger` branch; the second inequality sign is textual
error, while the executable action agrees with the surrounding prose. -/
theorem check_less_selects_lottery_action :
    (checkSigSetResult checkLessState).path2 = some ⟨0, 0, 0, 6⟩ := by
  rfl

/-! ## Totalization of reads from `⊥`

Several printed algorithms index `path`, `path2`, `path3`, `path4`, or `path5`
without first excluding `⊥`.  The current Lean convention makes each isolated
missing-payload read a no-op.  This theorem records representative choices; it
does not claim that the thesis specifies this convention.
-/

private def cleanAbsentConnect : AgentState 2 :=
  { auditState 0 with path := .some 0 0 }

/-- Representative absent optional payloads leave the corresponding local
helper unchanged under Lean's total no-op convention. -/
theorem optional_bottom_reads_are_noops :
    cleanSigCleanApply cleanAbsentConnect = cleanAbsentConnect ∧
    compareBitUpdateR (by omega : 2 > 0) (auditState 0) = auditState 0 ∧
    checkSigSetReady (auditState 0) = auditState 0 ∧
    writeActionApplyOverwrite (auditState 0) = auditState 0 ∧
    moveWsigCheckLast (auditState 0) = auditState 0 := by
  decide

end PPLLTranscriptionAudit
