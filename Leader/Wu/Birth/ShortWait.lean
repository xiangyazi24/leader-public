import Leader.Wu.Birth.GenerationControlRepair
import Leader.Wu.Protocol.DomainClosure
import Leader.Wu.WallSweep.Repair

set_option autoImplicit false

namespace BirthShortWait

open PPLL PPLLRepair PPLLDomain PPLLWallSweepRepair
open BirthGenerationControlRepair

/-- Existing physical label used as the shortened WAIT terminal. -/
def widthTerminal {psi width : Nat}
    (hwidth : 0 < width) (hle : width <= psi) : Fin psi :=
  ⟨width - 1, by omega⟩

/-- Both endpoints belong to the active WAIT prefix. -/
def activePair {psi : Nat} (width : Nat)
    (l r : AgentState psi) : Prop :=
  l.label.val < width ∧ r.label.val < width

instance activePair_decidable {psi : Nat} (width : Nat)
    (l r : AgentState psi) : Decidable (activePair width l r) := by
  unfold activePair
  infer_instance

/-- Original carry body, enabled only inside the active prefix. -/
def waitWidthCarry {psi width : Nat}
    (hwidth : 0 < width) (hle : width <= psi) (kappa : Nat)
    (l r : AgentState psi) : AgentState psi × AgentState psi :=
  if activePair width l r then
    if l.carry = true then
      if r.h_field = true then
        if r.label = widthTerminal hwidth hle then
          ({ l with carry := false },
           { r with h_field := false, count := satCountSucc kappa r.count })
        else
          ({ l with carry := false },
           { r with h_field := false, carry := true })
      else
        ({ l with carry := false }, { r with h_field := true })
    else (l, r)
  else (l, r)

/-- Original WAIT-reset body, enabled only inside the active prefix. -/
def waitWidthReset {psi width : Nat}
    (hwidth : 0 < width) (hle : width <= psi)
    (l r : AgentState psi) : AgentState psi × AgentState psi :=
  if activePair width l r then
    if l.reset = true then
      let r := if r.label ≠ widthTerminal hwidth hle then
        { r with reset := true }
      else r
      ({ l with reset := false }, { r with h_field := false })
    else (l, r)
  else (l, r)

/-- Cap at width-1, but keep the original full-psi WAIT movement boundary. -/
def waitWidthFinish {psi width : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (kappa : Nat) (l r : AgentState psi) : AgentState psi × AgentState psi :=
  let r := if r.label = widthTerminal hwidth hle ∧ r.count = kappa then
    { r with wait := false }
  else r
  if r.wait = false ∧
      l.label ≠ (⟨psi - 1, by omega⟩ : Fin psi) then
    ({ l with wait := false }, { r with wait := true })
  else (l, r)

/-- Prepare is literally the published stage; only Carry/Reset/Finish vary. -/
def waitWidth {psi width : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (kappa : Nat) (l r : AgentState psi) : AgentState psi × AgentState psi :=
  let q := waitSaturatedPrepare hpsi l r
  let q := waitWidthCarry hwidth hle kappa q.1 q.2
  let q := waitWidthReset hwidth hle q.1 q.2
  waitWidthFinish hpsi hwidth hle kappa q.1 q.2

/-- Count-only insertion at the actual SUPPRESS reset-command cut. -/
def shortCountReset {psi width : Nat}
    (hwidth : 0 < width) (hle : width <= psi)
    (l r : AgentState psi) : AgentState psi × AgentState psi :=
  if r.label = widthTerminal hwidth hle ∧ r.reset_cmd = true then
    (l, { r with count := 0 })
  else (l, r)

/-- The exact published prefix through reset movement and its second kill. -/
def suppressPrefix {psi : Nat} (l r : AgentState psi) :
    AgentState psi × AgentState psi :=
  let q0 := suppressSigStart l r
  let q0 := (resetKillComparison q0.1, resetKillComparison q0.2)
  let q1 := suppressSigMoveReset q0.1 q0.2
  (resetKillComparison q1.1, resetKillComparison q1.2)

/-- Repaired SUPPRESS with one count-only insertion; full-terminal echo is unchanged. -/
def suppressSigResetKillWidth {psi width : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AgentState psi) : AgentState psi × AgentState psi :=
  let q1 := suppressPrefix l r
  let q1 := shortCountReset hwidth hle q1.1 q1.2
  let q2 := suppressSigTerminal hpsi q1.1 q1.2
  let q3 := suppressSigEcho q2.1 q2.2
  suppressSigFinish q3.1 q3.2

/-- Generation changes only the WAIT call; all full-psi writers are unchanged. -/
def genCleanWidth {psi width : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (kappa : Nat) (l r : AgentState psi) : AgentState psi × AgentState psi :=
  let q := waitWidth hpsi hwidth hle kappa l r
  genCleanAfterWait hpsi q.1 q.2

private theorem widthTerminal_full {psi : Nat} (hpsi : 0 < psi) :
    widthTerminal (psi := psi) (width := psi) hpsi (Nat.le_refl psi) =
      (⟨psi - 1, by omega⟩ : Fin psi) := by
  apply Fin.ext
  rfl

private theorem activePair_full {psi : Nat} (l r : AgentState psi) :
    activePair psi l r :=
  ⟨l.label.isLt, r.label.isLt⟩

/-- Exact full-width carry regression. -/
theorem waitWidthCarry_full {psi : Nat} (hpsi : 0 < psi)
    (kappa : Nat) (l r : AgentState psi) :
    waitWidthCarry (psi := psi) (width := psi)
        hpsi (Nat.le_refl psi) kappa l r =
      waitSaturatedCarry hpsi kappa l r := by
  unfold waitWidthCarry
  rw [if_pos (activePair_full l r), widthTerminal_full hpsi]
  rfl

/-- Exact full-width reset regression. -/
theorem waitWidthReset_full {psi : Nat} (hpsi : 0 < psi)
    (l r : AgentState psi) :
    waitWidthReset (psi := psi) (width := psi)
        hpsi (Nat.le_refl psi) l r =
      waitSaturatedReset hpsi l r := by
  unfold waitWidthReset
  rw [if_pos (activePair_full l r), widthTerminal_full hpsi]
  rfl

/-- Exact full-width Finish regression. -/
theorem waitWidthFinish_full {psi : Nat} (hpsi : 0 < psi)
    (kappa : Nat) (l r : AgentState psi) :
    waitWidthFinish (psi := psi) (width := psi)
        hpsi hpsi (Nat.le_refl psi) kappa l r =
      waitSaturatedFinish hpsi kappa l r := by
  unfold waitWidthFinish
  rw [widthTerminal_full hpsi]
  rfl

/-- LDR-BIRTH-SHORT-WAIT-STAGES: exact original WAIT at full width. -/
theorem waitWidth_full {psi : Nat} (hpsi : 0 < psi)
    (kappa : Nat) (l r : AgentState psi) :
    waitWidth (psi := psi) (width := psi)
        hpsi hpsi (Nat.le_refl psi) kappa l r =
      waitSaturated hpsi kappa l r := by
  unfold waitWidth waitSaturated
  dsimp only
  rw [waitWidthCarry_full hpsi]
  rw [waitWidthReset_full hpsi]
  rw [waitWidthFinish_full hpsi]

private theorem shortCountReset_full_absorbed {psi : Nat}
    (hpsi : 0 < psi) (l r : AgentState psi) :
    let q := shortCountReset (psi := psi) (width := psi)
      hpsi (Nat.le_refl psi) l r
    suppressSigTerminal hpsi q.1 q.2 = suppressSigTerminal hpsi l r := by
  unfold shortCountReset
  rw [widthTerminal_full hpsi]
  by_cases h : r.label = (⟨psi - 1, by omega⟩ : Fin psi) ∧
      r.reset_cmd = true
  · simp [h, suppressSigTerminal]
  · simp [h, suppressSigTerminal]

/-- Exact original repaired SUPPRESS at full width. -/
theorem suppressWidth_full {psi : Nat} (hpsi : 0 < psi)
    (l r : AgentState psi) :
    suppressSigResetKillWidth (psi := psi) (width := psi)
        hpsi hpsi (Nat.le_refl psi) l r =
      suppressSigResetKill hpsi l r := by
  let p := suppressPrefix l r
  let s := shortCountReset (psi := psi) (width := psi)
    hpsi (Nat.le_refl psi) p.1 p.2
  have ht :
      suppressSigTerminal hpsi s.1 s.2 =
        suppressSigTerminal hpsi p.1 p.2 := by
    simpa only [s] using shortCountReset_full_absorbed hpsi p.1 p.2
  let tail : (AgentState psi × AgentState psi) →
      (AgentState psi × AgentState psi) := fun q =>
    let e := suppressSigEcho q.1 q.2
    suppressSigFinish e.1 e.2
  simpa [suppressSigResetKillWidth, suppressSigResetKill,
    suppressPrefix, p, s, tail] using congrArg tail ht

/-- Exact original generation row at full width. -/
theorem genCleanWidth_full {psi : Nat} (hpsi : 0 < psi)
    (kappa : Nat) (l r : AgentState psi) :
    genCleanWidth (psi := psi) (width := psi)
        hpsi hpsi (Nat.le_refl psi) kappa l r =
      genClean hpsi kappa l r := by
  unfold genCleanWidth genClean
  rw [waitWidth_full hpsi]

private theorem domain_of_count_payload_eq {psi kappa : Nat}
    (input output : AgentState psi) (hin : input.inProtocolDomain kappa)
    (hc : output.count = input.count)
    (hp : PayloadView.ofState output = PayloadView.ofState input) :
    output.inProtocolDomain kappa := by
  rw [inProtocolDomain_iff] at hin ⊢
  exact ⟨hc ▸ hin.1, hp ▸ hin.2⟩

private theorem domain_of_count_payload_bound {psi kappa : Nat}
    (input output : AgentState psi) (hin : input.inProtocolDomain kappa)
    (hc : output.count <= kappa)
    (hp : PayloadView.ofState output = PayloadView.ofState input) :
    output.inProtocolDomain kappa := by
  rw [inProtocolDomain_iff] at hin ⊢
  exact ⟨hc, hp ▸ hin.2⟩

private theorem prepare_frame {psi : Nat} (hpsi : 0 < psi)
    (l r : AgentState psi) :
    let q := waitSaturatedPrepare hpsi l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [waitSaturatedPrepare]
  repeat (first | constructor | rfl | split)

private theorem waitWidthCarry_payload {psi width kappa : Nat}
    (hwidth : 0 < width) (hle : width <= psi) (l r : AgentState psi) :
    let q := waitWidthCarry hwidth hle kappa l r
    PayloadView.ofState q.1 = PayloadView.ofState l ∧
      PayloadView.ofState q.2 = PayloadView.ofState r := by
  simp only [waitWidthCarry]
  repeat (first | constructor | rfl | split)

private theorem waitWidthCarry_count_closed {psi width kappa : Nat}
    (hwidth : 0 < width) (hle : width <= psi) (l r : AgentState psi)
    (hl : l.count <= kappa) (hr : r.count <= kappa) :
    let q := waitWidthCarry hwidth hle kappa l r
    q.1.count <= kappa ∧ q.2.count <= kappa := by
  simp only [waitWidthCarry]
  repeat (first | constructor | exact hl | exact hr |
    exact satCountSucc_le kappa r.count | split)

private theorem waitWidthReset_frame {psi width : Nat}
    (hwidth : 0 < width) (hle : width <= psi) (l r : AgentState psi) :
    let q := waitWidthReset hwidth hle l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [waitWidthReset]
  repeat (first | constructor | rfl | split)

private theorem waitWidthFinish_frame {psi width kappa : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AgentState psi) :
    let q := waitWidthFinish hpsi hwidth hle kappa l r
    (q.1.count = l.count ∧ PayloadView.ofState q.1 = PayloadView.ofState l) ∧
      (q.2.count = r.count ∧ PayloadView.ofState q.2 = PayloadView.ofState r) := by
  simp only [waitWidthFinish]
  repeat (first | constructor | rfl | split)

private theorem prepare_inProtocolDomain {psi kappa : Nat}
    (hpsi : 0 < psi) (l r : AgentState psi)
    (hl : l.inProtocolDomain kappa) (hr : r.inProtocolDomain kappa) :
    let q := waitSaturatedPrepare hpsi l r
    q.1.inProtocolDomain kappa ∧ q.2.inProtocolDomain kappa := by
  have hf := prepare_frame hpsi l r
  exact ⟨domain_of_count_payload_eq l _ hl hf.1.1 hf.1.2,
    domain_of_count_payload_eq r _ hr hf.2.1 hf.2.2⟩

theorem waitWidthCarry_inProtocolDomain {psi width kappa : Nat}
    (hwidth : 0 < width) (hle : width <= psi) (l r : AgentState psi)
    (hl : l.inProtocolDomain kappa) (hr : r.inProtocolDomain kappa) :
    let q := waitWidthCarry hwidth hle kappa l r
    q.1.inProtocolDomain kappa ∧ q.2.inProtocolDomain kappa := by
  have hp := waitWidthCarry_payload (kappa := kappa) hwidth hle l r
  have hc := waitWidthCarry_count_closed hwidth hle l r hl.1 hr.1
  exact ⟨domain_of_count_payload_bound l _ hl hc.1 hp.1,
    domain_of_count_payload_bound r _ hr hc.2 hp.2⟩

theorem waitWidthReset_inProtocolDomain {psi width kappa : Nat}
    (hwidth : 0 < width) (hle : width <= psi) (l r : AgentState psi)
    (hl : l.inProtocolDomain kappa) (hr : r.inProtocolDomain kappa) :
    let q := waitWidthReset hwidth hle l r
    q.1.inProtocolDomain kappa ∧ q.2.inProtocolDomain kappa := by
  have hf := waitWidthReset_frame hwidth hle l r
  exact ⟨domain_of_count_payload_eq l _ hl hf.1.1 hf.1.2,
    domain_of_count_payload_eq r _ hr hf.2.1 hf.2.2⟩

theorem waitWidthFinish_inProtocolDomain {psi width kappa : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AgentState psi) (hl : l.inProtocolDomain kappa)
    (hr : r.inProtocolDomain kappa) :
    let q := waitWidthFinish hpsi hwidth hle kappa l r
    q.1.inProtocolDomain kappa ∧ q.2.inProtocolDomain kappa := by
  have hf := waitWidthFinish_frame (kappa := kappa)
    hpsi hwidth hle l r
  exact ⟨domain_of_count_payload_eq l _ hl hf.1.1 hf.1.2,
    domain_of_count_payload_eq r _ hr hf.2.1 hf.2.2⟩

theorem waitWidth_inProtocolDomain {psi width kappa : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AgentState psi) (hl : l.inProtocolDomain kappa)
    (hr : r.inProtocolDomain kappa) :
    let q := waitWidth hpsi hwidth hle kappa l r
    q.1.inProtocolDomain kappa ∧ q.2.inProtocolDomain kappa := by
  let q0 := waitSaturatedPrepare hpsi l r
  have h0 := prepare_inProtocolDomain hpsi l r hl hr
  let q1 := waitWidthCarry hwidth hle kappa q0.1 q0.2
  have h1 := waitWidthCarry_inProtocolDomain hwidth hle q0.1 q0.2 h0.1 h0.2
  let q2 := waitWidthReset hwidth hle q1.1 q1.2
  have h2 := waitWidthReset_inProtocolDomain (kappa := kappa)
    hwidth hle q1.1 q1.2 h1.1 h1.2
  exact waitWidthFinish_inProtocolDomain hpsi hwidth hle
    q2.1 q2.2 h2.1 h2.2

theorem waitWidth_count_closed {psi width kappa : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AgentState psi) (hl : l.count <= kappa) (hr : r.count <= kappa) :
    let q := waitWidth hpsi hwidth hle kappa l r
    q.1.count <= kappa ∧ q.2.count <= kappa := by
  let q0 := waitSaturatedPrepare hpsi l r
  have f0 := prepare_frame hpsi l r
  have h0l : q0.1.count <= kappa := by rw [f0.1.1]; exact hl
  have h0r : q0.2.count <= kappa := by rw [f0.2.1]; exact hr
  let q1 := waitWidthCarry hwidth hle kappa q0.1 q0.2
  have h1 := waitWidthCarry_count_closed hwidth hle q0.1 q0.2 h0l h0r
  let q2 := waitWidthReset hwidth hle q1.1 q1.2
  have f2 := waitWidthReset_frame hwidth hle q1.1 q1.2
  have h2l : q2.1.count <= kappa := by rw [f2.1.1]; exact h1.1
  have h2r : q2.2.count <= kappa := by rw [f2.2.1]; exact h1.2
  let q3 := waitWidthFinish hpsi hwidth hle kappa q2.1 q2.2
  have f3 := waitWidthFinish_frame (kappa := kappa)
    hpsi hwidth hle q2.1 q2.2
  change q3.1.count <= kappa ∧ q3.2.count <= kappa
  exact ⟨by rw [f3.1.1]; exact h2l, by rw [f3.2.1]; exact h2r⟩

private theorem shortCountReset_payload {psi width : Nat}
    (hwidth : 0 < width) (hle : width <= psi) (l r : AgentState psi) :
    let q := shortCountReset hwidth hle l r
    PayloadView.ofState q.1 = PayloadView.ofState l ∧
      PayloadView.ofState q.2 = PayloadView.ofState r := by
  unfold shortCountReset
  repeat (first | constructor | rfl | split)

private theorem shortCountReset_count_closed {psi width kappa : Nat}
    (hwidth : 0 < width) (hle : width <= psi) (l r : AgentState psi)
    (hl : l.count <= kappa) (hr : r.count <= kappa) :
    let q := shortCountReset hwidth hle l r
    q.1.count <= kappa ∧ q.2.count <= kappa := by
  unfold shortCountReset
  repeat (first | constructor | exact hl | exact hr |
    exact Nat.zero_le kappa | split)

theorem shortCountReset_inProtocolDomain {psi width kappa : Nat}
    (hwidth : 0 < width) (hle : width <= psi) (l r : AgentState psi)
    (hl : l.inProtocolDomain kappa) (hr : r.inProtocolDomain kappa) :
    let q := shortCountReset hwidth hle l r
    q.1.inProtocolDomain kappa ∧ q.2.inProtocolDomain kappa := by
  have hp := shortCountReset_payload hwidth hle l r
  have hc := shortCountReset_count_closed hwidth hle l r hl.1 hr.1
  exact ⟨domain_of_count_payload_bound l _ hl hc.1 hp.1,
    domain_of_count_payload_bound r _ hr hc.2 hp.2⟩

private theorem waitWidthFinish_right_clock {psi width kappa : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AgentState psi) :
    let q := waitWidthFinish hpsi hwidth hle kappa l r
    q.2.h_field = r.h_field ∧ q.2.reset = r.reset := by
  simp only [waitWidthFinish]
  repeat (first | constructor | rfl | split)

/-- Root incoming prepare survives, while arbitrary tail carry/reset cannot enter. -/
theorem rootIncoming_noTailImport {psi width : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (hlt : width < psi) (kappa : Nat) (l r : AgentState psi)
    (hl : l.label = (⟨psi - 1, by omega⟩ : Fin psi))
    (hr : r.label = (⟨0, hpsi⟩ : Fin psi)) :
    let q := waitWidth hpsi hwidth hle kappa l r
    q.2.h_field = false ∧ q.2.reset = true := by
  have hl0 : l.label ≠ (⟨0, hpsi⟩ : Fin psi) := by
    intro h
    have hv := congrArg Fin.val (hl.symm.trans h)
    dsimp at hv
    omega
  let r0 : AgentState psi := { r with reset := true, h_field := false }
  have hp : waitSaturatedPrepare hpsi l r = (l, r0) := by
    simp [waitSaturatedPrepare, hl0, hr, r0]
  have ha : ¬ activePair width l r0 := by
    intro h
    have hv := h.1
    rw [hl] at hv
    dsimp at hv
    omega
  have hc : waitWidthCarry hwidth hle kappa l r0 = (l, r0) := by
    unfold waitWidthCarry
    rw [if_neg ha]
  have hz : waitWidthReset hwidth hle l r0 = (l, r0) := by
    unfold waitWidthReset
    rw [if_neg ha]
  have hf := waitWidthFinish_right_clock hpsi hwidth hle
    (kappa := kappa) l r0
  change
    (waitWidth hpsi hwidth hle kappa l r).2.h_field = false ∧
      (waitWidth hpsi hwidth hle kappa l r).2.reset = true
  unfold waitWidth
  rw [hp]
  dsimp only
  rw [hc]
  dsimp only
  rw [hz]
  simpa [r0] using hf

private theorem shortWait_resetKillComparison_label {psi : Nat}
    (u : AgentState psi) :
    (resetKillComparison u).label = u.label := by
  unfold resetKillComparison
  split <;> rfl

private theorem shortWait_suppressSigMoveReset_right_label {psi : Nat}
    (l r : AgentState psi) :
    (suppressSigMoveReset l r).2.label = r.label := by
  unfold suppressSigMoveReset
  split <;> rfl

private theorem suppressPrefix_right_label {psi : Nat} (l r : AgentState psi) :
    (suppressPrefix l r).2.label = r.label := by
  let q0 := suppressSigStart l r
  let q0k := (resetKillComparison q0.1, resetKillComparison q0.2)
  let q1 := suppressSigMoveReset q0k.1 q0k.2
  change (resetKillComparison q1.2).label = r.label
  calc
    (resetKillComparison q1.2).label = q1.2.label :=
      shortWait_resetKillComparison_label q1.2
    _ = q0k.2.label :=
      shortWait_suppressSigMoveReset_right_label q0k.1 q0k.2
    _ = q0.2.label := shortWait_resetKillComparison_label q0.2
    _ = r.label := by rfl

private theorem suppressPrefix_moving_reset {psi : Nat}
    (l r : AgentState psi) (hl : l.reset_cmd = true) :
    (suppressPrefix l r).2.reset_cmd = true ∧
      (suppressPrefix l r).2.label = r.label := by
  cases hleader : l.leader <;>
    simp [suppressPrefix, suppressSigStart, resetKillComparison,
      clearComparisonSignal, suppressSigMoveReset, hl, hleader]

private theorem suppressTerminal_preserves_zero {psi : Nat}
    (hpsi : 0 < psi) (l r : AgentState psi) (hr : r.count = 0) :
    (suppressSigTerminal hpsi l r).2.count = 0 := by
  unfold suppressSigTerminal
  split <;> simp_all

private theorem suppressEcho_right_count {psi : Nat} (l r : AgentState psi) :
    (suppressSigEcho l r).2.count = r.count := by
  unfold suppressSigEcho
  repeat (first | rfl | split)

private theorem suppressFinish_right_count {psi : Nat} (l r : AgentState psi) :
    (suppressSigFinish l r).2.count = r.count := by
  rfl

/-- A real moving reset_cmd zeroes the shortened physical counter. -/
theorem movingReset_zerosShortCount {psi width : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AgentState psi) (hl : l.reset_cmd = true)
    (hr : r.label = widthTerminal hwidth hle) :
    let q := suppressSigResetKillWidth hpsi hwidth hle l r
    q.2.count = 0 := by
  let p := suppressPrefix l r
  have hp := suppressPrefix_moving_reset l r hl
  have hreset : p.2.reset_cmd = true := hp.1
  have hlabel : p.2.label = widthTerminal hwidth hle := hp.2.trans hr
  let s := shortCountReset hwidth hle p.1 p.2
  have hs : s.2.count = 0 := by
    simp [s, shortCountReset, hlabel, hreset]
  let t := suppressSigTerminal hpsi s.1 s.2
  have ht : t.2.count = 0 := suppressTerminal_preserves_zero hpsi s.1 s.2 hs
  let e := suppressSigEcho t.1 t.2
  have he : e.2.count = 0 := (suppressEcho_right_count t.1 t.2).trans ht
  change (suppressSigFinish e.1 e.2).2.count = 0
  exact (suppressFinish_right_count e.1 e.2).trans he

/-- On the physical full terminal, shortening leaves the entire old SUPPRESS row exact. -/
theorem suppressWidth_fullTerminal {psi width : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (hlt : width < psi) (l r : AgentState psi)
    (hr : r.label = (⟨psi - 1, by omega⟩ : Fin psi)) :
    suppressSigResetKillWidth hpsi hwidth hle l r =
      suppressSigResetKill hpsi l r := by
  let p := suppressPrefix l r
  have hp : p.2.label = r.label := suppressPrefix_right_label l r
  have hne : p.2.label ≠ widthTerminal hwidth hle := by
    rw [hp, hr]
    intro h
    have hv := congrArg Fin.val h
    dsimp [widthTerminal] at hv
    omega
  have hs : shortCountReset hwidth hle p.1 p.2 = p := by
    unfold shortCountReset
    rw [if_neg]
    intro h
    exact hne h.1
  let tail : (AgentState psi × AgentState psi) →
      (AgentState psi × AgentState psi) := fun q =>
    let t := suppressSigTerminal hpsi q.1 q.2
    let e := suppressSigEcho t.1 t.2
    suppressSigFinish e.1 e.2
  simpa [suppressSigResetKillWidth, suppressSigResetKill,
    suppressPrefix, p, tail] using congrArg tail hs

private theorem genCleanAfterWait_count {psi : Nat} (hpsi : 0 < psi)
    (l r : AgentState psi) :
    let q := genCleanAfterWait hpsi l r
    q.1.count = l.count ∧ q.2.count = r.count := by
  simp only [genCleanAfterWait, genSigSaturatedStart, genCleanEmit,
    genCleanPropagate, genSigSaturatedFinish]
  repeat (first | constructor | rfl | split)

/-- genCleanWidth keeps every count in range once waitWidth has done so. -/
theorem genCleanWidth_count_closed {psi width kappa : Nat}
    (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (l r : AgentState psi) (hl : l.count <= kappa) (hr : r.count <= kappa) :
    let q := genCleanWidth hpsi hwidth hle kappa l r
    q.1.count <= kappa ∧ q.2.count <= kappa := by
  let w := waitWidth hpsi hwidth hle kappa l r
  have hw := waitWidth_count_closed hpsi hwidth hle l r hl hr
  let g := genCleanAfterWait hpsi w.1 w.2
  have hg := genCleanAfterWait_count hpsi w.1 w.2
  change g.1.count <= kappa ∧ g.2.count <= kappa
  exact ⟨by rw [hg.1]; exact hw.1, by rw [hg.2]; exact hw.2⟩

end BirthShortWait
