import Leader.Wu.Birth.ReacquireFrontDrift

set_option autoImplicit false

/-! # The reset/echo front drift is false on the public ring-four Reacquire fixture

`BirthB1ReacquireFrontDrift` proposes a proof-side front for the B4 Reacquire phase, read only
from reset commands in the right drain and echoes in the protected triple, and reduces
`ReacquireFrontDrift` to three interfaces (row frames, `FrontExtraction`, advance laws).

On the repository's own Reacquire fixture `BirthB1ReacquirePhaseMass.ringFourReacquire`
(n = 4, psi = 2, kappa = 2, tau = 3; proved Reacquire by `ringFourReacquire_is_reacquire`)
there is no reset command and no echo anywhere: the Local3 carrier is broken by comparison
metadata left on site 2 by the boundary crossing, not by a reset corridor. Consequently
* `FrontExtraction` is false (none of its four moving-front modes holds), and
* clause 3 fails for this front: for every scheduler edge the literal successor neither hits the
  cap target, nor is a Carrier (a protected cell still fails `Metadata`), nor raises the front
  (it stays 0). So `ReacquireFrontDrift ... (front ring anchor)` is false. -/

namespace BirthB4ReacquireFrontDriftNoGo

open PPLL PPLLRepair PPLLResearchFormulation PPLLExpiringComparisonRepair
open BirthWaitPassive BirthB1ReacquireFrontDrift

private theorem hpsi2 : 0 < 2 := by decide
private theorem h2 : 2 <= 2 := by decide
private theorem hn4 : 4 <= 4 := by decide

abbrev R4 : DirectedRing 4 := BirthPhaseWait2Transfer.boundaryRing4
abbrev A4 : Fin 4 := BirthPhaseWait2Transfer.boundaryAnchor4
abbrev C4 : FC 4 2 2 3 := BirthB1ReacquirePhaseMass.ringFourReacquire

theorem c4_reacquire :
    BirthPhaseWait2BlockProgress.Reacquire hpsi2 h2 hn4 2 3 R4 A4 C4 :=
  BirthB1ReacquirePhaseMass.ringFourReacquire_is_reacquire

/-- No reset command and no echo on any cell of the fixture. -/
theorem c4_reset_echo_free :
    ∀ i : Fin 4, (frontRaw (C4 i)).reset_cmd = false ∧ (frontRaw (C4 i)).echo = false := by
  decide

theorem c4_no_front_mode :
    ¬ (ResetReady R4 A4 C4 ∨ TailEchoReady R4 A4 C4 ∨ MiddleEchoReady R4 A4 C4 ∨
        AnchorEchoReady R4 A4 C4) := by
  unfold ResetReady TailEchoReady MiddleEchoReady AnchorEchoReady MaxResetLive ScanResetLive
  decide

/-- The extraction interface of the front drift is false. -/
theorem frontExtraction_false : ¬ FrontExtraction hpsi2 h2 hn4 2 3 R4 A4 := by
  intro h
  exact c4_no_front_mode (h C4 c4_reacquire)

theorem c4_no_rowCap : ∀ e : Fin 4, ¬ BirthShortDoneTerminalPassiveR4.RowCap2 hpsi2 h2 2 R4 C4 e := by
  unfold BirthShortDoneTerminalPassiveR4.RowCap2
  decide

theorem c4_target_false (e : Fin 4) :
    BirthPhaseWait2BlockProgress.target hpsi2 h2 2 R4 C4 [e] = false := by
  cases ht : BirthPhaseWait2BlockProgress.target hpsi2 h2 2 R4 C4 [e]
  · rfl
  · exfalso
    obtain ⟨pre, e', post, hu, hcap⟩ :=
      (BirthPhaseWait2BlockProgress.target_true_iff hpsi2 h2 2 R4 C4 [e]).1 ht
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hu
      obtain ⟨he, _⟩ := hu
      subst he
      exact c4_no_rowCap e hcap
    | cons a pre =>
      simp only [List.cons_append, List.cons.injEq] at hu
      obtain ⟨_, hnil⟩ := hu
      exact absurd hnil.symm (by simp)

set_option maxHeartbeats 200000000 in
set_option maxRecDepth 131072 in
/-- The front of the fixture and of each one-edge successor is zero. -/
theorem c4_front_zero :
    front R4 A4 C4 = 0 ∧
      ∀ e : Fin 4, front R4 A4 (BirthPhaseWait2BlockProgress.currentStep2 hpsi2 h2 R4 C4 e) = 0 := by
  decide

set_option maxHeartbeats 200000000 in
set_option maxRecDepth 131072 in
/-- Every one-edge successor still has a protected cell whose registers are not in metadata form. -/
theorem c4_successor_not_metadata :
    ∀ e : Fin 4,
      let D := BirthPhaseWait2BlockProgress.currentStep2 hpsi2 h2 R4 C4 e
      ¬ Metadata (raw (D A4)) ∨ ¬ Metadata (raw (D (R4.rightNeighbor A4))) ∨
        ¬ Metadata (raw (D (R4.rightNeighbor (R4.rightNeighbor A4)))) := by
  unfold Metadata
  decide

theorem c4_successor_not_carrier (e : Fin 4) :
    ¬ BirthPhaseWait2BlockProgress.Carrier hpsi2 h2 hn4 R4 A4
      (BirthPhaseWait2BlockProgress.currentStep2 hpsi2 h2 R4 C4 e) := by
  intro hC
  have hL := hC.1
  unfold BirthPhaseWait2BlockProgress.LocalCarrier BirthPhaseWait2Transfer.LocalWait2Carrier at hL
  rcases c4_successor_not_metadata e with h0 | h1 | h2'
  · exact h0 hL.pass0.1
  · exact h1 hL.pass1.1
  · exact h2' hL.pass2.1

/-- From the Reacquire fixture, no scheduler edge makes strict front progress. -/
theorem c4_no_strict_step (e : Fin 4) : ¬ StrictStep hpsi2 h2 hn4 2 3 R4 A4 C4 e := by
  unfold StrictStep
  intro h
  rcases h with ht | hc | ⟨_, hlt⟩
  · rw [c4_target_false e] at ht
    exact Bool.noConfusion ht
  · exact c4_successor_not_carrier e hc
  · rw [c4_front_zero.1, c4_front_zero.2 e] at hlt
    exact Nat.lt_irrefl 0 hlt

theorem frontClause3_false : ¬ FrontClause3 hpsi2 h2 hn4 2 3 R4 A4 := by
  intro h
  obtain ⟨e, he⟩ := h C4 c4_reacquire
  exact c4_no_strict_step e he

/-- The proposed front drift itself is false at n = 4. -/
theorem reacquireFrontDrift_front_false :
    ¬ BirthB1ReacquirePhaseMass.ReacquireFrontDrift hpsi2 h2 hn4 2 3 R4 A4 (front R4 A4) := by
  intro h
  obtain ⟨e, he⟩ := h.2.2 C4 c4_reacquire
  exact c4_no_strict_step e he

end BirthB4ReacquireFrontDriftNoGo
