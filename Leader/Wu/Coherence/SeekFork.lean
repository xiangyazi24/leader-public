import Leader.Wu.Coherence.BirthQuarantine

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31SeekFork

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open R2CoherenceV31
open R2CoherenceV31Closure
open R2CoherenceV31BirthQuarantine

private theorem h3 : 0 < 3 := by decide
private theorem h23 : 2 ≤ 3 := by decide
private def ring3 : DirectedRing 3 := ⟨by decide⟩

/-- Clean physical literal in the same regression style as the V31 entrance
and proxy witnesses. -/
private def literal
    (lab : Fin 3) (leader : Bool := false) : R2.Cell 3 3 48 :=
  let seed := WriterProducerRegression.clean h3 (fun _ => false) lab
  let b := seed.base.core.core
  let b' : BoundedAgentState 3 3 := {
    b with
      leader := leader
      shield := leader
      gen_ws := false
      label := lab
      state := .none
      path := .bot
      bit := false
      path2 := none
      path3 := none
      path4 := none
      path5 := none
      p := false
      p_carry := false
      reset_cmd := false
      echo := false
      write_state := .none
      write := .none
      b_carry := false
  }
  ⟨⟨⟨b', false⟩, 48⟩, 0⟩

/-- Temporary V3.1 wrapper.  `quarantineInitV31` below overwrites these
controls, so their initial value is semantically irrelevant. -/
private def preQ : FC 3 3 3 48 := fun i =>
  match i.val with
  | 0 => ⟨literal 0 true,  ⟨.open, .none⟩⟩
  | 1 => ⟨literal 1 false, ⟨.open, .none⟩⟩
  | _ => ⟨literal 2 false, ⟨.open, .none⟩⟩

/-- All-closing/token-none quarantine state with labels 0,1,2 and one leader
at label zero. -/
private def Q : FC 3 3 3 48 :=
  quarantineInitV31 preQ

private def Q1 : FC 3 3 3 48 :=
  stepV3 h3 h23 ring3 Q 0

private def Q2 : FC 3 3 3 48 :=
  stepV3 h3 h23 ring3 Q1 2

instance birthQuarantineV31Dec {n ψ κ τ : Nat} (C : R2CoherenceV31.FC n ψ κ τ) :
    Decidable (BirthQuarantineV31 C) := by
  unfold BirthQuarantineV31
  infer_instance

/-- Sanity: the fixture has exactly the intended controller initialization. -/
theorem fork_quarantine :
    BirthQuarantineV31 Q := by
  decide +kernel

/-- Sanity: the physical labels/leader satisfy the strong post-birth geometry. -/
theorem fork_geometry :
    AdmittedPostBirthGeometryV3 h3 ring3 Q := by
  decide +kernel

/-- Sanity: exactly the label-zero cell is the designated leader. -/
theorem fork_leader_fields :
    (raw (Q 0)).leader = true ∧
    (raw (Q 1)).leader = false ∧
    (raw (Q 2)).leader = false := by
  decide +kernel

/-- First service is edge 0 -> 1.  The pair is tokenless closing/closing,
its labels are successor 0,1, so the mixed/passive normalizer installs seek
at the responder. -/
theorem fork_step1_seek :
    (Q1 1).ctl.tok = .seek := by
  decide +kernel



/-- Second service is edge 2 -> 0.  Cell 0 is still tokenless; because its
label is zero, the passive edge test succeeds and installs a second seek.
Cell 1 is remote from this service and retains the first seek. -/
theorem fork_step2_two_seeks :
    (Q2 0).ctl.tok = .seek ∧
    (Q2 1).ctl.tok = .seek := by
  decide +kernel

/-- Full token readback after the two-letter word `[0,2]`. -/
theorem fork_step2_tokens :
    (Q2 0).ctl.tok = .seek ∧
    (Q2 1).ctl.tok = .seek ∧
    (Q2 2).ctl.tok = .none := by
  decide +kernel

/-- Weaker entrance certificate requested by the task fallback.  This is not
claimed to be `BirthEntranceV1`: proving that stronger proposition would need
an explicit `BirthEntranceV31` R1-train preimage for this literal carrier. -/
theorem fork_entrance :
    BirthQuarantineV31 Q ∧
      AdmittedPostBirthGeometryV3 h3 ring3 Q := by
  exact ⟨fork_quarantine, fork_geometry⟩



/-- Two concurrent seeks are not rejected by the current controller shape:
`ControllerShapeV3` constrains sealed/release/scrubL/openR, not seek. -/
theorem fork_step2_controllerShape :
    ControllerShapeV3 ring3 Q2 := by
  decide +kernel

/-- Explicit form of the ledger conclusion: the two-seek state is current-
shape-good, so no existing `ControllerShapeV3` clause forbids the fork. -/
theorem fork_step2_not_excluded :
    (Q2 0).ctl.tok = .seek ∧
    (Q2 1).ctl.tok = .seek ∧
    ControllerShapeV3 ring3 Q2 := by
  exact ⟨fork_step2_two_seeks.1,
    fork_step2_two_seeks.2,
    fork_step2_controllerShape⟩



end R2CoherenceV31SeekFork
