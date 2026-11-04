import Leader.Wu.Coherence.ReopenController

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV2LeafCounterexamples

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open R2Coherence R2CoherenceBranches R2CoherenceV2

private theorem h3 : 0 < 3 := by decide
private theorem h23 : 2 ≤ 3 := by decide
private def ring3 : DirectedRing 3 := ⟨by decide⟩
private def ring4 : DirectedRing 4 := ⟨by decide⟩

private abbrev WCfg3 := R2Coherence.FC 3 3 3 48
private abbrev WCfg4 := R2Coherence.FC 4 3 3 48

/-- Small literal whose unmentioned bounded fields are neutral. -/
private def literal (lab : Fin 3)
    (leader : Bool := false)
    (state : MainState := .none)
    (path : BoundedPathInfo 3 := .bot)
    (bit : Bool := false) : R2.Cell 3 3 48 :=
  let seed := WriterProducerRegression.clean h3 (fun _ => false) lab
  let b := seed.base.core.core
  let b' : BoundedAgentState 3 3 :=
    { b with
      leader := leader
      shield := leader
      gen_ws := false
      label := lab
      state := state
      path := path
      bit := bit
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
      b_carry := false }
  ⟨⟨⟨b', false⟩, 48⟩, 0⟩

private def openCell (p : R2.Cell 3 3 48) : Cell 3 3 48 :=
  ⟨p, ⟨.open, .none⟩⟩

private def reopenCell (p : R2.Cell 3 3 48) : Cell 3 3 48 :=
  ⟨p, ⟨.releasing, .reopen⟩⟩

/-! ### False OPEN-NO-HAZARD leaf

The live equal frontier is label 2 with a completely fresh 0/1/2 prefix.
Serving 0→1 executes the existing ELIMINATE cleanup at label 1.  It erases
that middle `path`, but changes neither resident bit nor resident label, so V2
classifies and installs the proposal as `.openNoHazard`.  The remote label-2
frontier remains `.equal`, now with a missing prefix component. -/

private def openPathEraseInput : WCfg3 := fun i =>
  match i.val with
  | 0 => openCell (literal 0 (path := .some 0 0))
  | 1 => openCell
      (literal 1 (state := .eliminate_signal) (path := .some 1 0))
  | _ => openCell (literal 2 (state := .equal) (path := .some 2 0))

private def openPathEraseAfter : WCfg3 :=
  stepV2 h3 h23 ring3 openPathEraseInput 0

/-- Field-level closed source image. -/
theorem openPathErase_input_fields :
    (raw (openPathEraseInput 0)).path = .some 0 0 ∧
    (raw (openPathEraseInput 1)).state = .eliminate_signal ∧
    (raw (openPathEraseInput 1)).path = .some 1 0 ∧
    (raw (openPathEraseInput 2)).state = .equal ∧
    (raw (openPathEraseInput 2)).path = .some 2 0 := by
  decide +kernel

theorem openPathErase_geometry :
    AdmittedPostBirthGeometry h3 ring3 openPathEraseInput := by
  decide +kernel

theorem openPathErase_before_coherent :
    CoherentPrefixes ring3 openPathEraseInput := by
  decide +kernel

theorem openPathErase_branch :
    branchAtV2 h3 h23 ring3 openPathEraseInput 0 = .openNoHazard := by
  decide +kernel

/-- The mutation which `pairHazard` does not see. -/
theorem openPathErase_after_fields :
    (raw (openPathEraseAfter 1)).path = .bot ∧
    (raw (openPathEraseAfter 2)).state = .equal ∧
    (raw (openPathEraseAfter 2)).path = .some 2 0 ∧
    (∀ i : Fin 3, (openPathEraseAfter i).ctl = ⟨.open, .none⟩) := by
  decide +kernel

theorem openPathErase_after_not_coherent :
    ¬ CoherentPrefixes ring3 openPathEraseAfter := by
  decide +kernel

theorem openNoHazardPreservationV2_false :
    ¬ OpenNoHazardPreservationObligationV2
      (κ := 3) (τ := 48) h3 h23 ring3 := by
  intro h
  exact openPathErase_after_not_coherent
    (h openPathEraseInput 0 openPathErase_geometry
      openPathErase_before_coherent openPathErase_branch)

/-! ### False REOPEN leaf

Physical positions have labels `[0,0,1,2]`; position 1 is a leader.  Geometry
therefore legitimately resets at edge 0→1.  Position 0 carries a stale equal
payload.  Before the service, the `.reopen` token at position 1 is a valid
`PrefixDead` witness for position 0.  `ReopenSuffixClear` at edge 0 checks the
leader-root suffix positions 1,2,3 only, all of which are MainClear.  The V2
gate therefore passes.  Since the responder itself is label zero,
`reopenStage` opens/clears only the responder and leaves position 0 unchanged.
That consumes the last non-open witness and exposes the stale equality. -/

private def reopenBoundaryInput : WCfg4 := fun i =>
  match i.val with
  | 0 => openCell
      (literal 0 (state := .equal) (path := .some 0 1) (bit := false))
  | 1 => reopenCell (literal 0 (leader := true))
  | 2 => openCell (literal 1)
  | _ => openCell (literal 2)

private def reopenBoundaryAfter : WCfg4 :=
  stepV2 h3 h23 ring4 reopenBoundaryInput 0

theorem reopenBoundary_input_fields :
    (raw (reopenBoundaryInput 0)).state = .equal ∧
    (raw (reopenBoundaryInput 0)).path = .some 0 1 ∧
    (raw (reopenBoundaryInput 0)).bit = false ∧
    (raw (reopenBoundaryInput 1)).leader = true ∧
    (raw (reopenBoundaryInput 1)).label = (0 : Fin 3) ∧
    (reopenBoundaryInput 1).ctl = ⟨.releasing, .reopen⟩ := by
  decide +kernel

theorem reopenBoundary_geometry :
    AdmittedPostBirthGeometry h3 ring4 reopenBoundaryInput := by
  decide +kernel

theorem reopenBoundary_before_coherent :
    CoherentPrefixes ring4 reopenBoundaryInput := by
  decide +kernel

/-- This is the decisive point: the present V2 certificate accepts the cut. -/
theorem reopenBoundary_suffix_clear :
    ReopenSuffixClear ring4 reopenBoundaryInput 0 := by
  decide +kernel

theorem reopenBoundary_branch :
    branchAtV2 h3 h23 ring4 reopenBoundaryInput 0 = .reopen := by
  decide +kernel

theorem reopenBoundary_after_fields :
    (raw (reopenBoundaryAfter 0)).state = .equal ∧
    (raw (reopenBoundaryAfter 0)).path = .some 0 1 ∧
    (raw (reopenBoundaryAfter 0)).bit = false ∧
    (reopenBoundaryAfter 0).ctl = ⟨.open, .none⟩ ∧
    (reopenBoundaryAfter 1).ctl = ⟨.open, .none⟩ := by
  decide +kernel

theorem reopenBoundary_after_not_coherent :
    ¬ CoherentPrefixes ring4 reopenBoundaryAfter := by
  decide +kernel

theorem reopenPreservationV2_false :
    ¬ ReopenPreservationObligationV2
      (κ := 3) (τ := 48) h3 h23 ring4 := by
  intro h
  exact reopenBoundary_after_not_coherent
    (h reopenBoundaryInput 0 reopenBoundary_geometry
      reopenBoundary_before_coherent reopenBoundary_branch)

end R2CoherenceV2LeafCounterexamples
