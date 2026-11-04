import Leader.Wu.Coherence.ReopenController

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV3DesignRegression

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open R2Coherence R2CoherenceBranches R2CoherenceV2

private theorem h3 : 0 < 3 := by decide
private theorem h23 : 2 ≤ 3 := by decide
private def ring3 : DirectedRing 3 := ⟨by decide⟩
private def ring4 : DirectedRing 4 := ⟨by decide⟩
private def ring5 : DirectedRing 5 := ⟨by decide⟩
private def ring6 : DirectedRing 6 := ⟨by decide⟩

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

/-- Existing `.reopen` is only a finite-state proxy for candidate `openR`. -/
private def openRProxy (p : R2.Cell 3 3 48) : Cell 3 3 48 :=
  ⟨p, ⟨.releasing, .reopen⟩⟩

/-- Candidate V3 final OPEN-R service, isolated from all global certificates. -/
private def finishOpenRStage
    (l r : Cell 3 3 48) : Cell 3 3 48 × Cell 3 3 48 :=
  if l.ctl.tok = .reopen then
    if successorB l r then
      if atTerminalB r then
        (setControl (clearMain l) .open .none,
         setControl (clearMain r) .open .none)
      else (l, r)
    else (l, r)
  else (l, r)

private def finishOpenRStep {n : Nat}
    (ring : DirectedRing n) (C : FC n 3 3 48) (e : Fin n) :
    FC n 3 3 48 :=
  pairUpdate ring C e
    (finishOpenRStage (C e) (C (ring.rightNeighbor e)))

private def staleRoot (leader : Bool) : Cell 3 3 48 :=
  openCell (literal 0 leader .equal (.some 0 1) false)

private def finishOwner : Cell 3 3 48 :=
  openRProxy (literal 1)

private def terminal : Cell 3 3 48 :=
  openCell (literal 2)

private def bad3 : FC 3 3 3 48 := fun i =>
  match i.val with
  | 0 => staleRoot false
  | 1 => finishOwner
  | _ => terminal

private def bad4 : FC 4 3 3 48 := fun i =>
  match i.val with
  | 0 => staleRoot true
  | 1 => finishOwner
  | 2 => terminal
  | _ => openCell (literal 0)

private def bad5 : FC 5 3 3 48 := fun i =>
  match i.val with
  | 0 => staleRoot true
  | 1 => finishOwner
  | 2 => terminal
  | 3 => openCell (literal 0)
  | _ => openCell (literal 1)

private def bad6 : FC 6 3 3 48 := fun i =>
  match i.val with
  | 0 => staleRoot true
  | 1 => finishOwner
  | 2 => terminal
  | 3 => openCell (literal 0)
  | 4 => openCell (literal 1)
  | _ => openCell (literal 2)

/-- n=3: smallest forged-completion attack. -/
theorem bad3_before :
    AdmittedPostBirthGeometry h3 ring3 bad3 ∧
      CoherentPrefixes ring3 bad3 := by
  decide +kernel

theorem bad3_after :
    ¬ CoherentPrefixes ring3 (finishOpenRStep ring3 bad3 1) := by
  decide +kernel

/-- n=4,5,6: the same radius-one cut embeds with follower/leader resets. -/
theorem bad4_before :
    AdmittedPostBirthGeometry h3 ring4 bad4 ∧
      CoherentPrefixes ring4 bad4 := by
  decide +kernel

theorem bad4_after :
    ¬ CoherentPrefixes ring4 (finishOpenRStep ring4 bad4 1) := by
  decide +kernel

theorem bad5_before :
    AdmittedPostBirthGeometry h3 ring5 bad5 ∧
      CoherentPrefixes ring5 bad5 := by
  decide +kernel

theorem bad5_after :
    ¬ CoherentPrefixes ring5 (finishOpenRStep ring5 bad5 1) := by
  decide +kernel

theorem bad6_before :
    AdmittedPostBirthGeometry h3 ring6 bad6 ∧
      CoherentPrefixes ring6 bad6 := by
  decide +kernel

theorem bad6_after :
    ¬ CoherentPrefixes ring6 (finishOpenRStep ring6 bad6 1) := by
  decide +kernel

/-- Closed check that the path-erasure pair is a local V3 hazard. -/
private def pathEraseCfg : FC 3 3 3 48 := fun i =>
  match i.val with
  | 0 => openCell (literal 0 false .none (.some 0 0))
  | 1 => openCell
      (literal 1 false .eliminate_signal (.some 1 0))
  | _ => openCell (literal 2 false .equal (.some 2 0))

private def pathChangedV3 (old out : R2.Cell 3 3 48) : Bool :=
  decide (old.base.core.core.path ≠ out.base.core.core.path)

private def pairPathChangesV3
    (l r ql qr : R2.Cell 3 3 48) : Bool :=
  pathChangedV3 l ql || pathChangedV3 r qr

theorem q13390_path_erasure_is_local_hazard :
    let q := proposalV2 h3 (by decide : 0 < 2) h23
      (pathEraseCfg 0) (pathEraseCfg 1)
    pairPathChangesV3
      (pathEraseCfg 0).phys (pathEraseCfg 1).phys q.1 q.2 = true := by
  decide +kernel

#print axioms bad3_before
#print axioms bad3_after
#print axioms bad4_after
#print axioms bad5_after
#print axioms bad6_after
#print axioms q13390_path_erasure_is_local_hazard

end R2CoherenceV3DesignRegression
-- END PART 1
