import Leader.Wu.Coherence.RecoveryDrift
import Leader.Wu.Coherence.LabelPreservation

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R2CoherenceV31ProxyComplete

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
open PPLLLeaderCreationCleanupRepair
open WriterProducerRepair
open R2CoherenceV31 R2CoherenceV31Drift
open R2CoherenceV31Closure R2CoherenceV31Closure2

/-- Companion of `R2CoherenceV31PhaseDebt.mainClearV3Dec`; the group form was
never needed before this witness. -/
instance groupMainClearV3Dec {n ψ κ τ : Nat}
    (ring : DirectedRing n) (C : FC n ψ κ τ) (i : Fin n) :
    Decidable (GroupMainClearV3 ring C i) := by
  unfold GroupMainClearV3
  infer_instance

private theorem h3 : 0 < 3 := by decide
private theorem h23 : 2 ≤ 3 := by decide
private def ring3 : DirectedRing 3 := ⟨by decide⟩

/-- Clean physical literal, except that `state` may be chosen non-main-clear.
No equality state is used in the counterexample, so current CHECK/ID coherence
is vacuous. -/
private def literal
    (lab : Fin 3) (state : MainState := .none) : R2.Cell 3 3 48 :=
  let seed := WriterProducerRegression.clean h3 (fun _ => false) lab
  let b := seed.base.core.core
  let b' : BoundedAgentState 3 3 := {
    b with
    leader := false
    shield := false
    gen_ws := false
    label := lab
    state := state
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

private def cell
    (p : R2.Cell 3 3 48)
    (m : R2Coherence.Mark) (t : TokenV3) : Cell 3 3 48 :=
  ⟨p, ⟨m, t⟩⟩

/-- Proxy-good forged commit.

Labels are 0,1,2 around the 3-cycle, so admitted geometry holds even with no
leaders.  Cell 1 carries remote main dirt (`compare1`).  The only live token is
a `.commit` at the label-zero responder.  Since current ControllerShapeV3 has
no commit clause, the state is shape-good. -/
private def commitProxy : FC 3 3 3 48 := fun i =>
  match i.val with
  | 0 => cell (literal 0) .open .commit
  | 1 => cell (literal 1 .compare1) .open .none
  | _ => cell (literal 2) .open .none

/-- Edge 2 -> 0 services the forged commit. -/
private def commitAfter : FC 3 3 3 48 :=
  stepV3 h3 h23 ring3 commitProxy 2

/-- This is not exploiting malformed label/election geometry. -/
theorem commitProxy_geometry :
    AdmittedPostBirthGeometryV3 h3 ring3 commitProxy := by
  decide +kernel

/-- Current shape is accepted because `.commit` is unconstrained. -/
theorem commitProxy_shape :
    ControllerShapeV3 ring3 commitProxy := by
  decide +kernel

/-- No cell is `.equal`; current CHECK/ID coherence is therefore vacuous. -/
theorem commitProxy_coherent :
    CoherentPrefixesV3 ring3 commitProxy := by
  decide +kernel

/-- Hence this state satisfies exactly the executable proxy. -/
theorem commitProxy_proxy :
    RecoveryProxyV3 ring3 commitProxy := by
  exact ⟨commitProxy_shape, commitProxy_coherent⟩

/-- Dispatcher identification: the wrap edge 2 -> 0 takes the commit branch. -/
theorem commitProxy_branch :
    branchAtV3 h3 h23
      (commitProxy 2) (commitProxy (ring3.rightNeighbor 2)) = .commit := by
  decide +kernel

/-- The service seals the label-zero responder. -/
theorem commitAfter_root_sealed :
    (commitAfter 0).ctl.mark = .sealed := by
  decide +kernel

/-- The remote label-one cell is untouched and still not main-clear. -/
theorem commitAfter_remote_dirty :
    ¬ MainClearV3 (commitAfter 1) := by
  decide +kernel

/-- Therefore the new sealed owner's 3-cell group is not main-clear. -/
theorem commitAfter_root_group_not_clear :
    ¬ GroupMainClearV3 ring3 commitAfter 0 := by
  decide +kernel

/-- Decisive failure: one legal V3.1 commit service leaves ControllerShapeV3. -/
theorem commitAfter_not_shape :
    ¬ ControllerShapeV3 ring3 commitAfter := by
  decide +kernel

/-- The exact one-step induction lemma needed by proxy completeness is false,
already on the commit branch. -/
theorem commit_shape_preservation_false :
    ¬ (∀ (C : FC 3 3 3 48) (e : Fin 3),
        AdmittedPostBirthGeometryV3 h3 ring3 C →
        ControllerShapeV3 ring3 C →
        CoherentPrefixesV3 ring3 C →
        branchAtV3 h3 h23 (C e) (C (ring3.rightNeighbor e)) = .commit →
        ControllerShapeV3 ring3 (stepV3 h3 h23 ring3 C e)) := by
  intro h
  exact commitAfter_not_shape
    (h commitProxy 2 commitProxy_geometry commitProxy_shape
      commitProxy_coherent commitProxy_branch)

/-- The one-letter word `[2]` witnesses failure of future controller soundness. -/
theorem commitProxy_not_sound :
    ¬ ControllerSoundV3 h3 h23 ring3 commitProxy := by
  intro hSound
  apply commitAfter_not_shape
  simpa [commitAfter] using hSound [2]

/-- Thus the proxy-good admitted state is not RecoveredV3. -/
theorem commitProxy_not_recovered :
    ¬ RecoveredV3 h3 h23 ring3 commitProxy := by
  intro h
  exact commitProxy_not_sound h.2.2

/-- Verdict: the proxy-completeness bridge itself is false. -/
theorem recoveryProxyCompleteV31_false :
    ¬ RecoveryProxyCompleteV31 (κ := 3) (τ := 48) h3 h23 ring3 := by
  intro hBridge
  have hRecovered :=
    hBridge commitProxy commitProxy_geometry commitProxy_proxy
  exact commitProxy_not_recovered hRecovered

end R2CoherenceV31ProxyComplete
