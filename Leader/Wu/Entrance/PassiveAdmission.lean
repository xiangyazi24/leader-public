import Leader.Wu.Entrance.Admission
import Leader.Wu.Splice.FullCarrierRows
import Leader.Wu.Safety.PermitRepairZeroIdObstruction


set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096


namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C
namespace FinalCandidateR2C


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open B9Host B9FullCarrierHost
open WriterProducerRepair
open B9FullCarrierRows


variable {n ψ κ τ : Nat}


/-- The frozen executable port, defined locally as requested. -/
noncomputable def concretePortLocal
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) :
    Port (κ := κ) (τ := τ) hψ h2 :=
  B9FullCarrierRows.fullRowPort
    (carrierLaws (ψ := ψ) (κ := κ) (τ := τ))
    (hostR2C (κ := κ) (τ := τ) hψ h2) hψ


/-- The original exact writer-clear frame, reproduced locally because
`FinalB7Admission.lean` deliberately does not export it. -/
def R1B7QuietPairFrame
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) : Prop :=
  ∀ (l r : ExpiringAgentState ψ κ τ),
    l.core.core.leader = false →
    r.core.core.leader = false →
    B9Host.Aligned l r →
    (l.core.core.path3 = none ∧
      l.core.core.write_state = .none ∧ l.core.core.write = .none) →
    (r.core.core.path3 = none ∧
      r.core.core.write_state = .none ∧ r.core.core.write = .none) →
    let q := BirthCheckPermitRepair.row
      hψ (by decide : 0 < 2) h2 l r
    q.1.core.core.leader = false →
    q.2.core.core.leader = false →
    (q.1.core.core.path3 = none ∧
      q.1.core.core.write_state = .none ∧ q.1.core.core.write = .none) ∧
    (q.2.core.core.path3 = none ∧
      q.2.core.core.write_state = .none ∧ q.2.core.core.write = .none) ∧
    q.1.core.core.bit = l.core.core.bit ∧
    q.2.core.core.bit = r.core.core.bit ∧
    q.1.core.core.label = l.core.core.label ∧
    q.2.core.core.label = r.core.core.label


/-- One bare-R1 cell is writer-passive: no payload, no command, and only the
source-sanctioned pathless `.depart` marker may remain. -/
def R1WriterPassiveCell (u : ExpiringAgentState ψ κ τ) : Prop :=
  u.core.core.path3 = none ∧
  u.core.core.write = .none ∧
  (u.core.core.write_state = .none ∨
    u.core.core.write_state = .depart)


/-- Replacement for the too-strong `FinalWriterClear` clause. -/
def FinalWriterPassive (C : Config n ψ κ τ) : Prop :=
  ∀ i : Fin n,
    let u := R2Coherence.raw (C i).phys
    u.path3 = none ∧ u.write = .none ∧
      (u.write_state = .none ∨ u.write_state = .depart)


/-- Concrete B7 admission with exactly the writer clause weakened; all other
admission fields are unchanged. -/
def ConcreteB7AdmittedPassive
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ)
    (ring : DirectedRing n) (C : Config n ψ κ τ) : Prop :=
  FinalNoProducer C ∧ FinalWriterPassive C ∧ FinalAllOpen C ∧
  (∀ e : Fin n,
    ¬ FinalGarbage hψ (C e) (C (ring.rightNeighbor e)) ∧
    (concretePortLocal (κ := κ) (τ := τ) hψ h2).action
        (C e) (C (ring.rightNeighbor e)) = .host ∧
    R2Coherence.ProposalNoWrite hψ (by decide : 0 < 2) h2
      (C e).phys (C (ring.rightNeighbor e)).phys)


/-- Passive version of the physical quiet-pair frame. -/
def R1B7PassivePairFrame
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) : Prop :=
  ∀ (l r : ExpiringAgentState ψ κ τ),
    l.core.core.leader = false →
    r.core.core.leader = false →
    B9Host.Aligned l r →
    R1WriterPassiveCell l →
    R1WriterPassiveCell r →
    let q := BirthCheckPermitRepair.row
      hψ (by decide : 0 < 2) h2 l r
    q.1.core.core.leader = false →
    q.2.core.core.leader = false →
    R1WriterPassiveCell q.1 ∧
    R1WriterPassiveCell q.2 ∧
    q.1.core.core.bit = l.core.core.bit ∧
    q.2.core.core.bit = r.core.core.bit ∧
    q.1.core.core.label = l.core.core.label ∧
    q.2.core.core.label = r.core.core.label


theorem writerPassive_raw_iff
    (u : ExpiringAgentState ψ κ τ) :
    R1ZeroIdClosedObstruction.WriterPassive
        (R1ZeroIdClosedObstruction.raw u) ↔
      R1WriterPassiveCell u := by
  simp only [R1ZeroIdClosedObstruction.WriterPassive,
    R1ZeroIdClosedObstruction.raw, R1WriterPassiveCell,
    AuthorizedBoundedAgentState.erase, BoundedAgentState.erase]
  cases h : u.core.core.path3 <;> simp [h]

theorem r1B7Passive_writer_bits_of_three
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (h3 : 2 < ψ)
    (l r : ExpiringAgentState ψ κ τ)
    (hl : l.core.core.leader = false)
    (hr : r.core.core.leader = false)
    (hlp : R1WriterPassiveCell l)
    (hrp : R1WriterPassiveCell r) :
    let q := BirthCheckPermitRepair.row
      hψ (by decide : 0 < 2) h2 l r
    R1WriterPassiveCell q.1 ∧
    R1WriterPassiveCell q.2 ∧
    q.1.core.core.bit = l.core.core.bit ∧
    q.2.core.core.bit = r.core.core.bit := by
  have hlp' : R1ZeroIdClosedObstruction.WriterPassive
      (R1ZeroIdClosedObstruction.raw l) :=
    (writerPassive_raw_iff l).2 hlp
  have hrp' : R1ZeroIdClosedObstruction.WriterPassive
      (R1ZeroIdClosedObstruction.raw r) :=
    (writerPassive_raw_iff r).2 hrp
  have hnl : R1ZeroIdClosedObstruction.Normalized
      (R1ZeroIdClosedObstruction.raw l) := by
    intro hlead
    change l.core.core.leader = true at hlead
    rw [hl] at hlead
    cases hlead
  have hnr : R1ZeroIdClosedObstruction.Normalized
      (R1ZeroIdClosedObstruction.raw r) := by
    intro hlead
    change r.core.core.leader = true at hlead
    rw [hr] at hlead
    cases hlead
  have hp := R1ZeroIdClosedObstruction.row_passive_normalized
    hψ h3 (by decide : 0 < 2) h2 l r hlp' hrp' hnl hnr
  let q := BirthCheckPermitRepair.row
    hψ (by decide : 0 < 2) h2 l r
  change
    (R1ZeroIdClosedObstruction.WriterPassive
        (R1ZeroIdClosedObstruction.raw q.1) ∧
      R1ZeroIdClosedObstruction.Normalized
        (R1ZeroIdClosedObstruction.raw q.1)) ∧
    (R1ZeroIdClosedObstruction.WriterPassive
        (R1ZeroIdClosedObstruction.raw q.2) ∧
      R1ZeroIdClosedObstruction.Normalized
        (R1ZeroIdClosedObstruction.raw q.2)) ∧
    (R1ZeroIdClosedObstruction.raw q.1).bit =
      (R1ZeroIdClosedObstruction.raw l).bit ∧
    (R1ZeroIdClosedObstruction.raw q.2).bit =
      (R1ZeroIdClosedObstruction.raw r).bit at hp
  change R1WriterPassiveCell q.1 ∧
    R1WriterPassiveCell q.2 ∧
    q.1.core.core.bit = l.core.core.bit ∧
    q.2.core.core.bit = r.core.core.bit
  have hq1 : R1WriterPassiveCell q.1 :=
    (writerPassive_raw_iff q.1).1 hp.1.1
  have hq2 : R1WriterPassiveCell q.2 :=
    (writerPassive_raw_iff q.2).1 hp.2.1.1
  have hb1 : q.1.core.core.bit = l.core.core.bit := by
    change (R1ZeroIdClosedObstruction.raw q.1).bit =
      (R1ZeroIdClosedObstruction.raw l).bit
    exact hp.2.2.1
  have hb2 : q.2.core.core.bit = r.core.core.bit := by
    change (R1ZeroIdClosedObstruction.raw q.2).bit =
      (R1ZeroIdClosedObstruction.raw r).bit
    exact hp.2.2.2
  exact ⟨hq1, hq2, hb1, hb2⟩



theorem r1B7PassivePairFrame_of_spliceLaws_of_three
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (h3 : 2 < ψ)
    (hLaws : B9Host.SpliceLaws
      (B9Host.r1Host (kappa := κ) (tau := τ) hψ h2)) :
    R1B7PassivePairFrame (κ := κ) (τ := τ) hψ h2 := by
  intro l r hl hr hA hlp hrp
  let q := BirthCheckPermitRepair.row
    hψ (by decide : 0 < 2) h2 l r
  change q.1.core.core.leader = false →
    q.2.core.core.leader = false →
    R1WriterPassiveCell q.1 ∧
    R1WriterPassiveCell q.2 ∧
    q.1.core.core.bit = l.core.core.bit ∧
    q.2.core.core.bit = r.core.core.bit ∧
    q.1.core.core.label = l.core.core.label ∧
    q.2.core.core.label = r.core.core.label
  intro hqL hqR

  have hw := r1B7Passive_writer_bits_of_three
    hψ h2 h3 l r hl hr hlp hrp
  change R1WriterPassiveCell q.1 ∧
    R1WriterPassiveCell q.2 ∧
    q.1.core.core.bit = l.core.core.bit ∧
    q.2.core.core.bit = r.core.core.bit at hw

  have hlH : B9Host.leader l = false := hl
  have hrH : B9Host.leader r = false := hr
  have hqLH :
      B9Host.leader
        ((B9Host.r1Host (kappa := κ) (tau := τ) hψ h2).row l r).1 = false := by
    change q.1.core.core.leader = false
    exact hqL
  have hqRH :
      B9Host.leader
        ((B9Host.r1Host (kappa := κ) (tau := τ) hψ h2).row l r).2 = false := by
    change q.2.core.core.leader = false
    exact hqR

  have hleft0 := hLaws.left_follower_label l r hlH
  have hleft : q.1.core.core.label = l.core.core.label := by
    exact hleft0

  have hout0 := hLaws.aligned_followers
    l r hlH hrH hqLH hqRH hA
  have hout : B9Host.Aligned q.1 q.2 := by
    exact hout0

  have hright : q.2.core.core.label = r.core.core.label := by
    apply Fin.ext
    unfold B9Host.Aligned B9Host.label at hA hout
    rw [hleft] at hout
    exact hout.trans hA.symm

  exact ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2,
    hleft, hright⟩



namespace QuietPairCounterexample


theorem hψ3 : 0 < 3 := by decide
theorem h23 : 2 ≤ 3 := by decide


/-- A completely passive follower cell.  We reuse the repository's finite
clean constructor, but turn off the root-only leader/shield/producer source.
The stall budget is positive only to keep zero-budget expiry out of the way. -/
def quietBase (i : Fin 3) : ExpiringAgentState 3 3 48 :=
  let seed := WriterProducerRegression.clean hψ3 (fun _ => false) i
  let b := seed.base.core.core
  let b' : BoundedAgentState 3 3 :=
    { b with leader := false, shield := false, gen_ws := false }
  ⟨⟨b', false⟩, Fin.last 48⟩


def left : ExpiringAgentState 3 3 48 := quietBase 0
def right : ExpiringAgentState 3 3 48 := quietBase 1


def out : ExpiringAgentState 3 3 48 × ExpiringAgentState 3 3 48 :=
  BirthCheckPermitRepair.row hψ3 (by decide : 0 < 2) h23 left right


/-! The five hypotheses of `R1B7QuietPairFrame` all hold literally. -/


theorem quiet_pair_left_follower :
    left.core.core.leader = false := by
  decide +kernel


theorem quiet_pair_right_follower :
    right.core.core.leader = false := by
  decide +kernel


theorem quiet_pair_aligned : B9Host.Aligned left right := by
  unfold B9Host.Aligned B9Host.label
  change right.core.core.label.val =
    (left.core.core.label.val + 1) % 3
  decide +kernel



theorem quiet_pair_left_writer_clear :
    left.core.core.path3 = none ∧
      left.core.core.write_state = .none ∧ left.core.core.write = .none := by
  decide +kernel


theorem quiet_pair_right_writer_clear :
    right.core.core.path3 = none ∧
      right.core.core.write_state = .none ∧ right.core.core.write = .none := by
  decide +kernel


/-- This is the exact primitive branch responsible for the failure: the
aligned `0 -> 1` labels satisfy Algorithm 19's increasing-label guard and the
primitive installs `.depart` on the responder even from an idle writer. -/
theorem quiet_pair_primitive_depart :
    let l := left.core.core.erase
    let r := right.core.core.erase
    l.label < r.label ∧
      (PPLLWriteSeqPersistenceRepair.writeActionExecutePreservingDepart
        hψ3 l r).2.write_state = .depart := by
  decide +kernel


theorem quiet_pair_path3_bits_frame :
    let q := BirthCheckPermitRepair.row
      hψ3 (by decide : 0 < 2) h23 left right
    B6WriterSilence.EmptyWriter q.1.core.erase.core ∧
      B6WriterSilence.EmptyWriter q.2.core.erase.core ∧
      q.1.core.erase.core.bit = left.core.erase.core.bit ∧
      q.2.core.erase.core.bit = right.core.erase.core.bit := by
  have hlf : left.core.erase.core.leader = false := by
    change left.core.core.leader = false
    exact quiet_pair_left_follower
  have hl3 : B6WriterSilence.EmptyWriter left.core.erase.core := by
    unfold B6WriterSilence.EmptyWriter
    simp only [AuthorizedBoundedAgentState.erase, BoundedAgentState.erase]
    rw [quiet_pair_left_writer_clear.1]
    rfl
  have hr3 : B6WriterSilence.EmptyWriter right.core.erase.core := by
    unfold B6WriterSilence.EmptyWriter
    simp only [AuthorizedBoundedAgentState.erase, BoundedAgentState.erase]
    rw [quiet_pair_right_writer_clear.1]
    rfl
  exact B6WriterSilence.row_empty_of_left_follower
    hψ3 (by decide : 0 < 2) h23 left right hlf hl3 hr3




/-- The complete R1 row does not escape through a birth on this witness. -/
theorem quiet_pair_output_leaderless :
    out.1.core.core.leader = false ∧
      out.2.core.core.leader = false := by
  decide +kernel


/-- The offending full-row field.  This is a fact about the complete
`BirthCheckPermitRepair.row`, not only about the Algorithm-19 subroutine. -/
theorem quiet_pair_output_right_depart :
    out.2.core.core.write_state = .depart := by
  decide +kernel


/-- Field-level census of the non-state coordinates requested:
both payloads remain absent, both commands remain absent, and both resident
bits and both individual labels frame exactly. -/
theorem quiet_pair_output_other_frames :
    out.1.core.core.path3 = none ∧
    out.2.core.core.path3 = none ∧
    out.1.core.core.write = .none ∧
    out.2.core.core.write = .none ∧
    out.1.core.core.bit = left.core.core.bit ∧
    out.2.core.core.bit = right.core.core.bit ∧
    out.1.core.core.label = left.core.core.label ∧
    out.2.core.core.label = right.core.core.label := by
  decide +kernel


set_option maxHeartbeats 400000000 in
set_option maxRecDepth 65536 in
theorem r1B7QuietPairFrame_false :
    ¬ R1B7QuietPairFrame (κ := 3) (τ := 48) hψ3 h23 := by
  intro h
  unfold R1B7QuietPairFrame at h
  have hf := h left right
    quiet_pair_left_follower quiet_pair_right_follower
    quiet_pair_aligned
    quiet_pair_left_writer_clear quiet_pair_right_writer_clear
  dsimp only at hf
  have hout := quiet_pair_output_leaderless
  have hc := hf hout.1 hout.2
  have hnone :
      (BirthCheckPermitRepair.row
        hψ3 (by decide : 0 < 2) h23 left right).2.core.core.write_state =
        .none :=
    hc.2.1.2.1
  have hdepart :
      (BirthCheckPermitRepair.row
        hψ3 (by decide : 0 < 2) h23 left right).2.core.core.write_state =
        .depart :=
    quiet_pair_output_right_depart
  have hbad : WriteState.none = WriteState.depart :=
    hnone.symm.trans hdepart
  cases hbad



/-!
STOP AT THE FIRST FALSE STEP.


Consequences for items 2--3:
* `all_host_leaderless_implies_neutral` and
  `fullRowPort_host_neutral_frame` may still be true controller facts, but they
  cannot establish closure of the CURRENT `FinalB7Admitted`, because the HOST
  service above leaves its physical R1 writer outside `FinalWriterClear`.
* Therefore no `FinalB7AdmissionClosedObligation` theorem for the concrete port
  is declared here.


The source-correct repair is to replace the writer-clear boundary class by the
already-used passive class


  path3 = none ∧ write = .none ∧
    (write_state = .none ∨ write_state = .depart)


(or to change the executable R1 row so that a pathless passive `.depart` is
normalized back to `.none` before the admission boundary).  A future closure
proof must use the same repaired predicate consistently in `FinalWriterClear`,
`FinalB7Admitted`, proposal-no-write re-establishment, and the R1 quiet-pair
frame; merely strengthening the concrete B9 port contract cannot fix this
physical counterexample.
-/


end QuietPairCounterexample


end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
end FinalCandidateR2C
