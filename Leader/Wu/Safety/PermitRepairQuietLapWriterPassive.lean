import Leader.Wu.Safety.PermitRepairQuietLapSignalEscape
import Leader.Wu.WriteSeq.StationaryWritePersistent

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace R1CandidatePrime

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
open PPLLWriteIncrementGate PPLLWriteSeqPersistenceRepair
open BirthSigMoveDisposalRepair BirthShortDoneCuts BirthStationaryWrite
open PPLLNoCheckBirthConditionTwoGeometry
open R1CandidateKernel

variable {n psi kappa tau : Nat}

/-! ## 1. The unmodified witness already leaves CandR1 -/

/-- One R1 interaction on edge zero of the original compiled witness. -/
def departAfter : FC 9 3 3 48 :=
  BirthCheckPermitRepairLeaf.step1 (by decide : 0 < 3)
    (by decide : 2 ≤ 3) witnessRing witness (0 : Fin 9)

/-- Evaluate only the one returned writer field needed by the counterexample. -/
theorem departAfter_one :
    (raw (departAfter (1 : Fin 9))).write_state = .depart := by
  decide +kernel

private theorem candidate_write_state_none
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (hC : CandR1 hpsi h2 ring C) (i : Fin n) :
    (raw (C i)).write_state = .none := by
  obtain ⟨root, hA⟩ := hC
  exact (hA.2.2.2.1 i).2.1.2.1

-- As in R1CandidateNotClosed: compute first, then keep the fixture/row opaque.
attribute [local irreducible]
  R1CandidateKernel.witness
  BirthCheckPermitRepairLeaf.step1 BirthCheckPermitRepair.row

theorem departAfter_not_candidate :
    ¬ CandR1 (by decide : 0 < 3) (by decide : 2 ≤ 3)
      witnessRing departAfter := by
  intro hC
  have hz := candidate_write_state_none (by decide) (by decide)
    witnessRing departAfter hC (1 : Fin 9)
  have hbad : WriteState.none = WriteState.depart :=
    hz.symm.trans departAfter_one
  cases hbad

/-- The simpler non-closure witness: no signal_ws mutation is needed. -/
theorem depart_not_closed :
    ∃ (C : FC 9 3 3 48) (e : Fin 9),
      CandR1 (by decide : 0 < 3) (by decide : 2 ≤ 3)
          witnessRing C ∧
      ¬ CandR1 (by decide : 0 < 3) (by decide : 2 ≤ 3)
          witnessRing
          (BirthCheckPermitRepairLeaf.step1 (by decide) (by decide)
            witnessRing C e) := by
  refine ⟨witness, (0 : Fin 9), witness_mem, ?_⟩
  change ¬ CandR1 (by decide : 0 < 3) (by decide : 2 ≤ 3)
    witnessRing departAfter
  exact departAfter_not_candidate

/-! ## 2. Prime candidate -/

/-- Boundary writer class which admits the source-sanctioned pathless depart. -/
def WriterPassive (u : AgentState psi) : Prop :=
  u.path3 = none ∧
  u.write = .none ∧
  (u.write_state = .none ∨ u.write_state = .depart)

/-- Only WriterDormant is weakened. -/
def LocalQuiet' (hpsi : 0 < psi)
    (u : ExpiringAgentState psi kappa tau) : Prop :=
  AuthQuiet u.core.erase ∧
  WriterPassive (raw u) ∧
  pendingTerminalDisposal hpsi (raw u) = false ∧
  deletionActive (prepared hpsi u) = false

/-- Literal cut tests retained, writer tests widened. -/
def EdgeSafe' (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : ExpiringAgentState psi kappa tau) : Prop :=
  PreparedRuler hpsi l r ∧
  AuthQuiet (checkInput hpsi h2 l r).1 ∧
  AuthQuiet (checkInput hpsi h2 l r).2 ∧
  (checkOutput hpsi h2 l r).1.core.state ≠ .equal ∧
  WriterPassive (writerInput hpsi h2 l r).1.core ∧
  WriterPassive (writerInput hpsi h2 l r).2.core ∧
  ((checkedSuffix hpsi h2 l r).1.core.bit =
      (writerInput hpsi h2 l r).1.core.bit ∧
    (checkedSuffix hpsi h2 l r).2.core.bit =
      (writerInput hpsi h2 l r).2.core.bit) ∧
  (let q := BirthCheckPermitRepair.expiring
      hpsi (by decide : 0 < 2) h2 l r
   AuthQuiet q.1.core.erase ∧ AuthQuiet q.2.core.erase)

/-- The simple prime gate is intentionally restricted to psi >= 3. -/
def CandR1At' (hpsi : 0 < psi) (h2 : 2 ≤ psi) (_h3 : 2 < psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (root : Fin n) : Prop :=
  RootedLap hpsi ring C root ∧
  K2PeacefulFinite ring C ∧
  PositivePeak ring C root ∧
  (∀ i : Fin n, LocalQuiet' hpsi (C i)) ∧
  (∀ e : Fin n, EdgeSafe' hpsi h2 (C e) (C (ring.rightNeighbor e)))

def CandR1' (hpsi : 0 < psi) (h2 : 2 ≤ psi) (h3 : 2 < psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau) : Prop :=
  ∃ root : Fin n, CandR1At' hpsi h2 h3 ring C root

instance candR1AtPrimeDecidable
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (h3 : 2 < psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau) (root : Fin n) :
    Decidable (CandR1At' hpsi h2 h3 ring C root) := by
  unfold CandR1At' RootedLap K2PeacefulFinite SupportFinite PositivePeak
    LocalQuiet' EdgeSafe' PreparedRuler AuthQuiet RawQuiet WriterPassive
  infer_instance

instance candR1PrimeDecidable
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (h3 : 2 < psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau) :
    Decidable (CandR1' hpsi h2 h3 ring C) := by
  unfold CandR1'
  infer_instance

def candR1PrimeB
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (h3 : 2 < psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau) : Bool :=
  decide (CandR1' hpsi h2 h3 ring C)

@[simp] theorem candR1PrimeB_iff
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (h3 : 2 < psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau) :
    candR1PrimeB hpsi h2 h3 ring C = true ↔
      CandR1' hpsi h2 h3 ring C := by
  simp only [candR1PrimeB, decide_eq_true_eq]

private theorem writerPassive_of_writerDormant
    {u : AgentState psi} (h : WriterDormant u) : WriterPassive u :=
  ⟨h.1, h.2.2.1, Or.inl h.2.1⟩

private theorem localQuiet_prime_of_localQuiet
    (hpsi : 0 < psi) (u : ExpiringAgentState psi kappa tau)
    (h : LocalQuiet hpsi u) : LocalQuiet' hpsi u :=
  ⟨h.1, writerPassive_of_writerDormant h.2.1, h.2.2.1, h.2.2.2⟩

private theorem edgeSafe_prime_of_edgeSafe
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (l r : ExpiringAgentState psi kappa tau)
    (h : EdgeSafe hpsi h2 l r) : EdgeSafe' hpsi h2 l r := by
  rcases h with ⟨hR, hI1, hI2, hNE, hW1, hW2, hB, hQ⟩
  exact ⟨hR, hI1, hI2, hNE,
    writerPassive_of_writerDormant hW1,
    writerPassive_of_writerDormant hW2, hB, hQ⟩

private theorem candR1At_prime_of_candR1At
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (h3 : 2 < psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau) (root : Fin n)
    (h : CandR1At hpsi h2 ring C root) :
    CandR1At' hpsi h2 h3 ring C root := by
  rcases h with ⟨hG, hK, hP, hL, hE⟩
  exact ⟨hG, hK, hP,
    fun i => localQuiet_prime_of_localQuiet hpsi (C i) (hL i),
    fun e => edgeSafe_prime_of_edgeSafe hpsi h2 _ _ (hE e)⟩

/-- The old candidate is a subset of the prime candidate whenever 2 < psi. -/
theorem candR1_prime_of_candR1
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (h3 : 2 < psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (h : CandR1 hpsi h2 ring C) : CandR1' hpsi h2 h3 ring C := by
  rcases h with ⟨root, hA⟩
  exact ⟨root, candR1At_prime_of_candR1At hpsi h2 h3 ring C root hA⟩

/-- Nonvacuity is inherited from the accepted psi=3 witness. -/
theorem witness_mem' :
    CandR1' (by decide : 0 < 3) (by decide : 2 ≤ 3)
      (by decide : 2 < 3) witnessRing witness :=
  candR1_prime_of_candR1 (by decide) (by decide) (by decide)
    witnessRing witness witness_mem

/-! ## 3a. The two central stationary-writer entrance cases -/

private def WriterIdle (u : AgentState psi) : Prop :=
  u.path3 = none ∧ u.write = .none ∧ u.write_state = .none

private theorem writerPassive_of_idle
    {u : AgentState psi} (h : WriterIdle u) : WriterPassive u :=
  ⟨h.1, h.2.1, Or.inl h.2.2⟩

private theorem clearIncrementAction_eq_of_none
    (u : AgentState psi) (h : u.write = .none) :
    clearIncrementAction u = u := by
  simp [clearIncrementAction, h]

/-- GROUP_INFO changes only last/last_set/last_unset among writer controls. -/
private theorem groupInfo_prime_frame
    (hpsi : 0 < psi) (l r : AgentState psi) :
    let q := groupInfo hpsi l r
    q.1.leader = l.leader ∧
    q.1.label = l.label ∧
    q.1.path3 = l.path3 ∧
    q.1.write = l.write ∧
    q.2.label = r.label ∧
    q.2.path3 = r.path3 ∧
    q.2.write = r.write := by
  rw [groupInfo_eq_staged]
  unfold groupInfoStaged groupInfoStart groupInfoSet groupInfoUnset
  dsimp only
  repeat (first
    | exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    | split)

/-- A pathless commandless pair is normalized to idle by transport preparation. -/
private theorem prepareTransport_idle_of_empty
    (hpsi : 0 < psi) (l r : AgentState psi)
    (hl3 : l.path3 = none) (hlw : l.write = .none)
    (hr3 : r.path3 = none) (hrw : r.write = .none) :
    let q := writeSeqPrepareTransport hpsi l r
    WriterIdle q.1 ∧ WriterIdle q.2 := by
  simp [writeSeqPrepareTransport, writeSeqReadyTransport,
    writeSeqSetWriteReadyTransport, writeSeqCompare, writeSeqCommands,
    writeSeqSetWriteAct, writeSeqFinalR, WriterIdle,
    hl3, hlw, hr3, hrw]

/-- A follower initiator cannot enter Algorithm 18 generation. -/
private theorem swThroughPrepare_follower_idle
    (hpsi : 0 < psi) (l r : AgentState psi)
    (hleader : l.leader = false)
    (hl : WriterPassive l) (hr : WriterPassive r) :
    let q := swPersistentThroughPrepare hpsi l r
    WriterIdle q.1 ∧ WriterIdle q.2 := by
  unfold swPersistentThroughPrepare clearInputIncrementPair
  rw [clearIncrementAction_eq_of_none l hl.2.1,
    clearIncrementAction_eq_of_none r hr.2.1]
  let g := groupInfo hpsi l r
  have hg := groupInfo_prime_frame hpsi l r
  dsimp only at hg
  rcases hg with ⟨hgl, _, hgl3, hglw, _, hgr3, hgrw⟩
  have hgleader : g.1.leader = false := hgl.trans hleader
  have hgen : writeSeqGenerate hpsi g.1 g.2 = g := by
    simp [writeSeqGenerate, hgleader]
  change
    WriterIdle
        (writeSeqPrepareTransport hpsi
          (writeSeqGenerate hpsi g.1 g.2).1
          (writeSeqGenerate hpsi g.1 g.2).2).1 ∧
      WriterIdle
        (writeSeqPrepareTransport hpsi
          (writeSeqGenerate hpsi g.1 g.2).1
          (writeSeqGenerate hpsi g.1 g.2).2).2
  rw [hgen]
  exact prepareTransport_idle_of_empty hpsi g.1 g.2
    (hgl3.trans hl.1) (hglw.trans hl.2.1)
    (hgr3.trans hr.1) (hgrw.trans hr.2.1)

/-- At psi >= 3, generation from the label-zero leader into label one cannot
emit the terminal path3 payload. -/
private theorem writeSeqGenerate_root_nonterminal_empty
    (hpsi : 0 < psi) (h3 : 2 < psi)
    (l r : AgentState psi)
    (hleader : l.leader = true)
    (hllabel : l.label = ⟨0, hpsi⟩)
    (hrval : r.label.val = 1)
    (hl3 : l.path3 = none) (hlw : l.write = .none)
    (hr3 : r.path3 = none) (hrw : r.write = .none) :
    let q := writeSeqGenerate hpsi l r
    q.1.path3 = none ∧ q.1.write = .none ∧
      q.2.path3 = none ∧ q.2.write = .none := by
  have hrzero : r.label ≠ ⟨0, hpsi⟩ := by
    intro h
    have hv := congrArg Fin.val h
    simp only at hv
    omega
  have hrterm : r.label ≠ ⟨psi - 1, by omega⟩ := by
    intro h
    have hv := congrArg Fin.val h
    simp only at hv
    omega
  have hlterm : l.label ≠ ⟨psi - 1, by omega⟩ := by
    intro h
    have h0 := congrArg Fin.val hllabel
    have ht := congrArg Fin.val h
    simp only at h0 ht
    omega
  unfold writeSeqGenerate
  by_cases hgen : l.leader = true ∧ l.gen_ws = true
  · rw [if_pos hgen, gensigWriteseq_eq_staged]
    simp [gensigWriteseqStaged, gensigWriteseqStart,
      gensigWriteseqEmit, gensigWriteseqPropagate,
      gensigWriteseqFinish, hllabel, hgen.2, hl3,
      hrzero, hr3, hrterm, hlterm, hlw, hrw]
  · rw [if_neg hgen]
    exact ⟨hl3, hlw, hr3, hrw⟩

/-- Root-outgoing Algorithm-18/prepare case. The caller supplies the physical
root and successor labels; the ring bridge is proved below. -/
private theorem swThroughPrepare_root_outgoing_idle
    (hpsi : 0 < psi) (h3 : 2 < psi)
    (l r : AgentState psi)
    (hleader : l.leader = true)
    (hllabel : l.label = ⟨0, hpsi⟩)
    (hrval : r.label.val = 1)
    (hl : WriterPassive l) (hr : WriterPassive r) :
    let q := swPersistentThroughPrepare hpsi l r
    WriterIdle q.1 ∧ WriterIdle q.2 := by
  unfold swPersistentThroughPrepare clearInputIncrementPair
  rw [clearIncrementAction_eq_of_none l hl.2.1,
    clearIncrementAction_eq_of_none r hr.2.1]
  let g := groupInfo hpsi l r
  have hg := groupInfo_prime_frame hpsi l r
  dsimp only at hg
  rcases hg with ⟨hgl, hgll, hgl3, hglw, hgrl, hgr3, hgrw⟩
  have hgleader : g.1.leader = true := hgl.trans hleader
  have hgllabel : g.1.label = ⟨0, hpsi⟩ := hgll.trans hllabel
  have hgrval : g.2.label.val = 1 :=
    (congrArg Fin.val hgrl).trans hrval
  let a := writeSeqGenerate hpsi g.1 g.2
  have ha := writeSeqGenerate_root_nonterminal_empty
    hpsi h3 g.1 g.2 hgleader hgllabel hgrval
    (hgl3.trans hl.1) (hglw.trans hl.2.1)
    (hgr3.trans hr.1) (hgrw.trans hr.2.1)
  dsimp only at ha
  rcases ha with ⟨ha13, ha1w, ha23, ha2w⟩
  change
    WriterIdle (writeSeqPrepareTransport hpsi a.1 a.2).1 ∧
      WriterIdle (writeSeqPrepareTransport hpsi a.1 a.2).2
  exact prepareTransport_idle_of_empty hpsi a.1 a.2
    ha13 ha1w ha23 ha2w

/-! ## 3b. Algorithm 19/20 suffix and stationary writer cases -/

private theorem gatePreparedIncrement_eq_of_idle
    (u : AgentState psi) (h : WriterIdle u) :
    gatePreparedIncrement u = u := by
  simp [gatePreparedIncrement, h.2.1]

/-- Algorithm 19 can turn an idle responder into pathless depart, but creates
no payload or command from an idle pair. -/
private theorem writeAction_idle_passive
    (hpsi : 0 < psi) (l r : AgentState psi)
    (hl : WriterIdle l) (hr : WriterIdle r) :
    let q := writeActionPreservingComparison hpsi l r
    WriterPassive q.1 ∧ WriterPassive q.2 := by
  rcases hl with ⟨hl3, hlw, hls⟩
  rcases hr with ⟨hr3, hrw, hrs⟩
  unfold writeActionPreservingComparison
  have hla : writeActionActivateNonempty hpsi l = l := by
    simp [writeActionActivateNonempty, hlw]
  have hra : writeActionActivateNonempty hpsi r = r := by
    simp [writeActionActivateNonempty, hrw]
  rw [hla, hra]
  unfold writeActionExecutePreservingComparison
  have hne : r.write_state ≠ .equal := by
    rw [hrs]
    decide
  rw [if_neg hne]
  unfold writeActionExecutePreservingDepart
  by_cases hstep : l.label < r.label ∨ r.label = ⟨0, hpsi⟩
  · rw [if_pos hstep]
    simp [hrs, WriterPassive, hl3, hlw, hls, hr3, hrw]
  · rw [if_neg hstep]
    exact ⟨⟨hl3, hlw, Or.inl hls⟩,
      ⟨hr3, hrw, Or.inl hrs⟩⟩

private theorem moveWsigStart_passive
    (l r : AgentState psi)
    (hl : WriterPassive l) (hr : WriterPassive r) :
    let q := moveWsigStart l r
    WriterPassive q.1 ∧ WriterPassive q.2 := by
  unfold moveWsigStart
  by_cases hleader : r.leader = true
  · rw [if_pos hleader]
    simp [moveWsigCheckGenWs, hl.1, WriterPassive,
      hr.1, hr.2.1, hr.2.2]
  · rw [if_neg hleader]
    exact ⟨hl, hr⟩

private theorem moveWsigCheckLast_eq_of_passive
    (u : AgentState psi) (h : WriterPassive u) :
    moveWsigCheckLast u = u := by
  simp [moveWsigCheckLast, h.1]

private theorem moveWsigTransferStopAligned_eq_of_passive
    (l r : AgentState psi) (hl : WriterPassive l) :
    moveWsigTransferStopAligned l r = (l, r) := by
  simp [moveWsigTransferStopAligned, hl.1]

private theorem moveWsigMoveWrite_eq_of_passive
    (l r : AgentState psi) (hl : WriterPassive l) :
    moveWsigMoveWritePreservingNonempty l r = (l, r) := by
  simp [moveWsigMoveWritePreservingNonempty, hl.2.1]

private theorem moveWsigLeaderSignal_passive
    (l r : AgentState psi)
    (hl : WriterPassive l) (hr : WriterPassive r) :
    let q := moveWsigLeaderSignal l r
    WriterPassive q.1 ∧ WriterPassive q.2 := by
  unfold moveWsigLeaderSignal
  by_cases h : r.leader = true
  · rw [if_pos h]
    exact ⟨by simpa [WriterPassive] using hl, hr⟩
  · rw [if_neg h]
    exact ⟨hl, hr⟩

private theorem moveWsigSignalMove_passive
    (l r : AgentState psi)
    (hl : WriterPassive l) (hr : WriterPassive r) :
    let q := moveWsigSignalMove l r
    WriterPassive q.1 ∧ WriterPassive q.2 := by
  unfold moveWsigSignalMove
  by_cases hs : r.signal_ws = true
  · rw [if_pos hs]
    by_cases hleader : l.leader = true
    · rw [if_pos hleader]
      exact ⟨by simpa [WriterPassive] using hl,
        by simpa [WriterPassive] using hr⟩
    · rw [if_neg hleader]
      exact ⟨by simpa [WriterPassive] using hl,
        by simpa [WriterPassive] using hr⟩
  · rw [if_neg hs]
    exact ⟨hl, hr⟩

private theorem moveWsigEchoMove_passive
    (l r : AgentState psi)
    (hl : WriterPassive l) (hr : WriterPassive r) :
    let q := moveWsigEchoMove l r
    WriterPassive q.1 ∧ WriterPassive q.2 := by
  unfold moveWsigEchoMove
  by_cases he : r.ws_echo = true
  · rw [if_pos he]
    by_cases hleader : l.leader = true
    · rw [if_pos hleader]
      exact ⟨hl, by simpa [WriterPassive] using hr⟩
    · rw [if_neg hleader]
      exact ⟨by simpa [WriterPassive] using hl,
        by simpa [WriterPassive] using hr⟩
  · rw [if_neg he]
    exact ⟨hl, hr⟩

/-- With no payload/command, Algorithm 20 only moves the ignored control bits. -/
private theorem moveWsigStopAligned_passive
    (hpsi : 0 < psi) (l r : AgentState psi)
    (hl : WriterPassive l) (hr : WriterPassive r) :
    let q := moveWsigStopAligned hpsi l r
    WriterPassive q.1 ∧ WriterPassive q.2 := by
  let q0 := moveWsigStart l r
  have h0 : WriterPassive q0.1 ∧ WriterPassive q0.2 :=
    moveWsigStart_passive l r hl hr
  let l1 := moveWsigCheckLast q0.1
  have hl1 : l1 = q0.1 :=
    moveWsigCheckLast_eq_of_passive q0.1 h0.1
  let q1 := moveWsigTransferStopAligned l1 q0.2
  have h1 : WriterPassive q1.1 ∧ WriterPassive q1.2 := by
    dsimp only [q1]
    rw [hl1, moveWsigTransferStopAligned_eq_of_passive q0.1 q0.2 h0.1]
    exact h0
  let q2 := moveWsigMoveWritePreservingNonempty q1.1 q1.2
  have h2 : WriterPassive q2.1 ∧ WriterPassive q2.2 := by
    dsimp only [q2]
    rw [moveWsigMoveWrite_eq_of_passive q1.1 q1.2 h1.1]
    exact h1
  let q3 := moveWsigLeaderSignal q2.1 q2.2
  have h3p : WriterPassive q3.1 ∧ WriterPassive q3.2 :=
    moveWsigLeaderSignal_passive q2.1 q2.2 h2.1 h2.2
  let q4 := moveWsigSignalMove q3.1 q3.2
  have h4 : WriterPassive q4.1 ∧ WriterPassive q4.2 :=
    moveWsigSignalMove_passive q3.1 q3.2 h3p.1 h3p.2
  let q5 := moveWsigEchoMove q4.1 q4.2
  have h5 : WriterPassive q5.1 ∧ WriterPassive q5.2 :=
    moveWsigEchoMove_passive q4.1 q4.2 h4.1 h4.2
  change WriterPassive q5.1 ∧ WriterPassive q5.2
  exact h5

private theorem writerSuffix_idle_passive
    (hpsi : 0 < psi) (l r : AgentState psi)
    (hl : WriterIdle l) (hr : WriterIdle r) :
    let q := writeSeqAfterPrepareComparisonTransport hpsi l r
    WriterPassive q.1 ∧ WriterPassive q.2 := by
  let x := writeActionPreservingComparison hpsi l r
  have hx : WriterPassive x.1 ∧ WriterPassive x.2 :=
    writeAction_idle_passive hpsi l r hl hr
  let m := moveWsigStopAligned hpsi x.1 x.2
  have hm : WriterPassive m.1 ∧ WriterPassive m.2 :=
    moveWsigStopAligned_passive hpsi x.1 x.2 hx.1 hx.2
  change WriterPassive m.1 ∧ WriterPassive m.2
  exact hm

/-- The complete stationary writer is passive when its initiator is a follower. -/
theorem stationary_follower_writerPassive
    (hpsi : 0 < psi) (l r : AgentState psi)
    (hleader : l.leader = false)
    (hl : WriterPassive l) (hr : WriterPassive r) :
    let q := stationaryPersistentRaw hpsi l r
    WriterPassive q.1 ∧ WriterPassive q.2 := by
  let p := swPersistentThroughPrepare hpsi l r
  have hp : WriterIdle p.1 ∧ WriterIdle p.2 :=
    swThroughPrepare_follower_idle hpsi l r hleader hl hr
  let gl := gatePreparedIncrement p.1
  let gr := gatePreparedIncrement p.2
  have hgl : gl = p.1 := gatePreparedIncrement_eq_of_idle p.1 hp.1
  have hgr : gr = p.2 := gatePreparedIncrement_eq_of_idle p.2 hp.2
  have hs := writerSuffix_idle_passive hpsi gl gr
    (by rw [hgl]; exact hp.1) (by rw [hgr]; exact hp.2)
  change WriterPassive
      (writeSeqAfterPrepareComparisonTransport hpsi gl gr).1 ∧
    WriterPassive (writeSeqAfterPrepareComparisonTransport hpsi gl gr).2
  exact hs

/-- The complete stationary writer is passive on a psi>=3 root-outgoing pair. -/
theorem stationary_root_outgoing_writerPassive
    (hpsi : 0 < psi) (h3 : 2 < psi)
    (l r : AgentState psi)
    (hleader : l.leader = true)
    (hllabel : l.label = ⟨0, hpsi⟩)
    (hrval : r.label.val = 1)
    (hl : WriterPassive l) (hr : WriterPassive r) :
    let q := stationaryPersistentRaw hpsi l r
    WriterPassive q.1 ∧ WriterPassive q.2 := by
  let p := swPersistentThroughPrepare hpsi l r
  have hp : WriterIdle p.1 ∧ WriterIdle p.2 :=
    swThroughPrepare_root_outgoing_idle
      hpsi h3 l r hleader hllabel hrval hl hr
  let gl := gatePreparedIncrement p.1
  let gr := gatePreparedIncrement p.2
  have hgl : gl = p.1 := gatePreparedIncrement_eq_of_idle p.1 hp.1
  have hgr : gr = p.2 := gatePreparedIncrement_eq_of_idle p.2 hp.2
  have hs := writerSuffix_idle_passive hpsi gl gr
    (by rw [hgl]; exact hp.1) (by rw [hgr]; exact hp.2)
  change WriterPassive
      (writeSeqAfterPrepareComparisonTransport hpsi gl gr).1 ∧
    WriterPassive (writeSeqAfterPrepareComparisonTransport hpsi gl gr).2
  exact hs

private theorem stationaryAuthorized_writerPassive
    (hpsi : 0 < psi) (l r : PPLLAuthorizedComparisonRepair.AuthorizedAgentState psi)
    (h : let q := stationaryPersistentRaw hpsi l.core r.core
      WriterPassive q.1 ∧ WriterPassive q.2) :
    let q := stationaryPersistentAuthorizedRow hpsi l r
    WriterPassive q.1.core ∧ WriterPassive q.2.core := by
  dsimp only at h ⊢
  have hc := stationaryPersistentAuthorizedRow_core hpsi l r
  have hl := congrArg (fun z : AgentState psi × AgentState psi => z.1) hc
  have hr := congrArg (fun z : AgentState psi × AgentState psi => z.2) hc
  dsimp only at hl hr
  rw [hl, hr]
  exact h

/-! ## 3c. Exact remaining R1-host seam -/

/-- Pre-writer field transport still needed from the actual R1 metadata prefix.
It is deliberately separate from the proved stationary writer cases. -/
def WriterInputFrameObligation
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) : Prop :=
  ∀ (l r : ExpiringAgentState psi kappa tau),
    LocalQuiet' hpsi l → LocalQuiet' hpsi r →
    let w := writerInput hpsi h2 l r
    WriterPassive w.1.core ∧
    WriterPassive w.2.core ∧
    w.1.core.leader = (raw l).leader ∧
    w.1.core.label = (raw l).label ∧
    w.2.core.label = (raw r).label

/-- Post-writer transport through mark/reification/expiry/normalization/K2.
The premise is the actual stationary writer at the literal writerInput cut. -/
def WriterOuterFrameObligation
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) : Prop :=
  ∀ (l r : ExpiringAgentState psi kappa tau),
    LocalQuiet' hpsi l → LocalQuiet' hpsi r →
    let w := writerInput hpsi h2 l r
    let z := stationaryPersistentAuthorizedRow hpsi w.1 w.2
    WriterPassive z.1.core → WriterPassive z.2.core →
    let q := BirthCheckPermitRepair.row
      hpsi (by decide : 0 < 2) h2 l r
    WriterPassive (raw q.1) ∧ WriterPassive (raw q.2)

/-- This is the named remaining proof obligation for an unconditional R1 row
writer lemma. It is a Prop argument, not an axiom or theorem. -/
def R1WriterPassiveHostObligation
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) : Prop :=
  WriterInputFrameObligation (kappa := kappa) (tau := tau) hpsi h2 ∧
  WriterOuterFrameObligation (kappa := kappa) (tau := tau) hpsi h2

/-- Actual R1 row, follower-initiator case, conditional only on the named
surrounding-host frame obligation. -/
theorem r1Row_follower_writerPassive_of_host
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (hHost : R1WriterPassiveHostObligation
      (kappa := kappa) (tau := tau) hpsi h2)
    (l r : ExpiringAgentState psi kappa tau)
    (hlq : LocalQuiet' hpsi l) (hrq : LocalQuiet' hpsi r)
    (hleader : (raw l).leader = false) :
    let q := BirthCheckPermitRepair.row
      hpsi (by decide : 0 < 2) h2 l r
    WriterPassive (raw q.1) ∧ WriterPassive (raw q.2) := by
  rcases hHost with ⟨hin, hout⟩
  let w := writerInput hpsi h2 l r
  have hw := hin l r hlq hrq
  change WriterPassive w.1.core ∧ WriterPassive w.2.core ∧
    w.1.core.leader = (raw l).leader ∧
    w.1.core.label = (raw l).label ∧
    w.2.core.label = (raw r).label at hw
  rcases hw with ⟨hwl, hwr, hwlead, _, _⟩
  have hlead : w.1.core.leader = false := hwlead.trans hleader
  have hraw := stationary_follower_writerPassive
    hpsi w.1.core w.2.core hlead hwl hwr
  have hz := stationaryAuthorized_writerPassive hpsi w.1 w.2 hraw
  exact hout l r hlq hrq hz.1 hz.2

/-- Actual R1 row, root-outgoing case, conditional on the same host seam. -/
theorem r1Row_root_outgoing_writerPassive_of_host
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (h3 : 2 < psi)
    (hHost : R1WriterPassiveHostObligation
      (kappa := kappa) (tau := tau) hpsi h2)
    (l r : ExpiringAgentState psi kappa tau)
    (hlq : LocalQuiet' hpsi l) (hrq : LocalQuiet' hpsi r)
    (hleader : (raw l).leader = true)
    (hllabel : (raw l).label = ⟨0, hpsi⟩)
    (hrval : (raw r).label.val = 1) :
    let q := BirthCheckPermitRepair.row
      hpsi (by decide : 0 < 2) h2 l r
    WriterPassive (raw q.1) ∧ WriterPassive (raw q.2) := by
  rcases hHost with ⟨hin, hout⟩
  let w := writerInput hpsi h2 l r
  have hw := hin l r hlq hrq
  change WriterPassive w.1.core ∧ WriterPassive w.2.core ∧
    w.1.core.leader = (raw l).leader ∧
    w.1.core.label = (raw l).label ∧
    w.2.core.label = (raw r).label at hw
  rcases hw with ⟨hwl, hwr, hwlead, hwllabel, hwrlabel⟩
  have hlead : w.1.core.leader = true := hwlead.trans hleader
  have hlabel : w.1.core.label = ⟨0, hpsi⟩ := hwllabel.trans hllabel
  have hrval' : w.2.core.label.val = 1 :=
    (congrArg Fin.val hwrlabel).trans hrval
  have hraw := stationary_root_outgoing_writerPassive
    hpsi h3 w.1.core w.2.core hlead hlabel hrval' hwl hwr
  have hz := stationaryAuthorized_writerPassive hpsi w.1 w.2 hraw
  exact hout l r hlq hrq hz.1 hz.2

private theorem rootedLap_follower_of_ne
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (C : FC n psi kappa tau) (root e : Fin n)
    (hG : RootedLap hpsi ring C root) (he : e ≠ root) :
    (raw (C e)).leader = false := by
  change (C e).core.core.leader = false
  cases h : (C e).core.core.leader with
  | false => rfl
  | true => exact (he (hG.2.1 e h)).elim

/-- RootedLap determines label one at the distinct clockwise successor.
The extra 1<n premise is necessary: DirectedRing itself assumes only 0<n. -/
private theorem rootedLap_right_label_one
    (hpsi : 0 < psi) (h3 : 2 < psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau) (root : Fin n)
    (hn : 1 < n) (hG : RootedLap hpsi ring C root) :
    (raw (C (ring.rightNeighbor root))).label.val = 1 := by
  have h := hG.2.2.2.1 (⟨1, hn⟩ : Fin n)
  have hs : cwPos ring root 1 = ring.rightNeighbor root := by
    simpa using (cwPos_succ ring root 0)
  rw [hs] at h
  have hv := congrArg Fin.val h
  change (C (ring.rightNeighbor root)).core.core.label.val = 1
  simpa [Nat.mod_eq_of_lt (by omega : 1 < psi)] using hv

/-- Configuration-level follower case requested by the gate analysis. -/
theorem r1Row_follower_case_of_host
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (root e : Fin n)
    (hHost : R1WriterPassiveHostObligation
      (kappa := kappa) (tau := tau) hpsi h2)
    (hG : RootedLap hpsi ring C root) (he : e ≠ root)
    (hlq : LocalQuiet' hpsi (C e))
    (hrq : LocalQuiet' hpsi (C (ring.rightNeighbor e))) :
    let q := BirthCheckPermitRepair.row hpsi (by decide : 0 < 2) h2
      (C e) (C (ring.rightNeighbor e))
    WriterPassive (raw q.1) ∧ WriterPassive (raw q.2) :=
  r1Row_follower_writerPassive_of_host hpsi h2 hHost
    (C e) (C (ring.rightNeighbor e)) hlq hrq
    (rootedLap_follower_of_ne hpsi ring C root e hG he)

/-- Configuration-level root-outgoing case requested by the gate analysis. -/
theorem r1Row_root_outgoing_case_of_host
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (h3 : 2 < psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau) (root : Fin n)
    (hn : 1 < n)
    (hHost : R1WriterPassiveHostObligation
      (kappa := kappa) (tau := tau) hpsi h2)
    (hG : RootedLap hpsi ring C root)
    (hlq : LocalQuiet' hpsi (C root))
    (hrq : LocalQuiet' hpsi (C (ring.rightNeighbor root))) :
    let q := BirthCheckPermitRepair.row hpsi (by decide : 0 < 2) h2
      (C root) (C (ring.rightNeighbor root))
    WriterPassive (raw q.1) ∧ WriterPassive (raw q.2) := by
  have hleader : (raw (C root)).leader = true := by
    change (C root).core.core.leader = true
    exact hG.1
  have hlabel : (raw (C root)).label = ⟨0, hpsi⟩ := by
    change (C root).core.core.label = ⟨0, hpsi⟩
    exact hG.2.2.1
  exact r1Row_root_outgoing_writerPassive_of_host
    hpsi h2 h3 hHost (C root) (C (ring.rightNeighbor root))
    hlq hrq hleader hlabel
    (rootedLap_right_label_one hpsi h3 ring C root hn hG)

/-- With the named host seam supplied, the two proved writer cases exhaust
all initiators in a rooted lap. -/
theorem r1Row_writerPassive_of_host
    (hpsi : 0 < psi) (h2 : 2 ≤ psi) (h3 : 2 < psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau) (root e : Fin n)
    (hn : 1 < n)
    (hHost : R1WriterPassiveHostObligation
      (kappa := kappa) (tau := tau) hpsi h2)
    (hG : RootedLap hpsi ring C root)
    (hlq : LocalQuiet' hpsi (C e))
    (hrq : LocalQuiet' hpsi (C (ring.rightNeighbor e))) :
    let q := BirthCheckPermitRepair.row hpsi (by decide : 0 < 2) h2
      (C e) (C (ring.rightNeighbor e))
    WriterPassive (raw q.1) ∧ WriterPassive (raw q.2) := by
  by_cases he : e = root
  · subst e
    exact r1Row_root_outgoing_case_of_host
      hpsi h2 h3 ring C root hn hHost hG hlq hrq
  · exact r1Row_follower_case_of_host
      hpsi h2 ring C root e hHost hG he hlq hrq

/- PLAN
psi2_passive_counterexample_statement:
At psi = 2, take a label-zero leader with gen_ws = true and passive writer
fields, and its idle label-one successor. Algorithm 18 reaches the terminal
label immediately, emits a real path3 and flips the responder bit. Therefore
WriterPassive is not closed at psi = 2. The repository already contains the
small stationary-writer witness shape in
BirthStationaryWrite.SwExamples.swPersistentGeneration, but this file does
not import or promote it to a new theorem.

Remaining proof work for an unconditional one-row result is exactly
R1WriterPassiveHostObligation: establish the symmetric writer-field frame from
LocalQuiet' to writerInput, then frame WriterPassive through markLeaderBirth,
bounded reification, deletionPriorityExpireOne, normalizeLeader, and
finalPhysical. No additional writer-generation case is hidden in that Prop.
-/

end R1CandidatePrime
