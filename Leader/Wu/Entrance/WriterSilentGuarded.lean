import Leader.Wu.Entrance.WriterSilence
import Leader.Wu.Entrance.Sanitation
import Leader.Wu.Entrance.LocalReverseFill
import Leader.Core.CyclicBitCover

/-!
Guarded writer silence for the actual R1 row.

The empty-prefix branch is unconditional once acquired. The blocked branch
requires an explicit full-row lift. Clearing and physical cover are separate
named obligations; neither is assumed globally by the proved empty branch.
-/

set_option autoImplicit false
set_option Elab.async false

namespace B6WriterSilentGuarded

open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLWriteIncrementGate PPLLWriteSeqPersistenceRepair
  PPLLWallSweepRepair PPLLWallSweepFinite
  PPLLWallSweepPreCheckResetRepair PPLLTerminalEqualSupportRepair
  PPLLCompleteMultiLeaderCleanup PPLLNoCheckBirthConditionTwoPhysical
  BirthGenerationControlRepair BirthGenerationDone
  BirthArrivalCaptureRepair BirthSingleUseReleaseRepair
  BirthTossCheckPreservationRepair BirthCheckCongestGuardRepair
  BirthSigMoveDisposalRepair BirthShortWait
  BirthShortWaitTerminalEntryRepair BirthShortDoneTerminalEntryCut
  BirthShortDoneCuts BirthStationaryWrite
  K2BirthDispatcher K2BirthDispatcherDone K2BirthLeaderNormalize
  ExpiringK2Projection

variable {ψ κ τ width : Nat}

private abbrev BV := Bool × Option Path3Info

private def bv (u : AgentState ψ) : BV := (u.bit, u.path3)

private def ev (u : ExpiringAgentState ψ κ τ) : BV :=
  bv u.core.erase.core

private theorem bv_ite (P : Prop) [Decidable P]
    (u v : AgentState ψ) :
    bv (if P then u else v) = if P then bv u else bv v := by
  split <;> rfl

private theorem clear_bv (u : AgentState ψ) :
    bv (clearIncrementAction u) = bv u := by
  unfold clearIncrementAction
  split <;> rfl

private theorem clear_leader (u : AgentState ψ) :
    (clearIncrementAction u).leader = u.leader := by
  unfold clearIncrementAction
  split <;> rfl

private theorem group_left_bv (hψ : 0 < ψ) (l r : AgentState ψ) :
    bv (groupInfo hψ l r).1 = bv l := by
  unfold groupInfo bv
  dsimp only
  repeat (first | rfl | split)

private theorem group_left_leader (hψ : 0 < ψ) (l r : AgentState ψ) :
    (groupInfo hψ l r).1.leader = l.leader := by
  unfold groupInfo
  dsimp only
  repeat (first | rfl | split)

private theorem ready_bv (u : AgentState ψ) :
    bv (writeSeqSetWriteReadyTransport u) = bv u := by
  unfold writeSeqSetWriteReadyTransport bv
  repeat (first | rfl | split)

private theorem set_act_bv (u : AgentState ψ) :
    bv (writeSeqSetWriteAct u) = bv u := by
  by_cases hlarge : u.write_state = .larger
  · cases hp : u.path3 with
    | none => simp [writeSeqSetWriteAct, hlarge, hp, bv]
    | some p =>
        by_cases hf : p.flag = 1
        · simp [writeSeqSetWriteAct, hlarge, hp, hf, bv]
        · simp [writeSeqSetWriteAct, hlarge, hp, hf, bv]
  · by_cases hless : u.write_state = .less
    · simp [writeSeqSetWriteAct, hlarge, hless, bv]
    · simp [writeSeqSetWriteAct, hlarge, hless, bv]

private theorem prepare_left_bv (hψ : 0 < ψ) (l r : AgentState ψ) :
    bv (writeSeqPrepareTransport hψ l r).1 = bv l := by
  change bv (writeSeqSetWriteAct (writeSeqSetWriteReadyTransport l)) = bv l
  exact (set_act_bv _).trans (ready_bv l)

private theorem through_prepare_left_bv
    (hψ : 0 < ψ) (l r : AgentState ψ) (hl : l.leader = false) :
    bv (swPersistentThroughPrepare hψ l r).1 = bv l := by
  let c := clearInputIncrementPair l r
  let g := groupInfo hψ c.1 c.2
  have hgl : g.1.leader = false :=
    (group_left_leader hψ c.1 c.2).trans ((clear_leader l).trans hl)
  have hg : writeSeqGenerate hψ g.1 g.2 = (g.1, g.2) := by
    simp [writeSeqGenerate, hgl]
  change bv (writeSeqPrepareTransport hψ
    (writeSeqGenerate hψ g.1 g.2).1
    (writeSeqGenerate hψ g.1 g.2).2).1 = bv l
  rw [hg]
  exact (prepare_left_bv hψ g.1 g.2).trans
    ((group_left_bv hψ c.1 c.2).trans (clear_bv l))

private theorem gate_bv (u : AgentState ψ) :
    bv (gatePreparedIncrement u) = bv u := by
  unfold gatePreparedIncrement clearIncrementAction bv
  repeat (first | rfl | split)

private theorem activate_bv (hψ : 0 < ψ) (u : AgentState ψ) :
    bv (writeActionActivateNonempty hψ u) = bv u := by
  unfold writeActionActivateNonempty
  split <;> rfl

private theorem propagate_bv (u : AgentState ψ) (s : WriteState) :
    bv (writeActionPropagateState u s) = bv u := by
  cases s <;> rfl

private theorem execute_left_bv (hψ : 0 < ψ) (l r : AgentState ψ) :
    bv (writeActionExecutePreservingDepart hψ l r).1 = bv l := by
  unfold writeActionExecutePreservingDepart
  split
  · dsimp only
    simp only [bv_ite, propagate_bv, ite_self]
  · rfl

private theorem action_left_bv (hψ : 0 < ψ) (l r : AgentState ψ) :
    bv (writeActionPreservingComparison hψ l r).1 = bv l := by
  let l0 := writeActionActivateNonempty hψ l
  let r0 := writeActionActivateNonempty hψ r
  have h : bv (writeActionExecutePreservingComparison hψ l0 r0).1 =
      bv l0 := by
    unfold writeActionExecutePreservingComparison
    split
    · rfl
    · exact execute_left_bv hψ l0 r0
  exact h.trans (activate_bv hψ l)

private theorem move_write_left_bv (l r : AgentState ψ) :
    bv (moveWsigMoveWritePreservingNonempty l r).1 = bv l := by
  unfold moveWsigMoveWritePreservingNonempty
  split <;> rfl

private theorem leader_signal_left_bv (l r : AgentState ψ) :
    bv (moveWsigLeaderSignal l r).1 = bv l := by
  unfold moveWsigLeaderSignal bv
  dsimp only
  repeat (first | rfl | split)

private theorem signal_left_bv (l r : AgentState ψ) :
    bv (moveWsigSignalMove l r).1 = bv l := by
  unfold moveWsigSignalMove bv
  dsimp only
  repeat (first | rfl | split)

private theorem echo_left_bv (l r : AgentState ψ) :
    bv (moveWsigEchoMove l r).1 = bv l := by
  unfold moveWsigEchoMove bv
  repeat (first | rfl | split)


private theorem finish_left_bv (l r : AgentState ψ) :
    bv (moveWsigFinishPreservingCommand l r).1 = bv l := by
  unfold moveWsigFinishPreservingCommand
  dsimp only
  rw [echo_left_bv, signal_left_bv, leader_signal_left_bv,
    move_write_left_bv]

private theorem move_start_left_bv_empty (l r : AgentState ψ)
    (hl : l.path3 = none) :
    bv (moveWsigStart l r).1 = bv l := by
  unfold moveWsigStart
  split
  · simp [bv, hl]
  · rfl

private theorem move_left_bv_empty (hψ : 0 < ψ) (l r : AgentState ψ)
    (hl : l.path3 = none) :
    bv (moveWsigStopAligned hψ l r).1 = bv l := by
  let s := moveWsigStart l r
  have hs : bv s.1 = bv l := move_start_left_bv_empty l r hl
  have he : s.1.path3 = none := (congrArg Prod.snd hs).trans hl
  have hc : moveWsigCheckLast s.1 = s.1 := by
    simp [moveWsigCheckLast, he]
  have ht : moveWsigTransferStopAligned s.1 s.2 = (s.1, s.2) := by
    simp [moveWsigTransferStopAligned, he]
  change bv (moveWsigFinishPreservingCommand
    (moveWsigTransferStopAligned (moveWsigCheckLast s.1) s.2).1
    (moveWsigTransferStopAligned (moveWsigCheckLast s.1) s.2).2).1 = bv l
  rw [hc, ht]
  exact (finish_left_bv s.1 s.2).trans hs

private theorem stationary_left_bv_empty
    (hψ : 0 < ψ) (l r : AgentState ψ)
    (hl : l.leader = false) (hel : l.path3 = none) :
    bv (stationaryPersistentRaw hψ l r).1 = bv l := by
  have hp := through_prepare_left_bv hψ l r hl
  simp only [stationaryPersistentRaw, writeSeqAfterPrepareComparisonTransport]
  generalize swPersistentThroughPrepare hψ l r = p at hp ⊢
  have hg : bv (gatePreparedIncrement p.1) = bv l :=
    (gate_bv p.1).trans hp
  have ha := action_left_bv hψ
    (gatePreparedIncrement p.1) (gatePreparedIncrement p.2)
  generalize writeActionPreservingComparison hψ
    (gatePreparedIncrement p.1) (gatePreparedIncrement p.2) = a at ha ⊢
  have he : a.1.path3 = none :=
    (congrArg Prod.snd (ha.trans hg)).trans hel
  exact (move_left_bv_empty hψ a.1 a.2 he).trans (ha.trans hg)

section
attribute [local irreducible]
  stationaryPersistentRaw stationaryPersistentAuthorizedRow

/-- No responder hypothesis: this conclusion concerns only the initiator. -/
theorem stationaryPersistentRaw_left_empty
    (hψ : 0 < ψ) (l r : AgentState ψ)
    (hl : l.leader = false) (he : B6WriterSilence.EmptyWriter l) :
    let q := stationaryPersistentRaw hψ l r
    B6WriterSilence.EmptyWriter q.1 ∧ q.1.bit = l.bit := by
  have h := stationary_left_bv_empty hψ l r hl he
  generalize stationaryPersistentRaw hψ l r = out at h ⊢
  have hpath : out.1.path3 = l.path3 := congrArg Prod.snd h
  have hbit : out.1.bit = l.bit := congrArg Prod.fst h
  exact ⟨hpath.trans he, hbit⟩

private theorem stationary_authorized_left_bv
    (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ)
    (hl : l.core.leader = false) (he : l.core.path3 = none) :
    bv (stationaryPersistentAuthorizedRow hψ l r).1.core = bv l.core := by
  have hc := stationaryPersistentAuthorizedRow_core hψ l r
  have hw := stationary_left_bv_empty hψ l.core r.core hl he
  generalize stationaryPersistentRaw hψ l.core r.core = p at hc hw
  generalize stationaryPersistentAuthorizedRow hψ l r = q at hc ⊢
  have hL : q.1.core = p.1 := congrArg Prod.fst hc
  exact (congrArg (fun u : AgentState ψ => bv u) hL).trans hw

theorem stationaryPersistentAuthorizedRow_left_empty
    (hψ : 0 < ψ) (l r : AuthorizedAgentState ψ)
    (hl : l.core.leader = false)
    (he : B6WriterSilence.EmptyWriter l.core) :
    let q := stationaryPersistentAuthorizedRow hψ l r
    B6WriterSilence.EmptyWriter q.1.core ∧ q.1.core.bit = l.core.bit := by
  have h := stationary_authorized_left_bv hψ l r hl he
  generalize stationaryPersistentAuthorizedRow hψ l r = out at h ⊢
  have hpath : out.1.core.path3 = l.core.path3 := congrArg Prod.snd h
  have hbit : out.1.core.bit = l.core.bit := congrArg Prod.fst h
  exact ⟨hpath.trans he, hbit⟩


end




private theorem mark_left_bv (born : Bool)
    (q : AuthorizedAgentState ψ × AuthorizedAgentState ψ) :
    bv (markLeaderBirth born q).1.core = bv q.1.core := by
  unfold markLeaderBirth markComparisonForDeletion bv
  dsimp only
  repeat (first | rfl | split)

private theorem ordinary_writer_eq
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (κ : Nat) (l r : AuthorizedAgentState ψ) :
    BirthCheckPermitRepair.ordinary hψ hw hle κ l r =
      (let p := B6WriterSilence.r1WriterInput hψ hw hle κ l r
       let w := stationaryPersistentAuthorizedRow hψ p.1 p.2
       markLeaderBirth (authBirth l r w) w) := by
  simp only [BirthCheckPermitRepair.ordinary, afterCheckMetadataWidth,
    B6WriterSilence.r1WriterInput]

private theorem ordinary_left_bv_empty
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (κ : Nat) (l r : AuthorizedAgentState ψ)
    (hl : l.core.leader = false) (he : l.core.path3 = none) :
    bv (BirthCheckPermitRepair.ordinary hψ hw hle κ l r).1.core =
      bv l.core := by
  have hp := B6WriterSilence.r1WriterInput_fields hψ hw hle κ l r
  have hlead := B6WriterSilence.r1WriterInput_left_leader hψ hw hle κ l r
  rw [ordinary_writer_eq hψ hw hle κ l r]
  generalize B6WriterSilence.r1WriterInput hψ hw hle κ l r = p
    at hp hlead ⊢
  dsimp only at hp hlead ⊢
  have ep : p.1.core.path3 = none := hp.2.2.1.trans he
  have hv := stationary_authorized_left_bv hψ p.1 p.2
    (hlead.trans hl) ep
  generalize stationaryPersistentAuthorizedRow hψ p.1 p.2 = w at hv ⊢
  have hb : bv p.1.core = bv l.core := Prod.ext hp.1 hp.2.2.1
  exact (mark_left_bv (authBirth l r w) w).trans (hv.trans hb)

private theorem normalize_deletion_view (u : AuthorizedAgentState ψ) :
    ((normalizeDeletion u).core.leader, bv (normalizeDeletion u).core) =
      (u.core.leader, bv u.core) := by
  unfold normalizeDeletion bv
  dsimp only
  repeat (first | rfl | split)

private theorem eliminate_left_bv (hψ : 0 < ψ)
    (l r : AuthorizedAgentState ψ) :
    bv (authorizedEliminateSig hψ l r).1.core = bv l.core := by
  change bv (eliminateSig hψ l.core r.core).1 = bv l.core
  unfold eliminateSig bv
  dsimp only
  repeat (first | rfl | split)

private theorem authorized_left_bv_empty
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (κ : Nat) (l r : AuthorizedAgentState ψ)
    (hl : l.core.leader = false) (he : l.core.path3 = none) :
    bv (BirthCheckPermitRepair.authorized hψ hw hle κ l r).1.core =
      bv l.core := by
  have hf := normalize_deletion_view l
  simp only [BirthCheckPermitRepair.authorized]
  generalize normalizeDeletion l = l0 at hf ⊢
  generalize normalizeDeletion r = r0
  have hb : bv l0.core = bv l.core := congrArg Prod.snd hf
  have hl0 : l0.core.leader = false := (congrArg Prod.fst hf).trans hl
  have he0 : l0.core.path3 = none := (congrArg Prod.snd hb).trans he
  split
  · exact (eliminate_left_bv hψ l0 r0).trans hb
  · split
    · exact hb
    · exact (ordinary_left_bv_empty hψ hw hle κ l0 r0 hl0 he0).trans hb

private theorem bounded_erase
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : AuthorizedBoundedAgentState ψ κ) :
    ((BirthCheckPermitRepair.bounded hψ hw hle l r).1.erase,
      (BirthCheckPermitRepair.bounded hψ hw hle l r).2.erase) =
      BirthCheckPermitRepair.authorized hψ hw hle κ l.erase r.erase := by
  simp only [BirthCheckPermitRepair.bounded,
    AuthorizedBoundedAgentState.erase, BoundedAgentState.erase_ofDomain] <;> rfl

private theorem disposal_view (hψ : 0 < ψ) (u : AuthorizedAgentState ψ) :
    ((prepareDisposal hψ u).core.leader, bv (prepareDisposal hψ u).core) =
      (u.core.leader, bv u.core) := by
  unfold prepareDisposal markComparisonForDeletion bv
  dsimp only
  repeat (first | rfl | split)

private theorem prepared_view (hψ : 0 < ψ) (u : ExpiringAgentState ψ κ τ) :
    ((prepareExpiringDisposal hψ u).core.erase.core.leader,
      ev (prepareExpiringDisposal hψ u)) =
      (u.core.erase.core.leader, ev u) := by
  change ((prepareBoundedDisposal hψ u.core).erase.core.leader,
      bv (prepareBoundedDisposal hψ u.core).erase.core) =
    (u.core.erase.core.leader, bv u.core.erase.core)
  simpa only [erase_prepareBoundedDisposal] using disposal_view hψ u.core.erase

private theorem expiry_ev (old out : ExpiringAgentState ψ κ τ) :
    ev (deletionPriorityExpireOne τ old out) = ev out := by
  unfold deletionPriorityExpireOne pathExpireOne clearComparisonCarrier ev bv
  dsimp only
  repeat (first | rfl | split)

private theorem normalize_ev (hψ : 0 < ψ) (u : ExpiringAgentState ψ κ τ) :
    ev (normalizeLeader hψ u) = ev u := by
  have h := congrArg (fun z : ExpiringAgentState ψ κ τ => ev z)
    (normalizeLeader_field_frame hψ u)
  change ev (normalizeLeader hψ u) = ev u at h
  exact h

private theorem final_left_ev (hψ : 0 < ψ)
    (oldL oldR metaL metaR : ExpiringAgentState ψ κ τ) :
    ev (K2BirthDispatcher.finalPhysical hψ oldL oldR metaL metaR).1 =
      ev metaL := by
  have h := K2BirthDispatcher.finalPhysical_frame hψ oldL oldR metaL metaR
  have hl := congrArg (fun z : ExpiringAgentState ψ κ τ => ev z) h.1
  change ev (K2BirthDispatcher.finalPhysical hψ oldL oldR metaL metaR).1 =
    ev metaL at hl
  exact hl

private theorem expiring_left_bv_empty
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : ExpiringAgentState ψ κ τ)
    (hl : l.core.erase.core.leader = false)
    (he : l.core.erase.core.path3 = none) :
    ev (BirthCheckPermitRepair.expiring hψ hw hle l r).1 = ev l := by
  have hf := prepared_view hψ l
  simp only [BirthCheckPermitRepair.expiring]
  generalize prepareExpiringDisposal hψ l = l0 at hf ⊢
  generalize prepareExpiringDisposal hψ r = r0
  have hprep : ev l0 = ev l := congrArg Prod.snd hf
  have hl0 : l0.core.erase.core.leader = false :=
    (congrArg Prod.fst hf).trans hl
  have he0 : l0.core.erase.core.path3 = none :=
    (congrArg Prod.snd hprep).trans he
  have hc := bounded_erase hψ hw hle l0.core r0.core
  have ha := authorized_left_bv_empty hψ hw hle κ
    l0.core.erase r0.core.erase hl0 he0
  generalize BirthCheckPermitRepair.bounded hψ hw hle l0.core r0.core = q
    at hc ⊢
  have hb : bv q.1.erase.core = bv l0.core.erase.core :=
    (congrArg (fun z : AuthorizedAgentState ψ × AuthorizedAgentState ψ =>
      bv z.1.core) hc).trans ha
  change ev (deletionPriorityExpireOne τ l0
    (⟨q.1, l0.stall⟩ : ExpiringAgentState ψ κ τ)) = ev l
  exact (expiry_ev l0 (⟨q.1, l0.stall⟩ : ExpiringAgentState ψ κ τ)).trans
    (hb.trans hprep)

/-- Full R1, including deletion dispatch and the physical tail.
Only the initiator's bit/path3 are asserted invariant. -/
theorem row_left_empty_of_left_follower
    (hψ : 0 < ψ) (hw : 0 < width) (hle : width ≤ ψ)
    (l r : ExpiringAgentState ψ κ τ)
    (hl : l.core.erase.core.leader = false)
    (he : B6WriterSilence.EmptyWriter l.core.erase.core) :
    let q := BirthCheckPermitRepair.row hψ hw hle l r
    B6WriterSilence.EmptyWriter q.1.core.erase.core ∧
      q.1.core.erase.core.bit = l.core.erase.core.bit := by
  let e := BirthCheckPermitRepair.expiring hψ hw hle l r
  have heq : ev e.1 = ev l := expiring_left_bv_empty hψ hw hle l r hl he
  have hfinal := final_left_ev hψ l r
    (normalizeLeader hψ e.1) (normalizeLeader hψ e.2)
  have h : ev (BirthCheckPermitRepair.row hψ hw hle l r).1 = ev l :=
    hfinal.trans ((normalize_ev hψ e.1).trans heq)
  exact ⟨(congrArg Prod.snd h).trans he, congrArg Prod.fst h⟩

/-- Why the left guard cannot instead be left arbitrarily occupied. -/
theorem transfer_boundary_ingress (l r : AgentState ψ) (p : Path3Info)
    (hl : l.path3 = some p) (hr : r.path3 = none)
    (hs : l.write_state = .depart) (he : r.ws_echo = false) :
    (moveWsigTransferStopAligned l r).2.path3 = some p :=
  B6WriterSilence.transfer_populates_receiver l r p hl hr hs he

-- All subsequent proofs use the public pair/other-cell equations.
attribute [local irreducible]
  BirthCheckPermitRepair.row BirthCheckPermitRepairLeaf.step1

open B6LocalReverseFill BirthCheckPermitRepairLeaf

variable {n : Nat}

abbrev Config (n ψ κ τ : Nat) := B6LocalReverseFill.Config n ψ κ τ

abbrev raw (u : ExpiringAgentState ψ κ τ) : AgentState ψ :=
  B6Sanitation.rawCell u

abbrev pos (ring : DirectedRing n) (I : Interval ring) (k : Nat) : Fin n :=
  BirthCheckChainR1Ring.cell ring I.first k

def GuardShape (ring : DirectedRing n) (I : Interval ring) : Prop :=
  2 ≤ I.size ∧ I.size < n

/-- Offset zero is empty too; only the final offset is unrestricted. -/
def PrefixEmpty (ring : DirectedRing n) (I : Interval ring)
    (C : Config n ψ κ τ) : Prop :=
  ∀ k : Nat, k + 1 < I.size →
    B6WriterSilence.EmptyWriter (raw (C (pos ring I k)))

def PrefixBitsAgree (ring : DirectedRing n) (I : Interval ring)
    (C D : Config n ψ κ τ) : Prop :=
  ∀ k : Nat, k + 1 < I.size →
    (raw (D (pos ring I k))).bit = (raw (C (pos ring I k))).bit

/-- The protected region J is exactly offsets 1,...,I.size-2. -/
def ProtectedBitsAgree (ring : DirectedRing n) (I : Interval ring)
    (C D : Config n ψ κ τ) : Prop :=
  ∀ k : Nat, 1 ≤ k → k + 1 < I.size →
    (raw (D (pos ring I k))).bit = (raw (C (pos ring I k))).bit

def BlockedAll (ring : DirectedRing n) (I : Interval ring)
    (C : Config n ψ κ τ) : Prop :=
  ∀ k : Nat, k < I.size →
    B6WriterSilence.BlockedCell (raw (C (pos ring I k)))

/-- Explicit, unproduced full-R1 obligation for retaining the blocked branch.
The existing stationaryPersistentAuthorizedRow_blocked is NOT this lift.
No output-follower fact is inferred merely from input follower status. -/
def BlockedFullRowLift (ψ κ τ : Nat) : Prop :=
  ∀ (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : ExpiringAgentState ψ κ τ),
    B6WriterSilence.BlockedWriter (raw l) (raw r) →
    let q := BirthCheckPermitRepair.row hψ (by decide : 0 < 2) h2 l r
    (raw q.1).leader = false → (raw q.2).leader = false →
    B6WriterSilence.BlockedWriter (raw q.1) (raw q.2) ∧
      (raw q.1).bit = (raw l).bit ∧ (raw q.2).bit = (raw r).bit

/-- The blocked branch is admitted only together with its full-row proof. -/
def WriterSilent' (ring : DirectedRing n) (I : Interval ring)
    (C : Config n ψ κ τ) : Prop :=
  GuardShape ring I ∧
    (PrefixEmpty ring I C ∨
      (BlockedFullRowLift ψ κ τ ∧ BlockedAll ring I C))

theorem writerSilent'_of_prefixEmpty
    (ring : DirectedRing n) (I : Interval ring) (C : Config n ψ κ τ)
    (hI : GuardShape ring I) (hC : PrefixEmpty ring I C) :
    WriterSilent' ring I C := ⟨hI, Or.inl hC⟩

theorem writerSilent'_of_old_empty
    (ring : DirectedRing n) (I : Interval ring) (C : Config n ψ κ τ)
    (hI : GuardShape ring I) (hC : B6Sanitation.EmptyWriter ring I C) :
    WriterSilent' ring I C := by
  apply writerSilent'_of_prefixEmpty ring I C hI
  intro k hk
  exact hC (pos ring I k) (support_cell I (by omega))

theorem writerSilent'_of_old_blocked
    (ring : DirectedRing n) (I : Interval ring) (C : Config n ψ κ τ)
    (hI : GuardShape ring I) (hLift : BlockedFullRowLift ψ κ τ)
    (hLL : BirthShortDoneTerminalFirstHit.Leaderless C)
    (hC : B6Sanitation.BlockedWriter ring I C) :
    WriterSilent' ring I C := by
  refine ⟨hI, Or.inr ⟨hLift, ?_⟩⟩
  intro k hk
  rcases hC (pos ring I k) (support_cell I hk) with
    ⟨hp, hs, hw, hlast, hset, hunset⟩
  exact ⟨hLL (pos ring I k), hp, hw, hs, hlast, hset, hunset⟩

private theorem support_iff_pos
    (ring : DirectedRing n) (I : Interval ring) (i : Fin n) :
    support I i = true ↔ ∃ k : Nat, k < I.size ∧ i = pos ring I k := by
  constructor
  · intro h
    change (List.range I.size).any
      (fun k => decide (i = pos ring I k)) = true at h
    obtain ⟨k, hk, he⟩ := List.any_eq_true.mp h
    exact ⟨k, List.mem_range.mp hk, of_decide_eq_true he⟩
  · rintro ⟨k, hk, rfl⟩
    exact support_cell I hk

private theorem right_pos (ring : DirectedRing n) (I : Interval ring)
    (k : Nat) : ring.rightNeighbor (pos ring I k) = pos ring I (k + 1) :=
  BirthCheckChainR1Ring.right_cell ring I.first k

private theorem pos_ne (ring : DirectedRing n) (I : Interval ring)
    {a b : Nat} (ha : a < I.size) (hb : b < I.size) (hne : a ≠ b) :
    pos ring I a ≠ pos ring I b :=
  BirthCheckChainR1Ring.cell_ne ring I.first
    (Nat.lt_of_lt_of_le ha I.fits) (Nat.lt_of_lt_of_le hb I.fits) hne

private theorem right_pos_ne (ring : DirectedRing n) (I : Interval ring)
    {a : Nat} (ha : a + 1 < I.size) :
    ring.rightNeighbor (pos ring I a) ≠ pos ring I a := by
  rw [right_pos]
  exact pos_ne ring I ha (by omega) (by omega)

/-- Properness rules out a wrap edge from the dirty right guard. -/
private theorem internal_offsets
    (ring : DirectedRing n) (I : Interval ring) (hI : GuardShape ring I)
    (e : Fin n) (he : internal I e) :
    ∃ a : Nat, a + 1 < I.size ∧ e = pos ring I a := by
  have hi := (internal_iff I e).mp he
  obtain ⟨a, ha, hea⟩ := (support_iff_pos ring I e).mp hi.1
  obtain ⟨b, hb, heb⟩ :=
    (support_iff_pos ring I (ring.rightNeighbor e)).mp hi.2
  have hproper : I.size < n := hI.2
  have hsucc : pos ring I (a + 1) = pos ring I b := by
    calc
      pos ring I (a + 1) = ring.rightNeighbor (pos ring I a) :=
        (right_pos ring I a).symm
      _ = ring.rightNeighbor e := congrArg ring.rightNeighbor hea.symm
      _ = pos ring I b := heb
  have ha1le : a + 1 ≤ I.size := Nat.succ_le_of_lt ha
  have ha1n : a + 1 < n := Nat.lt_of_le_of_lt ha1le hproper
  have hbn : b < n := Nat.lt_trans hb hproper
  have hab : a + 1 = b := by
    by_cases h : a + 1 = b
    · exact h
    · have hne := BirthCheckChainR1Ring.cell_ne
        ring I.first ha1n hbn h
      exact False.elim (hne hsucc)
  have ha1 : a + 1 < I.size := by
    rw [hab]
    exact hb
  exact ⟨a, ha1, hea⟩


/-- This empty-prefix result even includes a row that creates a first leader. -/
theorem prefixEmpty_internal_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (I : Interval ring) (C : Config n ψ κ τ)
    (hI : GuardShape ring I) (hC : PrefixEmpty ring I C)
    (hLL : BirthShortDoneTerminalFirstHit.Leaderless C)
    (e : Fin n) (he : internal I e) :
    PrefixEmpty ring I (step1 hψ h2 ring C e) ∧
      PrefixBitsAgree ring I C (step1 hψ h2 ring C e) := by
  obtain ⟨a, ha, rfl⟩ := internal_offsets ring I hI e he
  have hL := BirthCheckChainR1Ring.step1_left hψ h2 ring C (pos ring I a)
  have hR := BirthCheckChainR1Ring.step1_right hψ h2 ring C
    (pos ring I a) (right_pos_ne ring I ha)
  rw [right_pos] at hL hR
  have hl := row_left_empty_of_left_follower hψ (by decide : 0 < 2) h2
    (C (pos ring I a)) (C (pos ring I (a + 1)))
    (hLL (pos ring I a)) (hC a ha)
  have hall : ∀ k : Nat, k + 1 < I.size →
      B6WriterSilence.EmptyWriter
        (raw (step1 hψ h2 ring C (pos ring I a) (pos ring I k))) ∧
      (raw (step1 hψ h2 ring C (pos ring I a) (pos ring I k))).bit =
        (raw (C (pos ring I k))).bit := by
    intro k hk
    by_cases hka : k = a
    · subst k
      rw [hL]
      exact hl
    · by_cases hkb : k = a + 1
      · subst k
        rw [hR]
        have hr := B6WriterSilence.row_empty_of_left_follower
          hψ (by decide : 0 < 2) h2
          (C (pos ring I a)) (C (pos ring I (a + 1)))
          (hLL (pos ring I a)) (hC a ha) (hC (a + 1) hk)
        exact ⟨hr.2.1, hr.2.2.2⟩
      · have hkE := pos_ne ring I (by omega : k < I.size)
          (by omega : a < I.size) hka
        have hkR : pos ring I k ≠ ring.rightNeighbor (pos ring I a) := by
          rw [right_pos]
          exact pos_ne ring I (by omega) ha hkb
        rw [BirthCheckPermitRepairLeaf.step1_other
          hψ h2 ring C (pos ring I a) (pos ring I k) hkE hkR]
        exact ⟨hC k hk, rfl⟩
  exact ⟨fun k hk => (hall k hk).1, fun k hk => (hall k hk).2⟩

private theorem blocked_internal_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (I : Interval ring) (C : Config n ψ κ τ)
    (hI : GuardShape ring I) (hLift : BlockedFullRowLift ψ κ τ)
    (hC : BlockedAll ring I C) (e : Fin n) (he : internal I e)
    (hD : BirthShortDoneTerminalFirstHit.Leaderless (step1 hψ h2 ring C e)) :
    BlockedAll ring I (step1 hψ h2 ring C e) ∧
      PrefixBitsAgree ring I C (step1 hψ h2 ring C e) := by
  obtain ⟨a, ha, rfl⟩ := internal_offsets ring I hI e he
  have hL := BirthCheckChainR1Ring.step1_left hψ h2 ring C (pos ring I a)
  have hR := BirthCheckChainR1Ring.step1_right hψ h2 ring C
    (pos ring I a) (right_pos_ne ring I ha)
  rw [right_pos] at hL hR
  have hdl := hD (pos ring I a)
  have hdr := hD (pos ring I (a + 1))
  change (raw (step1 hψ h2 ring C (pos ring I a) (pos ring I a))).leader =
    false at hdl
  change (raw (step1 hψ h2 ring C (pos ring I a)
    (pos ring I (a + 1)))).leader = false at hdr
  rw [hL] at hdl
  rw [hR] at hdr
  have hb := hLift hψ h2
    (C (pos ring I a)) (C (pos ring I (a + 1)))
    ⟨hC a (by omega), hC (a + 1) ha⟩ hdl hdr
  have hall : ∀ k : Nat, k < I.size →
      B6WriterSilence.BlockedCell
        (raw (step1 hψ h2 ring C (pos ring I a) (pos ring I k))) ∧
      (raw (step1 hψ h2 ring C (pos ring I a) (pos ring I k))).bit =
        (raw (C (pos ring I k))).bit := by
    intro k hk
    by_cases hka : k = a
    · subst k
      rw [hL]
      exact ⟨hb.1.1, hb.2.1⟩
    · by_cases hkb : k = a + 1
      · subst k
        rw [hR]
        exact ⟨hb.1.2, hb.2.2⟩
      · have hkE := pos_ne ring I hk (by omega : a < I.size) hka
        have hkR : pos ring I k ≠ ring.rightNeighbor (pos ring I a) := by
          rw [right_pos]
          exact pos_ne ring I hk ha hkb
        rw [BirthCheckPermitRepairLeaf.step1_other
          hψ h2 ring C (pos ring I a) (pos ring I k) hkE hkR]
        exact ⟨hC k hk, rfl⟩
  exact ⟨fun k hk => (hall k hk).1,
    fun k hk => (hall k (by omega)).2⟩

/-- The common step theorem stops before any birth in the blocked branch. -/
theorem writerSilent'_internal_step
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (I : Interval ring) (C : Config n ψ κ τ)
    (hC : WriterSilent' ring I C)
    (hLL : BirthShortDoneTerminalFirstHit.Leaderless C)
    (e : Fin n) (he : internal I e)
    (hD : BirthShortDoneTerminalFirstHit.Leaderless (step1 hψ h2 ring C e)) :
    WriterSilent' ring I (step1 hψ h2 ring C e) ∧
      ProtectedBitsAgree ring I C (step1 hψ h2 ring C e) := by
  rcases hC with ⟨hI, hm⟩
  rcases hm with hp | ⟨hLift, hb⟩
  · have hs := prefixEmpty_internal_step hψ h2 ring I C hI hp hLL e he
    exact ⟨⟨hI, Or.inl hs.1⟩, fun k _ hk => hs.2 k hk⟩
  · have hs := blocked_internal_step hψ h2 ring I C hI hLift hb e he hD
    exact ⟨⟨hI, Or.inr ⟨hLift, hs.1⟩⟩, fun k _ hk => hs.2 k hk⟩

/-- Leaderlessness at the initial state and every subsequent word prefix. -/
def LeaderlessAlong (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    Config n ψ κ τ → List (Fin n) → Prop
  | C, [] => BirthShortDoneTerminalFirstHit.Leaderless C
  | C, e :: w => BirthShortDoneTerminalFirstHit.Leaderless C ∧
      LeaderlessAlong hψ h2 ring (step1 hψ h2 ring C e) w

private theorem leaderlessAlong_start
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (C : Config n ψ κ τ) (w : List (Fin n))
    (h : LeaderlessAlong hψ h2 ring C w) :
    BirthShortDoneTerminalFirstHit.Leaderless C := by
  cases w with
  | nil => exact h
  | cons e w => exact h.1

private theorem leaderlessAlong_append_left
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (u v : List (Fin n)) :
    ∀ C : Config n ψ κ τ,
      LeaderlessAlong hψ h2 ring C (u ++ v) →
      LeaderlessAlong hψ h2 ring C u := by
  induction u with
  | nil =>
      intro C h
      exact leaderlessAlong_start hψ h2 ring C v h
  | cons e u ih =>
      intro C h
      exact ⟨h.1, ih (step1 hψ h2 ring C e) h.2⟩

/-- The complete-record full-ring run; there is no clipped interval dynamics. -/
theorem writerSilent'_internal_word
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (I : Interval ring) (w : List (Fin n)) :
    ∀ C : Config n ψ κ τ,
      InternalWord I w → LeaderlessAlong hψ h2 ring C w →
      WriterSilent' ring I C →
      WriterSilent' ring I (runR hψ h2 ring w C) ∧
        ProtectedBitsAgree ring I C (runR hψ h2 ring w C) := by
  induction w with
  | nil =>
      intro C _ _ hC
      exact ⟨hC, fun _ _ _ => rfl⟩
  | cons e w ih =>
      intro C hInt hAlive hC
      let D := step1 hψ h2 ring C e
      have he : internal I e := hInt e (by simp)
      have ht : InternalWord I w := by
        intro f hf
        exact hInt f (List.mem_cons_of_mem e hf)
      have hD : BirthShortDoneTerminalFirstHit.Leaderless D :=
        leaderlessAlong_start hψ h2 ring D w hAlive.2
      have hs := writerSilent'_internal_step hψ h2 ring I C
        hC hAlive.1 e he hD
      have hh := ih D ht hAlive.2 hs.1
      change WriterSilent' ring I (runR hψ h2 ring w D) ∧
        ProtectedBitsAgree ring I C (runR hψ h2 ring w D)
      exact ⟨hh.1, fun k hk1 hk2 =>
        (hh.2 k hk1 hk2).trans (hs.2 k hk1 hk2)⟩

/-- Explicit certificate for every prefix, hence for later internal stages. -/
theorem writerSilent'_prefix_certificate
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (I : Interval ring) (C : Config n ψ κ τ) (w : List (Fin n))
    (hInt : InternalWord I w) (hAlive : LeaderlessAlong hψ h2 ring C w)
    (hC : WriterSilent' ring I C) :
    ∀ p : List (Fin n), p <+: w →
      WriterSilent' ring I (runR hψ h2 ring p C) ∧
        ProtectedBitsAgree ring I C (runR hψ h2 ring p C) := by
  intro p hp
  have hi := B6LocalReverseFill.internalWord_prefix I hInt hp
  have hl : LeaderlessAlong hψ h2 ring C p := by
    rcases hp with ⟨v, rfl⟩
    exact leaderlessAlong_append_left hψ h2 ring p v C hAlive
  exact writerSilent'_internal_word hψ h2 ring I p C hi hl hC

/-- The forward last-cleanup word; the right guard is never an initiator. -/
def forwardWord (ring : DirectedRing n) (I : Interval ring) : List (Fin n) :=
  (List.range (I.size - 1)).map (pos ring I)

theorem forwardWord_length (ring : DirectedRing n) (I : Interval ring) :
    (forwardWord ring I).length = I.size - 1 := by
  simp [forwardWord]

theorem forwardWord_internal (ring : DirectedRing n) (I : Interval ring) :
    InternalWord I (forwardWord ring I) := by
  intro e he
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp he
  have hk' : k < I.size - 1 := List.mem_range.mp hk
  apply (internal_iff I _).2
  constructor
  · exact support_cell I (by omega)
  · rw [right_pos]
    exact support_cell I (by omega)

/-- Exact raw record of the diagnostic family. -/
def neutralCell (lab : Fin ψ) : AgentState ψ :=
  { leader := false, probe := false, phase := false, bit := false,
    wait := true, state := .none, path := .bot,
    reset := false, carry := false, count := 0, label := lab,
    h_field := false, path2 := none, path3 := some ⟨lab.val, 0, 1⟩,
    path4 := none, path5 := none, p := false, p_carry := false,
    reset_cmd := false, echo := false, signal_B := 0, bullet := 0,
    shield := false, write_state := .equal, write := .none,
    last := true, last_set := false, last_unset := false,
    b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }

/-- Only internal successor edges are required. Exterior fields are untouched. -/
def NeutralClearingStart (hψ : 0 < ψ) (ring : DirectedRing n)
    (I : Interval ring) (C : Config n ψ κ τ) : Prop :=
  (∀ k : Nat, k < I.size →
    raw (C (pos ring I k)) = neutralCell (raw (C (pos ring I k))).label ∧
    (C (pos ring I k)).core.erase.path0Crossed = false ∧
    (C (pos ring I k)).stall.val = τ) ∧
  (∀ k : Nat, k + 1 < I.size →
    (raw (C (pos ring I (k + 1)))).label =
      ⟨((raw (C (pos ring I k))).label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)

/-- NEW physical producer obligation, not a conclusion of empty-preservation.
The conservative caps describe the diagnostic family, not an assertion that
these cap inequalities hold at every large-ring parameter witness. -/
def Q13208ClearingObligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) : Prop :=
  ∀ (I : Interval ring) (C : Config n ψ κ τ),
    GuardShape ring I → I.size ≤ κ → I.size ≤ τ →
    BirthShortDoneTerminalFirstHit.Leaderless C →
    NeutralClearingStart hψ ring I C →
    (∃ p : List (Fin n), p <+: forwardWord ring I ∧
      ¬ BirthShortDoneTerminalFirstHit.Leaderless (runR hψ h2 ring p C)) ∨
    PrefixEmpty ring I (runR hψ h2 ring (forwardWord ring I) C)

/-- Honest schema consumer: physical clearing is a named premise. -/
theorem clearing_prefix_of_obligation
    (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n)
    (hO : Q13208ClearingObligation (κ := κ) (τ := τ) hψ h2 ring)
    (I : Interval ring) (C : Config n ψ κ τ)
    (hI : GuardShape ring I) (hκ : I.size ≤ κ) (hτ : I.size ≤ τ)
    (hLL : BirthShortDoneTerminalFirstHit.Leaderless C)
    (hN : NeutralClearingStart hψ ring I C) :
    ∃ p : List (Fin n), p <+: forwardWord ring I ∧
      (¬ BirthShortDoneTerminalFirstHit.Leaderless (runR hψ h2 ring p C) ∨
       WriterSilent' ring I (runR hψ h2 ring p C)) := by
  rcases hO I C hI hκ hτ hLL hN with ⟨p, hp, hbirth⟩ | hempty
  · exact ⟨p, hp, Or.inl hbirth⟩
  · refine ⟨forwardWord ring I, ⟨[], by simp⟩, Or.inr ?_⟩
    exact writerSilent'_of_prefixEmpty ring I _ hI hempty

/-- Protected-core, workspace, and all-incident-edge budgets. -/
def V (ψ : Nat) : Nat := (4 * ψ + 2) * ψ

def W (ψ : Nat) : Nat := V ψ + 2

def M (ψ : Nat) : Nat := W ψ + 1

def blockCount (ψ : Nat) : Nat := 4 * ψ + 1

theorem geometry_constants (ψ : Nat) :
    V ψ = (4 * ψ + 2) * ψ ∧ W ψ = V ψ + 2 ∧ M ψ = W ψ + 1 :=
  ⟨rfl, rfl, rfl⟩

theorem touchCount_geometry
    (ring : DirectedRing n) (I : Interval ring) (hI : I.size ≤ W ψ) :
    B9OrderedWindowMatcher.touchCount
      (B6WindowLocality.touchOf ring (support I)) ≤ M ψ := by
  exact Nat.le_trans (touchCount_support_le I) (Nat.add_le_add_right hI 1)

/-- More covered blocks than the discarded 2*psi indices. -/
theorem covered_count_surplus (hψ : 0 < ψ)
    (w : B6BitCover.Word (blockCount ψ) ψ) :
    2 * ψ + 1 ≤ B6BitCover.coveredCount w (2 * ψ) := by
  have hm : 2 * ψ < blockCount ψ := by
    unfold blockCount
    omega
  have hcov :
      4 * ψ + 1 ≤
        2 * B6BitCover.coveredCount w (2 * ψ) := by
    simpa only [blockCount] using
      (B6BitCover.covered_count_ge w hψ hm)
  omega


#print axioms B6WriterSilentGuarded.stationaryPersistentRaw_left_empty
#print axioms B6WriterSilentGuarded.stationaryPersistentAuthorizedRow_left_empty
#print axioms B6WriterSilentGuarded.prefixEmpty_internal_step
#print axioms B6WriterSilentGuarded.writerSilent'_internal_step
#print axioms B6WriterSilentGuarded.covered_count_surplus


/-- a is the offset from the start of J to a chosen label-zero origin.
The bit-cover combinatorics itself does not need the ruler hypothesis. -/
def coreWord (ring : DirectedRing n) (I : Interval ring)
    (C : Config n ψ κ τ) (a : Nat) : B6BitCover.Word (blockCount ψ) ψ :=
  fun j k => (raw (C (pos ring I (1 + a + j.val * ψ + k.val)))).bit

/-- NEW remaining finite-selection/physical-index obligation.
It asks for a nonwrapping covered block and places BOTH that block and ALL
radius-2*psi supplier blocks in J, not merely inside the larger workspace.
The future ruler application chooses a < psi with physical label zero. -/
def GuardedCoverObligation (ψ : Nat) : Prop :=
  ∀ (n κ τ : Nat) (ring : DirectedRing n) (I : Interval ring)
    (C : Config n ψ κ τ) (a : Nat),
    0 < ψ → I.size = W ψ → GuardShape ring I → a < ψ →
    ∃ j : Fin (blockCount ψ),
      2 * ψ ≤ j.val ∧
      B6BitCover.Covered (coreWord ring I C a) (2 * ψ) j ∧
      (∀ k : Fin ψ,
        1 ≤ 1 + a + j.val * ψ + k.val ∧
        (1 + a + j.val * ψ + k.val) + 1 < I.size) ∧
      (∀ d : Nat, 1 ≤ d → d ≤ 2 * ψ →
        (B6BitCover.pred d j).val = j.val - d ∧
        ∀ k : Fin ψ,
          1 ≤ 1 + a + (B6BitCover.pred d j).val * ψ + k.val ∧
          (1 + a + (B6BitCover.pred d j).val * ψ + k.val) + 1 < I.size)

end B6WriterSilentGuarded
