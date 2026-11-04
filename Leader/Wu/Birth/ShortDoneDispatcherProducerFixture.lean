import Leader.Wu.Birth.ShortDoneDispatcher
import Leader.Wu.Safety.NoCheckBirthConditionTwoProtocol


namespace BirthShortDoneDispatcherProducerAudit


open PPLL PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLPathStallComparisonRepair PPLLLeaderCreationCleanupRepair
  PPLLNoCheckBirthConditionTwoPhysical PPLLNoCheckBirthConditionTwoProtocol
  BirthGenerationControlRepair BirthShortWait BirthShortDoneCuts
  BirthShortDoneDispatcher BirthSigMoveDisposalRepair
  BirthStationaryWrite ExpiringK2Projection


set_option autoImplicit false
set_option pp.structureInstances false


/- Exact supplied source records, specialized only to psi=4. -/
def sourcePeace4 (j : Fin 4) : PeaceView 4 :=
  { leader := false, label := j, shield := false, bullet := 0, signal_B := 0 }


def sourceBase4 (bits : Fin 4 → Bool) (j : Fin 4) : AgentState 4 :=
  { PeaceView.toState (sourcePeace4 j) with bit := bits j }


def sourcePayload4 (bits : Fin 4 → Bool) (j : Fin 4) : PathInfo :=
  .some j.val (if bits j then 1 else 0)


def preRaw4 (bits : Fin 4 → Bool) (j : Fin 4) : AgentState 4 :=
  if j.val < 3 then { sourceBase4 bits j with state := .produce }
  else sourceBase4 bits j


def ackRaw4 (bits : Fin 4 → Bool) (j : Fin 4) : AgentState 4 :=
  { sourceBase4 bits j with
    state := .done
    path := sourcePayload4 bits j
    path2 := none
    path4 := if 0 < j.val then some (Int.ofNat j.val, 1) else none }


def departRaw4 (bits : Fin 4 → Bool) (j : Fin 4) : AgentState 4 :=
  { sourceBase4 bits j with
    state := .depart
    wait := true
    path := sourcePayload4 bits j
    path2 := none
    h_field := decide (j.val = 0)
    path5 := if 0 < j.val ∧ j.val < 3 then
      some (Int.ofNat j.val, 1) else none
    write_state := if j.val = 0 then .none else .depart }


def authRaw4 (u : AgentState 4) : AuthorizedAgentState 4 := ⟨u, false⟩


/- State just before the stationary writer: WRITE has not yet supplied the
positive responder departure field. -/
def preWriterDepart4 (bits : Fin 4 → Bool) (j : Fin 4) : AgentState 4 :=
  { departRaw4 bits j with write_state := .none }


def bits23 (b2 b3 : Bool) (j : Fin 4) : Bool :=
  if j = (2 : Fin 4) then b2 else if j = (3 : Fin 4) then b3 else false


def bits01 (b0 b1 : Bool) (j : Fin 4) : Bool :=
  if j = (0 : Fin 4) then b0 else if j = (1 : Fin 4) then b1 else false


/-- First changed cut: on the requested terminal fixture, short GEN is exactly
the old full-width GEN stage, without identifying either complete host. -/
theorem terminal_short_gen_eq_old_gen_stage (b2 b3 : Bool) :
    let bits := bits23 b2 b3
    genCleanWidth (psi := 4) (width := 2)
        (by decide) (by decide) (by decide) 4
        (preRaw4 bits 2) (preRaw4 bits 3) =
      genClean (by decide) 4 (preRaw4 bits 2) (preRaw4 bits 3) := by
  cases b2 <;> cases b3 <;> decide


/-- Independent check of the genuinely different current writer. -/
theorem terminal_stationary_writer_exact (b2 b3 : Bool) :
    let bits := bits23 b2 b3
    stationaryPersistentRaw (by decide)
        (ackRaw4 bits 2) (preWriterDepart4 bits 3) =
      (ackRaw4 bits 2, departRaw4 bits 3) := by
  cases b2 <;> cases b3 <;> decide


private theorem pre2_domain (b2 b3 : Bool) :
    (preRaw4 (bits23 b2 b3) 2).inProtocolDomain 4 := by
  cases b2 <;> cases b3 <;> simp [preRaw4, ackRaw4, sourceBase4, sourcePeace4, sourcePayload4, PeaceView.toState, AgentState.inProtocolDomain]


private theorem pre3_domain (b2 b3 : Bool) :
    (preRaw4 (bits23 b2 b3) 3).inProtocolDomain 4 := by
  cases b2 <;> cases b3 <;> simp [preRaw4, ackRaw4, sourceBase4, sourcePeace4, sourcePayload4, PeaceView.toState, AgentState.inProtocolDomain]


private def pack4 (u : AgentState 4) (hu : u.inProtocolDomain 4) :
    ExpiringAgentState 4 4 16 :=
  ⟨⟨BoundedAgentState.ofDomain u hu, false⟩, freshStall 16⟩


private def terminalL (b2 b3 : Bool) : ExpiringAgentState 4 4 16 :=
  pack4 (preRaw4 (bits23 b2 b3) 2) (pre2_domain b2 b3)


private def terminalR (b2 b3 : Bool) : ExpiringAgentState 4 4 16 :=
  pack4 (preRaw4 (bits23 b2 b3) 3) (pre3_domain b2 b3)


set_option maxHeartbeats 32000000 in
set_option maxRecDepth 32768 in
/-- Complete physical/auth output through short WAIT, DONE/check, short
SUPPRESS, stationary persistent WRITE, finite reification, both expiry calls,
leader normalization and the one actual K2 tail. -/
theorem terminal_actual_row_all_bits (b2 b3 : Bool) :
    let bits := bits23 b2 b3
    let q := BirthShortDoneDispatcher.row
      (ψ := 4) (width := 2) (κ := 4) (τ := 16)
      (by decide) (by decide) (by decide) (terminalL b2 b3) (terminalR b2 b3)
    q.1.core.erase = authRaw4 (ackRaw4 bits 2) ∧
      q.1.stall.val = 16 ∧
      q.2.core.erase = authRaw4 (departRaw4 bits 3) ∧
      q.2.stall.val = 16 := by
  cases b2 <;> cases b3 <;> decide


/- Zero service: left pre-producer, right an already held ACK. -/
private theorem pre0_domain (b0 b1 : Bool) :
    (preRaw4 (bits01 b0 b1) 0).inProtocolDomain 4 := by
  cases b0 <;> cases b1 <;> simp [preRaw4, ackRaw4, sourceBase4, sourcePeace4, sourcePayload4, PeaceView.toState, AgentState.inProtocolDomain]


private theorem ack1_domain (b0 b1 : Bool) :
    (ackRaw4 (bits01 b0 b1) 1).inProtocolDomain 4 := by
  cases b0 <;> cases b1 <;> simp [bits01, preRaw4, ackRaw4, sourceBase4, sourcePeace4, sourcePayload4, PeaceView.toState, AgentState.inProtocolDomain]


private def zeroL (b0 b1 : Bool) : ExpiringAgentState 4 4 16 :=
  pack4 (preRaw4 (bits01 b0 b1) 0) (pre0_domain b0 b1)


private def zeroR (b0 b1 : Bool) : ExpiringAgentState 4 4 16 :=
  pack4 (ackRaw4 (bits01 b0 b1) 1) (ack1_domain b0 b1)


theorem zero_short_gen_eq_old_gen_stage (b0 b1 : Bool) :
    let bits := bits01 b0 b1
    genCleanWidth (psi := 4) (width := 2)
        (by decide) (by decide) (by decide) 4
        (preRaw4 bits 0) (ackRaw4 bits 1) =
      genClean (by decide) 4 (preRaw4 bits 0) (ackRaw4 bits 1) := by
  cases b0 <;> cases b1 <;> decide


theorem zero_stationary_writer_exact (b0 b1 : Bool) :
    let bits := bits01 b0 b1
    stationaryPersistentRaw (by decide)
        (departRaw4 bits 0) (preWriterDepart4 bits 1) =
      (departRaw4 bits 0, departRaw4 bits 1) := by
  cases b0 <;> cases b1 <;> decide


set_option maxHeartbeats 32000000 in
set_option maxRecDepth 32768 in
/-- Full new-host zero service: core identity survives, right timer does not
stay fresh because its existing path/permit is static. -/
theorem zero_actual_row_all_bits (b0 b1 : Bool) :
    let bits := bits01 b0 b1
    let q := BirthShortDoneDispatcher.row
      (ψ := 4) (width := 2) (κ := 4) (τ := 16)
      (by decide) (by decide) (by decide) (zeroL b0 b1) (zeroR b0 b1)
    q.1.core.erase = authRaw4 (departRaw4 bits 0) ∧
      q.1.stall.val = 16 ∧
      q.2.core.erase = authRaw4 (departRaw4 bits 1) ∧
      q.2.stall.val = 15 := by
  cases b0 <;> cases b1 <;> decide


/- Expose the literal current timer branch on one current finite zero-service
pair, rather than postulating a future-origin invariant. -/
private def zL0 := prepareExpiringDisposal (by decide) (zeroL false false)
private def zR0 := prepareExpiringDisposal (by decide) (zeroR false false)
private def zB := BirthShortDoneCuts.doneMetadataBoundedWidth
  (ψ := 4) (width := 2) (κ := 4)
  (by decide) (by decide) (by decide) zL0.core zR0.core
private def zROut : ExpiringAgentState 4 4 16 := ⟨zB.2, zR0.stall⟩


set_option maxHeartbeats 32000000 in
set_option maxRecDepth 32768 in
theorem zero_right_literal_timer_branch :
    PathProgressView.ofState zROut.core = PathProgressView.ofState zR0.core ∧
      deletionActive zROut.core.erase = false ∧
      zR0.stall.val = 16 ∧
      (deletionPriorityExpireOne 16 zR0 zROut).stall.val = 15 ∧
      (deletionPriorityExpireOne 16 zR0 zROut).core.erase =
        authRaw4 (departRaw4 (bits01 false false) 1) := by
  decide


#print axioms terminal_short_gen_eq_old_gen_stage
#print axioms terminal_stationary_writer_exact
#print axioms terminal_actual_row_all_bits
#print axioms zero_short_gen_eq_old_gen_stage
#print axioms zero_stationary_writer_exact
#print axioms zero_actual_row_all_bits
#print axioms zero_right_literal_timer_branch


end BirthShortDoneDispatcherProducerAudit
