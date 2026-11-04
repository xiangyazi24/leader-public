import Leader.Wu.Birth.CorridorAbsorption


namespace BirthB1ControlledWrap


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLAuthorizedComparisonRepair PPLLExpiringComparisonRepair
  PPLLWallSweepRepair
open PPLLWriteSeqPersistenceRegression
open BirthWaitPassive
open BirthShortDoneTerminalB1EntranceR2
open Q11632RightDrainCollar
open BirthB1RightDrainProducer


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


variable {n psi kappa tau : Nat}


abbrev FC (n psi kappa tau : Nat) :=
  BirthB1RightDrainProducer.FC n psi kappa tau


/-! ## The exact controlled-wrap trace -/


private theorem hTwo : 0 < 2 := by decide
private theorem hTwoLe : 2 <= 2 := by decide


def ringFour : DirectedRing 4 := ⟨by decide⟩


abbrev E4 := ExpiringAgentState 2 2 0
abbrev FC4 := Fin 4 -> E4


private theorem fin4_cases (i : Fin 4) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  omega


private def d0 : Registers 2 where
  label := 0
  h := false
  carry := false
  reset := false
  count := 0
  wait := true
  bit := false
  phase := false
  writer := .none


private def d1 : Registers 2 where
  label := 1
  h := false
  carry := false
  reset := false
  count := 0
  wait := true
  bit := false
  phase := false
  writer := .none


private def sourceRaw (i : Fin 4) : AgentState 2 :=
  if i = 0 then cell d0
  else if i = 1 then cell d1
  else if i = 2 then { cell d0 with reset_cmd := true }
  else cell d1


private theorem sourceRaw_domain (i : Fin 4) :
    (sourceRaw i).inProtocolDomain 2 := by
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
    simp [sourceRaw, d0, d1, AgentState.inProtocolDomain,
      BirthWaitPassive.cell]


private def source : FC4 := fun i =>
  ⟨⟨BoundedAgentState.ofDomain
      (sourceRaw i) (sourceRaw_domain i), false⟩, 0⟩


/-- The tail row, 2 -> 3. -/
private def frontier : FC4 :=
  currentRun hTwo hTwoLe ringFour source [(2 : Fin 4)]


/-- Counterclockwise echo, then the closing wrap collision. -/
def wrapWord : List (Fin 4) :=
  [(1 : Fin 4), (0 : Fin 4), (3 : Fin 4)]


private def afterOne : FC4 :=
  currentRun hTwo hTwoLe ringFour frontier [(1 : Fin 4)]


private def afterOneZero : FC4 :=
  currentRun hTwo hTwoLe ringFour frontier
    [(1 : Fin 4), (0 : Fin 4)]


private def absorbed : FC4 :=
  currentRun hTwo hTwoLe ringFour frontier wrapWord


set_option maxHeartbeats 200000000 in
set_option maxRecDepth 65536 in
private theorem frontier_leaderless :
    BirthShortDoneTerminalFirstHit.Leaderless frontier := by
  intro i
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;> decide


set_option maxHeartbeats 200000000 in
set_option maxRecDepth 65536 in
private theorem afterOne_leaderless :
    BirthShortDoneTerminalFirstHit.Leaderless afterOne := by
  intro i
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;> decide


set_option maxHeartbeats 200000000 in
set_option maxRecDepth 65536 in
private theorem afterOneZero_leaderless :
    BirthShortDoneTerminalFirstHit.Leaderless afterOneZero := by
  intro i
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;> decide


set_option maxHeartbeats 200000000 in
set_option maxRecDepth 65536 in
private theorem absorbed_leaderless :
    BirthShortDoneTerminalFirstHit.Leaderless absorbed := by
  intro i
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;> decide


set_option maxHeartbeats 200000000 in
set_option maxRecDepth 65536 in
private theorem frontier_labels :
    TripleLabels hTwo ringFour frontier (0 : Fin 4) := by
  unfold TripleLabels
  decide


set_option maxHeartbeats 200000000 in
set_option maxRecDepth 65536 in
private theorem afterOne_labels :
    TripleLabels hTwo ringFour afterOne (0 : Fin 4) := by
  unfold TripleLabels
  decide


set_option maxHeartbeats 200000000 in
set_option maxRecDepth 65536 in
private theorem afterOneZero_labels :
    TripleLabels hTwo ringFour afterOneZero (0 : Fin 4) := by
  unfold TripleLabels
  decide


set_option maxHeartbeats 200000000 in
set_option maxRecDepth 65536 in
private theorem absorbed_labels :
    TripleLabels hTwo ringFour absorbed (0 : Fin 4) := by
  unfold TripleLabels
  decide


set_option maxHeartbeats 200000000 in
set_option maxRecDepth 65536 in
private theorem frontier_reset_front :
    ResetFrontAt ringFour frontier frontier (0 : Fin 4) 1 := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · intro j hj
    have hj0 : j = 0 := by omega
    subst j
    decide
  · intro j hj hbound
    omega


set_option maxHeartbeats 200000000 in
set_option maxRecDepth 65536 in
/-- The literal current consumer realizes exactly the intended two reverse
    echo moves followed by the reset/echo collision. -/
theorem q11694_echo_reset_trace :
    (raw (frontier (2 : Fin 4))).echo = true ∧
      (raw (frontier (3 : Fin 4))).reset_cmd = true ∧
      (raw (afterOne (2 : Fin 4))).echo = false ∧
      (raw (afterOne (1 : Fin 4))).echo = true ∧
      (raw (afterOne (3 : Fin 4))).reset_cmd = true ∧
      (raw (afterOneZero (1 : Fin 4))).echo = false ∧
      (raw (afterOneZero (0 : Fin 4))).echo = true ∧
      (raw (afterOneZero (3 : Fin 4))).reset_cmd = true ∧
      (raw (absorbed (0 : Fin 4))).echo = false ∧
      (raw (absorbed (3 : Fin 4))).reset_cmd = false := by
  decide


/-- Ruler labels are unchanged at every one of the four prefixes of [1,0,3]. -/
theorem q11694_labels_every_prefix :
    AlignedAlong hTwo hTwoLe ringFour frontier wrapWord (0 : Fin 4) := by
  intro t ht
  have ht3 : t <= 3 := by
    simpa [wrapWord] using ht
  have hc : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  · exact frontier_labels
  · simpa [runPrefix, wrapWord, afterOne] using afterOne_labels
  · simpa [runPrefix, wrapWord, afterOneZero] using afterOneZero_labels
  · simpa [runPrefix, wrapWord, absorbed] using absorbed_labels


/-- No physical birth occurs on the concrete controlled-wrap suffix. -/
theorem q11694_leaderless_every_prefix :
    LeaderlessAlong hTwo hTwoLe ringFour frontier wrapWord := by
  intro t ht
  have ht3 : t <= 3 := by
    simpa [wrapWord] using ht
  have hc : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  · exact frontier_leaderless
  · simpa [runPrefix, wrapWord, afterOne] using afterOne_leaderless
  · simpa [runPrefix, wrapWord, afterOneZero] using afterOneZero_leaderless
  · simpa [runPrefix, wrapWord, absorbed] using absorbed_leaderless


private theorem fin4_in_maximal_region (i : Fin 4) :
    InDrainRegion ringFour (0 : Fin 4) 1 i := by
  rcases fin4_cases i with rfl | rfl | rfl | rfl
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩


/-- Maximal corridor means the declared support is the whole four-site ring,
    hence all three suffix rows, including 3 -> 0, are supported. -/
theorem q11694_wrap_supported :
    WordSupported ringFour (0 : Fin 4) 1 wrapWord := by
  intro e _he
  exact ⟨fin4_in_maximal_region e,
    fin4_in_maximal_region (ringFour.rightNeighbor e)⟩


set_option maxHeartbeats 200000000 in
set_option maxRecDepth 65536 in
/-- After collision the old tail and the maximal reset-front site contain no
    exported reset/echo/comparison/WRITE/K2 metadata. -/
theorem q11694_corridor_terminated :
    CorridorTerminated ringFour absorbed (0 : Fin 4) 1 := by
  intro k hk
  have hc : k = 0 ∨ k = 1 := by omega
  rcases hc with rfl | rfl
  · unfold DrainQuiescent BirthWaitPassive.Metadata
      BirthWaitPassive.InertWriter
    decide
  · unfold DrainQuiescent BirthWaitPassive.Metadata
      BirthWaitPassive.InertWriter
    decide


set_option maxHeartbeats 200000000 in
set_option maxRecDepth 65536 in
/-- The protected 0,1,2 triple is genuinely Passive again, with labels 0,1,0. -/
theorem q11694_final_sanitized :
    ThreeSiteSanitized hTwo ringFour absorbed (0 : Fin 4) := by
  unfold ThreeSiteSanitized TripleLabels
  unfold BirthWaitPassive.Passive BirthWaitPassive.Metadata
    BirthWaitPassive.InertWriter
  decide


/-- Exact no-birth conclusion of the adopted controlled-wrap body on this trace. -/
theorem q11694_controlled_wrap_conclusion :
    ∃ finish : List (Fin 4),
      WordSupported ringFour (0 : Fin 4) 1 finish ∧
      (let D := currentRun hTwo hTwoLe ringFour frontier finish
       HasLeaderAlong hTwo hTwoLe ringFour frontier finish ∨
        (LeaderlessAlong hTwo hTwoLe ringFour frontier finish ∧
          AlignedAlong hTwo hTwoLe ringFour frontier finish (0 : Fin 4) ∧
          CorridorTerminated ringFour D (0 : Fin 4) 1 ∧
          ThreeSiteSanitized hTwo ringFour D (0 : Fin 4))) := by
  refine ⟨wrapWord, q11694_wrap_supported, ?_⟩
  dsimp only
  exact Or.inr ⟨q11694_leaderless_every_prefix,
    q11694_labels_every_prefix,
    q11694_corridor_terminated,
    q11694_final_sanitized⟩


/-- This is the exact specialization of the body quantified by
    ControlledWrapAbsorptionStatement.  The universal statement itself ranges
    over arbitrary current states and is therefore strictly stronger than one
    decide fixture. -/
theorem controlledWrapAbsorptionStatement_q11694 :
    0 < (1 : Nat) ->
    2 + 1 + 1 = 4 ->
    BirthShortDoneTerminalFirstHit.Leaderless frontier ->
    TripleLabels hTwo ringFour frontier (0 : Fin 4) ->
    ResetFrontAt ringFour frontier frontier (0 : Fin 4) 1 ->
    ∃ finish : List (Fin 4),
      WordSupported ringFour (0 : Fin 4) 1 finish ∧
      (let D := currentRun hTwo hTwoLe ringFour frontier finish
       HasLeaderAlong hTwo hTwoLe ringFour frontier finish ∨
        (LeaderlessAlong hTwo hTwoLe ringFour frontier finish ∧
          AlignedAlong hTwo hTwoLe ringFour frontier finish (0 : Fin 4) ∧
          CorridorTerminated ringFour D (0 : Fin 4) 1 ∧
          ThreeSiteSanitized hTwo ringFour D (0 : Fin 4))) := by
  intro _hpos _hmax _hleaderless _hlabels _hfront
  exact q11694_controlled_wrap_conclusion


/-! ## General-n moving-pair invariant -/


/-- Exactly one echo scar lies in the protected triple. -/
def UniqueProtectedEchoAt
    (ring : DirectedRing n) (current : FC n psi kappa tau)
    (a : Fin n) (echoPos : Nat) : Prop :=
  echoPos <= 2 ∧
    (raw (current (groupOffset ring a echoPos))).echo = true ∧
    ∀ q, q <= 2 -> q ≠ echoPos ->
      (raw (current (groupOffset ring a q))).echo = false


/-- Protected sites already crossed by the counterclockwise echo are Passive. -/
def ProtectedClearedAfterEcho
    (ring : DirectedRing n) (current : FC n psi kappa tau)
    (a : Fin n) (echoPos : Nat) : Prop :=
  ∀ q, echoPos < q -> q <= 2 ->
    Passive (raw (current (groupOffset ring a q)))


/-- Positive corridor sites already crossed by the clockwise reset front are
    quiescent.  k=0 is the protected tail, so it is handled by the preceding
    protected-site clause while the echo is still leaving it. -/
def CorridorClearedBehindReset
    (ring : DirectedRing n) (current : FC n psi kappa tau)
    (a : Fin n) (resetK : Nat) : Prop :=
  ∀ k, 0 < k -> k < resetK ->
    DrainQuiescent (raw (current (drainSite ring a k)))


/-- General controlled-wrap state.  echoPos moves down, resetK moves up. -/
def ControlledWrapInvariant
    (hpsi : 0 < psi) (ring : DirectedRing n)
    (initial current : FC n psi kappa tau)
    (a : Fin n) (corridorLen echoPos resetK : Nat) : Prop :=
  0 < corridorLen ∧
    2 + corridorLen + 1 = n ∧
    0 < resetK ∧
    resetK <= corridorLen ∧
    BirthShortDoneTerminalFirstHit.Leaderless current ∧
    TripleLabels hpsi ring current a ∧
    ResetFrontAt ring initial current a resetK ∧
    UniqueProtectedEchoAt ring current a echoPos ∧
    ProtectedClearedAfterEcho ring current a echoPos ∧
    CorridorClearedBehindReset ring current a resetK


/-- The edge whose responder is the current echo site. -/
def echoTransportEdge
    (ring : DirectedRing n) (a : Fin n) (echoPos : Nat) : Fin n :=
  groupOffset ring a (echoPos - 1)


theorem echoTransportEdge_responder
    (ring : DirectedRing n) (a : Fin n) (echoPos : Nat)
    (hpos : 0 < echoPos) :
    ring.rightNeighbor (echoTransportEdge ring a echoPos) =
      groupOffset ring a echoPos := by
  have hs := rightNeighbor_groupOffset ring a (echoPos - 1)
  have hp : echoPos - 1 + 1 = echoPos := by omega
  simpa [echoTransportEdge, hp] using hs


/-- At a maximal corridor the final reset-front edge is exactly the closing
    edge into anchor a. -/
theorem maximal_reset_front_closes_at_anchor
    (ring : DirectedRing n) (a : Fin n) (corridorLen : Nat)
    (hmax : 2 + corridorLen + 1 = n) :
    ring.rightNeighbor (drainSite ring a corridorLen) = a := by
  unfold drainSite
  rw [rightNeighbor_groupOffset, hmax]
  apply Fin.ext
  change (a.val + n) % n = a.val
  rw [Nat.add_mod, Nat.mod_eq_of_lt a.isLt, Nat.mod_self,
    Nat.add_zero, Nat.mod_eq_of_lt a.isLt]


/-- Remaining noncollision distance of the two fronts.  At zero, reset is at
    the maximal predecessor and echo is at anchor, so the next row is collision. -/
def controlledWrapPairDistance
    (corridorLen echoPos resetK : Nat) : Nat :=
  echoPos + (corridorLen - resetK)


theorem controlledWrapPairDistance_echo_step
    {corridorLen echoPos resetK : Nat} (hpos : 0 < echoPos) :
    controlledWrapPairDistance corridorLen (echoPos - 1) resetK <
      controlledWrapPairDistance corridorLen echoPos resetK := by
  unfold controlledWrapPairDistance
  omega


theorem controlledWrapPairDistance_reset_step
    {corridorLen echoPos resetK : Nat} (hk : resetK < corridorLen) :
    controlledWrapPairDistance corridorLen echoPos (resetK + 1) <
      controlledWrapPairDistance corridorLen echoPos resetK := by
  unfold controlledWrapPairDistance
  omega


theorem controlledWrapPairDistance_collision_ready (corridorLen : Nat) :
    controlledWrapPairDistance corridorLen 0 corridorLen = 0 := by
  simp [controlledWrapPairDistance]


/-! ## The two local Algorithm-14 facts -/


/-- Follower/follower, reset-free responder-echo row: the repaired literal
    SUPPRESS call moves the echo exactly one edge counterclockwise and preserves
    both physical labels. -/
theorem suppress_echo_transport_row
    (hpsi : 0 < psi) (l r : AgentState psi)
    (hlLeader : l.leader = false)
    (hlReset : l.reset_cmd = false)
    (hrEcho : r.echo = true)
    (hrReset : r.reset_cmd = false) :
    let q := suppressSigResetKill hpsi l r
    q.1.echo = true ∧
      q.2.echo = false ∧
      q.1.reset_cmd = false ∧
      q.2.reset_cmd = false ∧
      q.1.label = l.label ∧
      q.2.label = r.label := by
  simp [suppressSigResetKill, suppressSigStart,
    resetKillComparison, clearComparisonSignal,
    suppressSigMoveReset, suppressSigTerminal,
    suppressSigEcho, suppressSigFinish,
    hlLeader, hlReset, hrEcho, hrReset]


/-- Closing row: a follower reset front entering a nonterminal follower carrying
    echo makes the responder carry reset and echo simultaneously, and repaired
    SUPPRESS cancels the pair in that same call. -/
theorem suppress_echo_collision_row
    (hpsi : 0 < psi) (l r : AgentState psi)
    (hlLeader : l.leader = false)
    (hlReset : l.reset_cmd = true)
    (hlEcho : l.echo = false)
    (hrEcho : r.echo = true)
    (hrTerminal :
      r.label ≠ (⟨psi - 1, by omega⟩ : Fin psi)) :
    let q := suppressSigResetKill hpsi l r
    q.1.echo = false ∧
      q.2.echo = false ∧
      q.1.reset_cmd = false ∧
      q.2.reset_cmd = false ∧
      q.1.label = l.label ∧
      q.2.label = r.label := by
  simp [suppressSigResetKill, suppressSigStart,
    resetKillComparison, clearComparisonSignal,
    suppressSigMoveReset, suppressSigTerminal,
    suppressSigEcho, suppressSigFinish,
    hlLeader, hlReset, hlEcho, hrEcho, hrTerminal]


/-- TripleLabels makes the closing responder anchor nonterminal whenever width
    two is admissible. -/
theorem anchor_not_terminal_of_tripleLabels
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) (C : FC n psi kappa tau) (a : Fin n)
    (hlabels : TripleLabels hpsi ring C a) :
    (raw (C a)).label ≠ (⟨psi - 1, by omega⟩ : Fin psi) := by
  intro h
  have hv := congrArg Fin.val h
  have h0 := hlabels.1
  rw [h0] at hv
  dsimp at hv
  omega


/-! ## Exact remaining full-consumer obligations -/


/-- Full current-consumer lift of one reverse echo step.  The two local
    Algorithm-14 assignments are already proved above; this Prop records the
    remaining interference audit for all other stages of the literal consumer. -/
def ControlledWrapEchoConsumerStepStatement
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) : Prop :=
  ∀ (initial current : FC n psi kappa tau)
      (a : Fin n) (corridorLen echoPos resetK : Nat),
    ControlledWrapInvariant hpsi ring initial current a
      corridorLen echoPos resetK ->
    0 < echoPos ->
    let e := echoTransportEdge ring a echoPos
    PreparedOrdinaryOpen hpsi
      (current e) (current (ring.rightNeighbor e)) ->
    BirthShortDoneTerminalPassiveR4.RowPreCap2
      hpsi h2 kappa ring current e ->
    let D := BirthShortDoneTerminalConsumer.step
      hpsi (by decide : 0 < 2) h2 ring current e
    HasLeader D ∨
      ControlledWrapInvariant hpsi ring initial D a
        corridorLen (echoPos - 1) resetK


/-- Full current-consumer lift of one clockwise reset-front step while the echo
    scar is retained.  This is the controlled-wrap strengthening of the R1
    FullConsumerFrontStepStatement. -/
def ControlledWrapResetConsumerStepStatement
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) : Prop :=
  ∀ (initial current : FC n psi kappa tau)
      (a : Fin n) (corridorLen echoPos resetK : Nat),
    ControlledWrapInvariant hpsi ring initial current a
      corridorLen echoPos resetK ->
    resetK < corridorLen ->
    let e := drainSite ring a resetK
    PreparedOrdinaryOpen hpsi
      (current e) (current (ring.rightNeighbor e)) ->
    let D := BirthShortDoneTerminalConsumer.step
      hpsi (by decide : 0 < 2) h2 ring current e
    HasLeader D ∨
      ControlledWrapInvariant hpsi ring initial D a
        corridorLen echoPos (resetK + 1)


/-- Full current-consumer closing row.  With distance zero, the maximal reset
    front enters anchor, where the unique echo sits; the no-birth branch must
    finish both corridor quiescence and protected-triple sanitation. -/
def ControlledWrapCollisionConsumerStepStatement
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) : Prop :=
  ∀ (initial current : FC n psi kappa tau)
      (a : Fin n) (corridorLen : Nat),
    ControlledWrapInvariant hpsi ring initial current a
      corridorLen 0 corridorLen ->
    let e := drainSite ring a corridorLen
    PreparedOrdinaryOpen hpsi
      (current e) (current (ring.rightNeighbor e)) ->
    BirthShortDoneTerminalPassiveR4.RowPreCap2
      hpsi h2 kappa ring current e ->
    let D := BirthShortDoneTerminalConsumer.step
      hpsi (by decide : 0 < 2) h2 ring current e
    HasLeader D ∨
      (BirthShortDoneTerminalFirstHit.Leaderless D ∧
        TripleLabels hpsi ring D a ∧
        CorridorTerminated ring D a corridorLen ∧
        ThreeSiteSanitized hpsi ring D a)


/-- Entry bridge from the maximal R1 reset-front endpoint into the moving-pair
    invariant.  The controlled-wrap trace supplies this concretely; general n still needs it. -/
def ControlledWrapEntryStatement
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) : Prop :=
  ∀ (current : FC n psi kappa tau) (a : Fin n)
      (corridorLen : Nat),
    0 < corridorLen ->
    2 + corridorLen + 1 = n ->
    BirthShortDoneTerminalFirstHit.Leaderless current ->
    TripleLabels hpsi ring current a ->
    ResetFrontAt ring current current a corridorLen ->
    HasLeader current ∨
      ControlledWrapInvariant hpsi ring current current a
        corridorLen 2 corridorLen


/-- Finite iteration theorem still required for general n.  The arithmetic
    measure above is the well-founded rank; this statement is the exact desired
    endpoint after iterating the two step laws and then the collision law. -/
def ControlledWrapTerminationStatement
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (ring : DirectedRing n) : Prop :=
  ControlledWrapEchoConsumerStepStatement
      (kappa := kappa) (tau := tau) hpsi h2 ring ->
  ControlledWrapResetConsumerStepStatement
      (kappa := kappa) (tau := tau) hpsi h2 ring ->
  ControlledWrapCollisionConsumerStepStatement
      (kappa := kappa) (tau := tau) hpsi h2 ring ->
  ∀ (initial current : FC n psi kappa tau)
      (a : Fin n) (corridorLen echoPos resetK : Nat),
    ControlledWrapInvariant hpsi ring initial current a
      corridorLen echoPos resetK ->
    ∃ finish : List (Fin n),
      WordSupported ring a corridorLen finish ∧
      (let D := currentRun hpsi h2 ring current finish
       HasLeaderAlong hpsi h2 ring current finish ∨
        (LeaderlessAlong hpsi h2 ring current finish ∧
          AlignedAlong hpsi h2 ring current finish a ∧
          CorridorTerminated ring D a corridorLen ∧
          ThreeSiteSanitized hpsi ring D a))


/-! ## Modified right-drain producer and B1 composition -/


/-- R2 producer interface: maximal corridor and no PassiveNoReentry clause. -/
def MaximalControlledWrapRightDrainProducer
    (hpsi : 0 < psi) (h2 : 2 <= psi) (_hn : 4 <= n)
    (ring : DirectedRing n) (C : FC n psi kappa tau)
    (a : Fin n) : Prop :=
  BirthShortDoneTerminalFirstHit.Leaderless C ->
  TripleLabels hpsi ring C a ->
  ∃ corridorLen : Nat, ∃ pre finish : List (Fin n),
    0 < corridorLen ∧
    2 + corridorLen + 1 = n ∧
    (let armed := currentRun hpsi h2 ring C pre
     let drain := rightDrainWord ring a corridorLen
     let full := pre ++ drain ++ finish
     let D := currentRun hpsi h2 ring C full
     WordSupported ring a corridorLen full ∧
       (HasLeaderAlong hpsi h2 ring C full ∨
         (LeaderlessAlong hpsi h2 ring C full ∧
          AlignedAlong hpsi h2 ring C full a ∧
          ResetFrontTrace hpsi h2 ring armed a corridorLen ∧
          CorridorTerminated ring D a corridorLen ∧
          ThreeSiteSanitized hpsi ring D a)))


/-- The sanitation endpoint is exactly the local passivation target consumed by
    the B1 clock-source continuation.  No PassiveNoReentry premise is needed. -/
theorem sanitized_endpoint_is_localLine3At
    (hpsi : 0 < psi) (hn : 4 <= n)
    (ring : DirectedRing n) (D : FC n psi kappa tau)
    (a : Fin n)
    (hsan : ThreeSiteSanitized hpsi ring D a) :
    BirthShortDoneTerminalPassiveLocal3Rotation.LocalLine3At
      hpsi hn ring a D := by
  exact Q11632RightDrainCollar.localLine3At_of_threeSiteSanitized
    hpsi hn ring D a hsan


end BirthB1ControlledWrap


#print axioms BirthB1ControlledWrap.q11694_echo_reset_trace
#print axioms BirthB1ControlledWrap.q11694_labels_every_prefix
#print axioms BirthB1ControlledWrap.q11694_leaderless_every_prefix
#print axioms BirthB1ControlledWrap.q11694_wrap_supported
#print axioms BirthB1ControlledWrap.q11694_corridor_terminated
#print axioms BirthB1ControlledWrap.q11694_final_sanitized
#print axioms BirthB1ControlledWrap.q11694_controlled_wrap_conclusion
#print axioms BirthB1ControlledWrap.controlledWrapAbsorptionStatement_q11694
#print axioms BirthB1ControlledWrap.echoTransportEdge_responder
#print axioms BirthB1ControlledWrap.maximal_reset_front_closes_at_anchor
#print axioms BirthB1ControlledWrap.controlledWrapPairDistance_echo_step
#print axioms BirthB1ControlledWrap.controlledWrapPairDistance_reset_step
#print axioms BirthB1ControlledWrap.suppress_echo_transport_row
#print axioms BirthB1ControlledWrap.suppress_echo_collision_row
#print axioms BirthB1ControlledWrap.anchor_not_terminal_of_tripleLabels
#print axioms BirthB1ControlledWrap.sanitized_endpoint_is_localLine3At
