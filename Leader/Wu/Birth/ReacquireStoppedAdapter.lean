import Leader.Wu.Birth.LocalTripleContinuationBridge


namespace BirthB1ReacquireStoppedAdapter


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLExpiringComparisonRepair
open BirthWaitPassive
open BirthShortDoneTerminalPassiveR4
open BirthShortDoneTerminalPassiveLocal3
open BirthShortDoneTerminalPassiveLocal3Rotation
open BirthB1ReacquireReentryMass


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


variable {n psi kappa tau : Nat}


abbrev FC (n psi kappa tau : Nat) :=
  BirthPhaseWait2BlockProgress.FC n psi kappa tau


private theorem hpsi2 : 0 < 2 := by decide
private theorem h2 : 2 <= 2 := by decide
private theorem hn4 : 4 <= 4 := by decide


private def ring4 : DirectedRing 4 := ⟨by decide⟩
private def anchor4 : Fin 4 := 0
private def boundaryEdge4 : Fin 4 := 2


private theorem right0 :
    ring4.rightNeighbor anchor4 = (1 : Fin 4) := by
  decide


private theorem right1 :
    ring4.rightNeighbor (ring4.rightNeighbor anchor4) = (2 : Fin 4) := by
  decide


private def regs (lab : Fin 2) (hh : Bool) : Registers 2 where
  label := lab
  h := hh
  carry := false
  reset := false
  count := 0
  wait := true
  bit := false
  phase := false
  writer := .none


/-- Rotated geometry.  The reset is outside the Local3 triple. -/
private def sourceRaw (i : Fin 4) : AgentState 2 :=
  if i = 0 then cell (regs 0 true)
  else if i = 1 then cell (regs 1 true)
  else if i = 2 then cell (regs 0 false)
  else { cell (regs 1 false) with reset_cmd := true }


private theorem sourceRaw_domain (i : Fin 4) :
    (sourceRaw i).inProtocolDomain 2 := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;>
    simp [sourceRaw, regs, AgentState.inProtocolDomain, cell]


private def sourcePack (i : Fin 4) : ExpiringAgentState 2 2 0 :=
  ⟨⟨BoundedAgentState.ofDomain
      (sourceRaw i) (sourceRaw_domain i), false⟩, 0⟩


private def sourceC : FC 4 2 2 0 := fun i => sourcePack i


@[simp] private theorem raw_sourceC (i : Fin 4) :
    raw (sourceC i) = sourceRaw i := by
  simp [sourceC, sourcePack, raw, BoundedAgentState.erase_ofDomain]


private theorem source_count :
    BirthPhaseWait2BlockProgress.shortCountAt
      ring4 anchor4 sourceC = 0 := by
  decide


private theorem source_carrier :
    BirthPhaseWait2BlockProgress.Carrier
      hpsi2 h2 hn4 ring4 anchor4 sourceC := by
  unfold BirthPhaseWait2BlockProgress.Carrier
    BirthPhaseWait2BlockProgress.LocalCarrier
    BirthPhaseWait2Transfer.LocalWait2Carrier
  constructor
  · refine {
      pass0 := ?_, pass1 := ?_, pass2 := ?_,
      lab0 := ?_, lab1 := ?_, lab2 := ?_ }
    · simp [anchor4, sourceRaw, regs, Passive, InertWriter, Metadata,
        BirthWaitPassive.registers, BirthWaitPassive.cell]
    · rw [right0]
      simp [sourceRaw, regs, Passive, InertWriter, Metadata,
        BirthWaitPassive.registers, BirthWaitPassive.cell]
    · rw [right1]
      simp [sourceRaw, regs, Passive, InertWriter, Metadata,
        BirthWaitPassive.registers, BirthWaitPassive.cell]
    · simp [anchor4, sourceRaw, regs, BirthWaitPassive.cell]
    · rw [right0]
      simp [sourceRaw, regs, BirthWaitPassive.cell]
    · rw [right1]
      simp [sourceRaw, regs, BirthWaitPassive.cell]
  · rw [source_count]
    decide


private theorem source_boundary_preCap :
    RowPreCap2 hpsi2 h2 2 ring4 sourceC boundaryEdge4 := by
  unfold RowPreCap2 RowCap2
  decide


private theorem source_boundary :
    BirthPhaseWait2Transfer.LocalWait2BoundaryNow
      hn4 ring4 anchor4 boundaryEdge4 := by
  unfold BirthPhaseWait2Transfer.LocalWait2BoundaryNow
    SafeLine3EdgeAt SafeLine3Edge
  decide


/-- The boundary row sees terminal reset on site 3; SUPPRESS leaves echo on
site 2, so the successor has left Local3 while remaining sub-cap. -/
private def startC : FC 4 2 2 0 :=
  BirthPhaseWait2BlockProgress.currentStep2
    hpsi2 h2 ring4 sourceC boundaryEdge4


set_option maxRecDepth 262144 in
set_option maxHeartbeats 0 in
private theorem start_tail_echo :
    (raw (startC (2 : Fin 4))).echo = true := by
  decide


set_option maxRecDepth 262144 in
theorem start_is_reacquire :
    BirthPhaseWait2BlockProgress.Reacquire
      hpsi2 h2 hn4 2 0 ring4 anchor4 startC := by
  refine ⟨?_, ?_, by decide⟩
  · exact ⟨sourceC, boundaryEdge4, [], source_carrier,
      source_boundary_preCap, source_boundary, rfl⟩
  · intro hlocal
    unfold BirthPhaseWait2BlockProgress.LocalCarrier
      BirthPhaseWait2Transfer.LocalWait2Carrier at hlocal
    have hp := hlocal.pass2
    rw [right1] at hp
    have hm := hp.1
    unfold Metadata at hm
    have he := congrArg AgentState.echo hm
    change (raw (startC (2 : Fin 4))).echo = false at he
    rw [start_tail_echo] at he
    cases he


/-- First edge 0 raises count 0 -> 1.  Edge 3 moves the outside reset to
anchor 0; the next edge 0 resets the tracked responder 1 -> 0. -/
private def hitWord : List (Fin 4) := [anchor4]
private def tailWord : List (Fin 4) :=
  [(3 : Fin 4), anchor4] ++ List.replicate 21 (3 : Fin 4)
private def badWord : List (Fin 4) := hitWord ++ tailWord


theorem badWord_length :
    badWord.length = BirthPhaseWait2BlockProgress.L 4 := by
  decide


set_option maxRecDepth 262144 in
set_option maxHeartbeats 0 in
theorem literal_trace :
    BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor4 startC = 0 ∧
    BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor4
      (prefixEndpoint hpsi2 h2 ring4 startC hitWord) = 1 ∧
    BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor4
      (prefixEndpoint hpsi2 h2 ring4 startC badWord) = 0 := by
  decide


/-- Literal cap-freeness at every prefix. -/
def NoCapAlong (C : FC 4 2 2 0) : List (Fin 4) -> Prop
  | [] => True
  | e :: es =>
      RowPreCap2 hpsi2 h2 2 ring4 C e ∧
      NoCapAlong
        (BirthPhaseWait2BlockProgress.currentStep2 hpsi2 h2 ring4 C e) es


private instance instDecidableRowCap2Stopped
    (C : FC 4 2 2 0) (e : Fin 4) :
    Decidable (RowCap2 hpsi2 h2 2 ring4 C e) := by
  unfold RowCap2
  dsimp only
  infer_instance


private instance instDecidableRowPreCap2Stopped
    (C : FC 4 2 2 0) (e : Fin 4) :
    Decidable (RowPreCap2 hpsi2 h2 2 ring4 C e) := by
  unfold RowPreCap2
  infer_instance


private instance instDecidableNoCapAlongStopped
    (C : FC 4 2 2 0) (u : List (Fin 4)) :
    Decidable (NoCapAlong C u) :=
  match u with
  | [] => isTrue trivial
  | e :: es =>
      letI : Decidable
          (NoCapAlong
            (BirthPhaseWait2BlockProgress.currentStep2
              hpsi2 h2 ring4 C e) es) :=
        instDecidableNoCapAlongStopped
          (BirthPhaseWait2BlockProgress.currentStep2
            hpsi2 h2 ring4 C e) es
      instDecidableAnd


private theorem noCapAlong_not_firstCapWithin
    (C : FC 4 2 2 0) (u : List (Fin 4))
    (h : NoCapAlong C u) :
    ¬ BirthPhaseWait2BlockProgress.FirstCapWithin
      hpsi2 h2 2 ring4 C u := by
  induction u generalizing C with
  | nil =>
      rintro ⟨pre, e, post, hword, _⟩
      simp at hword
  | cons e es ih =>
      change RowPreCap2 hpsi2 h2 2 ring4 C e ∧
        NoCapAlong
          (BirthPhaseWait2BlockProgress.currentStep2 hpsi2 h2 ring4 C e) es at h
      rintro ⟨pre, a, post, hword, hrow⟩
      cases pre with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at hword
          rcases hword with ⟨hea, _⟩
          subst a
          exact h.1 (by simpa using hrow)
      | cons b pre =>
          simp only [List.cons_append, List.cons.injEq] at hword
          rcases hword with ⟨heb, hrest⟩
          subst b
          apply ih
            (C := BirthPhaseWait2BlockProgress.currentStep2
              hpsi2 h2 ring4 C e) h.2
          exact ⟨pre, a, post, hrest, by simpa using hrow⟩


private theorem target_false_of_noCapAlong
    (C : FC 4 2 2 0) (u : List (Fin 4))
    (h : NoCapAlong C u) :
    BirthPhaseWait2BlockProgress.target hpsi2 h2 2 ring4 C u = false := by
  have hncap := noCapAlong_not_firstCapWithin C u h
  have hnot :
      BirthPhaseWait2BlockProgress.target hpsi2 h2 2 ring4 C u ≠ true := by
    intro ht
    exact hncap
      ((BirthPhaseWait2BlockProgress.target_true_iff
        hpsi2 h2 2 ring4 C u).1 ht)
  cases hv : BirthPhaseWait2BlockProgress.target hpsi2 h2 2 ring4 C u <;>
    simp_all


set_option maxRecDepth 262144 in
set_option maxHeartbeats 0 in
theorem badWord_noCap : NoCapAlong startC badWord := by
  decide


theorem badWord_target_free :
    BirthPhaseWait2BlockProgress.target
      hpsi2 h2 2 ring4 startC badWord = false :=
  target_false_of_noCapAlong startC badWord badWord_noCap


theorem hit_resolves :
    BirthPhaseB3ReacquireEvent.Resolves
      hpsi2 h2 2 ring4 anchor4 startC hitWord := by
  right
  rcases literal_trace with ⟨hs, hh, _⟩
  change BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor4 startC <
    BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor4
      (prefixEndpoint hpsi2 h2 ring4 startC hitWord)
  omega


theorem badWord_stopped :
    BirthB1Local3OneStep.StoppedResolves
      hpsi2 h2 2 ring4 anchor4 startC badWord :=
  ⟨hitWord, tailWord, rfl, hit_resolves⟩


theorem badWord_not_resolves :
    ¬ BirthPhaseB3ReacquireEvent.Resolves
      hpsi2 h2 2 ring4 anchor4 startC badWord := by
  rintro (ht | hinc)
  · rw [badWord_target_free] at ht
    cases ht
  · rcases literal_trace with ⟨hs, _, hf⟩
    change BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor4 startC <
      BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor4
        (prefixEndpoint hpsi2 h2 ring4 startC badWord) at hinc
    omega


/-- Exact refutation of the downstream adapter. -/
theorem reacquireStoppedEndpointAdapter_false :
    ¬ BirthB1Local3ContinuationBridge.ReacquireStoppedEndpointAdapter
      hpsi2 h2 hn4 2 0 ring4 anchor4 := by
  intro h
  exact badWord_not_resolves
    (h startC start_is_reacquire badWord badWord_length badWord_stopped)


/-- Weakest stopped-event strengthening still accepted by the current fixed
endpoint-rank Bellman consumer: the witnessed prefix gain must survive to the
block endpoint. -/
def PreservedPrefixProgressBridge
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (DirtySuccess : BirthPhaseWait2BlockProgress.DirtySuccessRel
      n psi kappa tau) : Prop :=
  forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor C ->
    forall u : List (Fin n), u.length = BirthPhaseWait2BlockProgress.L n ->
      DirtySuccess C u ->
      BirthPhaseWait2BlockProgress.target hpsi h2 kappa ring C u = true ∨
      exists hit tail, u = hit ++ tail ∧
        BirthPhaseWait2BlockProgress.shortCountAt ring anchor C <
          BirthPhaseWait2BlockProgress.shortCountAt ring anchor
            (prefixEndpoint hpsi h2 ring C hit) ∧
        BirthPhaseWait2BlockProgress.shortCountAt ring anchor
            (prefixEndpoint hpsi h2 ring C hit) <=
          BirthPhaseWait2BlockProgress.shortCountAt ring anchor
            (prefixEndpoint hpsi h2 ring C u)


theorem preservedPrefixProgress_stageA
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (DirtySuccess : BirthPhaseWait2BlockProgress.DirtySuccessRel
      n psi kappa tau)
    (h : PreservedPrefixProgressBridge
      hpsi h2 hn kappa tau ring anchor DirtySuccess) :
    BirthPhaseB3BridgeStageA.ReacquireStartBridge
      hpsi h2 hn kappa tau ring anchor DirtySuccess := by
  intro C hR u hlen hdirty
  rcases h C hR u hlen hdirty with ht | ⟨hit, tail, _, hgain, hkeep⟩
  · exact Or.inl ht
  · right
    change BirthPhaseWait2BlockProgress.shortCountAt ring anchor C <
      BirthPhaseWait2BlockProgress.shortCountAt ring anchor
        (prefixEndpoint hpsi h2 ring C u)
    exact Nat.lt_of_lt_of_le hgain hkeep


end BirthB1ReacquireStoppedAdapter


#print axioms BirthB1ReacquireStoppedAdapter.start_is_reacquire
#print axioms BirthB1ReacquireStoppedAdapter.literal_trace
#print axioms BirthB1ReacquireStoppedAdapter.badWord_noCap
#print axioms BirthB1ReacquireStoppedAdapter.reacquireStoppedEndpointAdapter_false
#print axioms BirthB1ReacquireStoppedAdapter.preservedPrefixProgress_stageA
