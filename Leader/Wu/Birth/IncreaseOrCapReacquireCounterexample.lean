import Leader.Wu.Birth.IncreaseOrCapCarrierBridge

set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false

namespace BirthPhaseB3ReacquireSide

open PPLL PPLLRepair PPLLResearchFormulation
  PPLLExpiringComparisonRepair

variable {n psi kappa tau : Nat}

abbrev FC (n psi kappa tau : Nat) :=
  BirthPhaseWait2BlockProgress.FC n psi kappa tau

/-! ## A computable no-cap predicate for literal fixture words -/

/-- Recursive spelling of “no RowCap2 occurs on this literal word”. -/
def NoCapAlong
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n)
    (C : FC n psi kappa tau) : List (Fin n) -> Prop
  | [] => True
  | e :: es =>
      ¬ BirthShortDoneTerminalPassiveR4.RowCap2
        hpsi h2 kappa ring C e /\
      NoCapAlong hpsi h2 kappa ring
        (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e) es

private theorem firstCapWithin_cons_iff
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n)
    (C : FC n psi kappa tau) (e : Fin n) (es : List (Fin n)) :
    BirthPhaseWait2BlockProgress.FirstCapWithin
        hpsi h2 kappa ring C (e :: es) <->
      BirthShortDoneTerminalPassiveR4.RowCap2
          hpsi h2 kappa ring C e \/
        BirthPhaseWait2BlockProgress.FirstCapWithin
          hpsi h2 kappa ring
          (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring C e) es := by
  constructor
  · rintro ⟨pre, a, post, hword, hcap⟩
    cases pre with
    | nil =>
        simp only [List.nil_append, List.cons.injEq] at hword
        rcases hword with ⟨hea, hrest⟩
        subst a
        subst post
        exact Or.inl hcap
    | cons b pre =>
        simp only [List.cons_append, List.cons.injEq] at hword
        rcases hword with ⟨heb, hrest⟩
        subst b
        right
        refine ⟨pre, a, post, hrest, ?_⟩
        simpa using hcap
  · intro h
    rcases h with hcap | htail
    · exact ⟨[], e, es, rfl, hcap⟩
    · rcases htail with ⟨pre, a, post, hword, hcap⟩
      refine ⟨e :: pre, a, post, ?_, ?_⟩
      · simp [hword]
      · simpa using hcap

private theorem noCapAlong_iff_not_firstCapWithin
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n)
    (C : FC n psi kappa tau) (u : List (Fin n)) :
    NoCapAlong hpsi h2 kappa ring C u <->
      ¬ BirthPhaseWait2BlockProgress.FirstCapWithin
        hpsi h2 kappa ring C u := by
  induction u generalizing C with
  | nil =>
      simp [NoCapAlong, BirthPhaseWait2BlockProgress.FirstCapWithin]
  | cons e es ih =>
      rw [firstCapWithin_cons_iff]
      simp [NoCapAlong, ih]

private theorem target_false_iff_noCapAlong
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n)
    (C : FC n psi kappa tau) (u : List (Fin n)) :
    BirthPhaseWait2BlockProgress.target
        hpsi h2 kappa ring C u = false <->
      NoCapAlong hpsi h2 kappa ring C u := by
  classical
  by_cases hcap : BirthPhaseWait2BlockProgress.FirstCapWithin
      hpsi h2 kappa ring C u
  · have hnc : ¬ NoCapAlong hpsi h2 kappa ring C u := by
      intro hncap
      exact (noCapAlong_iff_not_firstCapWithin
        hpsi h2 kappa ring C u).1 hncap hcap
    simp [BirthPhaseWait2BlockProgress.target, hcap, hnc]
  · have hnc : NoCapAlong hpsi h2 kappa ring C u :=
      (noCapAlong_iff_not_firstCapWithin
        hpsi h2 kappa ring C u).2 hcap
    simp [BirthPhaseWait2BlockProgress.target, hcap, hnc]

/-! ## The minimum-n literal counterexample -/

private theorem hpsi2 : 0 < 2 := by decide
private theorem h2 : 2 <= 2 := by decide
private theorem hn4 : 4 <= 4 := by decide

def padEdge4 : Fin 4 := 3

/-- Immediate literal successor of the public boundary row. -/
def boundarySuccessor : FC 4 2 2 3 :=
  BirthPhaseWait2BlockProgress.currentStep2
    hpsi2 h2
    BirthPhaseWait2Transfer.boundaryRing4
    BirthPhaseWait2Transfer.boundaryConfig4
    BirthPhaseWait2Transfer.boundaryEdge4

/-- Enter Reacquire on edge 2, then spend the remaining 23 letters on edge 3.
`L 4 = 24`. -/
def boundaryCounterWord : List (Fin 4) :=
  BirthPhaseWait2Transfer.boundaryEdge4 ::
    List.replicate 23 padEdge4

/-- A full block starting already in Reacquire, using only the opposite
boundary edge 3 -> 0. -/
def reacquireCounterWord : List (Fin 4) :=
  List.replicate 24 padEdge4

private theorem boundaryBreakRow_fixture :
    BirthPhaseB3BridgeStageA.BoundaryBreakRow
      hpsi2 h2 hn4 2 3
      BirthPhaseWait2Transfer.boundaryRing4
      BirthPhaseWait2Transfer.boundaryAnchor4
      BirthPhaseWait2Transfer.boundaryConfig4
      BirthPhaseWait2Transfer.boundaryEdge4 := by
  have hC := BirthPhaseB3DirtySuccess.boundaryCarrier.2
  have hpre :=
    BirthPhaseWait2Transfer.boundary_outgoing_preCap_destroys_carrier.2.1
  have hboundary :=
    BirthPhaseB3DirtySuccess.boundary_word_classification.2.2.1
  have hdestroy :=
    BirthPhaseWait2Transfer.boundary_outgoing_preCap_destroys_carrier.2.2.2
  have hstep := BirthPhaseWait2BlockProgress.hostStep_eq_currentStep2
    hpsi2 h2
    BirthPhaseWait2Transfer.boundaryRing4
    BirthPhaseWait2Transfer.boundaryConfig4
    BirthPhaseWait2Transfer.boundaryEdge4
  rw [hstep] at hdestroy
  have hbreak :
      ¬ BirthPhaseWait2BlockProgress.LocalCarrier
        hpsi2 h2 hn4
        BirthPhaseWait2Transfer.boundaryRing4
        BirthPhaseWait2Transfer.boundaryAnchor4
        (BirthPhaseWait2BlockProgress.currentStep2
          hpsi2 h2
          BirthPhaseWait2Transfer.boundaryRing4
          BirthPhaseWait2Transfer.boundaryConfig4
          BirthPhaseWait2Transfer.boundaryEdge4) := by
    exact hdestroy
  have hcount :=
    BirthPhaseB3DirtySuccess.boundary_word_classification.2.2.2
  have hsub0 := BirthPhaseB3DirtySuccess.boundaryCarrier.2.2
  have hsub :
      BirthPhaseWait2BlockProgress.shortCountAt
          BirthPhaseWait2Transfer.boundaryRing4
          BirthPhaseWait2Transfer.boundaryAnchor4
          (BirthPhaseWait2BlockProgress.currentStep2
            hpsi2 h2
            BirthPhaseWait2Transfer.boundaryRing4
            BirthPhaseWait2Transfer.boundaryConfig4
            BirthPhaseWait2Transfer.boundaryEdge4) < 2 := by
    rw [<- hcount]
    exact hsub0
  exact ⟨hC, hpre, hboundary, hbreak, hsub⟩

theorem boundaryCounterWord_length :
    boundaryCounterWord.length =
      BirthPhaseWait2BlockProgress.L 4 := by
  decide

theorem boundaryCounterWord_boundaryCase :
    BirthPhaseB3BridgeStageA.BoundaryCaseWithin
      hpsi2 h2 hn4 2 3
      BirthPhaseWait2Transfer.boundaryRing4
      BirthPhaseWait2Transfer.boundaryAnchor4
      BirthPhaseWait2Transfer.boundaryConfig4
      boundaryCounterWord := by
  refine ⟨[], BirthPhaseWait2Transfer.boundaryEdge4,
    List.replicate 23 padEdge4, ?_, ?_⟩
  · simp [boundaryCounterWord]
  · simpa using boundaryBreakRow_fixture

private instance instDecidableRowCap2B3ReacquireSide
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n)
    (C : FC n psi kappa tau) (e : Fin n) :
    Decidable (BirthShortDoneTerminalPassiveR4.RowCap2
      hpsi h2 kappa ring C e) := by
  unfold BirthShortDoneTerminalPassiveR4.RowCap2
  dsimp only
  infer_instance

private instance instDecidableNoCapAlongLocal
    (hpsi : 0 < psi) (h2 : 2 <= psi) (kappa : Nat)
    (ring : DirectedRing n)
    (C : FC n psi kappa tau) (u : List (Fin n)) :
    Decidable (NoCapAlong hpsi h2 kappa ring C u) :=
  match u with
  | [] => isTrue trivial
  | e :: es =>
      letI : Decidable
          (NoCapAlong hpsi h2 kappa ring
            (BirthPhaseWait2BlockProgress.currentStep2
              hpsi h2 ring C e) es) :=
        instDecidableNoCapAlongLocal hpsi h2 kappa ring
          (BirthPhaseWait2BlockProgress.currentStep2
            hpsi h2 ring C e) es
      instDecidableAnd

set_option maxHeartbeats 200000000 in
set_option maxRecDepth 131072 in
/-- Ground evaluation of all 24 literal current-consumer rows. -/
theorem boundaryCounterWord_noCap :
    NoCapAlong hpsi2 h2 2
      BirthPhaseWait2Transfer.boundaryRing4
      BirthPhaseWait2Transfer.boundaryConfig4
      boundaryCounterWord := by
  decide

set_option maxHeartbeats 200000000 in
set_option maxRecDepth 131072 in
/-- Both scheduled edges, 2 and 3, avoid the tracked site 1; the concrete
execution leaves its count unchanged. -/
theorem boundaryCounterWord_count_eq :
    BirthPhaseWait2BlockProgress.shortCountAt
        BirthPhaseWait2Transfer.boundaryRing4
        BirthPhaseWait2Transfer.boundaryAnchor4
        BirthPhaseWait2Transfer.boundaryConfig4 =
      BirthPhaseWait2BlockProgress.shortCountAt
        BirthPhaseWait2Transfer.boundaryRing4
        BirthPhaseWait2Transfer.boundaryAnchor4
        (BirthPhaseGenericRenewal.rawEndpoint
          (BirthPhaseWait2BlockProgress.currentStep2
            hpsi2 h2 BirthPhaseWait2Transfer.boundaryRing4)
          BirthPhaseWait2Transfer.boundaryConfig4
          boundaryCounterWord) := by
  decide

theorem boundaryCounterWord_target_false :
    BirthPhaseWait2BlockProgress.target
      hpsi2 h2 2 BirthPhaseWait2Transfer.boundaryRing4
      BirthPhaseWait2Transfer.boundaryConfig4
      boundaryCounterWord = false := by
  exact (target_false_iff_noCapAlong
    hpsi2 h2 2 BirthPhaseWait2Transfer.boundaryRing4
    BirthPhaseWait2Transfer.boundaryConfig4
    boundaryCounterWord).2 boundaryCounterWord_noCap

/-- Literal refutation of Stage A's unconditional boundary-suffix proposal. -/
theorem boundaryCaseResolvesBridge_counterexample :
    ¬ BirthPhaseB3BridgeStageA.BoundaryCaseResolvesBridge
      hpsi2 h2 hn4 2 3
      BirthPhaseWait2Transfer.boundaryRing4
      BirthPhaseWait2Transfer.boundaryAnchor4
      BirthPhaseWait2Transfer.boundaryConfig4 := by
  intro h
  have hout := h boundaryCounterWord
    boundaryCounterWord_length boundaryCounterWord_boundaryCase
  rcases hout with ht | hp
  · rw [boundaryCounterWord_target_false] at ht
    cases ht
  · have hbad := hp
    rw [<- boundaryCounterWord_count_eq] at hbad
    exact Nat.lt_irrefl _ hbad

/-! ## A block which starts in Reacquire need not resolve either -/

theorem boundarySuccessor_is_reacquire :
    BirthPhaseWait2BlockProgress.Reacquire
      hpsi2 h2 hn4 2 3
      BirthPhaseWait2Transfer.boundaryRing4
      BirthPhaseWait2Transfer.boundaryAnchor4
      boundarySuccessor := by
  simpa [boundarySuccessor] using
    BirthPhaseB3BridgeStageA.boundary_fixture_successor_is_reacquire

theorem reacquireCounterWord_length :
    reacquireCounterWord.length =
      BirthPhaseWait2BlockProgress.L 4 := by
  decide

set_option maxHeartbeats 200000000 in
set_option maxRecDepth 131072 in
theorem reacquireCounterWord_noCap :
    NoCapAlong hpsi2 h2 2
      BirthPhaseWait2Transfer.boundaryRing4
      boundarySuccessor reacquireCounterWord := by
  decide

set_option maxHeartbeats 200000000 in
set_option maxRecDepth 131072 in
theorem reacquireCounterWord_count_eq :
    BirthPhaseWait2BlockProgress.shortCountAt
        BirthPhaseWait2Transfer.boundaryRing4
        BirthPhaseWait2Transfer.boundaryAnchor4
        boundarySuccessor =
      BirthPhaseWait2BlockProgress.shortCountAt
        BirthPhaseWait2Transfer.boundaryRing4
        BirthPhaseWait2Transfer.boundaryAnchor4
        (BirthPhaseGenericRenewal.rawEndpoint
          (BirthPhaseWait2BlockProgress.currentStep2
            hpsi2 h2 BirthPhaseWait2Transfer.boundaryRing4)
          boundarySuccessor reacquireCounterWord) := by
  decide

theorem reacquireCounterWord_target_false :
    BirthPhaseWait2BlockProgress.target
      hpsi2 h2 2 BirthPhaseWait2Transfer.boundaryRing4
      boundarySuccessor reacquireCounterWord = false := by
  exact (target_false_iff_noCapAlong
    hpsi2 h2 2 BirthPhaseWait2Transfer.boundaryRing4
    boundarySuccessor reacquireCounterWord).2
      reacquireCounterWord_noCap

/-- Relation-free version of the proposed “a Reacquire block resolves within
this same block” claim. -/
def ReacquireBlockResolves
    (hpsi : 0 < psi) (h2 : 2 <= psi)
    (kappa : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (C : FC n psi kappa tau) : Prop :=
  forall u : List (Fin n),
    u.length = BirthPhaseWait2BlockProgress.L n ->
      BirthPhaseWait2BlockProgress.target
          hpsi h2 kappa ring C u = true \/
        BirthPhaseWait2BlockProgress.shortCountAt ring anchor C <
          BirthPhaseWait2BlockProgress.shortCountAt ring anchor
            (BirthPhaseGenericRenewal.rawEndpoint
              (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring)
              C u)

/-- The public Reacquire successor is real, but a whole literal `L 4` block
can still have neither cap nor tracked progress. -/
theorem reacquireBlockResolves_counterexample :
    BirthPhaseWait2BlockProgress.Reacquire
        hpsi2 h2 hn4 2 3
        BirthPhaseWait2Transfer.boundaryRing4
        BirthPhaseWait2Transfer.boundaryAnchor4
        boundarySuccessor /\
      ¬ ReacquireBlockResolves
        hpsi2 h2 2
        BirthPhaseWait2Transfer.boundaryRing4
        BirthPhaseWait2Transfer.boundaryAnchor4
        boundarySuccessor := by
  refine ⟨boundarySuccessor_is_reacquire, ?_⟩
  intro h
  have hout := h reacquireCounterWord reacquireCounterWord_length
  rcases hout with ht | hp
  · rw [reacquireCounterWord_target_false] at ht
    cases ht
  · have hbad := hp
    rw [<- reacquireCounterWord_count_eq] at hbad
    exact Nat.lt_irrefl _ hbad

/-- A decidable-in-spirit literal success relation selecting the bad word.
No configuration equality is used: the relation is only a word predicate. -/
def CounterDirty :
    BirthPhaseWait2BlockProgress.DirtySuccessRel 4 2 2 3 :=
  fun _ u => u = reacquireCounterWord

/-- `ReacquireStartBridge` is relation-dependent.  For a relation which marks
this literal word successful, it is false.  Taking the relation `False` would
instead make it vacuous; hence no protocol-only theorem can inhabit the Stage-A
name without first specifying the B1 success event. -/
theorem reacquireStartBridge_counterexample :
    ¬ BirthPhaseB3BridgeStageA.ReacquireStartBridge
      hpsi2 h2 hn4 2 3
      BirthPhaseWait2Transfer.boundaryRing4
      BirthPhaseWait2Transfer.boundaryAnchor4
      CounterDirty := by
  intro h
  have hout := h boundarySuccessor boundarySuccessor_is_reacquire
    reacquireCounterWord reacquireCounterWord_length (by rfl)
  rcases hout with ht | hp
  · rw [reacquireCounterWord_target_false] at ht
    cases ht
  · have hbad := hp
    rw [<- reacquireCounterWord_count_eq] at hbad
    exact Nat.lt_irrefl _ hbad

/-! ## Correct horizon-preserving Stage-B2 interfaces -/

/-- The universal Stage-A boundary condition was stronger than B3 needs.
Only a boundary occurrence on a word which is actually in the Carrier success
event has to resolve. -/
def BoundaryDirtyCaseResolvesBridge
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (DirtySuccess :
      BirthPhaseWait2BlockProgress.DirtySuccessRel n psi kappa tau) : Prop :=
  forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Carrier
        hpsi h2 hn ring anchor C ->
    forall u : List (Fin n),
      u.length = BirthPhaseWait2BlockProgress.L n ->
      DirtySuccess C u ->
      BirthPhaseB3BridgeStageA.BoundaryCaseWithin
          hpsi h2 hn kappa tau ring anchor C u ->
        BirthPhaseWait2BlockProgress.target
            hpsi h2 kappa ring C u = true \/
          BirthPhaseWait2BlockProgress.shortCountAt ring anchor C <
            BirthPhaseWait2BlockProgress.shortCountAt ring anchor
              (BirthPhaseGenericRenewal.rawEndpoint
                (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring)
                C u)

/-- Separate B1 event for starts which are already in Reacquire.  Keeping the
same `L` and requiring the same final two outcomes lets this branch feed the
existing `B3DirtySuccessBridge` without changing B5's horizon. -/
def ReacquirePhaseBridge
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (ReacquireSuccess :
      BirthPhaseWait2BlockProgress.DirtySuccessRel n psi kappa tau) : Prop :=
  forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor C ->
    forall u : List (Fin n),
      u.length = BirthPhaseWait2BlockProgress.L n ->
      ReacquireSuccess C u ->
        BirthPhaseWait2BlockProgress.target
            hpsi h2 kappa ring C u = true \/
          BirthPhaseWait2BlockProgress.shortCountAt ring anchor C <
            BirthPhaseWait2BlockProgress.shortCountAt ring anchor
              (BirthPhaseGenericRenewal.rawEndpoint
                (BirthPhaseWait2BlockProgress.currentStep2 hpsi h2 ring)
                C u)

/-- The Reacquire branch must have the same 1/Q source mass if the current
B4/B5 horizon is to remain literally unchanged. -/
def ReacquirePhaseMass
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (ReacquireSuccess :
      BirthPhaseWait2BlockProgress.DirtySuccessRel n psi kappa tau)
    [hdec : forall C u, Decidable (ReacquireSuccess C u)] : Prop :=
  forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor C ->
      n ^ BirthPhaseWait2BlockProgress.L n <=
        BirthPhaseWait2BlockProgress.Q *
          FixedSpanRenewalPayload.wordSum n
            (BirthPhaseWait2BlockProgress.L n)
            (fun u => if ReacquireSuccess C u then 1 else 0)

/-- Exact spelling of the Stage-A source gap. -/
theorem reacquireSourceMass_exact
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (DirtySuccess :
      BirthPhaseWait2BlockProgress.DirtySuccessRel n psi kappa tau)
    [hdec : forall C u, Decidable (DirtySuccess C u)] :
    BirthPhaseB3BridgeStageA.ReacquireSourceMass
        hpsi h2 hn kappa tau ring anchor DirtySuccess <->
      (forall C : FC n psi kappa tau,
        BirthPhaseWait2BlockProgress.Reacquire
            hpsi h2 hn kappa tau ring anchor C ->
          n ^ BirthPhaseWait2BlockProgress.L n <=
            BirthPhaseWait2BlockProgress.Q *
              FixedSpanRenewalPayload.wordSum n
                (BirthPhaseWait2BlockProgress.L n)
                (fun u => if DirtySuccess C u then 1 else 0)) := by
  rfl

#print axioms BirthPhaseB3ReacquireSide.boundaryCounterWord_length
#print axioms BirthPhaseB3ReacquireSide.boundaryCounterWord_boundaryCase
#print axioms BirthPhaseB3ReacquireSide.boundaryCounterWord_noCap
#print axioms BirthPhaseB3ReacquireSide.boundaryCounterWord_count_eq
#print axioms BirthPhaseB3ReacquireSide.boundaryCaseResolvesBridge_counterexample
#print axioms BirthPhaseB3ReacquireSide.boundarySuccessor_is_reacquire
#print axioms BirthPhaseB3ReacquireSide.reacquireCounterWord_noCap
#print axioms BirthPhaseB3ReacquireSide.reacquireCounterWord_count_eq
#print axioms BirthPhaseB3ReacquireSide.reacquireBlockResolves_counterexample
#print axioms BirthPhaseB3ReacquireSide.reacquireStartBridge_counterexample
#print axioms BirthPhaseB3ReacquireSide.reacquireSourceMass_exact

end BirthPhaseB3ReacquireSide
