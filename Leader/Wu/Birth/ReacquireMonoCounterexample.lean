import Leader.Wu.Birth.ControlledReacquireContract


/-!
# B4 Reacquire Mono counterexample


This file is the executable/fixture half of the B4 Mono decision.  It keeps the
four public counterexample statements from `BirthB4ReacquireMonoDecision` but
contains no `decide` over whole configurations or scheduler runs.  Closed local
facts are reduced one row/field at a time; the long padding suffix is symbolic
induction from a one-row fixed point.
-/


set_option autoImplicit false
set_option Elab.async false
set_option pp.structureInstances false


namespace BirthB4ReacquireMonoDecision


open PPLL PPLLRepair PPLLDomain PPLLResearchFormulation
  PPLLExpiringComparisonRepair
open BirthWaitPassive
open BirthShortDoneTerminalPassiveR4
open BirthShortDoneTerminalPassiveLocal3
open BirthShortDoneTerminalPassiveLocal3Rotation
open BirthB1ReacquireReentryMass


private theorem hpsi2 : 0 < 2 := by decide
private theorem h2 : 2 <= 2 := by decide
private theorem hn4 : 4 <= 4 := by decide


private def ring4 : DirectedRing 4 := ⟨by decide⟩
private def anchor4 : Fin 4 := 0
private def boundaryEdge4 : Fin 4 := 2
private def padEdge4 : Fin 4 := 3


private theorem right0 :
    ring4.rightNeighbor anchor4 = (1 : Fin 4) := by decide
private theorem right1 :
    ring4.rightNeighbor (ring4.rightNeighbor anchor4) = (2 : Fin 4) := by decide


private def regs (label : Fin 2) (count : Nat) : Registers 2 where
  label := label
  h := false
  carry := false
  reset := false
  count := count
  wait := true
  bit := false
  phase := false
  writer := .none


private def sourceRaw (i : Fin 4) : AgentState 2 :=
  if i = 0 then cell (regs 0 0)
  else if i = 1 then cell (regs 1 1)
  else if i = 2 then cell (regs 0 0)
  else { cell (regs 1 0) with reset_cmd := true }


private theorem sourceRaw_domain (i : Fin 4) :
    (sourceRaw i).inProtocolDomain 2 := by
  have hi : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;>
    simp [sourceRaw, regs, AgentState.inProtocolDomain, cell]


private def sourcePack (i : Fin 4) : ExpiringAgentState 2 2 0 :=
  ⟨⟨BoundedAgentState.ofDomain
      (sourceRaw i) (sourceRaw_domain i), false⟩, 0⟩


private def sourceC : FC 4 2 2 0 := fun i => sourcePack i


@[simp] private theorem raw_sourceC (i : Fin 4) :
    raw (sourceC i) = sourceRaw i := by
  simp [sourceC, sourcePack, raw, BoundedAgentState.erase_ofDomain]


private instance instDecidableRowCap2Fixture
    (C : FC 4 2 2 0) (e : Fin 4) :
    Decidable (RowCap2 hpsi2 h2 2 ring4 C e) := by
  unfold RowCap2
  dsimp only
  infer_instance


private instance instDecidableRowPreCap2Fixture
    (C : FC 4 2 2 0) (e : Fin 4) :
    Decidable (RowPreCap2 hpsi2 h2 2 ring4 C e) := by
  unfold RowPreCap2
  infer_instance


/-- Off-pair sites are framed without evaluating the host row. -/
private theorem currentStep2_other
    (C : FC 4 2 2 0) (e i : Fin 4)
    (hi : i != e) (hj : i != ring4.rightNeighbor e) :
    BirthPhaseWait2BlockProgress.currentStep2
        hpsi2 h2 ring4 C e i = C i := by
  simpa only [BirthPhaseWait2BlockProgress.currentStep2] using
    (BirthShortDoneTerminalConsumer.step_other
      hpsi2 hpsi2 h2 ring4 C e i (by simpa using hi) (by simpa using hj))


private theorem source_count :
    BirthPhaseWait2BlockProgress.shortCountAt
      ring4 anchor4 sourceC = 1 := by
  unfold BirthPhaseWait2BlockProgress.shortCountAt
  rw [right0]
  change (raw (sourceC (1 : Fin 4))).count = 1
  rw [raw_sourceC]
  rfl


private theorem source_carrier :
    BirthPhaseWait2BlockProgress.Carrier
      hpsi2 h2 hn4 ring4 anchor4 sourceC := by
  unfold BirthPhaseWait2BlockProgress.Carrier
    BirthPhaseWait2BlockProgress.LocalCarrier
    BirthPhaseWait2Transfer.LocalWait2Carrier
  constructor
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
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
    omega


private theorem source_boundary_preCap :
    RowPreCap2 hpsi2 h2 2 ring4 sourceC boundaryEdge4 := by
  decide +kernel


private theorem source_boundary :
    BirthPhaseWait2Transfer.LocalWait2BoundaryNow
      hn4 ring4 anchor4 boundaryEdge4 := by
  unfold BirthPhaseWait2Transfer.LocalWait2BoundaryNow
    SafeLine3EdgeAt SafeLine3Edge
  decide


private def afterBoundary : FC 4 2 2 0 :=
  BirthPhaseWait2BlockProgress.currentStep2
    hpsi2 h2 ring4 sourceC boundaryEdge4


/-- This is a single boundary-host-row field reduction.  The edge-2 pair is
exactly the already-used `(label 0, label 1 with reset_cmd)` pair. -/
private theorem afterBoundary_tail_echo :
    (raw (afterBoundary (2 : Fin 4))).echo = true := by
  decide +kernel


private theorem afterBoundary_site1 :
    afterBoundary (1 : Fin 4) = sourceC (1 : Fin 4) := by
  apply currentStep2_other <;> decide


/-- The tail letter 3 moves the outside reset to anchor zero. -/
def badStart : FC 4 2 2 0 :=
  BirthPhaseWait2BlockProgress.currentStep2
    hpsi2 h2 ring4 afterBoundary padEdge4


private theorem badStart_site1 :
    badStart (1 : Fin 4) = afterBoundary (1 : Fin 4) := by
  apply currentStep2_other <;> decide


private theorem badStart_site2 :
    badStart (2 : Fin 4) = afterBoundary (2 : Fin 4) := by
  apply currentStep2_other <;> decide


private theorem badStart_tail_echo :
    (raw (badStart (2 : Fin 4))).echo = true := by
  rw [badStart_site2]
  exact afterBoundary_tail_echo


private theorem badStart_count :
    BirthPhaseWait2BlockProgress.shortCountAt
      ring4 anchor4 badStart = 1 := by
  unfold BirthPhaseWait2BlockProgress.shortCountAt
  rw [right0, badStart_site1, afterBoundary_site1]
  change (raw (sourceC (1 : Fin 4))).count = 1
  rw [raw_sourceC]
  rfl


theorem badStart_is_reacquire :
    BirthPhaseWait2BlockProgress.Reacquire
      hpsi2 h2 hn4 2 0 ring4 anchor4 badStart := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨sourceC, boundaryEdge4, [padEdge4], source_carrier,
      source_boundary_preCap, source_boundary, rfl⟩
  · intro hlocal
    unfold BirthPhaseWait2BlockProgress.LocalCarrier
      BirthPhaseWait2Transfer.LocalWait2Carrier at hlocal
    have hm := hlocal.pass2.1
    rw [right1] at hm
    unfold Metadata at hm
    have he := congrArg AgentState.echo hm
    change (raw (badStart (2 : Fin 4))).echo = false at he
    rw [badStart_tail_echo] at he
    cases he
  · rw [badStart_count]
    omega


private def afterReset : FC 4 2 2 0 :=
  BirthPhaseWait2BlockProgress.currentStep2
    hpsi2 h2 ring4 badStart anchor4


private theorem badStart_preCap :
    RowPreCap2 hpsi2 h2 2 ring4 badStart anchor4 := by
  decide +kernel


/-- The only bad-row computation: one scheduled host row, projected to the
tracked responder count. -/
private theorem afterReset_count :
    BirthPhaseWait2BlockProgress.shortCountAt
      ring4 anchor4 afterReset = 0 := by
  decide +kernel


/-- Smallest bad row: it is pre-cap, yet SUPPRESS sends tracked count 1 to 0. -/
theorem first_bad_row_decide :
    RowPreCap2 hpsi2 h2 2 ring4 badStart anchor4 /\
    BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor4 badStart = 1 /\
    BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor4 afterReset = 0 /\
    BirthPhaseWait2BlockProgress.rank 2 ring4 anchor4 badStart = 2 /\
    BirthPhaseWait2BlockProgress.rank 2 ring4 anchor4 afterReset = 3 := by
  refine ⟨badStart_preCap, badStart_count, afterReset_count, ?_, ?_⟩
  · unfold BirthPhaseWait2BlockProgress.rank
    rw [badStart_count]
  · unfold BirthPhaseWait2BlockProgress.rank
    rw [afterReset_count]


/-- Literal cap-freeness at every prefix of a concrete scheduler word. -/
def NoCapAlong (C : FC 4 2 2 0) : List (Fin 4) -> Prop
  | [] => True
  | e :: es =>
      RowPreCap2 hpsi2 h2 2 ring4 C e /\
      NoCapAlong
        (BirthPhaseWait2BlockProgress.currentStep2 hpsi2 h2 ring4 C e) es


/-- One step of `NoCapAlong`, stated at a variable configuration so that
callers rewrite instead of unfolding a concrete state. -/
private theorem noCapAlong_cons (C : FC 4 2 2 0) (e : Fin 4)
    (es : List (Fin 4)) :
    NoCapAlong C (e :: es) =
      (RowPreCap2 hpsi2 h2 2 ring4 C e /\
        NoCapAlong
          (BirthPhaseWait2BlockProgress.currentStep2 hpsi2 h2 ring4 C e) es) :=
  rfl

/-- One step of `prefixEndpoint`, at a variable configuration. -/
private theorem prefixEndpoint_cons (C : FC 4 2 2 0) (e : Fin 4)
    (u : List (Fin 4)) :
    prefixEndpoint hpsi2 h2 ring4 C (e :: u) =
      prefixEndpoint hpsi2 h2 ring4
        (BirthPhaseWait2BlockProgress.currentStep2 hpsi2 h2 ring4 C e) u :=
  rfl

/-- The tracked count reads only site 1. -/
private theorem shortCountAt_of_site (C D : FC 4 2 2 0) (h : C 1 = D 1) :
    BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor4 C =
      BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor4 D := by
  unfold BirthPhaseWait2BlockProgress.shortCountAt
  rw [right0, h]

private theorem afterReset_eq :
    BirthPhaseWait2BlockProgress.currentStep2 hpsi2 h2 ring4 badStart anchor4 =
      afterReset :=
  rfl

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
      change RowPreCap2 hpsi2 h2 2 ring4 C e /\
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


private def padState : FC 4 2 2 0 :=
  BirthPhaseWait2BlockProgress.currentStep2
    hpsi2 h2 ring4 afterReset padEdge4


private theorem afterReset_pad_preCap :
    RowPreCap2 hpsi2 h2 2 ring4 afterReset padEdge4 := by
  decide +kernel


private theorem padState_eq :
    BirthPhaseWait2BlockProgress.currentStep2 hpsi2 h2 ring4 afterReset padEdge4 =
      padState :=
  rfl

private theorem padState_preCap :
    RowPreCap2 hpsi2 h2 2 ring4 padState padEdge4 := by
  decide +kernel


private theorem padState_site1 :
    padState (1 : Fin 4) = afterReset (1 : Fin 4) := by
  apply currentStep2_other <;> decide


private theorem padState_count :
    BirthPhaseWait2BlockProgress.shortCountAt
      ring4 anchor4 padState = 0 := by
  rw [shortCountAt_of_site padState afterReset padState_site1]
  exact afterReset_count


/-- Pointwise fixed-state certificate: only the two edge-3 endpoints are
computed, each by one local row equality; sites 1 and 2 use scheduler framing. -/
private theorem padState_fixed :
    BirthPhaseWait2BlockProgress.currentStep2
      hpsi2 h2 ring4 padState padEdge4 = padState := by
  funext i
  have hi : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl
  · decide +kernel
  · apply currentStep2_other <;> decide
  · apply currentStep2_other <;> decide
  · decide +kernel


private theorem padTail_noCap (m : Nat) :
    NoCapAlong padState (List.replicate m padEdge4) := by
  induction m with
  | zero => trivial
  | succ m ih =>
      rw [List.replicate_succ, noCapAlong_cons, padState_fixed]
      exact ⟨padState_preCap, ih⟩


private theorem padTail_endpoint (m : Nat) :
    prefixEndpoint hpsi2 h2 ring4 padState
      (List.replicate m padEdge4) = padState := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [List.replicate_succ, prefixEndpoint_cons, padState_fixed]
      exact ih


/-- Full fallback block: the first row drops the tracked count, the second
enters the fixed padding state, and the rest are harmless edge-3 rows. -/
def badWord : List (Fin 4) :=
  anchor4 :: padEdge4 ::
    List.replicate (fallbackReacquireL 4 - 2) padEdge4


theorem badWord_length : badWord.length = fallbackReacquireL 4 := by
  unfold badWord
  rw [List.length_cons, List.length_cons, List.length_replicate,
    BirthB1ReacquirePhaseMass.fallbackReacquireL_four]


/-- Full-length certificate; the 254-row tail is never kernel-evaluated. -/
theorem badWord_decide :
    NoCapAlong badStart badWord /\
    BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor4
      (prefixEndpoint hpsi2 h2 ring4 badStart badWord) = 0 := by
  constructor
  · unfold badWord
    rw [noCapAlong_cons, noCapAlong_cons, afterReset_eq, padState_eq]
    exact ⟨badStart_preCap, afterReset_pad_preCap,
      padTail_noCap (fallbackReacquireL 4 - 2)⟩
  · unfold badWord
    rw [prefixEndpoint_cons, prefixEndpoint_cons, afterReset_eq, padState_eq,
      padTail_endpoint]
    exact padState_count


theorem badWord_target_free :
    BirthPhaseWait2BlockProgress.target
      hpsi2 h2 2 ring4 badStart badWord = false :=
  target_false_of_noCapAlong badStart badWord badWord_decide.1


theorem badWord_rank_increase :
    BirthPhaseWait2BlockProgress.rank 2 ring4 anchor4 badStart <
      BirthPhaseWait2BlockProgress.rank 2 ring4 anchor4
        (prefixEndpoint hpsi2 h2 ring4 badStart badWord) := by
  unfold BirthPhaseWait2BlockProgress.rank
  rw [badStart_count, badWord_decide.2]
  omega


/-- The broad two-phase Reacquire Mono clause is therefore literally false. -/
theorem fallbackReacquireMono_false :
    ¬ FallbackReacquireMono hpsi2 h2 hn4 2 0 ring4 anchor4 := by
  intro hmono
  unfold FallbackReacquireMono at hmono
  have hle := hmono badStart badStart_is_reacquire
    badWord badWord_length badWord_target_free
  exact (Nat.not_le_of_lt badWord_rank_increase) hle


end BirthB4ReacquireMonoDecision


#print axioms BirthB4ReacquireMonoDecision.badStart_is_reacquire
#print axioms BirthB4ReacquireMonoDecision.first_bad_row_decide
#print axioms BirthB4ReacquireMonoDecision.badWord_decide
#print axioms BirthB4ReacquireMonoDecision.fallbackReacquireMono_false
