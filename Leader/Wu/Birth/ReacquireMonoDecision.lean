import Leader.Wu.Birth.ReacquirePhaseMass

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

variable {n psi kappa tau : Nat}

abbrev FC (n psi kappa tau : Nat) :=
  BirthPhaseWait2BlockProgress.FC n psi kappa tau

private theorem hpsi2 : 0 < 2 := by decide
private theorem h2 : 2 <= 2 := by decide
private theorem hn4 : 4 <= 4 := by decide

private def ring4 : DirectedRing 4 := ⟨by decide⟩
private def anchor4 : Fin 4 := 0
private def boundaryEdge4 : Fin 4 := 2
private def padEdge4 : Fin 4 := 3

private theorem right0 :
    ring4.rightNeighbor anchor4 = (1 : Fin 4) := by
  decide

private theorem right1 :
    ring4.rightNeighbor (ring4.rightNeighbor anchor4) = (2 : Fin 4) := by
  decide

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
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;>
    simp [sourceRaw, regs, AgentState.inProtocolDomain, cell]

private def sourcePack (i : Fin 4) : ExpiringAgentState 2 2 0 :=
  ⟨⟨BoundedAgentState.ofDomain (sourceRaw i) (sourceRaw_domain i), false⟩, 0⟩

private def sourceC : FC 4 2 2 0 := fun i => sourcePack i

@[simp] private theorem raw_sourceC (i : Fin 4) :
    raw (sourceC i) = sourceRaw i := by
  simp [sourceC, sourcePack, raw, BoundedAgentState.erase_ofDomain]

/-- Off-pair sites are framed without evaluating the host row. -/
private theorem currentStep2_other (C : FC 4 2 2 0) (e i : Fin 4)
    (hi : i ≠ e) (hj : i ≠ ring4.rightNeighbor e) :
    BirthPhaseWait2BlockProgress.currentStep2 hpsi2 h2 ring4 C e i = C i :=
  BirthShortDoneTerminalConsumer.step_other hpsi2 (by decide) h2 ring4 C e i hi hj

/-- The tracked count read at a variable configuration: site 1. -/
private theorem shortCountAt_eq (C : FC 4 2 2 0) :
    BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor4 C =
      (C 1).core.core.count.val := by
  unfold BirthPhaseWait2BlockProgress.shortCountAt
  rw [right0]

private theorem source_count :
    BirthPhaseWait2BlockProgress.shortCountAt
      ring4 anchor4 sourceC = 1 := by
  decide

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

private def afterBoundary : FC 4 2 2 0 :=
  BirthPhaseWait2BlockProgress.currentStep2
    hpsi2 h2 ring4 sourceC boundaryEdge4

/-- The tail letter 3 moves the outside reset to anchor zero. -/
def badStart : FC 4 2 2 0 :=
  BirthPhaseWait2BlockProgress.currentStep2
    hpsi2 h2 ring4 afterBoundary padEdge4

private theorem badStart_anchor_reset_cmd :
    (badStart anchor4).core.erase.core.reset_cmd = true := by
  decide +kernel

/-- Edges 2 and 3 do not touch the tracked site 1. -/
private theorem badStart_site1 : badStart 1 = sourceC 1 := by
  unfold badStart afterBoundary
  rw [currentStep2_other _ _ _ (by decide) (by decide),
    currentStep2_other _ _ _ (by decide) (by decide)]

private theorem badStart_count :
    BirthPhaseWait2BlockProgress.shortCountAt
      ring4 anchor4 badStart = 1 := by
  rw [shortCountAt_eq, badStart_site1, ← shortCountAt_eq]
  exact source_count

theorem badStart_is_reacquire :
    BirthPhaseWait2BlockProgress.Reacquire
      hpsi2 h2 hn4 2 0 ring4 anchor4 badStart := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨sourceC, boundaryEdge4, [padEdge4], source_carrier,
      source_boundary_preCap, source_boundary, rfl⟩
  · intro hlocal
    unfold BirthPhaseWait2BlockProgress.LocalCarrier
      BirthPhaseWait2Transfer.LocalWait2Carrier at hlocal
    have hm := hlocal.pass0.1
    unfold Metadata at hm
    have hz := congrArg AgentState.reset_cmd hm
    change (badStart anchor4).core.erase.core.reset_cmd = false at hz
    rw [badStart_anchor_reset_cmd] at hz
    cases hz
  · rw [badStart_count]
    decide

private def afterReset : FC 4 2 2 0 :=
  BirthPhaseWait2BlockProgress.currentStep2
    hpsi2 h2 ring4 badStart anchor4

private theorem badStart_preCap :
    RowPreCap2 hpsi2 h2 2 ring4 badStart anchor4 := by
  unfold RowPreCap2 RowCap2
  decide +kernel

private theorem afterReset_count :
    BirthPhaseWait2BlockProgress.shortCountAt
      ring4 anchor4 afterReset = 0 := by
  decide +kernel

/-- `rank` unfolded once at a variable configuration.  Unfolding it on a
concrete configuration instead (`unfold rank`) leaves the kernel to check
`2 + 1 - count C` against `rank C` by definitional unfolding, and its `Nat.sub`
literal reduction then evaluates `count C`; on the 256-row endpoint that is
the whole run (about 20 s of kernel time). -/
private theorem rank_eq (C : FC 4 2 2 0) :
    BirthPhaseWait2BlockProgress.rank 2 ring4 anchor4 C =
      2 + 1 - BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor4 C := rfl

/-- Smallest bad row: it is pre-cap, yet SUPPRESS sends tracked count 1 to 0. -/
theorem first_bad_row_decide :
    RowPreCap2 hpsi2 h2 2 ring4 badStart anchor4 ∧
    BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor4 badStart = 1 ∧
    BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor4 afterReset = 0 ∧
    BirthPhaseWait2BlockProgress.rank 2 ring4 anchor4 badStart = 2 ∧
    BirthPhaseWait2BlockProgress.rank 2 ring4 anchor4 afterReset = 3 := by
  refine ⟨badStart_preCap, badStart_count, afterReset_count, ?_, ?_⟩
  · rw [rank_eq, badStart_count]
  · rw [rank_eq, afterReset_count]

/-- Literal cap-freeness of every prefix of a concrete scheduler word. -/
def NoCapAlong (C : FC 4 2 2 0) : List (Fin 4) -> Prop
  | [] => True
  | e :: es =>
      RowPreCap2 hpsi2 h2 2 ring4 C e ∧
      NoCapAlong
        (BirthPhaseWait2BlockProgress.currentStep2 hpsi2 h2 ring4 C e) es

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

/-- One harmless edge-3 row after the reset parks the full configuration in a
literal fixed padding state.  The tracked site is not an endpoint of edge 3. -/
private def padState : FC 4 2 2 0 :=
  BirthPhaseWait2BlockProgress.currentStep2
    hpsi2 h2 ring4 afterReset padEdge4

/-- Names for the scheduled rows, used by rewriting instead of unfolding. -/
private theorem afterReset_eq :
    BirthPhaseWait2BlockProgress.currentStep2 hpsi2 h2 ring4 badStart anchor4 =
      afterReset := rfl

private theorem padState_eq :
    BirthPhaseWait2BlockProgress.currentStep2 hpsi2 h2 ring4 afterReset padEdge4 =
      padState := rfl

private theorem afterReset_pad_preCap :
    RowPreCap2 hpsi2 h2 2 ring4 afterReset padEdge4 := by
  unfold RowPreCap2 RowCap2
  decide +kernel

private theorem padState_preCap :
    RowPreCap2 hpsi2 h2 2 ring4 padState padEdge4 := by
  unfold RowPreCap2 RowCap2
  decide +kernel

/-- Edge 3 does not touch the tracked site 1. -/
private theorem padState_site1 : padState 1 = afterReset 1 := by
  unfold padState
  rw [currentStep2_other _ _ _ (by decide) (by decide)]

private theorem padState_count :
    BirthPhaseWait2BlockProgress.shortCountAt
      ring4 anchor4 padState = 0 := by
  rw [shortCountAt_eq, padState_site1, ← shortCountAt_eq]
  exact afterReset_count

private theorem padState_fixed :
    BirthPhaseWait2BlockProgress.currentStep2
      hpsi2 h2 ring4 padState padEdge4 = padState := by
  funext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl
  · decide +kernel
  · exact currentStep2_other _ _ _ (by decide) (by decide)
  · exact currentStep2_other _ _ _ (by decide) (by decide)
  · decide +kernel

private theorem padTail_noCap (m : Nat) :
    NoCapAlong padState (List.replicate m padEdge4) := by
  induction m with
  | zero => trivial
  | succ m ih =>
      rw [List.replicate_succ]
      change RowPreCap2 hpsi2 h2 2 ring4 padState padEdge4 ∧
        NoCapAlong
          (BirthPhaseWait2BlockProgress.currentStep2
            hpsi2 h2 ring4 padState padEdge4)
          (List.replicate m padEdge4)
      rw [padState_fixed]
      exact ⟨padState_preCap, ih⟩

private theorem padTail_endpoint (m : Nat) :
    prefixEndpoint hpsi2 h2 ring4 padState
      (List.replicate m padEdge4) = padState := by
  induction m with
  | zero => rfl
  | succ m ih =>
      unfold prefixEndpoint BirthPhaseGenericRenewal.rawEndpoint at ih ⊢
      rw [List.replicate_succ, List.foldl_cons, padState_fixed]
      exact ih

/-- Full fallback block: the first row drops the tracked count, the second
enters the fixed padding state, and the rest are harmless edge-3 rows. -/
def badWord : List (Fin 4) :=
  anchor4 :: padEdge4 ::
    List.replicate (fallbackReacquireL 4 - 2) padEdge4

theorem badWord_length : badWord.length = fallbackReacquireL 4 := by
  unfold badWord
  simp only [List.length_cons, List.length_replicate,
    BirthB1ReacquirePhaseMass.fallbackReacquireL_four]

/-- Full-length certificate, proved symbolically rather than by reducing 256
complete terminal-host interactions in the kernel. -/
theorem badWord_decide :
    NoCapAlong badStart badWord ∧
    BirthPhaseWait2BlockProgress.shortCountAt ring4 anchor4
      (prefixEndpoint hpsi2 h2 ring4 badStart badWord) = 0 := by
  constructor
  · unfold badWord
    rw [NoCapAlong, NoCapAlong, afterReset_eq, padState_eq]
    exact ⟨badStart_preCap, afterReset_pad_preCap,
      padTail_noCap (fallbackReacquireL 4 - 2)⟩
  · unfold badWord
    have hpad := padTail_endpoint (fallbackReacquireL 4 - 2)
    unfold prefixEndpoint BirthPhaseGenericRenewal.rawEndpoint at hpad ⊢
    rw [List.foldl_cons, List.foldl_cons, afterReset_eq, padState_eq, hpad]
    exact padState_count

theorem badWord_target_free :
    BirthPhaseWait2BlockProgress.target
      hpsi2 h2 2 ring4 badStart badWord = false :=
  target_false_of_noCapAlong badStart badWord badWord_decide.1

theorem badWord_rank_increase :
    BirthPhaseWait2BlockProgress.rank 2 ring4 anchor4 badStart <
      BirthPhaseWait2BlockProgress.rank 2 ring4 anchor4
        (prefixEndpoint hpsi2 h2 ring4 badStart badWord) := by
  rw [rank_eq, rank_eq, badStart_count, badWord_decide.2]
  decide

/-- The broad two-phase Reacquire Mono clause is therefore literally false. -/
theorem fallbackReacquireMono_false :
    ¬ FallbackReacquireMono hpsi2 h2 hn4 2 0 ring4 anchor4 := by
  intro hmono
  unfold FallbackReacquireMono at hmono
  have hle := hmono badStart badStart_is_reacquire
    badWord badWord_length badWord_target_free
  exact (Nat.not_le_of_lt badWord_rank_increase) hle

/-! Cheapest repair: strengthen the Reacquire phase, leaving the rank alone. -/

abbrev controlledEntranceL (n : Nat) : Nat := fallbackReacquireL n
abbrev controlledReacquireL (n : Nat) : Nat :=
  controlledEntranceL n + fallbackReacquireL n
abbrev controlledReacquireQ : Nat := fallbackReacquireQ * fallbackReacquireQ

def ControlledReacquire
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (Controlled : FC n psi kappa tau -> Prop)
    (C : FC n psi kappa tau) : Prop :=
  BirthPhaseWait2BlockProgress.Reacquire
      hpsi h2 hn kappa tau ring anchor C ∧ Controlled C

/-- Replacement Mono clause.  The intended `Controlled` invariant must exclude
exactly the tracked-reset configuration certified above. -/
def ControlledReacquireMono
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (Controlled : FC n psi kappa tau -> Prop) : Prop :=
  forall C : FC n psi kappa tau,
    ControlledReacquire hpsi h2 hn kappa tau ring anchor Controlled C ->
    forall u : List (Fin n),
      u.length = fallbackReacquireL n ->
      BirthPhaseWait2BlockProgress.target hpsi h2 kappa ring C u = false ->
      BirthPhaseWait2BlockProgress.rank kappa ring anchor
          (prefixEndpoint hpsi h2 ring C u) <=
        BirthPhaseWait2BlockProgress.rank kappa ring anchor C

/-- A successful entrance must establish the controlled class without spending
rank.  This is the new B1 entrance target. -/
def ControlledEntranceSuccess
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (Controlled : FC n psi kappa tau -> Prop)
    (C : FC n psi kappa tau) (u : List (Fin n)) : Prop :=
  BirthPhaseWait2BlockProgress.target hpsi h2 kappa ring C u = true ∨
    let D := prefixEndpoint hpsi h2 ring C u
    ControlledReacquire hpsi h2 hn kappa tau ring anchor Controlled D ∧
      BirthPhaseWait2BlockProgress.rank kappa ring anchor D <=
        BirthPhaseWait2BlockProgress.rank kappa ring anchor C

noncomputable def ControlledEntranceBit
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (Controlled : FC n psi kappa tau -> Prop)
    (C : FC n psi kappa tau) (u : List (Fin n)) : Nat :=
  @ite Nat
    (ControlledEntranceSuccess
      hpsi h2 hn kappa tau ring anchor Controlled C u)
    (Classical.propDecidable _) 1 0

/-- Conservative entrance cost: one existing quadratic Reacquire block with
its existing 1/8 mass denominator. -/
def ControlledReacquireEntranceMass
    (hpsi : 0 < psi) (h2 : 2 <= psi) (hn : 4 <= n)
    (kappa tau : Nat) (ring : DirectedRing n) (anchor : Fin n)
    (Controlled : FC n psi kappa tau -> Prop) : Prop :=
  forall C : FC n psi kappa tau,
    BirthPhaseWait2BlockProgress.Reacquire
        hpsi h2 hn kappa tau ring anchor C ->
      n ^ controlledEntranceL n <=
        fallbackReacquireQ *
          FixedSpanRenewalPayload.wordSum n (controlledEntranceL n)
            (ControlledEntranceBit
              hpsi h2 hn kappa tau ring anchor Controlled C)

/-- On the minimum ring the conservative replacement is 256+256 rows and
1/(8*8) mass. -/
theorem controlled_cost_four :
    controlledEntranceL 4 = 256 ∧
      controlledReacquireL 4 = 512 ∧
      controlledReacquireQ = 64 := by
  change fallbackReacquireL 4 = 256 ∧
    fallbackReacquireL 4 + fallbackReacquireL 4 = 512 ∧
    fallbackReacquireQ * fallbackReacquireQ = 64
  rw [BirthB1ReacquirePhaseMass.fallbackReacquireL_four]
  decide

#print axioms BirthB4ReacquireMonoDecision.badStart_is_reacquire
#print axioms BirthB4ReacquireMonoDecision.first_bad_row_decide
#print axioms BirthB4ReacquireMonoDecision.badWord_decide
#print axioms BirthB4ReacquireMonoDecision.fallbackReacquireMono_false
#print axioms BirthB4ReacquireMonoDecision.controlled_cost_four

end BirthB4ReacquireMonoDecision
