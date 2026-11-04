import Leader.Wu.Safety.NoCheckBirthRepair
import Leader.Wu.Safety.ConcreteProtocolProperties

/-!
# Leader-writer accounting before Algorithm 15

For the source-shaped no-CHECK-birth repair, every stage from saturated WAIT
through SUPPRESS_SIG must frame leader bits except P'_ψ.  This file proves that
accounting structurally.  At the boundary before Algorithm 15, both leader bits
are exactly the outputs of P'_ψ; no comparison, CHECK, or cleanup state can add
a leader.
-/

namespace PPLLNoCheckBirthLeaderFrames

open PPLL PPLLRepair PPLLVerify PPLLNoCheckBirthRepair

/-- Pair projection used to compose leader-frame contracts. -/
def leaderPair (q : AgentState ψ × AgentState ψ) : Bool × Bool :=
  (q.1.leader, q.2.leader)

private theorem leaderPair_eq_of_fields
    {q : AgentState ψ × AgentState ψ} {l r : AgentState ψ}
    (h : q.1.leader = l.leader ∧ q.2.leader = r.leader) :
    leaderPair q = leaderPair (l, r) := by
  exact Prod.ext h.1 h.2

private theorem waitSaturatedPrepare_leaders
    (hψ : ψ > 0) (l r : AgentState ψ) :
    leaderPair (waitSaturatedPrepare hψ l r) = (l.leader, r.leader) := by
  unfold leaderPair waitSaturatedPrepare
  repeat (first | constructor | rfl | split)

private theorem waitSaturatedCarry_leaders
    (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    leaderPair (waitSaturatedCarry hψ κ l r) = (l.leader, r.leader) := by
  unfold leaderPair waitSaturatedCarry satCountSucc
  repeat (first | constructor | rfl | split)

private theorem waitSaturatedReset_leaders
    (hψ : ψ > 0) (l r : AgentState ψ) :
    leaderPair (waitSaturatedReset hψ l r) = (l.leader, r.leader) := by
  unfold leaderPair waitSaturatedReset
  repeat (first | constructor | rfl | split)

private theorem waitSaturatedFinish_leaders
    (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    leaderPair (waitSaturatedFinish hψ κ l r) = (l.leader, r.leader) := by
  simp [leaderPair, waitSaturatedFinish]

/-- Saturating WAIT frames both leader bits. -/
theorem waitSaturated_leaders
    (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    leaderPair (waitSaturated hψ κ l r) = (l.leader, r.leader) := by
  let q0 := waitSaturatedPrepare hψ l r
  let q1 := waitSaturatedCarry hψ κ q0.1 q0.2
  let q2 := waitSaturatedReset hψ q1.1 q1.2
  calc
    leaderPair (waitSaturated hψ κ l r) = leaderPair q2 :=
      waitSaturatedFinish_leaders hψ κ q2.1 q2.2
    _ = leaderPair q1 := waitSaturatedReset_leaders hψ q1.1 q1.2
    _ = leaderPair q0 := waitSaturatedCarry_leaders hψ κ q0.1 q0.2
    _ = (l.leader, r.leader) := waitSaturatedPrepare_leaders hψ l r

private theorem genSigSaturatedStart_leaders
    (hψ : ψ > 0) (l r : AgentState ψ) :
    leaderPair (genSigSaturatedStart hψ l r) = (l.leader, r.leader) := by
  simp [leaderPair, genSigSaturatedStart]

private theorem genSigSaturatedEmit_leaders
    (hψ : ψ > 0) (l r : AgentState ψ) :
    leaderPair (genSigSaturatedEmit hψ l r) = (l.leader, r.leader) := by
  simp [leaderPair, genSigSaturatedEmit]

private theorem genSigSaturatedPropagate_leaders
    (hψ : ψ > 0) (l r : AgentState ψ) :
    leaderPair (genSigSaturatedPropagate hψ l r) = (l.leader, r.leader) := by
  simp [leaderPair, genSigSaturatedPropagate]

private theorem genSigSaturatedFinish_leaders
    (hψ : ψ > 0) (l r : AgentState ψ) :
    leaderPair (genSigSaturatedFinish hψ l r) = (l.leader, r.leader) := by
  simp [leaderPair, genSigSaturatedFinish]

private theorem genSigSaturatedAfterWait_leaders
    (hψ : ψ > 0) (l r : AgentState ψ) :
    leaderPair (genSigSaturatedAfterWait hψ l r) = (l.leader, r.leader) := by
  let q0 := genSigSaturatedStart hψ l r
  let q1 := genSigSaturatedEmit hψ q0.1 q0.2
  let q2 := genSigSaturatedPropagate hψ q1.1 q1.2
  calc
    leaderPair (genSigSaturatedAfterWait hψ l r) = leaderPair q2 :=
      genSigSaturatedFinish_leaders hψ q2.1 q2.2
    _ = leaderPair q1 := genSigSaturatedPropagate_leaders hψ q1.1 q1.2
    _ = leaderPair q0 := genSigSaturatedEmit_leaders hψ q0.1 q0.2
    _ = (l.leader, r.leader) := genSigSaturatedStart_leaders hψ l r

/-- Saturated GENSIG frames both leader bits. -/
theorem genSigSaturated_leaders
    (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    leaderPair (genSigSaturated hψ κ l r) = (l.leader, r.leader) := by
  let q := waitSaturated hψ κ l r
  calc
    leaderPair (genSigSaturated hψ κ l r) = leaderPair q :=
      genSigSaturatedAfterWait_leaders hψ q.1 q.2
    _ = (l.leader, r.leader) := waitSaturated_leaders hψ κ l r

/-- Saturated post-P'_ψ prefix through SIGMOVE, factored over an already
computed P'_ψ pair to keep leader accounting opaque and compositional. -/
def noCheckBirthCoreAfterPPsi (hψ : ψ > 0) (κ : Nat)
    (q0 : AgentState ψ × AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q1 := genSigSaturated hψ κ q0.1 q0.2
  let q2 := cleanSig hψ q1.1 q1.2
  let q3 := eliminateSig hψ q2.1 q2.2
  sigMove hψ q3.1 q3.2

/-- The post-P'_ψ prefix frames the supplied pair's leaders. -/
theorem noCheckBirthCoreAfterPPsi_leaders
    (hψ : ψ > 0) (κ : Nat) (q0 : AgentState ψ × AgentState ψ) :
    leaderPair (noCheckBirthCoreAfterPPsi hψ κ q0) = leaderPair q0 := by
  let q1 := genSigSaturated hψ κ q0.1 q0.2
  let q2 := cleanSig hψ q1.1 q1.2
  let q3 := eliminateSig hψ q2.1 q2.2
  have hsig := leaderPair_eq_of_fields
    (sigMove_leaders_eq hψ q3.1 q3.2)
  have helim := leaderPair_eq_of_fields
    (eliminateSig_leaders_eq hψ q2.1 q2.2)
  have hclean := leaderPair_eq_of_fields
    (cleanSig_leaders_eq hψ q1.1 q1.2)
  have hgen := genSigSaturated_leaders hψ κ q0.1 q0.2
  change leaderPair (sigMove hψ q3.1 q3.2) = leaderPair q0
  exact hsig.trans (helim.trans (hclean.trans hgen))

/-- Explicit saturated source-level prefix through SIGMOVE. -/
def noCheckBirthCoreBeforeCheck (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  noCheckBirthCoreAfterPPsi hψ κ (pPsi hψ l r)

/-- The complete saturated prefix through SIGMOVE has exactly P'_ψ's two
leader outputs. -/
theorem noCheckBirthCoreBeforeCheck_leaders
    (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    leaderPair (noCheckBirthCoreBeforeCheck hψ κ l r) =
      leaderPair (pPsi hψ l r) :=
  noCheckBirthCoreAfterPPsi_leaders hψ κ (pPsi hψ l r)

/-- AgentState-level CHECK wrapper with the same output framing as the physical
authorized repair. -/
def checkSigNoBirthCore (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := checkSig hψ l r
  ({ q.1 with leader := l.leader }, { q.2 with leader := r.leader })

/-- Core no-birth CHECK frames both leaders. -/
theorem checkSigNoBirthCore_leaders (hψ : ψ > 0)
    (l r : AgentState ψ) :
    leaderPair (checkSigNoBirthCore hψ l r) = (l.leader, r.leader) := by
  rfl

private theorem cmpUpdatePropagate_leaders
    (hψ : ψ > 0) (l r : AgentState ψ) :
    leaderPair (cmpUpdatePropagate hψ l r) = (l.leader, r.leader) := by
  unfold leaderPair cmpUpdatePropagate
  repeat (first | constructor | rfl | split)

private theorem cmpUpdateSetPath2_leader
    (hψ : ψ > 0) (l : AgentState ψ) :
    (cmpUpdateSetPath2 hψ l).leader = l.leader := by
  unfold cmpUpdateSetPath2
  repeat (first | rfl | split)

private theorem cmpUpdateNoSourceRearm_leaders
    (hψ : ψ > 0) (l r : AgentState ψ) :
    leaderPair (cmpUpdateNoSourceRearm hψ l r) = (l.leader, r.leader) := by
  let l0 := if l.label = ⟨0, hψ⟩ ∧ l.state ≠ .depart then
    { l with state := .congest } else l
  let q := cmpUpdatePropagate hψ l0 r
  have hl0 : l0.leader = l.leader := by
    dsimp [l0]
    split <;> rfl
  have hq := cmpUpdatePropagate_leaders hψ l0 r
  have hql : q.1.leader = l0.leader := congrArg Prod.fst hq
  have hqr : q.2.leader = r.leader := congrArg Prod.snd hq
  change leaderPair (cmpUpdateSetPath2 hψ q.1, q.2) =
    (l.leader, r.leader)
  unfold leaderPair
  rw [cmpUpdateSetPath2_leader, hql, hqr, hl0]

private theorem compareSigInit_leader_eq (l : AgentState ψ) :
    (compareSigInit l).leader = l.leader := by
  unfold compareSigInit
  split <;> rfl

/-- No-source-rearm COMPARE frames both leader bits. -/
theorem compareSigNoSourceRearm_leaders
    (hψ : ψ > 0) (l r : AgentState ψ) :
    leaderPair (compareSigNoSourceRearm hψ l r) = (l.leader, r.leader) := by
  unfold compareSigNoSourceRearm
  dsimp only
  split
  · exact Prod.ext (compareSigInit_leader_eq l) rfl
  · split
    · let l0 := compareSigInit l
      let q := cmpUpdateNoSourceRearm hψ l0 r
      have hcmp := cmpUpdateNoSourceRearm_leaders hψ l0 r
      have hdispatch := leaderPair_eq_of_fields
        (compareSigDispatch_leaders_eq hψ q.1 q.2)
      have hinit : leaderPair (l0, r) = (l.leader, r.leader) := by
        exact Prod.ext (compareSigInit_leader_eq l) rfl
      exact hdispatch.trans (hcmp.trans hinit)
    · exact Prod.ext (compareSigInit_leader_eq l) rfl

/-- Post-prefix no-birth CHECK, DISAPPEAR, COMPARE, and SUPPRESS stages
factored over an already computed pre-CHECK pair. -/
def noCheckBirthCoreAfterBeforeCheck (hψ : ψ > 0)
    (q0 : AgentState ψ × AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q1 := checkSigNoBirthCore hψ q0.1 q0.2
  let q2 := disappear hψ q1.1 q1.2
  let q3 := compareSigNoSourceRearm hψ q2.1 q2.2
  suppressSig hψ q3.1 q3.2

/-- Every stage after the named pre-CHECK pair and before Algorithm 15 frames
both leaders. -/
theorem noCheckBirthCoreAfterBeforeCheck_leaders
    (hψ : ψ > 0) (q0 : AgentState ψ × AgentState ψ) :
    leaderPair (noCheckBirthCoreAfterBeforeCheck hψ q0) = leaderPair q0 := by
  let q1 := checkSigNoBirthCore hψ q0.1 q0.2
  let q2 := disappear hψ q1.1 q1.2
  let q3 := compareSigNoSourceRearm hψ q2.1 q2.2
  have h1 := checkSigNoBirthCore_leaders hψ q0.1 q0.2
  have h2 := leaderPair_eq_of_fields
    (disappear_leaders_eq hψ q1.1 q1.2)
  have h3 := compareSigNoSourceRearm_leaders hψ q2.1 q2.2
  have h4 := leaderPair_eq_of_fields
    (suppressSig_leaders_eq hψ q3.1 q3.2)
  change leaderPair (suppressSig hψ q3.1 q3.2) = leaderPair q0
  exact h4.trans (h3.trans (h2.trans h1))

/-- Prefix from the raw inputs through SUPPRESS_SIG under no-CHECK-birth
semantics. -/
def noCheckBirthBeforeEliminate (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  noCheckBirthCoreAfterBeforeCheck hψ
    (noCheckBirthCoreBeforeCheck hψ κ l r)

/-- At the Algorithm-15 boundary, P'_ψ is the sole possible leader writer. -/
theorem noCheckBirthBeforeEliminate_leaders
    (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    leaderPair (noCheckBirthBeforeEliminate hψ κ l r) =
      leaderPair (pPsi hψ l r) :=
  (noCheckBirthCoreAfterBeforeCheck_leaders hψ
    (noCheckBirthCoreBeforeCheck hψ κ l r)).trans
      (noCheckBirthCoreBeforeCheck_leaders hψ κ l r)

/-- The no-collision Algorithm-15 repair never changes the responder's leader
bit. -/
theorem eliminateLeadersNoCollision_responder_leader_eq
    (hψ : ψ > 0) (l r : AgentState ψ) :
    (eliminateLeadersNoCollision hψ l r).2.leader = r.leader := by
  simp [eliminateLeadersNoCollision]

/-- Any initiator leader after repaired Algorithm 15 was already an initiator
leader before that stage. -/
theorem eliminateLeadersNoCollision_initiator_origin
    (hψ : ψ > 0) (l r : AgentState ψ)
    (h : (eliminateLeadersNoCollision hψ l r).1.leader = true) :
    l.leader = true := by
  cases hl : l.leader
  · simp [eliminateLeadersNoCollision, hl] at h
  · rfl

/-- An initiator leader survives repaired Algorithm 15 unless an unshielded
live responder bullet supplies the explicit kill event. -/
theorem eliminateLeadersNoCollision_initiator_survives
    (hψ : ψ > 0) (l r : AgentState ψ)
    (hl : l.leader = true)
    (hpeace : ¬(r.bullet = ⟨2, by omega⟩ ∧ l.shield = false)) :
    (eliminateLeadersNoCollision hψ l r).1.leader = true := by
  unfold eliminateLeadersNoCollision
  repeat (first | rfl | split)
  all_goals simp_all
  by_cases hf : r.leader = true ∧ r.signal_B = 1
  · simp [hf]
  · simp [hf]
    by_cases hb : r.bullet = 0
    · exact Or.inl hb
    · by_cases h2 : r.bullet = 2
      · exact Or.inr (Or.inr (hpeace h2))
      · exact Or.inr (Or.inl h2)

private theorem eliminateLeadersNoCollision_labels_eq
    (hψ : ψ > 0) (l r : AgentState ψ) :
    (eliminateLeadersNoCollision hψ l r).1.label = l.label ∧
      (eliminateLeadersNoCollision hψ l r).2.label = r.label := by
  simp [eliminateLeadersNoCollision]

/-- Algorithm-15 plus gated-WRITE suffix over an already computed boundary
pair. -/
def noCheckBirthCoreAfterBeforeEliminate (hψ : ψ > 0)
    (q0 : AgentState ψ × AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q1 := eliminateLeadersNoCollision hψ q0.1 q0.2
  PPLLWriteIncrementGate.writeSeqIncrementGate hψ q1.1 q1.2

/-- Exact factored suffix equation, exposed to prevent downstream unfolding. -/
theorem noCheckBirthCoreAfterBeforeEliminate_eq
    (hψ : ψ > 0) (q0 : AgentState ψ × AgentState ψ) :
    noCheckBirthCoreAfterBeforeEliminate hψ q0 =
      PPLLWriteIncrementGate.writeSeqIncrementGate hψ
        (eliminateLeadersNoCollision hψ q0.1 q0.2).1
        (eliminateLeadersNoCollision hψ q0.1 q0.2).2 := by
  rfl

/-- A boundary initiator leader survives Algorithm 15 and gated WRITE whenever
the bullet/shield kill condition is absent. -/
theorem noCheckBirthCoreAfterBeforeEliminate_initiator_survives
    (hψ : ψ > 0) (q0 : AgentState ψ × AgentState ψ)
    (hleft : q0.1.leader = true)
    (hpeace : ¬(q0.2.bullet = ⟨2, by omega⟩ ∧ q0.1.shield = false)) :
    (noCheckBirthCoreAfterBeforeEliminate hψ q0).1.leader = true := by
  rw [noCheckBirthCoreAfterBeforeEliminate_eq]
  apply PPLLWriteIncrementGate.writeSeqIncrementGate_initiator_survives
  exact eliminateLeadersNoCollision_initiator_survives
    hψ q0.1 q0.2 hleft hpeace

/-- A boundary responder leader at label zero survives Algorithm 15 and gated
WRITE at the same responder position. -/
theorem noCheckBirthCoreAfterBeforeEliminate_responder_survives
    (hψ : ψ > 0) (q0 : AgentState ψ × AgentState ψ)
    (hright : q0.2.leader = true)
    (hlabel : q0.2.label = ⟨0, hψ⟩) :
    (noCheckBirthCoreAfterBeforeEliminate hψ q0).2.leader = true := by
  rw [noCheckBirthCoreAfterBeforeEliminate_eq]
  apply PPLLWriteIncrementGate.writeSeqIncrementGate_responder_zero_survives
  · rw [eliminateLeadersNoCollision_responder_leader_eq]
    exact hright
  · rw [(eliminateLeadersNoCollision_labels_eq hψ q0.1 q0.2).2]
    exact hlabel

/-- A label-zero responder leader cannot migrate to a follower initiator
through the Algorithm-15 plus gated-WRITE suffix. -/
theorem noCheckBirthCoreAfterBeforeEliminate_no_zero_migration
    (hψ : ψ > 0) (q0 : AgentState ψ × AgentState ψ)
    (hl : q0.1.leader = false)
    (hrLabel : q0.2.label = ⟨0, hψ⟩) :
    (noCheckBirthCoreAfterBeforeEliminate hψ q0).1.leader = false := by
  rw [noCheckBirthCoreAfterBeforeEliminate_eq]
  let q1 := eliminateLeadersNoCollision hψ q0.1 q0.2
  have hq1L : q1.1.leader = false := by
    cases hval : q1.1.leader
    · rfl
    · have horigin := eliminateLeadersNoCollision_initiator_origin
        hψ q0.1 q0.2 hval
      rw [hl] at horigin
      contradiction
  cases hout : (PPLLWriteIncrementGate.writeSeqIncrementGate
      hψ q1.1 q1.2).1.leader
  · rfl
  · have hmigrate :=
      PPLLWriteIncrementGate.writeSeqIncrementGate_new_initiator_requires_responder
        hψ q1.1 q1.2 hout hq1L
    have hq1Label := (eliminateLeadersNoCollision_labels_eq hψ q0.1 q0.2).2
    exact (hmigrate.2 (hq1Label.trans hrLabel)).elim

/-- Every suffix leader originates in the supplied boundary pair; the responder
cannot receive a migrated initiator leader. -/
theorem noCheckBirthCoreAfterBeforeEliminate_leader_origins
    (hψ : ψ > 0) (q0 : AgentState ψ × AgentState ψ) :
    ((noCheckBirthCoreAfterBeforeEliminate hψ q0).1.leader = true →
      q0.1.leader = true ∨ q0.2.leader = true) ∧
    ((noCheckBirthCoreAfterBeforeEliminate hψ q0).2.leader = true →
      q0.2.leader = true) := by
  constructor
  · intro hout
    rw [noCheckBirthCoreAfterBeforeEliminate_eq] at hout
    have horigin := PPLLWriteIncrementGate.writeSeqIncrementGate_initiator_origin
      hψ (eliminateLeadersNoCollision hψ q0.1 q0.2).1
        (eliminateLeadersNoCollision hψ q0.1 q0.2).2 hout
    rcases horigin with hleft | hright
    · exact .inl (eliminateLeadersNoCollision_initiator_origin
        hψ q0.1 q0.2 hleft)
    · right
      rw [← eliminateLeadersNoCollision_responder_leader_eq hψ q0.1 q0.2]
      exact hright
  · intro hout
    rw [noCheckBirthCoreAfterBeforeEliminate_eq] at hout
    have hq1 := PPLLWriteIncrementGate.writeSeqIncrementGate_responder_origin
      hψ (eliminateLeadersNoCollision hψ q0.1 q0.2).1
        (eliminateLeadersNoCollision hψ q0.1 q0.2).2 hout
    rw [← eliminateLeadersNoCollision_responder_leader_eq hψ q0.1 q0.2]
    exact hq1

/-- Complete AgentState-level source-shaped transition used only for universal
leader-writer accounting. -/
def noCheckBirthCoreTransition (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  noCheckBirthCoreAfterBeforeEliminate hψ
    (noCheckBirthBeforeEliminate hψ κ l r)

/-- Exact full core equation at the pre-Algorithm-15 boundary. -/
theorem noCheckBirthCoreTransition_eq
    (hψ : ψ > 0) (κ : Nat) (l r : AgentState ψ) :
    noCheckBirthCoreTransition hψ κ l r =
      noCheckBirthCoreAfterBeforeEliminate hψ
        (noCheckBirthBeforeEliminate hψ κ l r) := by
  rfl

/-- Compose any proved P'_ψ boundary equality with the concrete Algorithm-15
and gated-WRITE suffix origin theorem.  Keeping the already-computed boundary
pair explicit prevents elaboration from unfolding the full protocol term. -/
theorem noCheckBirthSuffix_origins_of_pPsi_boundary
    (hψ : ψ > 0) (l r : AgentState ψ)
    (q0 : AgentState ψ × AgentState ψ)
    (hpre : leaderPair q0 = leaderPair (pPsi hψ l r)) :
    ((noCheckBirthCoreAfterBeforeEliminate hψ q0).1.leader = true →
      (pPsi hψ l r).1.leader = true ∨ (pPsi hψ l r).2.leader = true) ∧
    ((noCheckBirthCoreAfterBeforeEliminate hψ q0).2.leader = true →
      (pPsi hψ l r).2.leader = true) := by
  have hsuffix := noCheckBirthCoreAfterBeforeEliminate_leader_origins hψ q0
  have hpreL : q0.1.leader = (pPsi hψ l r).1.leader :=
    congrArg Prod.fst hpre
  have hpreR : q0.2.leader = (pPsi hψ l r).2.leader :=
    congrArg Prod.snd hpre
  constructor
  · intro hout
    rcases hsuffix.1 hout with hleft | hright
    · exact .inl (hpreL ▸ hleft)
    · exact .inr (hpreR ▸ hright)
  · intro hout
    exact hpreR ▸ hsuffix.2 hout

attribute [local irreducible] noCheckBirthCoreAfterBeforeEliminate

/-- Under the paper's no-free-barrier condition, any supplied boundary pair
whose leaders equal P'_ψ's pair remains follower/follower through Algorithm 15
and the gated WRITE suffix.  `noCheckBirthBeforeEliminate_leaders` supplies the
boundary equality for the concrete prefix. -/
theorem noCheckBirth_followerPair_preserved_of_boundary
    (hψ : ψ > 0) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hbarriers : noFreeBarrier hψ ring C)
    (e : Fin n)
    (hl : (C e).leader = false)
    (hr : (C (ring.rightNeighbor e)).leader = false)
    (q0 : AgentState ψ × AgentState ψ)
    (hpre : leaderPair q0 =
      leaderPair (pPsi hψ (C e) (C (ring.rightNeighbor e)))) :
    let q := noCheckBirthCoreAfterBeforeEliminate hψ q0
    q.1.leader ≠ true ∧ q.2.leader ≠ true := by
  let l := C e
  let r := C (ring.rightNeighbor e)
  have hpL : (pPsi hψ l r).1.leader = false := by
    rw [PPLLVerify.pPsi_initiator_leader_eq hψ l r, hl]
  have hpR : (pPsi hψ l r).2.leader = false := by
    cases hpr : (pPsi hψ l r).2.leader
    · rfl
    · have hbirth := PPLLVerify.pPsi_new_responder_leader_requires_probe_barrier
        hψ l r hpr hr
      have hleader := hbarriers e hbirth.2
      simp [AgentState.isLeader, hr] at hleader
  have horigin := noCheckBirthSuffix_origins_of_pPsi_boundary
    hψ l r q0 hpre
  constructor
  · intro hout
    rcases horigin.1 hout with h | h
    · rw [hpL] at h
      contradiction
    · rw [hpR] at h
      contradiction
  · intro hout
    have h := horigin.2 hout
    rw [hpR] at h
    contradiction

end PPLLNoCheckBirthLeaderFrames
