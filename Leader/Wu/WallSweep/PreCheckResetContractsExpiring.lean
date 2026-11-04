import Leader.Wu.WallSweep.PreCheckResetContractsEchoCollision

/-!
# Pre-CHECK reset contracts: Expiring

This module is one dependency-ordered part of the former contract monolith.
-/

namespace PPLLWallSweepPreCheckResetContracts

open PPLL PPLLResearchFormulation PPLLAuthorizedComparisonRepair
  PPLLRepair PPLLWriteIncrementGate
  PPLLExpiringComparisonRepair PPLLPathStallComparisonRepair
  PPLLLeaderCreationCleanupRepair PPLLWallSweepRepair
  PPLLWallSweepFinite PPLLWallSweepFiniteCleanup
  PPLLTerminalEqualSupportRepair
  PPLLWallSweepNormalResetContract PPLLWallSweepEchoDrain
  PPLLWallSweepPreCheckResetRepair
  PPLLNoCheckBirthLeaderFrames
  PPLLNoCheckBirthConditionTwoFrames
  PPLLNoCheckBirthConditionTwoKernel
  PPLLNoCheckBirthConditionTwoPhysical

variable {psi kappa tau : Nat}

/-! ## Bounded and path-stall lifts -/

/-- The corrected transition inherits the exact active-responder deletion
contract because that priority branch precedes the new ordinary wall. -/
theorem wallSweepPreCheckResetPathStall_active_responder_contract
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hr : deletionActive r.core.erase = true) :
    let q := wallSweepPreCheckResetPathStallTransition
      hpsi kappa tau l r
    comparisonPathMass q.1 + comparisonPathMass q.2 <
        comparisonPathMass l + comparisonPathMass r ∧
      comparisonPathMass q.1 ≤ comparisonPathMass l ∧
      comparisonPathMass q.2 < comparisonPathMass r ∧
      ResetEchoFrame l q.1 ∧ ResetEchoFrame r q.2 := by
  rw [wallSweepPreCheckResetPathStall_eq_wallSweep_of_responder_active
    hpsi kappa tau l r hr]
  exact wallSweepPathStall_active_responder_contract hpsi l r hr

/-- Active-responder deletion also inherits the old two-shield frame. -/
theorem wallSweepPreCheckResetPathStall_active_responder_shields
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hr : deletionActive r.core.erase = true) :
    let q := wallSweepPreCheckResetPathStallTransition
      hpsi kappa tau l r
    q.1.core.erase.core.shield = l.core.erase.core.shield ∧
      q.2.core.erase.core.shield = r.core.erase.core.shield := by
  rw [wallSweepPreCheckResetPathStall_eq_wallSweep_of_responder_active
    hpsi kappa tau l r hr]
  exact wallSweepPathStall_active_responder_shields hpsi l r hr

/-- The corrected path-stall transition is bounded reification followed by
the two pointwise expiry stages. -/
theorem wallSweepPreCheckResetPathStall_eq_expiryStages
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau) :
    let bounded := wallSweepPreCheckResetBoundedTransition
      hpsi kappa l.core r.core
    let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
    let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
    wallSweepPreCheckResetPathStallTransition hpsi kappa tau l r =
      (deletionPriorityExpireOne tau l lBase,
        deletionPriorityExpireOne tau r rBase) := by
  rfl

/-- Every priority-open corrected finite edge clears its responder echo. -/
theorem wallSweepPreCheckResetPathStall_priority_open_responder_echo_false
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r) :
    expiringResponderEchoFalse
      (wallSweepPreCheckResetPathStallTransition hpsi kappa tau l r) := by
  let bounded := wallSweepPreCheckResetBoundedTransition
    hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  have ha :=
    wallSweepPreCheckResetAuthorized_priority_open_responder_echo_false
      hpsi kappa l.core.erase r.core.erase hopen
  have he := erase_wallSweepPreCheckResetBoundedTransition
    hpsi kappa l.core r.core
  have hR := congrArg Prod.snd he
  change bounded.2.erase =
    (wallSweepPreCheckResetAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).2 at hR
  have hbase : rBase.core.erase.core.echo = false := by
    change bounded.2.erase.core.echo = false
    rw [hR]
    exact ha
  have hf := deletionPriorityExpireOne_path_frame r rBase
  have hfinal :
      (deletionPriorityExpireOne tau r rBase).core.erase.core.echo = false :=
    hf.2.2.2.2.1.trans hbase
  rw [wallSweepPreCheckResetPathStall_eq_expiryStages]
  exact hfinal

/-- Proof certificate that the finite/path-stall output initiator keeps the
input label without forcing elaboration to unfold the complete transition. -/
inductive ExpiringInitiatorLabelFrame
    (input : ExpiringAgentState psi kappa tau)
    (output : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau) : Prop where
  | intro (witness : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau)
      (witness_eq : witness = output)
      (label_eq : witness.1.core.erase.core.label =
        input.core.erase.core.label)

theorem ExpiringInitiatorLabelFrame.exact_eq
    {input : ExpiringAgentState psi kappa tau}
    {output : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau}
    (h : ExpiringInitiatorLabelFrame input output) :
    output.1.core.erase.core.label = input.core.erase.core.label := by
  rcases h with ⟨witness, hwitness, hlabel⟩
  rw [← hwitness]
  exact hlabel

/-- A priority-open shielded initiator survives the corrected finite edge. -/
theorem wallSweepPreCheckResetPathStall_priority_open_initiator_anchor
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hanchor : InitiatorAnchor l.core.erase.core) :
    expiringInitiatorAnchor
      (wallSweepPreCheckResetPathStallTransition hpsi kappa tau l r) := by
  let bounded := wallSweepPreCheckResetBoundedTransition
    hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  have ha := wallSweepPreCheckResetAuthorized_priority_open_initiator_anchor
    hpsi kappa l.core.erase r.core.erase hopen hanchor
  have he := erase_wallSweepPreCheckResetBoundedTransition
    hpsi kappa l.core r.core
  have hL := congrArg Prod.fst he
  change bounded.1.erase =
    (wallSweepPreCheckResetAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).1 at hL
  have hbase : InitiatorAnchor lBase.core.erase.core := by
    change InitiatorAnchor bounded.1.erase.core
    rw [hL]
    exact ha
  have hf := deletionPriorityExpireOne_path_frame l lBase
  have hs := deletionPriorityExpireOne_shield_frame l lBase
  have hfinal : InitiatorAnchor
      (deletionPriorityExpireOne tau l lBase).core.erase.core :=
    ⟨hf.2.1.trans hbase.1, hs.trans hbase.2⟩
  rw [wallSweepPreCheckResetPathStall_eq_expiryStages]
  exact hfinal

/-- The same protected initiator keeps its label through finite reification and
expiry. -/
theorem wallSweepPreCheckResetPathStall_priority_open_label_of_anchor
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hanchor : InitiatorAnchor l.core.erase.core) :
    ExpiringInitiatorLabelFrame l
      (wallSweepPreCheckResetPathStallTransition hpsi kappa tau l r) := by
  let bounded := wallSweepPreCheckResetBoundedTransition
    hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  have ha := wallSweepPreCheckResetAuthorized_priority_open_label_of_anchor
    hpsi kappa l.core.erase r.core.erase hopen hanchor
  have he := erase_wallSweepPreCheckResetBoundedTransition
    hpsi kappa l.core r.core
  have hL := congrArg Prod.fst he
  change bounded.1.erase =
    (wallSweepPreCheckResetAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).1 at hL
  have hbase : lBase.core.erase.core.label = l.core.erase.core.label := by
    change bounded.1.erase.core.label = l.core.erase.core.label
    rw [hL]
    exact ha.exact_eq
  have hf := deletionPriorityExpireOne_path_frame l lBase
  let output := wallSweepPreCheckResetPathStallTransition
    hpsi kappa tau l r
  let final := (deletionPriorityExpireOne tau l lBase,
    deletionPriorityExpireOne tau r
      ⟨bounded.2, r.stall⟩)
  have heq := wallSweepPreCheckResetPathStall_eq_expiryStages
    hpsi kappa tau l r
  change output = final at heq
  exact ⟨final, heq.symm,
    hf.2.2.1.trans hbase⟩

/-- The protected initiator also consumes its echo through the corrected
finite edge. -/
theorem wallSweepPreCheckResetPathStall_priority_open_initiator_echo_false
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hanchor : InitiatorAnchor l.core.erase.core) :
    expiringInitiatorEchoFalse
      (wallSweepPreCheckResetPathStallTransition hpsi kappa tau l r) := by
  let bounded := wallSweepPreCheckResetBoundedTransition
    hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  have ha :=
    wallSweepPreCheckResetAuthorized_priority_open_initiator_echo_false
      hpsi kappa l.core.erase r.core.erase hopen hanchor
  have he := erase_wallSweepPreCheckResetBoundedTransition
    hpsi kappa l.core r.core
  have hL := congrArg Prod.fst he
  change bounded.1.erase =
    (wallSweepPreCheckResetAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).1 at hL
  have hbase : lBase.core.erase.core.echo = false := by
    change bounded.1.erase.core.echo = false
    rw [hL]
    exact ha
  have hf := deletionPriorityExpireOne_path_frame l lBase
  have hfinal :
      (deletionPriorityExpireOne tau l lBase).core.erase.core.echo = false :=
    hf.2.2.2.2.1.trans hbase
  rw [wallSweepPreCheckResetPathStall_eq_expiryStages]
  exact hfinal

/-- The corrected finite leader edge reseeds reset and clears both echoes. -/
theorem wallSweepPreCheckResetPathStall_priority_open_leader_reseed
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hanchor : InitiatorAnchor l.core.erase.core)
    (hrEcho : r.core.erase.core.echo = false) :
    expiringLeaderReseedResult
      (wallSweepPreCheckResetPathStallTransition hpsi kappa tau l r) := by
  let bounded := wallSweepPreCheckResetBoundedTransition
    hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  have ha := wallSweepPreCheckResetAuthorized_priority_open_leader_reseed
    hpsi kappa l.core.erase r.core.erase hopen hanchor hrEcho
  have he := erase_wallSweepPreCheckResetBoundedTransition
    hpsi kappa l.core r.core
  have hL := congrArg Prod.fst he
  have hR := congrArg Prod.snd he
  change bounded.1.erase =
    (wallSweepPreCheckResetAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).1 at hL
  change bounded.2.erase =
    (wallSweepPreCheckResetAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).2 at hR
  have hLf := deletionPriorityExpireOne_path_frame l lBase
  have hRf := deletionPriorityExpireOne_path_frame r rBase
  have hfinal :
      (deletionPriorityExpireOne tau l lBase).core.erase.core.echo = false ∧
      (deletionPriorityExpireOne tau r rBase).core.erase.core.echo = false ∧
      (deletionPriorityExpireOne tau r rBase).core.erase.core.reset_cmd = true := by
    refine ⟨hLf.2.2.2.2.1.trans ?_, hRf.2.2.2.2.1.trans ?_,
      hRf.2.2.2.1.trans ?_⟩
    · change bounded.1.erase.core.echo = false
      rw [hL]
      exact ha.1
    · change bounded.2.erase.core.echo = false
      rw [hR]
      exact ha.2.1
    · change bounded.2.erase.core.reset_cmd = true
      rw [hR]
      exact ha.2.2
  rw [wallSweepPreCheckResetPathStall_eq_expiryStages]
  exact hfinal

/-- The same leader seed leaves both corrected finite endpoints neutral. -/
theorem wallSweepPreCheckResetPathStall_priority_open_leader_reseed_neutral
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hanchor : InitiatorAnchor l.core.erase.core)
    (hrEcho : r.core.erase.core.echo = false) :
    expiringBothNeutral
      (wallSweepPreCheckResetPathStallTransition hpsi kappa tau l r) := by
  let bounded := wallSweepPreCheckResetBoundedTransition
    hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  have ha :=
    wallSweepPreCheckResetAuthorized_priority_open_leader_reseed_neutral
      hpsi kappa l.core.erase r.core.erase hopen hanchor hrEcho
  have he := erase_wallSweepPreCheckResetBoundedTransition
    hpsi kappa l.core r.core
  have hL := congrArg Prod.fst he
  have hR := congrArg Prod.snd he
  change bounded.1.erase =
    (wallSweepPreCheckResetAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).1 at hL
  change bounded.2.erase =
    (wallSweepPreCheckResetAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).2 at hR
  have hbaseL : ComparisonNeutral lBase.core.erase.core := by
    change ComparisonNeutral bounded.1.erase.core
    rw [hL]
    exact ha.1
  have hbaseR : ComparisonNeutral rBase.core.erase.core := by
    change ComparisonNeutral bounded.2.erase.core
    rw [hR]
    exact ha.2
  have hLf := deletionPriorityExpireOne_neutral_fields l lBase hbaseL
  have hRf := deletionPriorityExpireOne_neutral_fields r rBase hbaseR
  rw [wallSweepPreCheckResetPathStall_eq_expiryStages]
  exact ⟨hLf.1, hRf.1⟩

/-- Reset/echo collision projected to the finite/path-stall carrier. -/
def ExpiringResetCollision
    (q : ExpiringAgentState psi kappa tau ×
      ExpiringAgentState psi kappa tau) : Prop :=
  ComparisonNeutral q.1.core.erase.core ∧
    ComparisonNeutral q.2.core.erase.core ∧
    q.1.core.erase.core.reset_cmd = false ∧
    q.2.core.erase.core.reset_cmd = false ∧
    q.2.core.erase.core.echo = false

/-- A priority-open blocking echo consumes a leader- or reset-generated token
through bounded reification and path-stall expiry. -/
theorem wallSweepPreCheckResetPathStall_priority_open_source_echo_collision
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hsource : l.core.erase.core.leader = true ∨
      l.core.erase.core.reset_cmd = true)
    (hrEcho : r.core.erase.core.echo = true) :
    ExpiringResetCollision
      (wallSweepPreCheckResetPathStallTransition hpsi kappa tau l r) := by
  let bounded := wallSweepPreCheckResetBoundedTransition
    hpsi kappa l.core r.core
  let lBase : ExpiringAgentState psi kappa tau := ⟨bounded.1, l.stall⟩
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  have ha :=
    wallSweepPreCheckResetAuthorized_priority_open_source_echo_collision
      hpsi kappa l.core.erase r.core.erase hopen hsource hrEcho
  have he := erase_wallSweepPreCheckResetBoundedTransition
    hpsi kappa l.core r.core
  have hL := congrArg Prod.fst he
  have hR := congrArg Prod.snd he
  change bounded.1.erase =
    (wallSweepPreCheckResetAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).1 at hL
  change bounded.2.erase =
    (wallSweepPreCheckResetAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).2 at hR
  have hbaseL : ComparisonNeutral lBase.core.erase.core := by
    change ComparisonNeutral bounded.1.erase.core
    rw [hL]
    exact ha.1
  have hbaseR : ComparisonNeutral rBase.core.erase.core := by
    change ComparisonNeutral bounded.2.erase.core
    rw [hR]
    exact ha.2.1
  have hLf := deletionPriorityExpireOne_neutral_fields l lBase hbaseL
  have hRf := deletionPriorityExpireOne_neutral_fields r rBase hbaseR
  have hbaseLReset : lBase.core.erase.core.reset_cmd = false := by
    change bounded.1.erase.core.reset_cmd = false
    rw [hL]
    exact ha.2.2.1
  have hbaseRReset : rBase.core.erase.core.reset_cmd = false := by
    change bounded.2.erase.core.reset_cmd = false
    rw [hR]
    exact ha.2.2.2.1
  have hbaseREcho : rBase.core.erase.core.echo = false := by
    change bounded.2.erase.core.echo = false
    rw [hR]
    exact ha.2.2.2.2
  rw [wallSweepPreCheckResetPathStall_eq_expiryStages]
  exact ⟨hLf.1, hRf.1,
    hLf.2.2.2.1.trans hbaseLReset,
    hRf.2.2.2.1.trans hbaseRReset,
    hRf.2.2.2.2.1.trans hbaseREcho⟩

/-- On the final reset-covered wrap edge, a label-zero responder leader
survives the corrected finite transition. -/
theorem wallSweepPreCheckResetPathStall_priority_open_responder_zero_survives
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hlReset : l.core.erase.core.reset_cmd = true)
    (hzero : ResponderZeroAnchor hpsi r.core.erase.core) :
    expiringResponderLeader
      (wallSweepPreCheckResetPathStallTransition hpsi kappa tau l r) := by
  let bounded := wallSweepPreCheckResetBoundedTransition
    hpsi kappa l.core r.core
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  have ha :=
    wallSweepPreCheckResetAuthorized_priority_open_responder_zero_survives
      hpsi kappa l.core.erase r.core.erase hopen hlReset hzero
  have he := erase_wallSweepPreCheckResetBoundedTransition
    hpsi kappa l.core r.core
  have hR := congrArg Prod.snd he
  change bounded.2.erase =
    (wallSweepPreCheckResetAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).2 at hR
  have hbase : rBase.core.erase.core.leader = true := by
    change bounded.2.erase.core.leader = true
    rw [hR]
    exact ha
  have hf := deletionPriorityExpireOne_path_frame r rBase
  have hfinal :
      (deletionPriorityExpireOne tau r rBase).core.erase.core.leader = true :=
    hf.2.1.trans hbase
  rw [wallSweepPreCheckResetPathStall_eq_expiryStages]
  exact hfinal

/-- Finite reification and path-stall expiry preserve a first leader created
by the complete repaired interaction on a priority-open barrier/probe edge. -/
theorem wallSweepPreCheckResetPathStall_priority_open_barrier_probe_birth
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hl : l.core.erase.core.leader = false)
    (hr : r.core.erase.core.leader = false)
    (hprobe : r.core.erase.core.probe = true)
    (hbarrier : isBarrier hpsi l.core.erase.core r.core.erase.core) :
    expiringResponderLeader
      (wallSweepPreCheckResetPathStallTransition hpsi kappa tau l r) := by
  let bounded := wallSweepPreCheckResetBoundedTransition
    hpsi kappa l.core r.core
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  have ha :=
    wallSweepPreCheckResetAuthorized_priority_open_barrier_probe_birth
      hpsi kappa l.core.erase r.core.erase hopen hl hr hprobe hbarrier
  have he := erase_wallSweepPreCheckResetBoundedTransition
    hpsi kappa l.core r.core
  have hR := congrArg Prod.snd he
  change bounded.2.erase =
    (wallSweepPreCheckResetAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).2 at hR
  have hbase : rBase.core.erase.core.leader = true := by
    change bounded.2.erase.core.leader = true
    rw [hR]
    exact ha
  have hf := deletionPriorityExpireOne_path_frame r rBase
  have hfinal :
      (deletionPriorityExpireOne tau r rBase).core.erase.core.leader = true :=
    hf.2.1.trans hbase
  rw [wallSweepPreCheckResetPathStall_eq_expiryStages]
  exact hfinal

/-- Finite reification and expiry also preserve a first barrier/probe leader
under the rooted leader-sink transition. -/
theorem
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_barrier_probe_birth
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hl : l.core.erase.core.leader = false)
    (hr : r.core.erase.core.leader = false)
    (hprobe : r.core.erase.core.probe = true)
    (hbarrier : isBarrier hpsi l.core.erase.core r.core.erase.core) :
    expiringResponderLeader
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r) := by
  let bounded := wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l.core r.core
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  have ha :=
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_barrier_probe_birth
      hpsi kappa l.core.erase r.core.erase hopen hl hr hprobe hbarrier
  have he := erase_wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l.core r.core
  have hR := congrArg Prod.snd he
  change bounded.2.erase =
    (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).2 at hR
  have hbase : rBase.core.erase.core.leader = true := by
    change bounded.2.erase.core.leader = true
    rw [hR]
    exact ha
  have hf := deletionPriorityExpireOne_path_frame r rBase
  have hfinal :
      (deletionPriorityExpireOne tau r rBase).core.erase.core.leader = true :=
    hf.2.1.trans hbase
  rw [wallSweepPreCheckResetLeaderSinkPathStall_eq_expiryStages]
  exact hfinal

/-- Bounded reification and expiry retain the exact label-zero responder born
on the decisive rooted leader-sink barrier/probe edge. -/
theorem
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_barrier_probe_birth_zero
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r)
    (hl : l.core.erase.core.leader = false)
    (hr : r.core.erase.core.leader = false)
    (hprobe : r.core.erase.core.probe = true)
    (hbarrier : isBarrier hpsi l.core.erase.core r.core.erase.core) :
    ResponderZeroAnchor hpsi
      (wallSweepPreCheckResetLeaderSinkPathStallTransition
        hpsi kappa tau l r).2.core.erase.core := by
  let bounded := wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l.core r.core
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  have ha :=
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_barrier_probe_birth_zero
      hpsi kappa l.core.erase r.core.erase hopen hl hr hprobe hbarrier
  have he := erase_wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l.core r.core
  have hR := congrArg Prod.snd he
  change bounded.2.erase =
    (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).2 at hR
  have hbase : ResponderZeroAnchor hpsi rBase.core.erase.core := by
    change ResponderZeroAnchor hpsi bounded.2.erase.core
    rw [hR]
    exact ha
  have hf := deletionPriorityExpireOne_path_frame r rBase
  have hfinal : ResponderZeroAnchor hpsi
      (deletionPriorityExpireOne tau r rBase).core.erase.core :=
    ⟨hf.2.1.trans hbase.1, hf.2.2.1.trans hbase.2⟩
  rw [wallSweepPreCheckResetLeaderSinkPathStall_eq_expiryStages]
  exact hfinal

/-- The outer bounded/expiry wrappers preserve the general responder-zero
classification of a priority-open rooted leader-sink interaction. -/
theorem
    wallSweepPreCheckResetLeaderSinkPathStall_priority_open_responder_leader_zero
    (hpsi : psi > 0)
    (l r : ExpiringAgentState psi kappa tau)
    (hopen : WallPriorityOpen l r) :
    let out := wallSweepPreCheckResetLeaderSinkPathStallTransition
      hpsi kappa tau l r
    out.2.core.erase.core.leader = true →
      out.2.core.erase.core.label = ⟨0, hpsi⟩ := by
  dsimp only
  let bounded := wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l.core r.core
  let rBase : ExpiringAgentState psi kappa tau := ⟨bounded.2, r.stall⟩
  have ha :=
    wallSweepPreCheckResetLeaderSinkAuthorized_priority_open_responder_leader_zero
      hpsi kappa l.core.erase r.core.erase hopen
  have he := erase_wallSweepPreCheckResetLeaderSinkBoundedTransition
    hpsi kappa l.core r.core
  have hR := congrArg Prod.snd he
  change bounded.2.erase =
    (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
      hpsi kappa l.core.erase r.core.erase).2 at hR
  have hf := deletionPriorityExpireOne_path_frame r rBase
  rw [wallSweepPreCheckResetLeaderSinkPathStall_eq_expiryStages]
  dsimp only
  intro hout
  have hbaseLeader : bounded.2.erase.core.leader = true :=
    hf.2.1.symm.trans hout
  have haLeader :
      (wallSweepPreCheckResetLeaderSinkAuthorizedTransition
        hpsi kappa l.core.erase r.core.erase).2.core.leader = true :=
    (congrArg
      (fun u : AuthorizedAgentState psi => u.core.leader) hR).symm.trans
        hbaseLeader
  have haZero := ha haLeader
  exact hf.2.2.1.trans ((congrArg
    (fun u : AuthorizedAgentState psi => u.core.label) hR).trans haZero)


end PPLLWallSweepPreCheckResetContracts
