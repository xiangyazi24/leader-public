import Leader.Wu.Comparison.HostAlignedRepairCounterexample

/-!
# Finite stale-comparison expiration repair

Authorization alone cannot clean arbitrary complete `path` garbage: even with
both authorization bits false, a reversed complete carrier forms a closed
leaderless class. This module adds a separately counted *stall budget* to the
already finite authorized carrier. Physical movement or comparison-state/path2
progress resets the budget; a scheduled endpoint with no such progress spends
one unit; at zero, its comparison carrier and cleanup controls are deleted.

The timer is ordinary arbitrary-initialized protocol state. The local theorems
below show exact expiration and that real comparison progress is never erased in
the same interaction. The first regression breaks the seven-state trap. A full
random-scheduler cleanup theorem still requires a global argument that every
stale endpoint is scheduled through enough no-progress interactions, rather
than merely resetting through genuine progress.
-/

namespace PPLLExpiringComparisonRepair

open PPLL PPLLResearchFormulation
open PPLLAuthorizedComparisonRepair
open PPLLAuthorizedRepairCounterexample

/-- Exactly the physical fields whose change counts as useful comparison
progress. CLEAN path4/path5 oscillation is deliberately excluded. -/
structure ComparisonProgressView (ψ κ : Nat) where
  state : MainState
  path : BoundedPathInfo ψ
  path2 : Option (BoundedPath2Info ψ)
  path0Crossed : Bool
  deriving DecidableEq, Repr

/-- Project an authorized bounded state to useful comparison progress. -/
def ComparisonProgressView.ofState
    (s : AuthorizedBoundedAgentState ψ κ) : ComparisonProgressView ψ κ :=
  ⟨s.core.state, s.core.path, s.core.path2, s.path0Crossed⟩

/-- Finite executable carrier with a local no-progress budget `0,…,τ`. -/
structure ExpiringAgentState (ψ κ τ : Nat) where
  core : AuthorizedBoundedAgentState ψ κ
  stall : Fin (τ + 1)
  deriving DecidableEq, Repr

/-- Maximum local no-progress budget. -/
def freshStall (τ : Nat) : Fin (τ + 1) := ⟨τ, Nat.lt_succ_self τ⟩

/-- Decrement a positive finite budget. -/
def decStall (x : Fin (τ + 1)) (_hx : x.val > 0) : Fin (τ + 1) :=
  ⟨x.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) x.isLt⟩

/-- Delete all comparison carriers and their local cleanup/lottery controls,
while retaining unrelated leader, bullet, reset, and write machinery. -/
def clearComparisonCarrier
    (s : AuthorizedBoundedAgentState ψ κ) : AuthorizedBoundedAgentState ψ κ :=
  ⟨{ s.core with state := .none, path := .bot, path2 := none, path4 := none, path5 := none, p := false, p_carry := false }, false⟩

/-- Apply one endpoint's expiration policy after the base authorized physical
transition has already computed its output. -/
def expireOne (τ : Nat)
    (old out : ExpiringAgentState ψ κ τ) : ExpiringAgentState ψ κ τ :=
  if ComparisonProgressView.ofState out.core ≠
      ComparisonProgressView.ofState old.core then
    ⟨out.core, freshStall τ⟩
  else if hzero : old.stall.val = 0 then
    ⟨clearComparisonCarrier out.core, freshStall τ⟩
  else
    ⟨out.core, decStall old.stall (Nat.pos_of_ne_zero hzero)⟩

/-- Total finite transition: run the authorized comparison repair, then apply
endpoint-local stale-carrier expiration. -/
def expiringTransition (hψ : ψ > 0) (κ τ : Nat)
    (l r : ExpiringAgentState ψ κ τ) :
    ExpiringAgentState ψ κ τ × ExpiringAgentState ψ κ τ :=
  let q := authorizedBoundedTransition hψ κ l.core r.core
  let lOut : ExpiringAgentState ψ κ τ := ⟨q.1, l.stall⟩
  let rOut : ExpiringAgentState ψ κ τ := ⟨q.2, r.stall⟩
  (expireOne τ l lOut, expireOne τ r rOut)

/-- Real state/path/path2/authorization progress preserves the base output and
resets the timer; expiration cannot erase that output in the same interaction. -/
theorem expireOne_of_progress (τ : Nat)
    (old out : ExpiringAgentState ψ κ τ)
    (hprogress : ComparisonProgressView.ofState out.core ≠
      ComparisonProgressView.ofState old.core) :
    expireOne τ old out = ⟨out.core, freshStall τ⟩ := by
  simp [expireOne, hprogress]

/-- At zero budget and no useful progress, the comparison carrier is deleted. -/
theorem expireOne_zero_of_no_progress (τ : Nat)
    (old out : ExpiringAgentState ψ κ τ)
    (hprogress : ComparisonProgressView.ofState out.core =
      ComparisonProgressView.ofState old.core)
    (hzero : old.stall.val = 0) :
    expireOne τ old out =
      ⟨clearComparisonCarrier out.core, freshStall τ⟩ := by
  simp [expireOne, hprogress, hzero]

/-- A positive no-progress budget decrements by exactly one. -/
theorem expireOne_succ_of_no_progress (τ : Nat)
    (old out : ExpiringAgentState ψ κ τ)
    (hprogress : ComparisonProgressView.ofState out.core =
      ComparisonProgressView.ofState old.core)
    (hpos : old.stall.val > 0) :
    expireOne τ old out = ⟨out.core, decStall old.stall hpos⟩ := by
  unfold expireOne
  rw [if_neg (not_not_intro hprogress)]
  split
  · rename_i hzero
    have : False := by omega
    exact this.elim
  · rfl

/-- Every positive no-progress tick strictly decreases the executable stall
budget. -/
theorem expireOne_stall_decreases (τ : Nat)
    (old out : ExpiringAgentState ψ κ τ)
    (hprogress : ComparisonProgressView.ofState out.core =
      ComparisonProgressView.ofState old.core)
    (hpos : old.stall.val > 0) :
    (expireOne τ old out).stall.val < old.stall.val := by
  rw [expireOne_succ_of_no_progress τ old out hprogress hpos]
  unfold decStall
  dsimp only
  omega

/-- Zero-budget no-progress expiration physically removes path, path2, and the
permission bit. -/
theorem expireOne_zero_clears_comparison (τ : Nat)
    (old out : ExpiringAgentState ψ κ τ)
    (hprogress : ComparisonProgressView.ofState out.core =
      ComparisonProgressView.ofState old.core)
    (hzero : old.stall.val = 0) :
    let q := expireOne τ old out
    q.core.core.path = .bot ∧ q.core.core.path2 = none ∧
      q.core.path0Crossed = false := by
  rw [expireOne_zero_of_no_progress τ old out hprogress hzero]
  simp [clearComparisonCarrier]

/-- Parameter regime with at least two ψ-agent groups. The lower bound excludes
the one-group n=2,ψ=2 leaderless class while retaining the asymptotic family. -/
structure ExpiringRepairRegime (ψ n : Nat) where
  hψ : ψ > 0
  ring : DirectedRing n
  twoGroups : 2 * ψ ≤ n

/-- The ψ=2 one-group ring is outside the stated expiration-repair regime. -/
theorem no_expiring_regime_two_two : ExpiringRepairRegime 2 2 → False := by
  intro h
  have htwo := h.twoGroups
  omega

/-- Packaged finite population protocol for the expiration repair. -/
def expiringProtocol (hψ : ψ > 0) (κ τ : Nat) : PopulationProtocol where
  Q := ExpiringAgentState ψ κ τ
  Y := LeaderOutput
  transition := expiringTransition hψ κ τ
  output := fun s => if s.core.core.leader then .leader else .follower

/-- Constructive exhaustive list for the timer-extended finite carrier. -/
def expiringAgentState (ψ κ τ : Nat) :
    ExhaustiveList (ExpiringAgentState ψ κ τ) :=
  ExhaustiveList.mapSurjective
    (ExhaustiveList.prod (authorizedBoundedAgentState ψ κ)
      (ExhaustiveList.fin (τ + 1)))
    (fun x => ⟨x.1, x.2⟩)
    (by
      intro s
      exact ⟨(s.core, s.stall), rfl⟩)

/-- The timer-extended certificate is duplicate-free. -/
theorem expiringAgentState_values_nodup (ψ κ τ : Nat) :
    (expiringAgentState ψ κ τ).values.Nodup := by
  unfold expiringAgentState
  apply ExhaustiveList.values_nodup_mapSurjective
  · apply ExhaustiveList.values_nodup_prod
    · exact authorizedBoundedAgentState_values_nodup ψ κ
    · exact ExhaustiveList.values_nodup_fin (τ + 1)
  · intro x y h
    rcases x with ⟨xc, xs⟩
    rcases y with ⟨yc, ys⟩
    cases h
    rfl

/-- The timer-extended certificate multiplies exact semantic cardinality by
`τ+1`. -/
theorem expiringAgentState_values_length (ψ κ τ : Nat) :
    (expiringAgentState ψ κ τ).values.length =
      (2 * (PPLLFinite.boundedAgentState ψ κ).values.length) * (τ + 1) := by
  unfold expiringAgentState ExhaustiveList.mapSurjective
  rw [List.length_map, ExhaustiveList.values_length_prod,
    authorizedBoundedAgentState_values_length,
    ExhaustiveList.values_length_fin]

/-- Every timer-extended state has an explicit finite index. -/
theorem expiringAgentState_decode_surjective (ψ κ τ : Nat) :
    Function.Surjective (expiringAgentState ψ κ τ).decode :=
  (expiringAgentState ψ κ τ).decode_surjective

/-- Exact finite-index representation of expiration states. -/
theorem expiringAgentState_decode_bijective (ψ κ τ : Nat) :
    Function.Injective (expiringAgentState ψ κ τ).decode ∧
      Function.Surjective (expiringAgentState ψ κ τ).decode :=
  ⟨ExhaustiveList.decode_injective_of_values_nodup _
      (expiringAgentState_values_nodup ψ κ τ),
    expiringAgentState_decode_surjective ψ κ τ⟩

/-! ## Seven-state-trap regression -/

private def reifyTrapAgent (u : AuthorizedAgentState 2)
    (hu : u.core.inProtocolDomain 0) : AuthorizedBoundedAgentState 2 0 :=
  ⟨BoundedAgentState.ofDomain u.core hu, u.path0Crossed⟩

private theorem trapPairDomain :
    trapInitial.1.core.inProtocolDomain 0 ∧
      trapInitial.2.core.inProtocolDomain 0 :=
  trap_inProtocolDomain trapInitial_mem

private def expiringTrapLeft : ExpiringAgentState 2 0 0 :=
  ⟨reifyTrapAgent trapInitial.1 trapPairDomain.1, 0⟩

private def expiringTrapRight : ExpiringAgentState 2 0 0 :=
  ⟨reifyTrapAgent trapInitial.2 trapPairDomain.2, 0⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- With zero stall budget, one interaction deletes both reversed carrier
components; the former seven-state class is not closed in this repair. -/
theorem expiring_breaks_authorized_trap :
    let q := expiringTransition (by omega : 2 > 0) 0 0
      expiringTrapLeft expiringTrapRight
    q.1.core.core.path = .bot ∧ q.2.core.core.path = .bot ∧
      q.1.core.path0Crossed = false ∧ q.2.core.path0Crossed = false := by
  decide

private def progressAuditLeft : AuthorizedAgentState 2 :=
  ⟨{ PPLLCounterexample.state2 0 false .depart with path := .some 0 0 }, true⟩

private def progressAuditRight : AuthorizedAgentState 2 :=
  ⟨{ PPLLCounterexample.state2 1 false .depart with path := .some 1 0 }, false⟩

private theorem progressAuditDomain :
    progressAuditLeft.core.inProtocolDomain 0 ∧
      progressAuditRight.core.inProtocolDomain 0 := by
  simp [progressAuditLeft, progressAuditRight, AgentState.inProtocolDomain,
    PPLLCounterexample.state2]

private def progressLeft : ExpiringAgentState 2 0 0 :=
  ⟨⟨BoundedAgentState.ofDomain progressAuditLeft.core progressAuditDomain.1,
      true⟩, 0⟩

private def progressRight : ExpiringAgentState 2 0 0 :=
  ⟨⟨BoundedAgentState.ofDomain progressAuditRight.core progressAuditDomain.2,
      false⟩, 0⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- A genuine authorized comparison changes state, so even zero budget does not
erase its paths in that interaction. -/
theorem expiring_preserves_real_comparison_progress :
    let q := expiringTransition (by omega : 2 > 0) 0 0
      progressLeft progressRight
    q.1.core.core.state = .congest ∧ q.2.core.core.state = .congest ∧
      q.1.core.core.path ≠ .bot ∧ q.2.core.core.path ≠ .bot := by
  decide

/-! ## Nondegenerate n=4 recovery witness -/

private def recoveryAuditA : AuthorizedAgentState 2 :=
  ⟨{ PPLLCounterexample.state2 0 false .depart with wait := false, path := .some 1 0, path4 := some (1, 1) }, false⟩

private def recoveryAuditB : AuthorizedAgentState 2 :=
  ⟨{ PPLLCounterexample.state2 1 false .depart with wait := true, path := .some 0 0, path5 := some (0, 1) }, true⟩

private theorem recoveryAuditDomain :
    recoveryAuditA.core.inProtocolDomain 0 ∧
      recoveryAuditB.core.inProtocolDomain 0 := by
  simp [recoveryAuditA, recoveryAuditB, AgentState.inProtocolDomain,
    PPLLCounterexample.state2]

private def recoveryA : ExpiringAgentState 2 0 0 :=
  ⟨⟨BoundedAgentState.ofDomain recoveryAuditA.core recoveryAuditDomain.1,
      false⟩, 0⟩

private def recoveryB : ExpiringAgentState 2 0 0 :=
  ⟨⟨BoundedAgentState.ofDomain recoveryAuditB.core recoveryAuditDomain.2,
      true⟩, 0⟩

abbrev recoveryRing : DirectedRing 4 := ⟨by omega⟩

def recoveryConfig : Fin 4 → ExpiringAgentState 2 0 0
  | ⟨0, _⟩ => recoveryA
  | ⟨1, _⟩ => recoveryB
  | ⟨2, _⟩ => recoveryA
  | ⟨3, _⟩ => recoveryB

def recoveryAfter : Fin 4 → ExpiringAgentState 2 0 0 :=
  runLocalSchedule recoveryRing (expiringTransition (by omega) 0 0)
    recoveryConfig [1, 0, 3, 0]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- On a nondegenerate two-group ring, the explicit four-edge schedule first
expires the repeated reversed carriers and then produces exactly one leader at
position zero. This witnesses a real recovery route but not a universal phase. -/
theorem expiring_n4_recovery_schedule_outputs :
    (recoveryAfter 0).core.core.leader = true ∧
      (recoveryAfter 1).core.core.leader = false ∧
      (recoveryAfter 2).core.core.leader = false ∧
      (recoveryAfter 3).core.core.leader = false := by
  decide

private def recoveryBadFuture : Fin 4 → ExpiringAgentState 2 0 0 :=
  runLocalSchedule recoveryRing (expiringTransition (by omega) 0 0)
    recoveryAfter [1, 0, 2, 1, 2]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- The recovered unique leader is not yet Definition-1 stable: an explicit
five-edge continuation creates a second leader at position two. -/
theorem expiring_n4_recovery_not_output_stable :
    (recoveryBadFuture 0).core.core.leader = true ∧
      (recoveryBadFuture 2).core.core.leader = true := by
  decide

end PPLLExpiringComparisonRepair
