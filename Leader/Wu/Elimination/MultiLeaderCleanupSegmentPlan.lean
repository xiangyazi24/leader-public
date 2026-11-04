import Leader.Wu.Elimination.MultiLeaderCleanup
import Leader.Wu.Safety.SafeConfig
import Leader.Wu.Safety.NoCheckBirthConditionTwoProtocol

/-!
# Multi-leader cleanup producer audit

The existing `TwoLeaderCleanupReady` predicate is an exact-two-leader base
case.  This module isolates the selector and segment interfaces needed by an
arbitrary multi-leader round, while allowing untouched leaders outside the two
active arcs.
-/

namespace PPLLCompleteMultiLeaderCleanup

open PPLL PPLLRepair PPLLResearchFormulation
  PPLLNoCheckBirthConditionTwoGeometry
  PPLLNoCheckBirthConditionTwoPhysical
  PPLLNoCheckBirthConditionTwoProtocol

variable {n psi : Nat}

private def rawLeaderTrueCount {m : Nat}
    (bits : Fin m → Bool) : Nat :=
  (List.ofFn fun i => if bits i then 1 else 0).sum

private theorem rawLeaderTrueCount_succ {m : Nat}
    (bits : Fin (m + 1) → Bool) :
    rawLeaderTrueCount bits =
      (if bits 0 then 1 else 0) +
        rawLeaderTrueCount (fun i : Fin m => bits i.succ) := by
  rw [rawLeaderTrueCount, List.ofFn_succ]
  rfl

private theorem rawPhysicalLeaderCount_eq_rawLeaderTrueCount
    (C : Fin n → AgentState psi) :
    rawPhysicalLeaderCount C =
      rawLeaderTrueCount (fun i => (C i).leader) := by
  rfl

private theorem exists_true_of_rawLeaderTrueCount_pos {m : Nat}
    (bits : Fin m → Bool)
    (hcount : 0 < rawLeaderTrueCount bits) :
    ∃ i, bits i = true := by
  induction m with
  | zero =>
      simp [rawLeaderTrueCount] at hcount
  | succ m ih =>
      rw [rawLeaderTrueCount_succ] at hcount
      cases hhead : bits 0 with
      | false =>
          have htail :
              0 < rawLeaderTrueCount (fun i : Fin m => bits i.succ) := by
            simpa [hhead] using hcount
          obtain ⟨i, hi⟩ := ih (fun j : Fin m => bits j.succ) htail
          exact ⟨i.succ, hi⟩
      | true =>
          exact ⟨0, hhead⟩

private theorem exists_two_true_of_rawLeaderTrueCount_gt_one {m : Nat}
    (bits : Fin m → Bool)
    (hcount : 1 < rawLeaderTrueCount bits) :
    ∃ i j, i ≠ j ∧ bits i = true ∧ bits j = true := by
  induction m with
  | zero =>
      simp [rawLeaderTrueCount] at hcount
  | succ m ih =>
      rw [rawLeaderTrueCount_succ] at hcount
      cases hhead : bits 0 with
      | false =>
          have htail :
              1 < rawLeaderTrueCount (fun i : Fin m => bits i.succ) := by
            simpa [hhead] using hcount
          obtain ⟨i, j, hij, hi, hj⟩ :=
            ih (fun k : Fin m => bits k.succ) htail
          have hneSucc : i.succ ≠ j.succ := by
            intro hEq
            apply hij
            exact Fin.succ_inj.mp hEq
          exact ⟨i.succ, j.succ, hneSucc, hi, hj⟩
      | true =>
          have htailPos :
              0 < rawLeaderTrueCount (fun i : Fin m => bits i.succ) := by
            have hsum :
                1 < 1 + rawLeaderTrueCount
                  (fun i : Fin m => bits i.succ) := by
              simpa [hhead] using hcount
            omega
          obtain ⟨j, hj⟩ :=
            exists_true_of_rawLeaderTrueCount_pos
              (fun i : Fin m => bits i.succ) htailPos
          have hzeroNe : (0 : Fin (m + 1)) ≠ j.succ := by
            intro hEq
            have hv := congrArg Fin.val hEq
            simp at hv
          exact ⟨0, j.succ, hzeroNe, hhead, hj⟩

private theorem cwDist_self
    (ring : DirectedRing n) (i : Fin n) :
    cwDist ring i i = 0 := by
  unfold cwDist
  have hsum : i.val + n - i.val = n := by omega
  rw [hsum, Nat.mod_self]

private theorem cwDist_pos_of_ne
    (ring : DirectedRing n) {i j : Fin n} (hij : i ≠ j) :
    0 < cwDist ring i j := by
  have hne : cwDist ring i j ≠ 0 := by
    intro hzero
    have hpos := cwPos_cwDist ring i j
    rw [hzero, cwPos_zero] at hpos
    exact hij hpos
  omega

/-- The first physical leader clockwise from `L1`; only the strict open arc
is asserted to contain followers. -/
structure ClockwiseConsecutivePhysicalLeaders
    (ring : DirectedRing n) (C : Fin n → AgentState psi) where
  L1 : Fin n
  L2 : Fin n
  distance : Nat
  L1_leader : (C L1).leader = true
  L2_leader : (C L2).leader = true
  leaders_ne : L1 ≠ L2
  distance_eq : distance = cwDist ring L1 L2
  distance_pos : 0 < distance
  distance_lt : distance < n
  L2_eq : L2 = cwPos ring L1 distance
  no_leader_between : ∀ k, 0 < k → k < distance →
    (C (cwPos ring L1 k)).leader = false

/-- The first physical leader clockwise from a fixed named start. -/
structure FirstClockwisePhysicalLeader
    (ring : DirectedRing n) (C : Fin n → AgentState psi)
    (start : Fin n) where
  target : Fin n
  distance : Nat
  start_leader : (C start).leader = true
  target_leader : (C target).leader = true
  leaders_ne : start ≠ target
  distance_eq : distance = cwDist ring start target
  distance_pos : 0 < distance
  distance_lt : distance < n
  target_eq : target = cwPos ring start distance
  no_leader_between : ∀ k, 0 < k → k < distance →
    (C (cwPos ring start k)).leader = false

theorem firstClockwisePhysicalLeader_of_other
    (ring : DirectedRing n) (C : Fin n → AgentState psi)
    (start other : Fin n)
    (hstart : (C start).leader = true)
    (hother : (C other).leader = true)
    (hne : start ≠ other) :
    Nonempty (FirstClockwisePhysicalLeader ring C start) := by
  classical
  let P : Nat → Prop := fun k =>
    0 < k ∧ k < n ∧ (C (cwPos ring start k)).leader = true
  have hWitness : ∃ k, P k := by
    refine ⟨cwDist ring start other,
      cwDist_pos_of_ne ring hne,
      cwDist_lt ring start other, ?_⟩
    rw [cwPos_cwDist]
    exact hother
  have minimalDistance : ∀ d, P d →
      ∃ e, P e ∧ ∀ k, 0 < k → k < e →
        (C (cwPos ring start k)).leader = false := by
    intro d hd
    induction d using Nat.strongRecOn with
    | ind d ih =>
        by_cases hsmaller : ∃ k, 0 < k ∧ k < d ∧
            (C (cwPos ring start k)).leader = true
        · obtain ⟨k, hkPos, hkLt, hkLeader⟩ := hsmaller
          exact ih k hkLt ⟨hkPos, by omega, hkLeader⟩
        · refine ⟨d, hd, ?_⟩
          intro k hkPos hkLt
          cases hbit : (C (cwPos ring start k)).leader with
          | false => exact rfl
          | true =>
              exact (hsmaller ⟨k, hkPos, hkLt, hbit⟩).elim
  obtain ⟨d, hdSpec, hdMinimal⟩ :=
    minimalDistance (cwDist ring start other)
      ⟨cwDist_pos_of_ne ring hne, cwDist_lt ring start other, by
        rw [cwPos_cwDist]
        exact hother⟩
  have hdPos : 0 < d := hdSpec.1
  have hdLt : d < n := hdSpec.2.1
  let target := cwPos ring start d
  have htarget : (C target).leader = true := by
    simpa [target] using hdSpec.2.2
  have hstartTarget : start ≠ target := by
    intro hEq
    have hpos : cwPos ring start d = start := by
      simpa [target] using hEq.symm
    have hd0 : d = cwDist ring start start :=
      cwPos_bounded_unique ring start start d hdLt hpos
    rw [cwDist_self] at hd0
    omega
  have hdEq : d = cwDist ring start target := by
    simpa [target] using
      (cwPos_bounded_unique ring start
        (cwPos ring start d) d hdLt rfl)
  exact ⟨{
    target := target
    distance := d
    start_leader := hstart
    target_leader := htarget
    leaders_ne := hstartTarget
    distance_eq := hdEq
    distance_pos := hdPos
    distance_lt := hdLt
    target_eq := rfl
    no_leader_between := hdMinimal }⟩

def NoAdjacentPhysicalLeaders
    (ring : DirectedRing n) (C : Fin n → AgentState psi) : Prop :=
  ∀ i, (C i).leader = true →
    (C (ring.rightNeighbor i)).leader = false

theorem FirstClockwisePhysicalLeader.distance_nonadjacent
    {ring : DirectedRing n} {C : Fin n → AgentState psi}
    {start : Fin n}
    (first : FirstClockwisePhysicalLeader ring C start)
    (hnoAdjacent : NoAdjacentPhysicalLeaders ring C) :
    1 < first.distance := by
  have hright := hnoAdjacent start first.start_leader
  have hneOne : first.distance ≠ 1 := by
    intro hd
    have ht : first.target = ring.rightNeighbor start := by
      calc
        first.target = cwPos ring start first.distance := first.target_eq
        _ = cwPos ring start 1 := by rw [hd]
        _ = ring.rightNeighbor start := by
          simpa using (cwPos_succ ring start 0)
    have htarget := first.target_leader
    rw [ht, hright] at htarget
    simp at htarget
  have hpos : 0 < first.distance := first.distance_pos
  omega

theorem exists_clockwiseConsecutivePhysicalLeaders_of_count_gt_one
    (ring : DirectedRing n) (C : Fin n → AgentState psi)
    (hcount : 1 < rawPhysicalLeaderCount C) :
    Nonempty (ClockwiseConsecutivePhysicalLeaders ring C) := by
  classical
  have hbits :
      1 < rawLeaderTrueCount (fun i => (C i).leader) := by
    rw [← rawPhysicalLeaderCount_eq_rawLeaderTrueCount C]
    exact hcount
  obtain ⟨L1, Lx, hne, hL1, hLx⟩ :=
    exists_two_true_of_rawLeaderTrueCount_gt_one
      (fun i => (C i).leader) hbits
  let P : Nat → Prop := fun k =>
    0 < k ∧ k < n ∧ (C (cwPos ring L1 k)).leader = true
  have hWitness : ∃ k, P k := by
    refine ⟨cwDist ring L1 Lx,
      cwDist_pos_of_ne ring hne,
      cwDist_lt ring L1 Lx, ?_⟩
    rw [cwPos_cwDist]
    exact hLx
  have minimalDistance : ∀ d, P d →
      ∃ e, P e ∧ ∀ k, 0 < k → k < e →
        (C (cwPos ring L1 k)).leader = false := by
    intro d hd
    induction d using Nat.strongRecOn with
    | ind d ih =>
        by_cases hsmaller : ∃ k, 0 < k ∧ k < d ∧
            (C (cwPos ring L1 k)).leader = true
        · obtain ⟨k, hkPos, hkLt, hkLeader⟩ := hsmaller
          exact ih k hkLt ⟨hkPos, by omega, hkLeader⟩
        · refine ⟨d, hd, ?_⟩
          intro k hkPos hkLt
          cases hbit : (C (cwPos ring L1 k)).leader with
          | false => exact rfl
          | true =>
              exact (hsmaller ⟨k, hkPos, hkLt, hbit⟩).elim
  obtain ⟨d, hdSpec, hdMinimal⟩ :=
    minimalDistance (cwDist ring L1 Lx)
      ⟨cwDist_pos_of_ne ring hne, cwDist_lt ring L1 Lx, by
        rw [cwPos_cwDist]
        exact hLx⟩
  have hdPos : 0 < d := hdSpec.1
  have hdLt : d < n := hdSpec.2.1
  let L2 := cwPos ring L1 d
  have hL2 : (C L2).leader = true := by
    simpa [L2] using hdSpec.2.2
  have hL1L2 : L1 ≠ L2 := by
    intro hEq
    have hpos : cwPos ring L1 d = L1 := by
      simpa [L2] using hEq.symm
    have hd0 : d = cwDist ring L1 L1 :=
      cwPos_bounded_unique ring L1 L1 d hdLt hpos
    rw [cwDist_self] at hd0
    omega
  have hdEq : d = cwDist ring L1 L2 := by
    simpa [L2] using
      (cwPos_bounded_unique ring L1 (cwPos ring L1 d) d hdLt rfl)
  refine ⟨{
    L1 := L1
    L2 := L2
    distance := d
    L1_leader := hL1
    L2_leader := hL2
    leaders_ne := hL1L2
    distance_eq := hdEq
    distance_pos := hdPos
    distance_lt := hdLt
    L2_eq := rfl
    no_leader_between := ?_ }⟩
  intro k hkPos hkLt
  cases hbit : (C (cwPos ring L1 k)).leader with
  | false => exact rfl
  | true =>
      simpa [hbit] using hdMinimal k hkPos hkLt

/-- Raw physical fields sufficient to expose any consecutive-leader arc. -/
structure MultiLeaderStaticEntry
    (hpsi : psi > 0) (ring : DirectedRing n)
    (C : Fin n → AgentState psi) : Prop where
  leaders_zero : ∀ i, (C i).leader = true →
    (C i).label = ⟨0, hpsi⟩
  leaders_shielded : ∀ i, (C i).leader = true →
    (C i).shield = true
  bullets_zero : ∀ i, (C i).bullet = ⟨0, by omega⟩
  signals_zero : ∀ i, (C i).signal_B = ⟨0, by omega⟩
  no_free_barrier : noFreeBarrier hpsi ring C

/-- The clean one-arc slice selected from an arbitrary multi-leader entry. -/
structure ConsecutiveArcReady
    (hpsi : psi > 0) (ring : DirectedRing n)
    (C : Fin n → AgentState psi)
    (pair : ClockwiseConsecutivePhysicalLeaders ring C) : Prop where
  source_zero : (C pair.L1).label = ⟨0, hpsi⟩
  target_zero : (C pair.L2).label = ⟨0, hpsi⟩
  source_shielded : (C pair.L1).shield = true
  target_shielded : (C pair.L2).shield = true
  bullets_zero : ∀ k, k ≤ pair.distance →
    (C (cwPos ring pair.L1 k)).bullet = ⟨0, by omega⟩
  signals_zero : ∀ k, k ≤ pair.distance →
    (C (cwPos ring pair.L1 k)).signal_B = ⟨0, by omega⟩
  followers : ∀ k, 0 < k → k < pair.distance →
    (C (cwPos ring pair.L1 k)).leader = false
  aligned : ∀ k, k + 1 < pair.distance →
    (C (cwPos ring pair.L1 (k + 1))).label =
      ⟨((C (cwPos ring pair.L1 k)).label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩

theorem MultiLeaderStaticEntry.arcReady
    {hpsi : psi > 0} {ring : DirectedRing n}
    {C : Fin n → AgentState psi}
    (hentry : MultiLeaderStaticEntry hpsi ring C)
    (pair : ClockwiseConsecutivePhysicalLeaders ring C) :
    ConsecutiveArcReady hpsi ring C pair := by
  refine {
    source_zero := hentry.leaders_zero pair.L1 pair.L1_leader
    target_zero := hentry.leaders_zero pair.L2 pair.L2_leader
    source_shielded :=
      hentry.leaders_shielded pair.L1 pair.L1_leader
    target_shielded :=
      hentry.leaders_shielded pair.L2 pair.L2_leader
    bullets_zero := ?_
    signals_zero := ?_
    followers := pair.no_leader_between
    aligned := ?_ }
  · intro k _
    exact hentry.bullets_zero _
  · intro k _
    exact hentry.signals_zero _
  · intro k hk
    have hfollow :
        (C (cwPos ring pair.L1 (k + 1))).leader = false :=
      pair.no_leader_between (k + 1) (by omega) hk
    have hnotLeader :
        ¬(C (ring.rightNeighbor (cwPos ring pair.L1 k))).isLeader := by
      have hpos :
          ring.rightNeighbor (cwPos ring pair.L1 k) =
            cwPos ring pair.L1 (k + 1) :=
        (cwPos_succ ring pair.L1 k).symm
      rw [hpos, AgentState.isLeader, hfollow]
      decide
    have hlabel :=
      successor_label_of_noFreeBarrier_of_right_not_leader
        hpsi ring C hentry.no_free_barrier
        (cwPos ring pair.L1 k) hnotLeader
    simpa only [cwPos_succ] using hlabel

theorem exists_consecutiveArcReady_of_static_count_gt_one
    {hpsi : psi > 0} {ring : DirectedRing n}
    {C : Fin n → AgentState psi}
    (hentry : MultiLeaderStaticEntry hpsi ring C)
    (hcount : 1 < rawPhysicalLeaderCount C) :
    ∃ pair : ClockwiseConsecutivePhysicalLeaders ring C,
      ConsecutiveArcReady hpsi ring C pair := by
  obtain ⟨pair⟩ :=
    exists_clockwiseConsecutivePhysicalLeaders_of_count_gt_one
      ring C hcount
  exact ⟨pair, hentry.arcReady pair⟩

theorem TwoLeaderCleanupReady.leader_false_of_ne
    {hpsi : psi > 0} {ring : DirectedRing n}
    {plan : TwoLeaderCleanupSchedule ring}
    {C : Fin n → AgentState psi}
    (hready : TwoLeaderCleanupReady hpsi ring plan C)
    (i : Fin n) (hi1 : i ≠ plan.L1) (hi2 : i ≠ plan.L2) :
    (C i).leader = false := by
  cases hleader : (C i).leader with
  | false => exact rfl
  | true =>
      rcases (hready.leaders_exact i).1 hleader with h | h
      · exact (hi1 h).elim
      · exact (hi2 h).elim

/-- A cleanup segment uses two consecutive-leader arcs.  `pred = source`
recovers the exact-two-leader base case. -/
structure SegmentCleanupPlan (ring : DirectedRing n) where
  pred : Fin n
  victim : Fin n
  source : Fin n
  pred_ne_victim : pred ≠ victim
  victim_ne_source : victim ≠ source
  dPV : Nat
  dVS : Nat
  dPV_eq : dPV = cwDist ring pred victim
  dVS_eq : dVS = cwDist ring victim source
  dPV_pos : 0 < dPV
  dVS_pos : 0 < dVS
  dPV_lt : dPV < n
  dVS_lt : dVS < n
  dPV_nonadjacent : 1 < dPV
  dVS_nonadjacent : 1 < dVS

namespace SegmentCleanupPlan

variable {ring : DirectedRing n}

theorem cwPos_add_segment
    (ring : DirectedRing n) (start : Fin n) (a b : Nat) :
    cwPos ring (cwPos ring start a) b = cwPos ring start (a + b) := by
  apply Fin.ext
  unfold cwPos
  dsimp only
  rw [Nat.mod_add_mod]
  congr 1
  omega

theorem cwPos_ne_of_ne_below_segment
    (ring : DirectedRing n) (start : Fin n)
    {a b : Nat} (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    cwPos ring start a ≠ cwPos ring start b := by
  intro hpos
  apply hab
  have ha' := cwPos_bounded_unique ring start
    (cwPos ring start a) a ha rfl
  have hb' := cwPos_bounded_unique ring start
    (cwPos ring start a) b hb hpos.symm
  exact ha'.trans hb'.symm

/-- Incoming edge of the victim on the predecessor arc. -/
def predIncoming (plan : SegmentCleanupPlan ring) : Fin n :=
  cwPos ring plan.pred (plan.dPV - 1)

/-- The surviving source is exactly one edge beyond the repaired follower
interval.  This identity uses only the two canonical clockwise distances and
does not need a separate sum-of-arcs field. -/
theorem source_eq_cwPos_predIncoming_dVS_succ
    (plan : SegmentCleanupPlan ring) :
    cwPos ring plan.predIncoming (plan.dVS + 1) = plan.source := by
  have hdPV := plan.dPV_pos
  calc
    cwPos ring plan.predIncoming (plan.dVS + 1) =
        cwPos ring plan.pred
          ((plan.dPV - 1) + (plan.dVS + 1)) := by
      rw [predIncoming, cwPos_add_segment]
    _ = cwPos ring plan.pred (plan.dPV + plan.dVS) := by
      congr 1
      omega
    _ = cwPos ring (cwPos ring plan.pred plan.dPV) plan.dVS := by
      rw [cwPos_add_segment]
    _ = cwPos ring plan.victim plan.dVS := by
      rw [plan.dPV_eq, cwPos_cwDist]
    _ = plan.source := by
      rw [plan.dVS_eq, cwPos_cwDist]

theorem targetPV (plan : SegmentCleanupPlan ring) :
    cwPos ring plan.pred plan.dPV = plan.victim := by
  rw [plan.dPV_eq, cwPos_cwDist]

theorem targetVS (plan : SegmentCleanupPlan ring) :
    cwPos ring plan.victim plan.dVS = plan.source := by
  rw [plan.dVS_eq, cwPos_cwDist]

theorem targetPVS (plan : SegmentCleanupPlan ring) :
    cwPos ring plan.pred (plan.dPV + plan.dVS) = plan.source := by
  rw [← cwPos_add_segment, plan.targetPV, plan.targetVS]

theorem predIncoming_right (plan : SegmentCleanupPlan ring) :
    ring.rightNeighbor plan.predIncoming = plan.victim := by
  have hdPV := plan.dPV_pos
  calc
    ring.rightNeighbor plan.predIncoming =
        cwPos ring plan.pred ((plan.dPV - 1) + 1) := by
      rw [predIncoming, cwPos_succ]
    _ = cwPos ring plan.pred plan.dPV := by congr 1 <;> omega
    _ = plan.victim := plan.targetPV

theorem predIncoming_ne_victim (plan : SegmentCleanupPlan ring) :
    plan.predIncoming ≠ plan.victim := by
  have hdPV := plan.dPV_pos
  have hdPVlt := plan.dPV_lt
  rw [← plan.targetPV, predIncoming]
  exact cwPos_ne_of_ne_below_segment ring plan.pred
    (by omega) plan.dPV_lt (by omega)

theorem arcVS_as_pred (plan : SegmentCleanupPlan ring) (k : Nat) :
    cwPos ring plan.victim k = cwPos ring plan.pred (plan.dPV + k) := by
  calc
    cwPos ring plan.victim k =
        cwPos ring (cwPos ring plan.pred plan.dPV) k := by
      rw [plan.targetPV]
    _ = cwPos ring plan.pred (plan.dPV + k) :=
      cwPos_add_segment ring plan.pred plan.dPV k

theorem arcVS_interior_ne_predIncoming
    (plan : SegmentCleanupPlan ring)
    (hsum : plan.dPV + plan.dVS ≤ n)
    (k : Nat) (hk0 : 0 < k) (hk : k < plan.dVS) :
    cwPos ring plan.victim k ≠ plan.predIncoming := by
  rw [plan.arcVS_as_pred, predIncoming]
  exact cwPos_ne_of_ne_below_segment ring plan.pred
    (by omega) (by omega) (by omega)

theorem arcVS_interior_ne_victim
    (plan : SegmentCleanupPlan ring)
    (k : Nat) (hk0 : 0 < k) (hk : k < plan.dVS) :
    cwPos ring plan.victim k ≠ plan.victim := by
  have hdVSlt := plan.dVS_lt
  simpa using cwPos_ne_of_ne_below_segment ring plan.victim
    (a := k) (b := 0) (by omega) ring.hn (by omega)

theorem arcVS_interior_ne_source
    (plan : SegmentCleanupPlan ring)
    (k : Nat) (hk0 : 0 < k) (hk : k < plan.dVS) :
    cwPos ring plan.victim k ≠ plan.source := by
  have hdVSlt := plan.dVS_lt
  rw [← plan.targetVS]
  exact cwPos_ne_of_ne_below_segment ring plan.victim
    (by omega) plan.dVS_lt (by omega)

theorem source_ne_predIncoming_of_dVS_succ_lt
    (plan : SegmentCleanupPlan ring) (hbound : plan.dVS + 1 < n) :
    plan.source ≠ plan.predIncoming := by
  rw [← plan.source_eq_cwPos_predIncoming_dVS_succ]
  simpa using cwPos_ne_of_ne_below_segment ring plan.predIncoming
    (a := plan.dVS + 1) (b := 0) hbound ring.hn (by omega)

theorem source_ne_rightNeighbor_victim
    (plan : SegmentCleanupPlan ring) :
    plan.source ≠ ring.rightNeighbor plan.victim := by
  have hdVS := plan.dVS_nonadjacent
  have hdVSlt := plan.dVS_lt
  rw [← plan.targetVS,
    show ring.rightNeighbor plan.victim = cwPos ring plan.victim 1 by simp]
  exact cwPos_ne_of_ne_below_segment ring plan.victim
    plan.dVS_lt (by omega) (by omega)

/-- Raw leader-kill word.  The complete repaired transition must subsequently
sweep the new merged follower segment. -/
def word (plan : SegmentCleanupPlan ring) : DetSchedule n :=
  clockwiseEdgeSchedule ring plan.pred plan.dPV ++
    [plan.predIncoming] ++
    clockwiseEdgeSchedule ring plan.victim plan.dVS ++
    [plan.source] ++
    reversePositiveEdgeSchedule ring plan.victim (plan.dVS - 1) ++
    [plan.victim]

/-- Post-kill sweep of the merged follower segment.  It starts at the edge
entering the deleted victim and stops before the surviving source leader. -/
def repairTail (plan : SegmentCleanupPlan ring) : DetSchedule n :=
  clockwiseEdgeSchedule ring plan.predIncoming plan.dVS

@[simp] theorem repairTail_length (plan : SegmentCleanupPlan ring) :
    plan.repairTail.length = plan.dVS := by
  simp [repairTail]

/-- Round word for the actual reset-aware transition.  A singleton interaction
at `predIncoming` is insufficient: it can move the free barrier one edge
clockwise.  The whole merged follower segment is swept. -/
def fullWord (plan : SegmentCleanupPlan ring) : DetSchedule n :=
  plan.word ++ plan.repairTail

theorem word_length (plan : SegmentCleanupPlan ring) :
    plan.word.length = plan.dPV + 2 * plan.dVS + 2 := by
  have hVS := plan.dVS_pos
  simp [word]
  omega

theorem fullWord_length (plan : SegmentCleanupPlan ring) :
    plan.fullWord.length = plan.dPV + 3 * plan.dVS + 2 := by
  rw [fullWord, List.length_append, word_length]
  simp
  omega

def output (hpsi : psi > 0)
    (plan : SegmentCleanupPlan ring)
    (C : Fin n → AgentState psi) : Fin n → AgentState psi :=
  applySchedule ring
    (eliminateLeadersNoCollisionEgressSink hpsi) C plan.word

def ofTwo (plan : TwoLeaderCleanupSchedule ring) :
    SegmentCleanupPlan ring where
  pred := plan.L1
  victim := plan.L2
  source := plan.L1
  pred_ne_victim := plan.leaders_ne
  victim_ne_source := plan.leaders_ne.symm
  dPV := plan.d12
  dVS := plan.d21
  dPV_eq := plan.d12_eq
  dVS_eq := plan.d21_eq
  dPV_pos := plan.d12_pos
  dVS_pos := plan.d21_pos
  dPV_lt := plan.d12_lt
  dVS_lt := plan.d21_lt
  dPV_nonadjacent := plan.d12_nonadjacent
  dVS_nonadjacent := plan.d21_nonadjacent

@[simp] theorem word_ofTwo
    (plan : TwoLeaderCleanupSchedule ring) :
    (ofTwo plan).word = plan.word := by
  rfl

@[simp] theorem predIncoming_ofTwo
    (plan : TwoLeaderCleanupSchedule ring) :
    (ofTwo plan).predIncoming =
      cwPos ring plan.L1 (plan.d12 - 1) := by
  rfl

@[simp] theorem fullWord_ofTwo
    (plan : TwoLeaderCleanupSchedule ring) :
    (ofTwo plan).fullWord =
      plan.word ++ clockwiseEdgeSchedule ring
        (cwPos ring plan.L1 (plan.d12 - 1)) plan.d21 := by
  rfl

@[simp] theorem output_ofTwo
    (hpsi : psi > 0) (plan : TwoLeaderCleanupSchedule ring)
    (C : Fin n → AgentState psi) :
    (ofTwo plan).output hpsi C = plan.output hpsi C := by
  rfl

end SegmentCleanupPlan

/-- Three cyclic roles with follower-only open arcs.  `source = pred` is
allowed, and is the exact-two-leader case. -/
structure SelectedSegment
    (ring : DirectedRing n) (C : Fin n → AgentState psi) where
  plan : SegmentCleanupPlan ring
  pred_leader : (C plan.pred).leader = true
  victim_leader : (C plan.victim).leader = true
  source_leader : (C plan.source).leader = true
  source_outgoing_follower :
    (C (ring.rightNeighbor plan.source)).leader = false
  arcPV_followers : ∀ k, 0 < k → k < plan.dPV →
    (C (cwPos ring plan.pred k)).leader = false
  arcVS_followers : ∀ k, 0 < k → k < plan.dVS →
    (C (cwPos ring plan.victim k)).leader = false

namespace SelectedSegment

variable {ring : DirectedRing n} {C : Fin n → AgentState psi}

/-- A genuinely selected segment has room for its complete repair interval and
the following surviving source.  The bare plan does not imply this bound:
selection supplies the fact that `predIncoming` is a follower whereas
`source` is a leader. -/
theorem dVS_succ_lt
    (selected : SelectedSegment ring C) :
    selected.plan.dVS + 1 < n := by
  have hdVSlt := selected.plan.dVS_lt
  have hdPV := selected.plan.dPV_nonadjacent
  have hle : selected.plan.dVS + 1 ≤ n := by
    omega
  apply Nat.lt_of_le_of_ne hle
  intro heq
  have hincomingFollower :
      (C selected.plan.predIncoming).leader = false := by
    simpa [SegmentCleanupPlan.predIncoming] using
      selected.arcPV_followers (selected.plan.dPV - 1) (by omega) (by omega)
  have hsourceEq : selected.plan.source = selected.plan.predIncoming := by
    rw [← selected.plan.source_eq_cwPos_predIncoming_dVS_succ,
      heq, cwPos_period]
  have hsourceLeader := selected.source_leader
  rw [hsourceEq, hincomingFollower] at hsourceLeader
  simp at hsourceLeader

end SelectedSegment

theorem exists_selectedSegment_of_count_gt_one
    (ring : DirectedRing n) (C : Fin n → AgentState psi)
    (hnoAdjacent : NoAdjacentPhysicalLeaders ring C)
    (hcount : 1 < rawPhysicalLeaderCount C) :
    Nonempty (SelectedSegment ring C) := by
  have hbits :
      1 < rawLeaderTrueCount (fun i => (C i).leader) := by
    rw [← rawPhysicalLeaderCount_eq_rawLeaderTrueCount C]
    exact hcount
  obtain ⟨pred, other, hne, hpred, hother⟩ :=
    exists_two_true_of_rawLeaderTrueCount_gt_one
      (fun i => (C i).leader) hbits
  obtain ⟨first⟩ := firstClockwisePhysicalLeader_of_other
    ring C pred other hpred hother hne
  obtain ⟨second⟩ := firstClockwisePhysicalLeader_of_other
    ring C first.target pred first.target_leader hpred
      first.leaders_ne.symm
  let plan : SegmentCleanupPlan ring := {
    pred := pred
    victim := first.target
    source := second.target
    pred_ne_victim := first.leaders_ne
    victim_ne_source := second.leaders_ne
    dPV := first.distance
    dVS := second.distance
    dPV_eq := first.distance_eq
    dVS_eq := second.distance_eq
    dPV_pos := first.distance_pos
    dVS_pos := second.distance_pos
    dPV_lt := first.distance_lt
    dVS_lt := second.distance_lt
    dPV_nonadjacent := first.distance_nonadjacent hnoAdjacent
    dVS_nonadjacent := second.distance_nonadjacent hnoAdjacent }
  exact ⟨{
    plan := plan
    pred_leader := hpred
    victim_leader := first.target_leader
    source_leader := second.target_leader
    source_outgoing_follower :=
      hnoAdjacent second.target second.target_leader
    arcPV_followers := first.no_leader_between
    arcVS_followers := second.no_leader_between }⟩

/-- Raw physical entry for one segment round.  Other leaders may remain
outside the two active open arcs. -/
structure SegmentCleanupReady
    (hpsi : psi > 0) (ring : DirectedRing n)
    (plan : SegmentCleanupPlan ring)
    (C : Fin n → AgentState psi) : Prop where
  pred_leader : (C plan.pred).leader = true
  victim_leader : (C plan.victim).leader = true
  source_leader : (C plan.source).leader = true
  source_outgoing_follower :
    (C (ring.rightNeighbor plan.source)).leader = false
  pred_zero : (C plan.pred).label = ⟨0, hpsi⟩
  victim_zero : (C plan.victim).label = ⟨0, hpsi⟩
  source_zero : (C plan.source).label = ⟨0, hpsi⟩
  pred_shielded : (C plan.pred).shield = true
  victim_shielded : (C plan.victim).shield = true
  source_shielded : (C plan.source).shield = true
  bullets_zero : ∀ i, (C i).bullet = ⟨0, by omega⟩
  arcPV_signals_zero : ∀ k, k ≤ plan.dPV →
    (C (cwPos ring plan.pred k)).signal_B = ⟨0, by omega⟩
  arcVS_signals_zero : ∀ k, k ≤ plan.dVS →
    (C (cwPos ring plan.victim k)).signal_B = ⟨0, by omega⟩
  arcPV_followers : ∀ k, 0 < k → k < plan.dPV →
    (C (cwPos ring plan.pred k)).leader = false
  arcVS_followers : ∀ k, 0 < k → k < plan.dVS →
    (C (cwPos ring plan.victim k)).leader = false
  arcPV_aligned : ∀ k, k + 1 < plan.dPV →
    (C (cwPos ring plan.pred (k + 1))).label =
      ⟨((C (cwPos ring plan.pred k)).label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩
  arcVS_aligned : ∀ k, k + 1 < plan.dVS →
    (C (cwPos ring plan.victim (k + 1))).label =
      ⟨((C (cwPos ring plan.victim k)).label.val + 1) % psi,
        Nat.mod_lt _ hpsi⟩

structure SegmentCleanupTrace
    (hpsi : psi > 0) (ring : DirectedRing n)
    (plan : SegmentCleanupPlan ring)
    (C : Fin n → AgentState psi) : Prop where
  victim_before : (C plan.victim).leader = true
  source_after : (plan.output hpsi C plan.source).leader = true
  victim_after : (plan.output hpsi C plan.victim).leader = false
  other_leaders_frame : ∀ i, i ≠ plan.victim →
    (plan.output hpsi C i).leader = (C i).leader

namespace SegmentCleanupReady

variable {hpsi : psi > 0} {ring : DirectedRing n}
  {plan : SegmentCleanupPlan ring} {C : Fin n → AgentState psi}

/-- The two selected active arcs do not overlap past the predecessor leader.
This follows from raw readiness: if the victim-to-source arc wrapped past
`pred`, its follower premise would classify the leader `pred` as a follower. -/
theorem arc_sum_le
    (hready : SegmentCleanupReady hpsi ring plan C) :
    plan.dPV + plan.dVS ≤ n := by
  apply Nat.le_of_not_lt
  intro hsum
  have hdPVlt := plan.dPV_lt
  have hkpos : 0 < n - plan.dPV := by omega
  have hklt : n - plan.dPV < plan.dVS := by omega
  have hvictim : cwPos ring plan.pred plan.dPV = plan.victim := by
    rw [plan.dPV_eq, cwPos_cwDist]
  have hpredAt :
      cwPos ring plan.victim (n - plan.dPV) = plan.pred := by
    calc
      cwPos ring plan.victim (n - plan.dPV) =
          cwPos ring (cwPos ring plan.pred plan.dPV)
            (n - plan.dPV) := by rw [hvictim]
      _ = cwPos ring plan.pred (plan.dPV + (n - plan.dPV)) :=
        SegmentCleanupPlan.cwPos_add_segment
          ring plan.pred plan.dPV (n - plan.dPV)
      _ = cwPos ring plan.pred n := by
        congr 1
        omega
      _ = plan.pred := cwPos_period ring plan.pred
  have hfollower := hready.arcVS_followers
    (n - plan.dPV) hkpos hklt
  rw [hpredAt, hready.pred_leader] at hfollower
  simp at hfollower

theorem dVS_succ_lt
    (hready : SegmentCleanupReady hpsi ring plan C) :
    plan.dVS + 1 < n := by
  have hdVSlt := plan.dVS_lt
  have hdPV := plan.dPV_nonadjacent
  have hle : plan.dVS + 1 ≤ n := by omega
  apply Nat.lt_of_le_of_ne hle
  intro heq
  have hincomingFollower : (C plan.predIncoming).leader = false := by
    simpa [SegmentCleanupPlan.predIncoming] using
      hready.arcPV_followers (plan.dPV - 1) (by omega) (by omega)
  have hsourceEq : plan.source = plan.predIncoming := by
    rw [← plan.source_eq_cwPos_predIncoming_dVS_succ,
      heq, cwPos_period]
  have hsourceLeader := hready.source_leader
  rw [hsourceEq, hincomingFollower] at hsourceLeader
  simp at hsourceLeader

end SegmentCleanupReady

theorem SegmentCleanupTrace.rawPhysicalLeaderCount_lt
    {hpsi : psi > 0} {ring : DirectedRing n}
    {plan : SegmentCleanupPlan ring}
    {C : Fin n → AgentState psi}
    (h : SegmentCleanupTrace hpsi ring plan C) :
    rawPhysicalLeaderCount (plan.output hpsi C) <
      rawPhysicalLeaderCount C :=
  rawPhysicalLeaderCount_lt_of_single_drop
    C (plan.output hpsi C) plan.victim
      h.victim_before h.victim_after h.other_leaders_frame

theorem SegmentCleanupReady.ofTwo
    {hpsi : psi > 0} {ring : DirectedRing n}
    {plan : TwoLeaderCleanupSchedule ring}
    {C : Fin n → AgentState psi}
    (hready : TwoLeaderCleanupReady hpsi ring plan C) :
    SegmentCleanupReady hpsi ring (SegmentCleanupPlan.ofTwo plan) C := by
  exact {
    pred_leader :=
      (hready.leaders_exact plan.L1).2 (Or.inl rfl)
    victim_leader :=
      (hready.leaders_exact plan.L2).2 (Or.inr rfl)
    source_leader :=
      (hready.leaders_exact plan.L1).2 (Or.inl rfl)
    source_outgoing_follower := by
      have hd := plan.d12_nonadjacent
      simpa only [SegmentCleanupPlan.ofTwo, cwPos_zero, cwPos_succ] using
        hready.arc12_followers 1 (by omega) (by omega)
    pred_zero := hready.l1_zero
    victim_zero := hready.l2_zero
    source_zero := hready.l1_zero
    pred_shielded := hready.l1_shielded
    victim_shielded := hready.l2_shielded
    source_shielded := hready.l1_shielded
    bullets_zero := hready.bullets_zero
    arcPV_signals_zero := fun _ _ => hready.signals_zero _
    arcVS_signals_zero := fun _ _ => hready.signals_zero _
    arcPV_followers := hready.arc12_followers
    arcVS_followers := hready.arc21_followers
    arcPV_aligned := hready.arc12_aligned
    arcVS_aligned := hready.arc21_aligned }

/-- The static arbitrary-multi-leader invariant plus a selected consecutive
segment supplies every raw physical premise of the segment word. -/
theorem SegmentCleanupReady.ofSelected
    {hpsi : psi > 0} {ring : DirectedRing n}
    {C : Fin n → AgentState psi}
    (hentry : MultiLeaderStaticEntry hpsi ring C)
    (selected : SelectedSegment ring C) :
    SegmentCleanupReady hpsi ring selected.plan C := by
  exact {
    pred_leader := selected.pred_leader
    victim_leader := selected.victim_leader
    source_leader := selected.source_leader
    source_outgoing_follower := selected.source_outgoing_follower
    pred_zero := hentry.leaders_zero _ selected.pred_leader
    victim_zero := hentry.leaders_zero _ selected.victim_leader
    source_zero := hentry.leaders_zero _ selected.source_leader
    pred_shielded := hentry.leaders_shielded _ selected.pred_leader
    victim_shielded := hentry.leaders_shielded _ selected.victim_leader
    source_shielded := hentry.leaders_shielded _ selected.source_leader
    bullets_zero := hentry.bullets_zero
    arcPV_signals_zero := fun _ _ => hentry.signals_zero _
    arcVS_signals_zero := fun _ _ => hentry.signals_zero _
    arcPV_followers := selected.arcPV_followers
    arcVS_followers := selected.arcVS_followers
    arcPV_aligned := by
      intro k hk
      have hr := selected.arcPV_followers (k + 1) (by omega) hk
      have hr' : ¬(C (ring.rightNeighbor
          (cwPos ring selected.plan.pred k))).isLeader := by
        intro hleader
        change (C (ring.rightNeighbor
          (cwPos ring selected.plan.pred k))).leader = true at hleader
        have hfalse : (C (ring.rightNeighbor
            (cwPos ring selected.plan.pred k))).leader = false := by
          simpa only [cwPos_succ] using hr
        rw [hfalse] at hleader
        simp at hleader
      simpa only [cwPos_succ] using
        successor_label_of_noFreeBarrier_of_right_not_leader
          hpsi ring C hentry.no_free_barrier
            (cwPos ring selected.plan.pred k) hr'
    arcVS_aligned := by
      intro k hk
      have hr := selected.arcVS_followers (k + 1) (by omega) hk
      have hr' : ¬(C (ring.rightNeighbor
          (cwPos ring selected.plan.victim k))).isLeader := by
        intro hleader
        change (C (ring.rightNeighbor
          (cwPos ring selected.plan.victim k))).leader = true at hleader
        have hfalse : (C (ring.rightNeighbor
            (cwPos ring selected.plan.victim k))).leader = false := by
          simpa only [cwPos_succ] using hr
        rw [hfalse] at hleader
        simp at hleader
      simpa only [cwPos_succ] using
        successor_label_of_noFreeBarrier_of_right_not_leader
          hpsi ring C hentry.no_free_barrier
            (cwPos ring selected.plan.victim k) hr' }

/-- Every static nonadjacent multi-leader entry with count above one therefore
has a selected segment together with the complete raw word premises. -/
theorem exists_selectedSegment_cleanupReady_of_count_gt_one
    {hpsi : psi > 0} (ring : DirectedRing n)
    (C : Fin n → AgentState psi)
    (hentry : MultiLeaderStaticEntry hpsi ring C)
    (hnoAdjacent : NoAdjacentPhysicalLeaders ring C)
    (hcount : 1 < rawPhysicalLeaderCount C) :
    ∃ selected : SelectedSegment ring C,
      SegmentCleanupReady hpsi ring selected.plan C := by
  obtain ⟨selected⟩ :=
    exists_selectedSegment_of_count_gt_one ring C hnoAdjacent hcount
  exact ⟨selected, SegmentCleanupReady.ofSelected hentry selected⟩

/-- The general three-role segment word executes the same two signal circuits
and reverse live-bullet kill as the exact-two base case.  Leaders outside the
two active arcs are framed rather than excluded. -/
theorem SegmentCleanupReady.trace
    {hpsi : psi > 0} {ring : DirectedRing n}
    {plan : SegmentCleanupPlan ring}
    {C : Fin n → AgentState psi}
    (hready : SegmentCleanupReady hpsi ring plan C) :
    SegmentCleanupTrace hpsi ring plan C := by
  let T := eliminateLeadersNoCollisionEgressSink hpsi
  have hsum := hready.arc_sum_le
  have hsourceAhead := hready.dVS_succ_lt

  let C1 := applySchedule ring T C
    (clockwiseEdgeSchedule ring plan.pred plan.dPV)
  have hC1 : ForwardCleanupSignalState hpsi ring plan.pred plan.dPV
      C C1 plan.dPV := by
    simpa [C1, T] using
      forwardCleanupSignalSchedule hpsi ring plan.pred plan.dPV plan.dPV C
        (Nat.le_refl _) plan.dPV_lt
        (fun k _ => hready.bullets_zero _)
        hready.arcPV_signals_zero hready.pred_leader
        (by rw [plan.targetPV]; exact hready.victim_leader)
        hready.arcPV_followers hready.arcPV_aligned
  have hC1Bullets : ∀ i, (C1 i).bullet = ⟨0, by omega⟩ :=
    hC1.bullets_zero_of_initial hready.bullets_zero
  let p := plan.predIncoming
  have hpSignal : (C1 p).signal_B = ⟨1, by omega⟩ := by
    have hd := plan.dPV_nonadjacent
    exact hC1.visited_signal_one (plan.dPV - 1) (by omega) (by omega)
  have hpFollower : (C1 p).leader = false := by
    have hd := plan.dPV_nonadjacent
    rw [hC1.leaders_frame]
    exact hready.arcPV_followers (plan.dPV - 1) (by omega) (by omega)
  have hC1VictimSignal : (C1 plan.victim).signal_B = ⟨1, by omega⟩ := by
    rw [← plan.targetPV]
    exact hC1.visited_signal_one plan.dPV plan.dPV_pos (Nat.le_refl _)
  have hC1VictimLeader : (C1 plan.victim).leader = true := by
    rw [hC1.leaders_frame]
    exact hready.victim_leader
  have hC1VictimLabel : (C1 plan.victim).label = ⟨0, hpsi⟩ := by
    rw [hC1.labels_frame]
    exact hready.victim_zero
  have hrepeat := cleanupRightFireOutput hpsi (C1 p) (C1 plan.victim)
    hpFollower hpSignal hC1VictimLeader hC1VictimLabel hC1VictimSignal

  let C2 := stepConfig ring T C1 p
  have hpredRight : ring.rightNeighbor p = plan.victim := by
    exact plan.predIncoming_right
  have hpne : p ≠ ring.rightNeighbor p := by
    rw [hpredRight]
    exact plan.predIncoming_ne_victim
  have hrepeat' : CleanupRightFireOutput
      (C1 p) (C1 (ring.rightNeighbor p))
      (T (C1 p) (C1 (ring.rightNeighbor p))) := by
    simpa [T, hpredRight] using hrepeat
  have hC2LeadersC1 : ∀ i, (C2 i).leader = (C1 i).leader :=
    stepConfig_view_frame_cleanup (view := fun u => u.leader)
      ring T C1 p
        (hrepeat'.leaderL.trans hpFollower.symm)
        (hrepeat'.leaderR.trans
          (by simpa [hpredRight] using hC1VictimLeader.symm))
  have hC2LabelsC1 : ∀ i, (C2 i).label = (C1 i).label :=
    stepConfig_view_frame_cleanup (view := fun u => u.label)
      ring T C1 p hrepeat'.labelL hrepeat'.labelR
  have hC2LeadersC : ∀ i, (C2 i).leader = (C i).leader := fun i =>
    (hC2LeadersC1 i).trans (hC1.leaders_frame i)
  have hC2LabelsC : ∀ i, (C2 i).label = (C i).label := fun i =>
    (hC2LabelsC1 i).trans (hC1.labels_frame i)
  have hC2Victim : C2 plan.victim =
      (T (C1 p) (C1 plan.victim)).2 := by
    have h := stepConfig_right_cleanup ring T C1 p hpne
    simpa [C2, hpredRight] using h
  have hC2P : C2 p = (T (C1 p) (C1 plan.victim)).1 := by
    simpa [C2, hpredRight] using stepConfig_left_cleanup ring T C1 p
  have hC2VictimLeader : (C2 plan.victim).leader = true := by
    rw [hC2Victim]
    exact hrepeat.leaderR
  have hC2VictimShield : (C2 plan.victim).shield = false := by
    rw [hC2Victim]
    exact hrepeat.shieldR
  have hC2VictimBullet : (C2 plan.victim).bullet = ⟨0, by omega⟩ := by
    rw [hC2Victim]
    exact hrepeat.bulletR
  have hC2VictimSignal : (C2 plan.victim).signal_B = ⟨0, by omega⟩ := by
    rw [hC2Victim]
    exact hrepeat.signalR
  have hC2PBullet : (C2 p).bullet = ⟨1, by omega⟩ := by
    rw [hC2P]
    exact hrepeat.bulletL
  have hsourceNeP : plan.source ≠ p :=
    plan.source_ne_predIncoming_of_dVS_succ_lt hsourceAhead
  have hsourceNeVictim : plan.source ≠ plan.victim :=
    plan.victim_ne_source.symm
  have hC2SourceEq : C2 plan.source = C1 plan.source := by
    apply stepConfig_untouched_cleanup ring T C1 p plan.source hsourceNeP
    simpa [hpredRight] using hsourceNeVictim
  have hCSourceSignal : (C plan.source).signal_B = ⟨0, by omega⟩ := by
    rw [← plan.targetVS]
    exact hready.arcVS_signals_zero plan.dVS (Nat.le_refl _)
  have hC1SourceSignal : (C1 plan.source).signal_B = ⟨0, by omega⟩ := by
    by_cases heq : plan.dPV + plan.dVS = n
    · have hsourcePred : plan.source = plan.pred := by
        rw [← plan.targetPVS, heq, cwPos_period]
      rw [hsourcePred]
      exact hC1.source_signal_zero
    · have hdVS := plan.dVS_pos
      have hsumlt : plan.dPV + plan.dVS < n := by omega
      have hafter : plan.dPV < plan.dPV + plan.dVS := by omega
      have hCSourceAt :
          (C (cwPos ring plan.pred (plan.dPV + plan.dVS))).signal_B =
            ⟨0, by omega⟩ := by
        rw [plan.targetPVS]
        exact hCSourceSignal
      rw [← plan.targetPVS,
        hC1.outside_signal_frame (plan.dPV + plan.dVS) hafter hsumlt]
      exact hCSourceAt
  have hC2SourceSignal : (C2 plan.source).signal_B = ⟨0, by omega⟩ := by
    rw [hC2SourceEq]
    exact hC1SourceSignal
  have hC2SourceBullet : (C2 plan.source).bullet = ⟨0, by omega⟩ := by
    rw [hC2SourceEq]
    exact hC1Bullets _
  have hC2SourceLeader : (C2 plan.source).leader = true := by
    rw [hC2LeadersC]
    exact hready.source_leader
  have hC2SourceShield : (C2 plan.source).shield = true := by
    rw [hC2SourceEq, hC1.shields_frame]
    exact hready.source_shielded
  have hC2ArcVSBullets : ∀ k, k ≤ plan.dVS →
      (C2 (cwPos ring plan.victim k)).bullet = ⟨0, by omega⟩ := by
    intro k hk
    by_cases hk0 : k = 0
    · subst k
      simpa using hC2VictimBullet
    by_cases hkend : k = plan.dVS
    · subst k
      rw [plan.targetVS]
      exact hC2SourceBullet
    have hkpos : 0 < k := by omega
    have hklt : k < plan.dVS := by omega
    let i := cwPos ring plan.victim k
    have hu : C2 i = C1 i := by
      apply stepConfig_untouched_cleanup ring T C1 p i
        (plan.arcVS_interior_ne_predIncoming hsum k hkpos hklt)
      simpa [hpredRight] using
        plan.arcVS_interior_ne_victim k hkpos hklt
    rw [hu]
    exact hC1Bullets i
  have hC2ArcVSSignals : ∀ k, k ≤ plan.dVS →
      (C2 (cwPos ring plan.victim k)).signal_B = ⟨0, by omega⟩ := by
    intro k hk
    by_cases hk0 : k = 0
    · subst k
      simpa using hC2VictimSignal
    by_cases hkend : k = plan.dVS
    · subst k
      rw [plan.targetVS]
      exact hC2SourceSignal
    have hkpos : 0 < k := by omega
    have hklt : k < plan.dVS := by omega
    let i := cwPos ring plan.victim k
    have hu : C2 i = C1 i := by
      apply stepConfig_untouched_cleanup ring T C1 p i
        (plan.arcVS_interior_ne_predIncoming hsum k hkpos hklt)
      simpa [hpredRight] using
        plan.arcVS_interior_ne_victim k hkpos hklt
    rw [hu]
    change (C1 (cwPos ring plan.victim k)).signal_B = ⟨0, by omega⟩
    rw [plan.arcVS_as_pred,
      hC1.outside_signal_frame (plan.dPV + k) (by omega) (by omega)]
    rw [← plan.arcVS_as_pred]
    exact hready.arcVS_signals_zero k hk

  let C3 := applySchedule ring T C2
    (clockwiseEdgeSchedule ring plan.victim plan.dVS)
  have hC3 : ForwardCleanupSignalState hpsi ring plan.victim plan.dVS
      C2 C3 plan.dVS := by
    simpa [C3, T] using
      forwardCleanupSignalSchedule hpsi ring plan.victim plan.dVS plan.dVS C2
        (Nat.le_refl _) plan.dVS_lt hC2ArcVSBullets hC2ArcVSSignals
        hC2VictimLeader
        (by rw [plan.targetVS]; exact hC2SourceLeader)
        (fun k hk0 hk => by
          rw [hC2LeadersC]
          exact hready.arcVS_followers k hk0 hk)
        (fun k hk => by
          rw [hC2LabelsC, hC2LabelsC]
          exact hready.arcVS_aligned k hk)
  have hC3LeadersC : ∀ i, (C3 i).leader = (C i).leader := fun i =>
    (hC3.leaders_frame i).trans (hC2LeadersC i)
  have hC3LabelsC : ∀ i, (C3 i).label = (C i).label := fun i =>
    (hC3.labels_frame i).trans (hC2LabelsC i)
  have hC3SourceSignal : (C3 plan.source).signal_B = ⟨1, by omega⟩ := by
    rw [← plan.targetVS]
    exact hC3.visited_signal_one plan.dVS plan.dVS_pos (Nat.le_refl _)
  have hC3SourceLeader : (C3 plan.source).leader = true := by
    rw [hC3LeadersC]
    exact hready.source_leader
  have hC3VictimSignal : (C3 plan.victim).signal_B = ⟨0, by omega⟩ :=
    hC3.source_signal_zero
  have hC3VictimShield : (C3 plan.victim).shield = false := by
    rw [hC3.shields_frame]
    exact hC2VictimShield

  let r1 := ring.rightNeighbor plan.source
  have hr1pos : r1 = cwPos ring plan.source 1 := by simp [r1]
  have hC3R1Follower : (C3 r1).leader = false := by
    rw [hC3LeadersC]
    exact hready.source_outgoing_follower
  have hr1Offset : cwPos ring plan.victim (plan.dVS + 1) = r1 := by
    rw [cwPos_succ, plan.targetVS]
  have hC3R1BulletEq : (C3 r1).bullet = (C2 r1).bullet := by
    rw [← hr1Offset]
    exact hC3.outside_bullet_frame (plan.dVS + 1) (by omega) hsourceAhead
  have hr1NeVictim : r1 ≠ plan.victim := by
    intro heq
    have hf := hready.source_outgoing_follower
    change ring.rightNeighbor plan.source = plan.victim at heq
    rw [heq, hready.victim_leader] at hf
    simp at hf
  have hC2R1NotLive : (C2 r1).bullet ≠ ⟨2, by omega⟩ := by
    by_cases hrp : r1 = p
    · intro hlive
      have heq : (C2 p).bullet = ⟨2, by omega⟩ := by
        rw [← hrp]
        exact hlive
      rw [hC2PBullet] at heq
      simp at heq
    · have hu : C2 r1 = C1 r1 := by
        apply stepConfig_untouched_cleanup ring T C1 p r1 hrp
        simpa [hpredRight] using hr1NeVictim
      intro hlive
      rw [hu, hC1Bullets] at hlive
      simp at hlive
  have hC3R1NotLive : (C3 r1).bullet ≠ ⟨2, by omega⟩ := by
    rw [hC3R1BulletEq]
    exact hC2R1NotLive
  have hfire := cleanupLeftFireOutput hpsi (C3 plan.source) (C3 r1)
    hC3SourceLeader hC3SourceSignal hC3R1Follower hC3R1NotLive

  let C4 := stepConfig ring T C3 plan.source
  have hn : 1 < n := by omega
  have hsourceNeR1 : plan.source ≠ r1 := by
    exact Ne.symm (rightNeighbor_ne_self_of_one_lt ring hn plan.source)
  have hfire' : CleanupLeftFireOutput
      (C3 plan.source) (C3 (ring.rightNeighbor plan.source))
      (T (C3 plan.source) (C3 (ring.rightNeighbor plan.source))) := by
    simpa [T, r1] using hfire
  have hC4LeadersC3 : ∀ i, (C4 i).leader = (C3 i).leader :=
    stepConfig_view_frame_cleanup (view := fun u => u.leader)
      ring T C3 plan.source
        (hfire'.leaderL.trans hC3SourceLeader.symm)
        (hfire'.leaderR.trans (by simpa [r1] using hC3R1Follower.symm))
  have hC4LabelsC3 : ∀ i, (C4 i).label = (C3 i).label :=
    stepConfig_view_frame_cleanup (view := fun u => u.label)
      ring T C3 plan.source hfire'.labelL hfire'.labelR
  have hC4LeadersC : ∀ i, (C4 i).leader = (C i).leader := fun i =>
    (hC4LeadersC3 i).trans (hC3LeadersC i)
  have hC4LabelsC : ∀ i, (C4 i).label = (C i).label := fun i =>
    (hC4LabelsC3 i).trans (hC3LabelsC i)
  have hC4Source : C4 plan.source =
      (T (C3 plan.source) (C3 r1)).1 := by
    simpa [C4, r1] using stepConfig_left_cleanup ring T C3 plan.source
  have hC4SourceBullet : (C4 plan.source).bullet = ⟨2, by omega⟩ := by
    rw [hC4Source]
    exact hfire.bulletL
  have hC4SourceSignal : (C4 plan.source).signal_B = ⟨0, by omega⟩ := by
    rw [hC4Source]
    exact hfire.signalL
  have hvictimNeR1 : plan.victim ≠ r1 := hr1NeVictim.symm
  have hC4VictimEq : C4 plan.victim = C3 plan.victim := by
    apply stepConfig_untouched_cleanup ring T C3 plan.source plan.victim
      plan.victim_ne_source
    simpa [r1] using hvictimNeR1
  have hC4VictimLeader : (C4 plan.victim).leader = true := by
    rw [hC4VictimEq, hC3LeadersC]
    exact hready.victim_leader
  have hC4VictimShield : (C4 plan.victim).shield = false := by
    rw [hC4VictimEq]
    exact hC3VictimShield
  have hC4VictimSignal : (C4 plan.victim).signal_B = ⟨0, by omega⟩ := by
    rw [hC4VictimEq]
    exact hC3VictimSignal

  let C5 := applySchedule ring T C4
    (reversePositiveEdgeSchedule ring plan.victim (plan.dVS - 1))
  have hreverse : ReverseCleanupLiveOutput ring plan.victim C4 C5 := by
    have hdVS := plan.dVS_nonadjacent
    apply reversePositiveEdgeSchedule_moves_live_cleanup hpsi ring plan.victim
      (plan.dVS - 1) C4
    · omega
    · rw [show plan.dVS - 1 + 1 = plan.dVS by omega, plan.targetVS]
      exact hC4SourceBullet
    · rw [show plan.dVS - 1 + 1 = plan.dVS by omega, plan.targetVS]
      exact hC4SourceSignal
    · intro k hk0 hkle
      rw [hC4LeadersC]
      exact hready.arcVS_followers k hk0 (by omega)
    · intro k hk0 hkle
      by_cases htop : k = plan.dVS - 1
      · right
        have hk1 : k + 1 = plan.dVS := by omega
        rw [hk1, plan.targetVS, hC4LeadersC, hC4LabelsC]
        exact ⟨hready.source_leader, hready.source_zero⟩
      · left
        rw [hC4LabelsC, hC4LabelsC]
        exact hready.arcVS_aligned k (by omega)

  let r2 := ring.rightNeighbor plan.victim
  have hr2pos : r2 = cwPos ring plan.victim 1 := by simp [r2]
  have hC5R2Bullet : (C5 r2).bullet = ⟨2, by omega⟩ := by
    rw [hr2pos]
    exact hreverse.live_at_one
  have hC5R2Follower : (C5 r2).leader = false := by
    have hdVS := plan.dVS_nonadjacent
    rw [hreverse.leaders_frame, hC4LeadersC, hr2pos]
    exact hready.arcVS_followers 1 (by omega) (by omega)
  have hC5VictimEq : C5 plan.victim = C4 plan.victim := hreverse.start_unchanged
  have hC5VictimLeader : (C5 plan.victim).leader = true := by
    rw [hC5VictimEq]
    exact hC4VictimLeader
  have hC5VictimShield : (C5 plan.victim).shield = false := by
    rw [hC5VictimEq]
    exact hC4VictimShield
  have hC5VictimSignal : (C5 plan.victim).signal_B = ⟨0, by omega⟩ := by
    rw [hC5VictimEq]
    exact hC4VictimSignal
  have hhit := cleanupLiveKillOutput hpsi (C5 plan.victim) (C5 r2)
    hC5VictimLeader hC5VictimShield hC5VictimSignal
      hC5R2Follower hC5R2Bullet

  let C6 := stepConfig ring T C5 plan.victim
  have hvictimNeR2 : plan.victim ≠ r2 := by
    exact Ne.symm (rightNeighbor_ne_self_of_one_lt ring hn plan.victim)
  have hC6Victim : C6 plan.victim =
      (T (C5 plan.victim) (C5 r2)).1 := by
    simpa [C6, r2] using stepConfig_left_cleanup ring T C5 plan.victim
  have hC6R2 : C6 r2 = (T (C5 plan.victim) (C5 r2)).2 := by
    have h := stepConfig_right_cleanup ring T C5 plan.victim hvictimNeR2
    simpa [C6, r2] using h
  have hC6VictimLeader : (C6 plan.victim).leader = false := by
    rw [hC6Victim]
    exact hhit.leaderL
  have hC5LeadersC : ∀ i, (C5 i).leader = (C i).leader := fun i =>
    (hreverse.leaders_frame i).trans (hC4LeadersC i)
  have hC6SourceEq : C6 plan.source = C5 plan.source := by
    apply stepConfig_untouched_cleanup ring T C5 plan.victim plan.source
      plan.victim_ne_source.symm
    exact plan.source_ne_rightNeighbor_victim
  have hC6SourceLeader : (C6 plan.source).leader = true := by
    rw [hC6SourceEq, hC5LeadersC]
    exact hready.source_leader
  have houtput : plan.output hpsi C = C6 := by
    have hsched : plan.word =
        clockwiseEdgeSchedule ring plan.pred plan.dPV ++
          ([plan.predIncoming] ++
            (clockwiseEdgeSchedule ring plan.victim plan.dVS ++
              ([plan.source] ++
                (reversePositiveEdgeSchedule ring plan.victim
                    (plan.dVS - 1) ++ [plan.victim])))) := by
      simp [SegmentCleanupPlan.word, List.append_assoc]
    rw [SegmentCleanupPlan.output, hsched]
    simp only [applySchedule_append_cleanup, applySchedule]
    rfl
  refine
    { victim_before := hready.victim_leader
      source_after := by rw [houtput]; exact hC6SourceLeader
      victim_after := by rw [houtput]; exact hC6VictimLeader
      other_leaders_frame := ?_ }
  intro i hi
  rw [houtput]
  by_cases hir : i = r2
  · subst i
    calc
      (C6 r2).leader = (T (C5 plan.victim) (C5 r2)).2.leader :=
        congrArg (fun u => u.leader) hC6R2
      _ = false := hhit.leaderR
      _ = (C r2).leader := by
        have hdVS := plan.dVS_nonadjacent
        rw [hr2pos]
        exact (hready.arcVS_followers 1 (by omega) (by omega)).symm
  · have hu : C6 i = C5 i := by
      apply stepConfig_untouched_cleanup ring T C5 plan.victim i hi
      simpa [r2] using hir
    rw [hu]
    exact hC5LeadersC i

theorem SegmentCleanupReady.rawPhysicalLeaderCount_lt
    {hpsi : psi > 0} {ring : DirectedRing n}
    {plan : SegmentCleanupPlan ring}
    {C : Fin n → AgentState psi}
    (hready : SegmentCleanupReady hpsi ring plan C) :
    rawPhysicalLeaderCount (plan.output hpsi C) <
      rawPhysicalLeaderCount C :=
  hready.trace.rawPhysicalLeaderCount_lt

/-- Static nonadjacent multi-leader entries now have a concrete selected raw
round whose literal kill word strictly lowers physical leader count. -/
theorem exists_selectedSegment_raw_count_lt_of_count_gt_one
    {hpsi : psi > 0} (ring : DirectedRing n)
    (C : Fin n → AgentState psi)
    (hentry : MultiLeaderStaticEntry hpsi ring C)
    (hnoAdjacent : NoAdjacentPhysicalLeaders ring C)
    (hcount : 1 < rawPhysicalLeaderCount C) :
    ∃ selected : SelectedSegment ring C,
      rawPhysicalLeaderCount (selected.plan.output hpsi C) <
        rawPhysicalLeaderCount C := by
  obtain ⟨selected, hready⟩ :=
    exists_selectedSegment_cleanupReady_of_count_gt_one
      ring C hentry hnoAdjacent hcount
  exact ⟨selected, hready.rawPhysicalLeaderCount_lt⟩

theorem SegmentCleanupReady.trace_of_two
    {hpsi : psi > 0} {ring : DirectedRing n}
    {plan : TwoLeaderCleanupSchedule ring}
    {C : Fin n → AgentState psi}
    (hready : TwoLeaderCleanupReady hpsi ring plan C) :
    SegmentCleanupTrace hpsi ring (SegmentCleanupPlan.ofTwo plan) C := by
  have ht : TwoLeaderCleanupTrace hpsi ring plan C :=
    TwoLeaderCleanupReady.trace hready
  refine {
    victim_before := ?_
    source_after := ?_
    victim_after := ?_
    other_leaders_frame := ?_ }
  · exact ht.victim_before
  · change (plan.output hpsi C plan.L1).leader = true
    exact ht.survivor_after
  · change (plan.output hpsi C plan.L2).leader = false
    exact ht.victim_after
  · intro i hi
    have hi' : i ≠ plan.L2 := by
      simpa [SegmentCleanupPlan.ofTwo] using hi
    simpa using ht.other_leaders_frame i hi'

end PPLLCompleteMultiLeaderCleanup
