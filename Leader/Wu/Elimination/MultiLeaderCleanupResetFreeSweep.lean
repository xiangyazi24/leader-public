import Leader.Wu.Elimination.MultiLeaderCleanupResetFreeBridge
import Leader.Wu.Elimination.MultiLeaderCleanupFullWordDescent

/-!
# Prefixwise reset-free repair sweep

This module iterates the complete reset-free follower-edge bridge along a
literal schedule.  Hidden CHECK/COMPARE readiness remains an explicit
per-prefix obligation; the theorem here proves that this obligation is enough
to obtain the visible follower and successor-label geometry of the complete
expiring transition.
-/

namespace PPLLCompleteMultiLeaderCleanup
namespace PhysicalBridge

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
  PPLLLeaderCreationCleanupRepair
  PPLLNoCheckBirthConditionTwoPhysical
  PPLLNoCheckBirthConditionTwoGeometry
  PPLLWallSweepNormalResetContract PPLLWallSweepRestartableGeneric
  PPLLWallSweepClockwiseScheduler

variable {n psi kappa tau : Nat}

/-- Reset-free readiness must be reconstructed at every concrete full-state
prefix, since its idle fields are not determined by leader/label geometry. -/
def MultiLeaderCleanupResetFreeReadyAlong
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau) :
    DetSchedule n → Prop
  | [] => True
  | e :: rest =>
      ExpiringMultiLeaderCleanupResetFreePairReady
        hpsi kappa (C e) (C (ring.rightNeighbor e)) ∧
      MultiLeaderCleanupResetFreeReadyAlong
        hpsi kappa tau ring
        (localStep ring
          (multiLeaderCleanupTransition hpsi kappa tau) C e) rest

theorem multiLeaderCleanupResetFreeReadyAlong_append_iff
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n)
    (C : Fin n → ExpiringAgentState psi kappa tau)
    (xs ys : DetSchedule n) :
    MultiLeaderCleanupResetFreeReadyAlong
        hpsi kappa tau ring C (xs ++ ys) ↔
      MultiLeaderCleanupResetFreeReadyAlong
          hpsi kappa tau ring C xs ∧
        MultiLeaderCleanupResetFreeReadyAlong
          hpsi kappa tau ring
          (runLocalSchedule ring
            (multiLeaderCleanupTransition hpsi kappa tau) C xs) ys := by
  induction xs generalizing C with
  | nil => simp [MultiLeaderCleanupResetFreeReadyAlong, runLocalSchedule]
  | cons e rest ih =>
      simp only [List.cons_append,
        MultiLeaderCleanupResetFreeReadyAlong, runLocalSchedule]
      rw [ih]
      constructor
      · rintro ⟨hedge, hrest, hys⟩
        exact ⟨⟨hedge, hrest⟩, hys⟩
      · rintro ⟨⟨hedge, hrest⟩, hys⟩
        exact ⟨hedge, hrest, hys⟩

private theorem resetFreeReady_input_followers
    (hpsi : psi > 0) (kappa tau : Nat)
    (l r : ExpiringAgentState psi kappa tau)
    (hready : ExpiringMultiLeaderCleanupResetFreePairReady
      hpsi kappa l r) :
    l.core.erase.core.leader = false ∧
      r.core.erase.core.leader = false := by
  have hl := congrArg PeaceView.leader
    (normalizeDeletion_peaceView l.core.erase)
  have hr := congrArg PeaceView.leader
    (normalizeDeletion_peaceView r.core.erase)
  exact ⟨hl.symm.trans hready.left_follower,
    hr.symm.trans hready.right_follower⟩

/-- Global one-step frame for a complete reset-free repair edge. -/
theorem localStep_multiLeaderCleanup_resetFree_follower_edge
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) (hn : 1 < n)
    (C : Fin n → ExpiringAgentState psi kappa tau) (e : Fin n)
    (hready : ExpiringMultiLeaderCleanupResetFreePairReady
      hpsi kappa (C e) (C (ring.rightNeighbor e))) :
    let D := localStep ring
      (multiLeaderCleanupTransition hpsi kappa tau) C e
    (∀ i, (D i).core.erase.core.leader =
      (C i).core.erase.core.leader) ∧
      (D e).core.erase.core.label = (C e).core.erase.core.label ∧
      (D (ring.rightNeighbor e)).core.erase.core.label =
        ⟨((C e).core.erase.core.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩ ∧
      (D (ring.rightNeighbor e)).core.erase.core.leader = false ∧
      (∀ i, i ≠ e → i ≠ ring.rightNeighbor e → D i = C i) := by
  let j := ring.rightNeighbor e
  let T := multiLeaderCleanupTransition hpsi kappa tau
  let q := T (C e) (C j)
  let D := localStep ring T C e
  have hene : e ≠ j :=
    Ne.symm (rightNeighbor_ne_self_of_one_lt ring hn e)
  have hedge := multiLeaderCleanupTransition_resetFree_follower_edge
    hpsi kappa tau (C e) (C j) (by simpa [j] using hready)
  change q.1.core.erase.core.leader = false ∧
      q.2.core.erase.core.leader = false ∧
      q.1.core.erase.core.label = (C e).core.erase.core.label ∧
      q.2.core.erase.core.label =
        ⟨((C e).core.erase.core.label.val + 1) % psi,
          Nat.mod_lt _ hpsi⟩ at hedge
  have hinput := resetFreeReady_input_followers
    hpsi kappa tau (C e) (C j) (by simpa [j] using hready)
  have hleft : D e = q.1 := by
    simp [D, q, T, localStep, j]
  have hright : D j = q.2 := by
    simp [D, q, T, localStep, j, Ne.symm hene]
  have hoff : ∀ i, i ≠ e → i ≠ j → D i = C i := by
    intro i hie hij
    simp [D, T, localStep, j, hie, hij]
  have hleaderFrame : ∀ i,
      (D i).core.erase.core.leader =
        (C i).core.erase.core.leader := by
    intro i
    by_cases hie : i = e
    · subst i
      rw [hleft, hedge.1, hinput.1]
    · by_cases hij : i = j
      · subst i
        rw [hright, hedge.2.1, hinput.2]
      · rw [hoff i hie hij]
  change (∀ i, (D i).core.erase.core.leader =
      (C i).core.erase.core.leader) ∧ _
  exact ⟨hleaderFrame,
    (congrArg (fun u => u.core.erase.core.label) hleft).trans
      hedge.2.2.1,
    (congrArg (fun u => u.core.erase.core.label) hright).trans
      hedge.2.2.2,
    (congrArg (fun u => u.core.erase.core.leader) hright).trans
      hedge.2.1,
    by simpa [j] using hoff⟩

/-- A prefixwise-ready clockwise sweep of the complete transition installs the
successor-label chain without changing any physical leader bit. -/
theorem runLocalSchedule_multiLeaderCleanup_resetFree_sweep
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) (hn : 1 < n)
    (start : Fin n) (C : Fin n → ExpiringAgentState psi kappa tau)
    (steps : Nat) (hsteps : steps < n)
    (hsourceFollower : (C start).core.erase.core.leader = false)
    (halong : MultiLeaderCleanupResetFreeReadyAlong
      hpsi kappa tau ring C
        (clockwiseEdgeSchedule ring start steps)) :
    let D := runLocalSchedule ring
      (multiLeaderCleanupTransition hpsi kappa tau) C
      (clockwiseEdgeSchedule ring start steps)
    (∀ i, (D i).core.erase.core.leader =
      (C i).core.erase.core.leader) ∧
      (D (cwPos ring start steps)).core.erase.core.leader = false ∧
      (D (cwPos ring start steps)).core.erase.core.label =
        ⟨((C start).core.erase.core.label.val + steps) % psi,
          Nat.mod_lt _ hpsi⟩ ∧
      (∀ k, k ≤ steps →
        (D (cwPos ring start k)).core.erase.core.label =
          ⟨((C start).core.erase.core.label.val + k) % psi,
            Nat.mod_lt _ hpsi⟩) ∧
      (∀ k, steps < k → k < n →
        D (cwPos ring start k) = C (cwPos ring start k)) := by
  let T := multiLeaderCleanupTransition hpsi kappa tau
  induction steps with
  | zero =>
      simp only [clockwiseEdgeSchedule, runLocalSchedule, cwPos_zero]
      have hbaseLabel : (C start).core.erase.core.label =
          ⟨((C start).core.erase.core.label.val + 0) % psi,
            Nat.mod_lt _ hpsi⟩ := by
        apply Fin.ext
        simp [Nat.mod_eq_of_lt
          (C start).core.erase.core.label.isLt]
      exact ⟨fun _ => True.intro, hsourceFollower, hbaseLabel,
        (by
          intro k hk
          have hk0 : k = 0 := by omega
          subst k
          simpa using hbaseLabel),
        fun _ _ _ => True.intro⟩
  | succ s ih =>
      have hslt : s < n := by omega
      let xs := clockwiseEdgeSchedule ring start s
      let e := cwPos ring start s
      have halong' : MultiLeaderCleanupResetFreeReadyAlong
          hpsi kappa tau ring C (xs ++ [e]) := by
        simpa [xs, e, clockwiseEdgeSchedule] using halong
      have hsplit :=
        (multiLeaderCleanupResetFreeReadyAlong_append_iff
          hpsi kappa tau ring C xs [e]).1 halong'
      have hprev := ih hslt hsplit.1
      let D := runLocalSchedule ring T C xs
      change (∀ i, (D i).core.erase.core.leader =
            (C i).core.erase.core.leader) ∧
          (D (cwPos ring start s)).core.erase.core.leader = false ∧
          (D (cwPos ring start s)).core.erase.core.label =
            ⟨((C start).core.erase.core.label.val + s) % psi,
              Nat.mod_lt _ hpsi⟩ ∧
          (∀ k, k ≤ s →
            (D (cwPos ring start k)).core.erase.core.label =
              ⟨((C start).core.erase.core.label.val + k) % psi,
                Nat.mod_lt _ hpsi⟩) ∧
          (∀ k, s < k → k < n →
            D (cwPos ring start k) = C (cwPos ring start k)) at hprev
      have hedge : ExpiringMultiLeaderCleanupResetFreePairReady
          hpsi kappa (D e) (D (ring.rightNeighbor e)) := by
        have hsingle := hsplit.2
        change ExpiringMultiLeaderCleanupResetFreePairReady
            hpsi kappa (D e) (D (ring.rightNeighbor e)) ∧ True
          at hsingle
        exact hsingle.1
      let j := ring.rightNeighbor e
      let E := localStep ring T D e
      have hstep := localStep_multiLeaderCleanup_resetFree_follower_edge
        hpsi kappa tau ring hn D e hedge
      change (∀ i, (E i).core.erase.core.leader =
            (D i).core.erase.core.leader) ∧
          (E e).core.erase.core.label = (D e).core.erase.core.label ∧
          (E j).core.erase.core.label =
            ⟨((D e).core.erase.core.label.val + 1) % psi,
              Nat.mod_lt _ hpsi⟩ ∧
          (E j).core.erase.core.leader = false ∧
          (∀ i, i ≠ e → i ≠ j → E i = D i) at hstep
      have hj : j = cwPos ring start (s + 1) := by
        simpa [j, e] using (cwPos_succ ring start s).symm
      have hleaderFrame : ∀ i,
          (E i).core.erase.core.leader =
            (C i).core.erase.core.leader := fun i =>
        (hstep.1 i).trans (hprev.1 i)
      have hendLeader :
          (E (cwPos ring start (s + 1))).core.erase.core.leader =
            false := by
        rw [← hj]
        exact hstep.2.2.2.1
      have hendLabel :
          (E (cwPos ring start (s + 1))).core.erase.core.label =
            ⟨((C start).core.erase.core.label.val + (s + 1)) % psi,
              Nat.mod_lt _ hpsi⟩ := by
        rw [← hj]
        calc
          (E j).core.erase.core.label =
              ⟨((D e).core.erase.core.label.val + 1) % psi,
                Nat.mod_lt _ hpsi⟩ := hstep.2.2.1
          _ = ⟨((C start).core.erase.core.label.val + (s + 1)) % psi,
                Nat.mod_lt _ hpsi⟩ := by
            apply Fin.ext
            have hfront := congrArg Fin.val hprev.2.2.1
            change (D (cwPos ring start s)).core.erase.core.label.val =
              ((C start).core.erase.core.label.val + s) % psi at hfront
            change ((D e).core.erase.core.label.val + 1) % psi =
              ((C start).core.erase.core.label.val + (s + 1)) % psi
            rw [show (D e).core.erase.core.label.val =
              ((C start).core.erase.core.label.val + s) % psi by
                simpa [e] using hfront]
            simpa [Nat.add_assoc] using
              mod_add_one (C start).core.erase.core.label.val s psi
      have hvisited : ∀ k, k ≤ s + 1 →
          (E (cwPos ring start k)).core.erase.core.label =
            ⟨((C start).core.erase.core.label.val + k) % psi,
              Nat.mod_lt _ hpsi⟩ := by
        intro k hk
        by_cases hlast : k = s + 1
        · subst k
          exact hendLabel
        have hkle : k ≤ s := by omega
        by_cases hcurrent : k = s
        · subst k
          calc
            (E (cwPos ring start s)).core.erase.core.label =
                (D e).core.erase.core.label := by
              simpa [e] using hstep.2.1
            _ = ⟨((C start).core.erase.core.label.val + s) % psi,
                  Nat.mod_lt _ hpsi⟩ := by
              simpa [e] using hprev.2.2.2.1 s (Nat.le_refl _)
        · have hklt : k < s := by omega
          have hkn : k < n := by omega
          have hke : cwPos ring start k ≠ e := by
            simpa [e] using
              SegmentCleanupPlan.cwPos_ne_of_ne_below_segment
                ring start hkn hslt (by omega)
          have hkj : cwPos ring start k ≠ j := by
            rw [hj]
            exact SegmentCleanupPlan.cwPos_ne_of_ne_below_segment
              ring start hkn hsteps (by omega)
          calc
            (E (cwPos ring start k)).core.erase.core.label =
                (D (cwPos ring start k)).core.erase.core.label :=
              congrArg (fun u => u.core.erase.core.label)
                (hstep.2.2.2.2 (cwPos ring start k) hke hkj)
            _ = ⟨((C start).core.erase.core.label.val + k) % psi,
                  Nat.mod_lt _ hpsi⟩ := hprev.2.2.2.1 k hkle
      have hahead : ∀ k, s + 1 < k → k < n →
          E (cwPos ring start k) = C (cwPos ring start k) := by
        intro k hk hkn
        have hke : cwPos ring start k ≠ e := by
          simpa [e] using
            SegmentCleanupPlan.cwPos_ne_of_ne_below_segment
              ring start hkn hslt (by omega)
        have hkj : cwPos ring start k ≠ j := by
          rw [hj]
          exact SegmentCleanupPlan.cwPos_ne_of_ne_below_segment
            ring start hkn hsteps (by omega)
        exact (hstep.2.2.2.2 (cwPos ring start k) hke hkj).trans
          (hprev.2.2.2.2 k (by omega) hkn)
      have hrun : runLocalSchedule ring T C
          (clockwiseEdgeSchedule ring start (s + 1)) = E := by
        change runLocalSchedule ring T C (xs ++ [e]) = E
        rw [runLocalSchedule_append_generic]
        rfl
      rw [hrun]
      exact ⟨hleaderFrame, hendLeader, hendLabel, hvisited, hahead⟩

/-- The generic reset-free sweep, specialized to the literal post-kill
`repairTail` and transported through the `word ++ repairTail` execution. -/
theorem physicalFullOutput_repairTail_of_resetFreeReadyAlong
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) (hn : 1 < n)
    (plan : SegmentCleanupPlan ring)
    (C : EConfig n psi kappa tau)
    (hsourceFollower :
      ((plan.physicalWordOutput hpsi kappa tau C)
        plan.predIncoming).core.erase.core.leader = false)
    (halong : MultiLeaderCleanupResetFreeReadyAlong
      hpsi kappa tau ring
        (plan.physicalWordOutput hpsi kappa tau C) plan.repairTail) :
    let B := plan.physicalWordOutput hpsi kappa tau C
    let D := plan.physicalFullOutput hpsi kappa tau C
    (∀ i, (D i).core.erase.core.leader =
      (B i).core.erase.core.leader) ∧
      (D (cwPos ring plan.predIncoming plan.dVS)).core.erase.core.leader =
        false ∧
      (D (cwPos ring plan.predIncoming plan.dVS)).core.erase.core.label =
        ⟨((B plan.predIncoming).core.erase.core.label.val + plan.dVS) % psi,
          Nat.mod_lt _ hpsi⟩ ∧
      (∀ k, k ≤ plan.dVS →
        (D (cwPos ring plan.predIncoming k)).core.erase.core.label =
          ⟨((B plan.predIncoming).core.erase.core.label.val + k) % psi,
            Nat.mod_lt _ hpsi⟩) ∧
      (∀ k, plan.dVS < k → k < n →
        D (cwPos ring plan.predIncoming k) =
          B (cwPos ring plan.predIncoming k)) := by
  let B := plan.physicalWordOutput hpsi kappa tau C
  let D := plan.physicalFullOutput hpsi kappa tau C
  have hsweep := runLocalSchedule_multiLeaderCleanup_resetFree_sweep
    hpsi kappa tau ring hn plan.predIncoming B plan.dVS plan.dVS_lt
      hsourceFollower (by simpa [SegmentCleanupPlan.repairTail] using halong)
  let tailOut := runLocalSchedule ring
    (multiLeaderCleanupTransition hpsi kappa tau) B plan.repairTail
  change (∀ i, (tailOut i).core.erase.core.leader =
        (B i).core.erase.core.leader) ∧
      (tailOut (cwPos ring plan.predIncoming plan.dVS)).core.erase.core.leader =
        false ∧
      (tailOut (cwPos ring plan.predIncoming plan.dVS)).core.erase.core.label =
        ⟨((B plan.predIncoming).core.erase.core.label.val + plan.dVS) % psi,
          Nat.mod_lt _ hpsi⟩ ∧
      (∀ k, k ≤ plan.dVS →
        (tailOut (cwPos ring plan.predIncoming k)).core.erase.core.label =
          ⟨((B plan.predIncoming).core.erase.core.label.val + k) % psi,
            Nat.mod_lt _ hpsi⟩) ∧
      (∀ k, plan.dVS < k → k < n →
        tailOut (cwPos ring plan.predIncoming k) =
          B (cwPos ring plan.predIncoming k)) at hsweep
  have hfull : D = tailOut := by
    unfold D tailOut SegmentCleanupPlan.physicalFullOutput
      SegmentCleanupPlan.fullWord SegmentCleanupPlan.repairTail B
    exact runLocalSchedule_append_generic ring
      (multiLeaderCleanupTransition hpsi kappa tau) C plan.word
        (clockwiseEdgeSchedule ring plan.predIncoming plan.dVS)
  change (∀ i, (D i).core.erase.core.leader =
        (B i).core.erase.core.leader) ∧
      (D (cwPos ring plan.predIncoming plan.dVS)).core.erase.core.leader =
        false ∧
      (D (cwPos ring plan.predIncoming plan.dVS)).core.erase.core.label =
        ⟨((B plan.predIncoming).core.erase.core.label.val + plan.dVS) % psi,
          Nat.mod_lt _ hpsi⟩ ∧
      (∀ k, k ≤ plan.dVS →
        (D (cwPos ring plan.predIncoming k)).core.erase.core.label =
          ⟨((B plan.predIncoming).core.erase.core.label.val + k) % psi,
            Nat.mod_lt _ hpsi⟩) ∧
      (∀ k, plan.dVS < k → k < n →
        D (cwPos ring plan.predIncoming k) =
          B (cwPos ring plan.predIncoming k))
  rw [hfull]
  exact hsweep

/-- Correct strict-descent theorem for the literal full word.  The kill prefix
uses the existing physical readiness certificate; the repair suffix uses the
reset-free certificate proved above, so no nonexistent reset-token producer
is assumed. -/
theorem SegmentCleanupReady.physicalFullOutput_count_lt_of_readyAlong_resetFree
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) (hn : 1 < n)
    (plan : SegmentCleanupPlan ring)
    (C : EConfig n psi kappa tau)
    (hready : SegmentCleanupReady
      hpsi ring plan (eraseExpiringCleanupConfig C))
    (hkill : MultiLeaderCleanupPhysicalReadyAlong
      hpsi kappa tau ring C plan.word)
    (hsourceFollower :
      ((plan.physicalWordOutput hpsi kappa tau C)
        plan.predIncoming).core.erase.core.leader = false)
    (htail : MultiLeaderCleanupResetFreeReadyAlong
      hpsi kappa tau ring
        (plan.physicalWordOutput hpsi kappa tau C) plan.repairTail) :
    rawPhysicalLeaderCount
        (eraseExpiringCleanupConfig
          (plan.physicalFullOutput hpsi kappa tau C)) <
      rawPhysicalLeaderCount (eraseExpiringCleanupConfig C) := by
  let B := plan.physicalWordOutput hpsi kappa tau C
  let D := plan.physicalFullOutput hpsi kappa tau C
  have hword :=
    PPLLCompleteMultiLeaderCleanup.PhysicalBridge.SegmentCleanupReady.expiringPhysicalLeaderCount_lt_of_readyAlong
      hpsi kappa tau ring plan C hready hkill
  change rawPhysicalLeaderCount (eraseExpiringCleanupConfig B) <
      rawPhysicalLeaderCount (eraseExpiringCleanupConfig C) at hword
  have hsweep := physicalFullOutput_repairTail_of_resetFreeReadyAlong
    hpsi kappa tau ring hn plan C hsourceFollower htail
  change (∀ i, (D i).core.erase.core.leader =
      (B i).core.erase.core.leader) ∧ _ at hsweep
  have hcountFrame :=
    rawPhysicalLeaderCount_erase_eq_of_leader_frame B D hsweep.1
  change rawPhysicalLeaderCount (eraseExpiringCleanupConfig D) <
    rawPhysicalLeaderCount (eraseExpiringCleanupConfig C)
  rw [hcountFrame]
  exact hword

/-- Barrier reconstruction for the literal full word using the reset-free
prefix certificate.  This is the replacement for the invalid reset-token
producer assumption in the older theorem. -/
theorem physicalFullOutput_noFreeBarrier_of_reference_resetFree
    (hpsi : psi > 0) (kappa tau : Nat)
    (ring : DirectedRing n) (hn : 1 < n)
    (plan : SegmentCleanupPlan ring)
    (C : EConfig n psi kappa tau)
    (A : Fin n → AgentState psi)
    (hsourceAhead : plan.dVS + 1 < n)
    (hfreeA : noFreeBarrier hpsi ring A)
    (hsourceFollower :
      ((plan.physicalWordOutput hpsi kappa tau C)
        plan.predIncoming).core.erase.core.leader = false)
    (halong : MultiLeaderCleanupResetFreeReadyAlong
      hpsi kappa tau ring
        (plan.physicalWordOutput hpsi kappa tau C) plan.repairTail)
    (hstartLabel :
      ((plan.physicalWordOutput hpsi kappa tau C)
        plan.predIncoming).core.erase.core.label =
          (A plan.predIncoming).label)
    (hstartLeader :
      ((plan.physicalWordOutput hpsi kappa tau C)
        plan.predIncoming).core.erase.core.leader =
          (A plan.predIncoming).leader)
    (hsurvivor :
      ((plan.physicalWordOutput hpsi kappa tau C)
        (cwPos ring plan.predIncoming (plan.dVS + 1))).core.erase.core.leader =
          true)
    (houtside : ∀ k, plan.dVS < k → k < n →
      ((plan.physicalWordOutput hpsi kappa tau C)
        (cwPos ring plan.predIncoming k)).core.erase.core =
          A (cwPos ring plan.predIncoming k)) :
    noFreeBarrier hpsi ring (fun i =>
      ((plan.physicalFullOutput hpsi kappa tau C) i).core.erase.core) := by
  let B := plan.physicalWordOutput hpsi kappa tau C
  let D := plan.physicalFullOutput hpsi kappa tau C
  have hsweep := physicalFullOutput_repairTail_of_resetFreeReadyAlong
    hpsi kappa tau ring hn plan C hsourceFollower halong
  change (∀ i, (D i).core.erase.core.leader =
        (B i).core.erase.core.leader) ∧
      (D (cwPos ring plan.predIncoming plan.dVS)).core.erase.core.leader =
        false ∧
      (D (cwPos ring plan.predIncoming plan.dVS)).core.erase.core.label =
        ⟨((B plan.predIncoming).core.erase.core.label.val + plan.dVS) % psi,
          Nat.mod_lt _ hpsi⟩ ∧
      (∀ k, k ≤ plan.dVS →
        (D (cwPos ring plan.predIncoming k)).core.erase.core.label =
          ⟨((B plan.predIncoming).core.erase.core.label.val + k) % psi,
            Nat.mod_lt _ hpsi⟩) ∧
      (∀ k, plan.dVS < k → k < n →
        D (cwPos ring plan.predIncoming k) =
          B (cwPos ring plan.predIncoming k)) at hsweep
  have hstartD :
      (D plan.predIncoming).core.erase.core.label =
        (B plan.predIncoming).core.erase.core.label := by
    have hzero := hsweep.2.2.2.1 0 (by omega)
    simpa [Nat.mod_eq_of_lt
      (B plan.predIncoming).core.erase.core.label.isLt] using hzero
  change noFreeBarrier hpsi ring (fun i => (D i).core.erase.core)
  apply noFreeBarrier_of_clockwise_repaired_interval
    hpsi ring plan.predIncoming plan.dVS
      (A := A) (D := fun i => (D i).core.erase.core)
      hsourceAhead hfreeA
  · exact hstartD.trans hstartLabel
  · exact (hsweep.1 plan.predIncoming).trans hstartLeader
  · exact (hsweep.1
      (cwPos ring plan.predIncoming (plan.dVS + 1))).trans hsurvivor
  · intro k hk
    calc
      (D (cwPos ring plan.predIncoming k)).core.erase.core.label =
          ⟨((B plan.predIncoming).core.erase.core.label.val + k) % psi,
            Nat.mod_lt _ hpsi⟩ := hsweep.2.2.2.1 k hk
      _ = ⟨((D plan.predIncoming).core.erase.core.label.val + k) % psi,
            Nat.mod_lt _ hpsi⟩ := by rw [hstartD]
  · intro k hk hkn
    calc
      (D (cwPos ring plan.predIncoming k)).core.erase.core =
          (B (cwPos ring plan.predIncoming k)).core.erase.core :=
        congrArg (fun u => u.core.erase.core)
          (hsweep.2.2.2.2 k hk hkn)
      _ = A (cwPos ring plan.predIncoming k) := houtside k hk hkn

end PhysicalBridge
end PPLLCompleteMultiLeaderCleanup
