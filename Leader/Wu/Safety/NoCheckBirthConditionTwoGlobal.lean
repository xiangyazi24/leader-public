import Leader.Wu.Safety.NoCheckBirthConditionTwoKernel

/-!
# Global Algorithm-15 preservation for corrected condition 2

This module embeds the no-collision Algorithm-15 kernel into one ring update.
It proves pointwise leader and label preservation, canonical target/shield and
zero-signal interval preservation, leftward witness extension, and finally the
full global `noNonPeacefulBullet` invariant on every nontrivial output-safe ring.
-/

namespace PPLLNoCheckBirthConditionTwoGlobal
open PPLL PPLLRepair PPLLNoCheckBirthConditionTwoGeometry
  PPLLNoCheckBirthConditionTwoKernel PPLLNoCheckBirthLeaderFrames

/-- On an output-safe edge, no-collision Algorithm 15 preserves both endpoint
leader bits. -/
theorem noCollision_leaders_eq_of_paperSafe
    (hψ : ψ > 0) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hSafe : OutputSafeConfig hψ ring C)
    (e : Fin n) :
    let r := ring.rightNeighbor e
    let q := eliminateLeadersNoCollision hψ (C e) (C r)
    q.1.leader = (C e).leader ∧ q.2.leader = (C r).leader := by
  let r := ring.rightNeighbor e
  let q := eliminateLeadersNoCollision hψ (C e) (C r)
  constructor
  · cases hl : (C e).leader
    · cases hq : q.1.leader
      · rfl
      · have hbad := eliminateLeadersNoCollision_initiator_origin hψ (C e) (C r) hq
        rw [hl] at hbad
        simp at hbad
    · apply eliminateLeadersNoCollision_initiator_survives hψ (C e) (C r) hl
      intro hkill
      have hpeace := hSafe.no_nonpeaceful_bullet r hkill.1
      obtain ⟨_, d, hd, htarget, hshield, _, _⟩ := hpeace
      have htargetEq :
          (⟨(r.val + d) % n, Nat.mod_lt _ ring.hn⟩ : Fin n) = e := by
        obtain ⟨leaderPos, hleaderPos, honly⟩ := hSafe.unique_leader
        have he : e = leaderPos := by
          apply honly
          simpa [AgentState.isLeader] using hl
        have ht : (⟨(r.val + d) % n,
            Nat.mod_lt _ ring.hn⟩ : Fin n) = leaderPos := by
          apply honly
          exact htarget
        exact ht.trans he.symm
      rw [htargetEq] at hshield
      rw [hkill.2] at hshield
      simp at hshield
  · exact eliminateLeadersNoCollision_responder_leader_eq hψ (C e) (C r)

/-- Configuration update consisting only of the repaired Algorithm-15 kernel. -/
def noCollisionStep (hψ : ψ > 0) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (e : Fin n) : Fin n → AgentState ψ :=
  updatePair C e (ring.rightNeighbor e)
    (eliminateLeadersNoCollision hψ (C e) (C (ring.rightNeighbor e)))

/-- On output-safe input, the isolated kernel preserves every leader bit. -/
theorem noCollisionStep_leader_eq
    (hψ : ψ > 0) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hSafe : OutputSafeConfig hψ ring C)
    (e k : Fin n) :
    (noCollisionStep hψ ring C e k).leader = (C k).leader := by
  have hq := noCollision_leaders_eq_of_paperSafe hψ ring C hSafe e
  unfold noCollisionStep updatePair
  by_cases hke : k = e
  · simp [hke, hq.1]
  · by_cases hkr : k = ring.rightNeighbor e
    · have hre : ring.rightNeighbor e ≠ e := by
        intro hre
        exact hke (hkr.trans hre)
      simp [hkr, hre, hq.2]
    · simp [hke, hkr]

/-- The isolated kernel preserves every label without a safety assumption. -/
theorem noCollisionStep_label_eq
    (hψ : ψ > 0) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (e k : Fin n) :
    (noCollisionStep hψ ring C e k).label = (C k).label := by
  have hq := noCollision_labels hψ (C e) (C (ring.rightNeighbor e))
  unfold noCollisionStep updatePair
  by_cases hke : k = e
  · simp [hke, hq.1]
  · by_cases hkr : k = ring.rightNeighbor e
    · have hre : ring.rightNeighbor e ≠ e := by
        intro hre
        exact hke (hkr.trans hre)
      simp [hkr, hre, hq.2]
    · simp [hke, hkr]

/-- The canonical target of an old live bullet remains a shielded leader after
the isolated Algorithm-15 update. -/
theorem noCollisionStep_canonical_target_fields
    (hψ : ψ > 0) (hn2 : 1 < n) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hSafe : OutputSafeConfig hψ ring C)
    (e leaderPos start : Fin n)
    (hframe : CanonicalBulletFrame hψ ring C leaderPos start) :
    let D := noCollisionStep hψ ring C e
    (D leaderPos).isLeader ∧ (D leaderPos).shield = true := by
  let r := ring.rightNeighbor e
  let q := eliminateLeadersNoCollision hψ (C e) (C r)
  let D := noCollisionStep hψ ring C e
  let d := cwDist ring start leaderPos
  have hne : r ≠ e := rightNeighbor_ne_self_of_one_lt ring hn2 e
  have htargetPos : cwPos ring start d = leaderPos :=
    cwPos_cwDist ring start leaderPos
  constructor
  · change (D leaderPos).leader = true
    rw [noCollisionStep_leader_eq hψ ring C hSafe e leaderPos]
    exact hframe.target_leader
  · have htargetZero := hframe.signal_zero d (by omega)
    have htargetZeroAt : (C leaderPos).signal_B = ⟨0, by omega⟩ := by
      rw [← htargetPos]
      exact htargetZero
    change (updatePair C e r q leaderPos).shield = true
    by_cases hle : leaderPos = e
    · have hzero : (C e).signal_B = ⟨0, by omega⟩ := by
        simpa [hle] using htargetZeroAt
      have hshield : (C e).shield = true := by
        simpa [hle] using hframe.target_shield
      rw [hle, updatePair_initiator]
      rw [noCollision_left_shield_of_signal_zero hψ (C e) (C r) hzero]
      exact hshield
    · by_cases hlr : leaderPos = r
      · have hzero : (C r).signal_B = ⟨0, by omega⟩ := by
          simpa [hlr] using htargetZeroAt
        have hshield : (C r).shield = true := by
          simpa [hlr] using hframe.target_shield
        rw [hlr, updatePair_responder C e r q hne]
        rw [noCollision_right_shield_of_signal_zero hψ (C e) (C r) hzero]
        exact hshield
      · rw [updatePair_other C e r leaderPos q hle hlr]
        exact hframe.target_shield

/-- The old canonical zero-signal interval survives Algorithm 15 once the
special case in which the interval starts at the responder is supplied. -/
theorem noCollisionStep_canonical_signals
    (hψ : ψ > 0) (hn2 : 1 < n) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hSafe : OutputSafeConfig hψ ring C)
    (e leaderPos start : Fin n)
    (hframe : CanonicalBulletFrame hψ ring C leaderPos start)
    (hresponderStart : start = ring.rightNeighbor e →
      (eliminateLeadersNoCollision hψ
        (C e) (C (ring.rightNeighbor e))).2.signal_B = ⟨0, by omega⟩) :
    ∀ k : Nat, k ≤ cwDist ring start leaderPos →
      (noCollisionStep hψ ring C e
        (cwPos ring start k)).signal_B = ⟨0, by omega⟩ := by
  intro k hk
  let r := ring.rightNeighbor e
  let q := eliminateLeadersNoCollision hψ (C e) (C r)
  let m := cwPos ring start k
  let d := cwDist ring start leaderPos
  have hne : r ≠ e := rightNeighbor_ne_self_of_one_lt ring hn2 e
  have hdlt : d < n := cwDist_lt ring start leaderPos
  have hmzero := hframe.signal_zero k hk
  change (C m).signal_B = ⟨0, by omega⟩ at hmzero
  change (updatePair C e r q m).signal_B = ⟨0, by omega⟩
  by_cases hme : m = e
  · rw [hme] at hmzero ⊢
    rw [updatePair_initiator]
    exact noCollision_left_signal_zero_of_zero hψ (C e) (C r) hmzero
  · by_cases hmr : m = r
    · rw [hmr] at hmzero ⊢
      rw [updatePair_responder C e r q hne]
      by_cases hstart : start = r
      · exact hresponderStart hstart
      · have hmpos : cwPos ring start k = ring.rightNeighbor e := hmr
        obtain ⟨k0, hkEq, hk0Pos⟩ :=
          interval_predecessor ring start e k hmpos hstart
        have hk0le : k0 ≤ d := by omega
        have hleftZero := hframe.signal_zero k0 hk0le
        have hleftFollower : (C e).leader = false := by
          cases hel : (C e).leader
          · rfl
          · obtain ⟨uniquePos, _, honly⟩ := hSafe.unique_leader
            have heUnique : e = uniquePos := by
              apply honly
              simpa [AgentState.isLeader] using hel
            have hlUnique : leaderPos = uniquePos := by
              apply honly
              exact hframe.target_leader
            have heLeader : e = leaderPos := heUnique.trans hlUnique.symm
            have hk0lt : k0 < n := by omega
            have hk0Eq := cwPos_bounded_unique ring start leaderPos k0
              hk0lt (hk0Pos.trans heLeader)
            change k0 = d at hk0Eq
            omega
        have hleftZeroAt : (C e).signal_B = ⟨0, by omega⟩ := by
          rw [← hk0Pos]
          exact hleftZero
        exact noCollision_right_signal_zero_of_zeros_follower
          hψ (C e) (C r) hleftZeroAt hmzero hleftFollower
    · rw [updatePair_other C e r m q hme hmr]
      exact hmzero

/-- Every input live bullet that remains at its position after the isolated
Algorithm-15 update keeps its canonical peacefulness witness. -/
theorem noCollisionStep_old_live_stays_peaceful
    (hψ : ψ > 0) (hn2 : 1 < n) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hSafe : OutputSafeConfig hψ ring C)
    (e leaderPos start : Fin n)
    (hleader : (C leaderPos).isLeader)
    (holdLive : (C start).bullet = ⟨2, by omega⟩)
    (hnewLive : (noCollisionStep hψ ring C e start).bullet =
      ⟨2, by omega⟩) :
    isPeacefulBullet hψ ring (noCollisionStep hψ ring C e) start := by
  let r := ring.rightNeighbor e
  let q := eliminateLeadersNoCollision hψ (C e) (C r)
  let D := noCollisionStep hψ ring C e
  let d := cwDist ring start leaderPos
  have hne : r ≠ e := rightNeighbor_ne_self_of_one_lt ring hn2 e
  have hframe := canonicalBulletFrame_of_paperSafe
    hψ ring C hSafe leaderPos start hleader holdLive
  have htargetPos : cwPos ring start d = leaderPos :=
    cwPos_cwDist ring start leaderPos
  have hdlt : d < n := cwDist_lt ring start leaderPos
  refine ⟨hnewLive, d, hdlt, ?_, ?_, ?_, ?_⟩
  · change (D (cwPos ring start d)).isLeader
    rw [htargetPos]
    change (D leaderPos).leader = true
    rw [noCollisionStep_leader_eq hψ ring C hSafe e leaderPos]
    exact hleader
  · change (D (cwPos ring start d)).shield = true
    rw [htargetPos]
    have htargetZero := hframe.signal_zero d (by omega)
    have htargetZeroAt : (C leaderPos).signal_B = ⟨0, by omega⟩ := by
      rw [← htargetPos]
      exact htargetZero
    change (updatePair C e r q leaderPos).shield = true
    by_cases hle : leaderPos = e
    · have hzero : (C e).signal_B = ⟨0, by omega⟩ := by
        simpa [hle] using htargetZeroAt
      have hshield : (C e).shield = true := by
        simpa [hle] using hframe.target_shield
      rw [hle, updatePair_initiator]
      rw [noCollision_left_shield_of_signal_zero
        hψ (C e) (C r) hzero]
      exact hshield
    · by_cases hlr : leaderPos = r
      · have hzero : (C r).signal_B = ⟨0, by omega⟩ := by
          simpa [hlr] using htargetZeroAt
        have hshield : (C r).shield = true := by
          simpa [hlr] using hframe.target_shield
        rw [hlr, updatePair_responder C e r q hne]
        rw [noCollision_right_shield_of_signal_zero
          hψ (C e) (C r) hzero]
        exact hshield
      · rw [updatePair_other C e r leaderPos q hle hlr]
        exact hframe.target_shield
  · intro k hk
    let m := cwPos ring start k
    have hmzero := hframe.signal_zero k hk
    change (C m).signal_B = ⟨0, by omega⟩ at hmzero
    change (D m).signal_B = ⟨0, by omega⟩
    change (updatePair C e r q m).signal_B = ⟨0, by omega⟩
    by_cases hme : m = e
    · rw [hme] at hmzero ⊢
      rw [updatePair_initiator]
      apply noCollision_left_signal_zero_of_zero
      exact hmzero
    · by_cases hmr : m = r
      · rw [hmr] at hmzero ⊢
        rw [updatePair_responder C e r q hne]
        by_cases hstart : start = r
        · have hqLive : q.2.bullet = ⟨2, by omega⟩ := by
            have h := hnewLive
            change (updatePair C e r q start).bullet = ⟨2, by omega⟩ at h
            rw [hstart, updatePair_responder C e r q hne] at h
            exact h
          exact noCollision_right_live_signal_zero hψ (C e) (C r) hqLive
        · have hmpos : cwPos ring start k = ring.rightNeighbor e := by
            exact hmr
          obtain ⟨k0, hkEq, hk0Pos⟩ :=
            interval_predecessor ring start e k hmpos hstart
          have hk0le : k0 ≤ d := by omega
          have hleftZero := hframe.signal_zero k0 hk0le
          have hleftFollower : (C e).leader = false := by
            cases hel : (C e).leader
            · rfl
            · obtain ⟨uniquePos, hunique, honly⟩ := hSafe.unique_leader
              have heUnique : e = uniquePos := by
                apply honly
                simpa [AgentState.isLeader] using hel
              have hlUnique : leaderPos = uniquePos := by
                apply honly
                exact hleader
              have heLeader : e = leaderPos :=
                heUnique.trans hlUnique.symm
              have hk0lt : k0 < n := by omega
              have hk0Eq :=
                cwPos_bounded_unique ring start leaderPos k0 hk0lt
                  (hk0Pos.trans heLeader)
              change k0 = d at hk0Eq
              omega
          have hleftZeroAt : (C e).signal_B = ⟨0, by omega⟩ := by
            rw [← hk0Pos]
            exact hleftZero
          exact noCollision_right_signal_zero_of_zeros_follower
            hψ (C e) (C r) hleftZeroAt hmzero hleftFollower
      · rw [updatePair_other C e r m q hme hmr]
        exact hmzero
  · intro k hk
    change (D (cwPos ring start (k + 1))).label =
      ⟨((D (cwPos ring start k)).label.val + 1) % ψ,
        Nat.mod_lt _ hψ⟩
    rw [noCollisionStep_label_eq hψ ring C e,
      noCollisionStep_label_eq hψ ring C e]
    exact hframe.label_successor k hk

/-- The repaired Algorithm-15 kernel preserves the full global
`noNonPeacefulBullet` predicate on every nontrivial output-safe ring. -/
theorem noNonPeacefulBullet_preserved_noCollisionStep
    (hψ : ψ > 0) (hn2 : 1 < n) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (hSafe : OutputSafeConfig hψ ring C)
    (e : Fin n) :
    noNonPeacefulBullet hψ ring (noCollisionStep hψ ring C e) := by
  intro start hnewLive
  let r := ring.rightNeighbor e
  let q := eliminateLeadersNoCollision hψ (C e) (C r)
  let D := noCollisionStep hψ ring C e
  have hne : r ≠ e := rightNeighbor_ne_self_of_one_lt ring hn2 e
  by_cases hstartE : start = e
  · have hnewAtE := hnewLive
    change (D start).bullet = ⟨2, by omega⟩ at hnewAtE
    rw [hstartE] at hnewAtE
    have hqLive : q.1.bullet = ⟨2, by omega⟩ := by
      have h := hnewLive
      change (updatePair C e r q start).bullet = ⟨2, by omega⟩ at h
      rw [hstartE, updatePair_initiator] at h
      exact h
    rcases noCollision_left_live_origin hψ (C e) (C r) hqLive with
      hold | hfire | hmove
    · exact noCollisionStep_old_live_stays_peaceful
        hψ hn2 ring C hSafe e hSafe.unique_leader.choose start
        hSafe.unique_leader.choose_spec.1
        (by simpa [hstartE] using hold) hnewLive
    · have hfields := noCollision_left_fire_fields
        hψ (C e) (C r) hfire.1 hfire.2
      have hrFollower : (C r).leader = false := by
        cases hr : (C r).leader
        · rfl
        · obtain ⟨leaderPos, _, honly⟩ := hSafe.unique_leader
          have he : e = leaderPos := by
            apply honly
            simpa [AgentState.isLeader] using hfire.1
          have hrr : r = leaderPos := by
            apply honly
            simpa [AgentState.isLeader] using hr
          exact (hne (hrr.trans he.symm)).elim
      have hinputLabel := paperSafe_successor_label_of_responder_follower
        hψ ring C hSafe e hrFollower
      apply peacefulBullet_zero hψ ring D start hnewLive
      · change (D start).leader = true
        rw [noCollisionStep_leader_eq hψ ring C hSafe e start, hstartE]
        exact hfire.1
      · change (updatePair C e r q start).shield = true
        rw [hstartE, updatePair_initiator]
        exact hfields.1
      · change (updatePair C e r q start).signal_B = ⟨0, by omega⟩
        rw [hstartE, updatePair_initiator]
        exact hfields.2
      · rw [noCollisionStep_label_eq hψ ring C e,
          noCollisionStep_label_eq hψ ring C e, hstartE]
        exact hinputLabel
    · have hpeace := hSafe.no_nonpeaceful_bullet r hmove.1
      obtain ⟨_, d0, hd0, htarget, _, hsignals, hlabels⟩ := hpeace
      let target := cwPos ring r d0
      have hcanon := canonicalBulletFrame_of_paperSafe
        hψ ring C hSafe target r htarget hmove.1
      have hdEq : d0 = cwDist ring r target :=
        cwPos_bounded_unique ring r target d0 hd0 rfl
      have htargetFields := noCollisionStep_canonical_target_fields
        hψ hn2 ring C hSafe e target r hcanon
      have hrzero : (C r).signal_B = ⟨0, by omega⟩ := by
        have h := hsignals 0 (by omega)
        change (C (cwPos ring r 0)).signal_B = ⟨0, by omega⟩ at h
        rw [cwPos_zero] at h
        exact h
      have hqRzero := noCollision_right_signal_zero_of_moved_live
        hψ (C e) (C r) hmove.1 hmove.2.1 hmove.2.2 hrzero
      have hqLzero := noCollision_left_signal_zero_of_moved_live
        hψ (C e) (C r) hmove.1 hmove.2.1 hmove.2.2 hrzero
      have hcanonicalSignals := noCollisionStep_canonical_signals
        hψ hn2 ring C hSafe e target r hcanon (fun _ => hqRzero)
      rw [hstartE]
      apply peacefulBullet_of_move_left_fields
        hψ ring C D e d0 hd0 htarget hmove.2.1 hnewAtE
      · exact htargetFields.1
      · exact htargetFields.2
      · change (updatePair C e r q e).signal_B = ⟨0, by omega⟩
        rw [updatePair_initiator]
        exact hqLzero
      · intro k hk
        apply hcanonicalSignals k
        omega
      · rw [noCollisionStep_label_eq hψ ring C e,
          noCollisionStep_label_eq hψ ring C e]
        exact hmove.2.2
      · intro k hk
        rw [noCollisionStep_label_eq hψ ring C e,
          noCollisionStep_label_eq hψ ring C e]
        exact hlabels k hk
  · by_cases hstartR : start = r
    · have hqLive : q.2.bullet = ⟨2, by omega⟩ := by
        have h := hnewLive
        change (updatePair C e r q start).bullet = ⟨2, by omega⟩ at h
        rw [hstartR, updatePair_responder C e r q hne] at h
        exact h
      have hold := (noCollision_right_live_origin
        hψ (C e) (C r) hqLive).1
      exact noCollisionStep_old_live_stays_peaceful
        hψ hn2 ring C hSafe e hSafe.unique_leader.choose start
        hSafe.unique_leader.choose_spec.1 (by simpa [hstartR] using hold)
        hnewLive
    · have hold : (C start).bullet = ⟨2, by omega⟩ := by
        have h := hnewLive
        change (updatePair C e r q start).bullet = ⟨2, by omega⟩ at h
        rw [updatePair_other C e r start q hstartE hstartR] at h
        exact h
      exact noCollisionStep_old_live_stays_peaceful
        hψ hn2 ring C hSafe e hSafe.unique_leader.choose start
        hSafe.unique_leader.choose_spec.1 hold hnewLive

end PPLLNoCheckBirthConditionTwoGlobal
