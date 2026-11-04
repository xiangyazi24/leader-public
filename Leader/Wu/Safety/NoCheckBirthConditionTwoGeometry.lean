import Leader.Wu.Safety.NoCheckBirthPhysicalConditionOne

/-!
# Ring geometry for corrected condition 2

The literal peaceful-bullet predicate stores a bounded clockwise witness.  This
module canonicalizes that witness at the unique leader, proves the interval
geometry needed for one-edge movement, and constructs the `d+1` witness when a
live responder bullet moves left.  All objects are proof-only: no protocol
state or legitimacy premise is added.
-/

namespace PPLLNoCheckBirthConditionTwoGeometry

open PPLL

/-- Position reached after `k` clockwise edges from `i`; modular reduction
makes this total on the finite directed ring. -/
def cwPos (ring : DirectedRing n) (i : Fin n) (k : Nat) : Fin n :=
  ⟨(i.val + k) % n, Nat.mod_lt _ ring.hn⟩

/-- The unique clockwise distance from `i` to `j` in `[0,n)`. -/
def cwDist (_ring : DirectedRing n) (i j : Fin n) : Nat :=
  (j.val + n - i.val) % n

@[simp] theorem cwPos_zero (_ring : DirectedRing n) (i : Fin n) :
    cwPos _ring i 0 = i := by
  apply Fin.ext
  simp [cwPos, Nat.mod_eq_of_lt i.isLt]

/-- Canonical clockwise distance is strictly smaller than the ring size. -/
theorem cwDist_lt (ring : DirectedRing n) (i j : Fin n) :
    cwDist ring i j < n := by
  exact Nat.mod_lt _ ring.hn

/-- Advancing by the canonical clockwise distance reaches the target. -/
theorem cwPos_cwDist (ring : DirectedRing n) (i j : Fin n) :
    cwPos ring i (cwDist ring i j) = j := by
  apply Fin.ext
  unfold cwPos cwDist
  dsimp only
  rw [Nat.add_mod_mod]
  have hsum : i.val + (j.val + n - i.val) = j.val + n := by
    omega
  rw [hsum]
  simp [Nat.mod_eq_of_lt j.isLt]

/-- Any bounded clockwise witness reaching a target equals the canonical
distance.  This removes the existential-distance ambiguity from peacefulness. -/
theorem cwPos_bounded_unique (ring : DirectedRing n) (i j : Fin n)
    (d : Nat) (hd : d < n) (hpos : cwPos ring i d = j) :
    d = cwDist ring i j := by
  have hv := congrArg Fin.val hpos
  have hc := congrArg Fin.val (cwPos_cwDist ring i j)
  unfold cwPos at hv hc
  dsimp only at hv hc
  have hmod : (i.val + d) % n =
      (i.val + cwDist ring i j) % n := hv.trans hc.symm
  have hdist := cwDist_lt ring i j
  by_cases hdWrap : i.val + d < n
  · rw [Nat.mod_eq_of_lt hdWrap] at hmod
    by_cases hcWrap : i.val + cwDist ring i j < n
    · rw [Nat.mod_eq_of_lt hcWrap] at hmod
      omega
    · rw [Nat.mod_eq_sub_mod (by omega),
        Nat.mod_eq_of_lt (by omega)] at hmod
      omega
  · rw [Nat.mod_eq_sub_mod (by omega),
      Nat.mod_eq_of_lt (by omega)] at hmod
    by_cases hcWrap : i.val + cwDist ring i j < n
    · rw [Nat.mod_eq_of_lt hcWrap] at hmod
      omega
    · rw [Nat.mod_eq_sub_mod (by omega),
        Nat.mod_eq_of_lt (by omega)] at hmod
      omega

/-- Existing peacefulness, together with a unique leader, canonically fixes
both the target and the only bounded clockwise distance to it. -/
structure CanonicalBulletFrame (hψ : ψ > 0) (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (leaderPos start : Fin n) : Prop where
  target_leader : (C leaderPos).isLeader
  target_shield : (C leaderPos).shield = true
  signal_zero : ∀ k : Nat, k ≤ cwDist ring start leaderPos →
    (C (cwPos ring start k)).signal_B = ⟨0, by omega⟩
  label_successor : ∀ k : Nat, k ≤ cwDist ring start leaderPos →
    (C (cwPos ring start (k + 1))).label =
      ⟨((C (cwPos ring start k)).label.val + 1) % ψ,
        Nat.mod_lt _ hψ⟩

/-- `OutputSafeConfig` supplies the canonical current-state frame of every live
bullet; no history or physical provenance field is added. -/
theorem canonicalBulletFrame_of_paperSafe
    (hψ : ψ > 0) (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hSafe : OutputSafeConfig hψ ring C)
    (leaderPos start : Fin n)
    (hleader : (C leaderPos).isLeader)
    (hbullet : (C start).bullet = ⟨2, by omega⟩) :
    CanonicalBulletFrame hψ ring C leaderPos start := by
  obtain ⟨_, d, hd, htarget, hshield, hsignal, hlabels⟩ :=
    hSafe.no_nonpeaceful_bullet start hbullet
  obtain ⟨uniquePos, huniqueLeader, honly⟩ := hSafe.unique_leader
  have htargetUnique : cwPos ring start d = uniquePos := by
    apply honly
    exact htarget
  have hleaderUnique : leaderPos = uniquePos := by
    apply honly
    exact hleader
  have htargetEq : cwPos ring start d = leaderPos :=
    htargetUnique.trans hleaderUnique.symm
  have hdEq : d = cwDist ring start leaderPos :=
    cwPos_bounded_unique ring start leaderPos d hd htargetEq
  constructor
  · exact hleader
  · change (C (cwPos ring start d)).shield = true at hshield
    rw [htargetEq] at hshield
    exact hshield
  · intro k hk
    have hk' : k ≤ d := by omega
    simpa [cwPos] using hsignal k hk'
  · intro k hk
    have hk' : k ≤ d := by omega
    simpa [cwPos, Nat.add_assoc] using hlabels k hk'

@[simp] theorem cwPos_period (ring : DirectedRing n) (i : Fin n) :
    cwPos ring i n = i := by
  apply Fin.ext
  unfold cwPos
  dsimp only
  simp [Nat.mod_eq_of_lt i.isLt]

/-- Clockwise successor is injective on every nonempty directed ring. -/
theorem rightNeighbor_injective (ring : DirectedRing n) :
    Function.Injective ring.rightNeighbor := by
  intro a b hab
  apply Fin.ext
  have hv := congrArg Fin.val hab
  unfold DirectedRing.rightNeighbor at hv
  dsimp only at hv
  by_cases ha : a.val + 1 < n
  · rw [Nat.mod_eq_of_lt ha] at hv
    by_cases hb : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb] at hv
      omega
    · have hbeq : b.val + 1 = n := by omega
      rw [hbeq, Nat.mod_self] at hv
      omega
  · have haeq : a.val + 1 = n := by omega
    rw [haeq, Nat.mod_self] at hv
    by_cases hb : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb] at hv
      omega
    · have hbeq : b.val + 1 = n := by omega
      omega

/-- Starting at the right neighbor and taking `k` steps equals taking `k+1`
steps from the original position. -/
theorem cwPos_rightNeighbor (ring : DirectedRing n) (i : Fin n) (k : Nat) :
    cwPos ring (ring.rightNeighbor i) k = cwPos ring i (k + 1) := by
  apply Fin.ext
  unfold cwPos DirectedRing.rightNeighbor
  dsimp only
  rw [Nat.mod_add_mod]
  congr 1
  omega

@[simp] theorem cwPos_succ (ring : DirectedRing n) (i : Fin n) (k : Nat) :
    cwPos ring i (k + 1) = ring.rightNeighbor (cwPos ring i k) := by
  apply Fin.ext
  unfold cwPos DirectedRing.rightNeighbor
  dsimp only
  rw [mod_succ_eq]
  congr 1

/-- `noFreeBarrier` makes every edge entering a follower label-consecutive. -/
theorem paperSafe_successor_label_of_responder_follower
    (hψ : ψ > 0) (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (hSafe : OutputSafeConfig hψ ring C) (left : Fin n)
    (hr : (C (ring.rightNeighbor left)).leader = false) :
    (C (ring.rightNeighbor left)).label =
      ⟨((C left).label.val + 1) % ψ, Nat.mod_lt _ hψ⟩ := by
  by_cases hbarrier : isBarrier hψ (C left) (C (ring.rightNeighbor left))
  · have hleader := hSafe.no_free_barrier left hbarrier
    change (C (ring.rightNeighbor left)).leader = true at hleader
    rw [hr] at hleader
    simp at hleader
  · exact Decidable.not_not.mp hbarrier

/-- If an adjacent responder occurs at a noninitial offset of a clockwise
interval, its initiator occurs at the preceding offset. -/
theorem interval_predecessor
    (ring : DirectedRing n) (start left : Fin n) (k : Nat)
    (hpos : cwPos ring start k = ring.rightNeighbor left)
    (hne : start ≠ ring.rightNeighbor left) :
    ∃ k0 : Nat, k = k0 + 1 ∧ cwPos ring start k0 = left := by
  cases k with
  | zero =>
      rw [cwPos_zero] at hpos
      exact (hne hpos).elim
  | succ k =>
      refine ⟨k, rfl, ?_⟩
      apply rightNeighbor_injective ring
      rw [← cwPos_succ]
      exact hpos

/-- A live bullet colocated with a shielded leader is peaceful at distance zero
when the outgoing label edge is consecutive. -/
theorem peacefulBullet_zero
    (hψ : ψ > 0) (ring : DirectedRing n) (C : Fin n → AgentState ψ)
    (i : Fin n)
    (hbullet : (C i).bullet = ⟨2, by omega⟩)
    (hleader : (C i).isLeader)
    (hshield : (C i).shield = true)
    (hsignal : (C i).signal_B = ⟨0, by omega⟩)
    (hlabel : (C (ring.rightNeighbor i)).label =
      ⟨((C i).label.val + 1) % ψ, Nat.mod_lt _ hψ⟩) :
    isPeacefulBullet hψ ring C i := by
  refine ⟨hbullet, 0, ring.hn, ?_, ?_, ?_, ?_⟩
  · change (C (cwPos ring i 0)).isLeader
    rw [cwPos_zero]
    exact hleader
  · change (C (cwPos ring i 0)).shield = true
    rw [cwPos_zero]
    exact hshield
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    change (C (cwPos ring i 0)).signal_B = ⟨0, by omega⟩
    rw [cwPos_zero]
    exact hsignal
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    change (C (cwPos ring i 1)).label =
      ⟨((C (cwPos ring i 0)).label.val + 1) % ψ,
        Nat.mod_lt _ hψ⟩
    rw [cwPos_succ, cwPos_zero]
    exact hlabel

/-- A peaceful live bullet moved one edge left cannot already have used the
full `n-1` distance: that would make the new host its old leader target. -/
theorem peaceful_move_distance_succ_lt
    (ring : DirectedRing n)
    (C : Fin n → AgentState ψ) (left : Fin n) (d : Nat)
    (hd : d < n)
    (htarget : (C (cwPos ring (ring.rightNeighbor left) d)).isLeader)
    (hleftFollower : (C left).leader = false) : d + 1 < n := by
  by_cases hlt : d + 1 < n
  · exact hlt
  · have hdEq : d + 1 = n := by omega
    have hpos := cwPos_rightNeighbor ring left d
    rw [hdEq, cwPos_period] at hpos
    have hleader : (C left).leader = true := by
      change (C left).isLeader = true
      rw [← hpos]
      exact htarget
    rw [hleftFollower] at hleader
    simp at hleader

/-- The existing peacefulness witness extends by one when its live bullet moves
from a responder to the responder's left neighbor.  All hypotheses concern the
current output fields; no historical provenance is used. -/
theorem peacefulBullet_of_move_left_fields
    (hψ : ψ > 0) (ring : DirectedRing n)
    (C C' : Fin n → AgentState ψ) (left : Fin n) (d : Nat)
    (hd : d < n)
    (holdTarget : (C (cwPos ring (ring.rightNeighbor left) d)).isLeader)
    (hleftFollower : (C left).leader = false)
    (hnewBullet : (C' left).bullet = ⟨2, by omega⟩)
    (hnewTarget :
      (C' (cwPos ring (ring.rightNeighbor left) d)).isLeader)
    (hnewShield :
      (C' (cwPos ring (ring.rightNeighbor left) d)).shield = true)
    (hleftSignal : (C' left).signal_B = ⟨0, by omega⟩)
    (holdSignals : ∀ k : Nat, k ≤ d →
      (C' (cwPos ring (ring.rightNeighbor left) k)).signal_B =
        ⟨0, by omega⟩)
    (hnewEdge : (C' (ring.rightNeighbor left)).label =
      ⟨((C' left).label.val + 1) % ψ, Nat.mod_lt _ hψ⟩)
    (holdLabels : ∀ k : Nat, k ≤ d →
      (C' (cwPos ring (ring.rightNeighbor left) (k + 1))).label =
        ⟨((C' (cwPos ring (ring.rightNeighbor left) k)).label.val + 1) % ψ,
          Nat.mod_lt _ hψ⟩) :
    isPeacefulBullet hψ ring C' left := by
  have hlt := peaceful_move_distance_succ_lt
    ring C left d hd holdTarget hleftFollower
  refine ⟨hnewBullet, d + 1, hlt, ?_, ?_, ?_, ?_⟩
  · change (C' (cwPos ring left (d + 1))).isLeader
    rw [← cwPos_rightNeighbor]
    exact hnewTarget
  · change (C' (cwPos ring left (d + 1))).shield = true
    rw [← cwPos_rightNeighbor]
    exact hnewShield
  · intro k hk
    change (C' (cwPos ring left k)).signal_B = ⟨0, by omega⟩
    cases k with
    | zero => simpa using hleftSignal
    | succ k =>
        rw [← cwPos_rightNeighbor]
        apply holdSignals
        omega
  · intro k hk
    change (C' (cwPos ring left (k + 1))).label =
      ⟨((C' (cwPos ring left k)).label.val + 1) % ψ,
        Nat.mod_lt _ hψ⟩
    cases k with
    | zero =>
        simpa using hnewEdge
    | succ k =>
        have hcur := cwPos_rightNeighbor ring left k
        have hnext := cwPos_rightNeighbor ring left (k + 1)
        rw [← hnext, ← hcur]
        apply holdLabels
        omega

end PPLLNoCheckBirthConditionTwoGeometry
