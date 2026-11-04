import Leader.Wu.Safety.SafeConfig

set_option autoImplicit false

namespace B9ClearLeaderRuler

variable {n psi : Nat}

/-- Clear exactly the leader bit at `v`; every other field at every site is
unchanged. -/
def clearLeaderAt
    (C : Fin n -> AgentState psi) (v : Fin n) : Fin n -> AgentState psi :=
  fun i => if i = v then { C i with leader := false } else C i

/-- Clearing a leader bit does not change any label. -/
@[simp] theorem clearLeaderAt_label
    (C : Fin n -> AgentState psi) (v i : Fin n) :
    (clearLeaderAt C v i).label = (C i).label := by
  unfold clearLeaderAt
  split <;> rfl

/-- If `noFreeBarrier` holds now and still holds after clearing any current
leader, then every directed edge already carries the cyclic successor label. -/
theorem deletionRobustNoFreeBarrier_all_successor_labels
    (hpsi : 0 < psi) (_hn : 2 <= n)
    (ring : DirectedRing n)
    (C : Fin n -> AgentState psi)
    (hfree : noFreeBarrier hpsi ring C)
    (hclear : forall v : Fin n,
      (C v).isLeader = true ->
        noFreeBarrier hpsi ring (clearLeaderAt C v)) :
    forall i : Fin n,
      (C (ring.rightNeighbor i)).label =
        ⟨((C i).label.val + 1) % psi, Nat.mod_lt _ hpsi⟩ := by
  intro i
  cases hright : (C (ring.rightNeighbor i)).isLeader with
  | false =>
      apply Classical.byContradiction
      intro hbar
      have hleader := hfree i hbar
      simpa [hright] using hleader
  | true =>
      have hfreeClear :
          noFreeBarrier hpsi ring
            (clearLeaderAt C (ring.rightNeighbor i)) :=
        hclear (ring.rightNeighbor i) hright
      apply Classical.byContradiction
      intro hbar
      have hbarClear :
          isBarrier hpsi
            (clearLeaderAt C (ring.rightNeighbor i) i)
            (clearLeaderAt C (ring.rightNeighbor i)
              (ring.rightNeighbor i)) := by
        unfold isBarrier
        simpa only [clearLeaderAt_label] using hbar
      have hleaderClear := hfreeClear i hbarClear
      simpa [clearLeaderAt, AgentState.isLeader] using hleaderClear

/-- Going once around a finite ring with successor labels on every edge forces
the label modulus to divide the ring size. -/
theorem all_successor_labels_dvd
    (hpsi : 0 < psi) (_hn : 2 <= n)
    (ring : DirectedRing n)
    (C : Fin n -> AgentState psi)
    (hall : forall i : Fin n,
      (C (ring.rightNeighbor i)).label =
        ⟨((C i).label.val + 1) % psi, Nat.mod_lt _ hpsi⟩) :
    psi ∣ n := by
  exact dvd_of_all_successor_labels hpsi ring C hall

/-- In the nondivisible branch there is no configuration containing a leader
for which `noFreeBarrier` survives clearing every current leader while labels
are held fixed. -/
theorem not_dvd_no_leader_deletionRobustNoFreeBarrier
    (hpsi : 0 < psi) (hn : 2 <= n)
    (ring : DirectedRing n)
    (hndvd : ¬ (psi ∣ n)) :
    ¬ exists C : Fin n -> AgentState psi,
      (exists v : Fin n, (C v).isLeader = true) ∧
      noFreeBarrier hpsi ring C ∧
      (forall v : Fin n,
        (C v).isLeader = true ->
          noFreeBarrier hpsi ring (clearLeaderAt C v)) := by
  rintro ⟨C, _hleader, hfree, hclear⟩
  have hall :=
    deletionRobustNoFreeBarrier_all_successor_labels
      hpsi hn ring C hfree hclear
  exact hndvd (all_successor_labels_dvd hpsi hn ring C hall)

end B9ClearLeaderRuler

#print axioms B9ClearLeaderRuler.clearLeaderAt_label
#print axioms B9ClearLeaderRuler.deletionRobustNoFreeBarrier_all_successor_labels
#print axioms B9ClearLeaderRuler.all_successor_labels_dvd
#print axioms B9ClearLeaderRuler.not_dvd_no_leader_deletionRobustNoFreeBarrier
