import Leader.Wu.Protocol.State

/-!
# Sub-protocol P'_ψ: Barrier and Probe Mechanism

Algorithm 2 (p.15): the modified SSLE sub-protocol from [7] that creates leaders
via barriers and probes on the directed ring.
-/

/-- An edge (u, v) is a barrier if v.label ≠ (u.label + 1) mod ψ. -/
def isBarrier {ψ : Nat} (hψ : ψ > 0) (u v : AgentState ψ) : Prop :=
  v.label ≠ ⟨(u.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩

/-- A barrier is free if the right agent is not a leader. -/
def isFreeBarrier {ψ : Nat} (hψ : ψ > 0) (u v : AgentState ψ) : Prop :=
  isBarrier hψ u v ∧ ¬v.isLeader

/-- Apply sub-protocol P'_ψ transition (Algorithm 2). -/
def transitionPpsi {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let isBarrierEdge := r.label ≠ ⟨(l.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
  if isBarrierEdge then
    let (l', r') :=
      if r.probe then
        (l, { r with leader := true, label := ⟨0, by omega⟩, probe := false })
      else (l, r)
    let (l'', r'') :=
      if l'.phase = false then
        let l2 := { l' with phase := true }
        if ¬l2.isLeader then ({ l2 with probe := true }, r')
        else (l2, r')
      else (l', r')
    if ¬r''.isLeader then
      (l'', { r'' with
        label := ⟨(l''.label.val + 1) % ψ, Nat.mod_lt _ hψ⟩
        phase := false })
    else (l'', r'')
  else
    if r.probe then
      ({ l with probe := true }, { r with probe := false })
    else (l, r)

/-! ## Barrier existence via pigeonhole -/

/-- If (a + n) % ψ = a and a < ψ, then ψ divides n. -/
private theorem dvd_of_add_mod_eq (a n ψ : Nat) (hψ : ψ > 0) (ha : a < ψ)
    (h : (a + n) % ψ = a) : ψ ∣ n := by
  suffices n % ψ = 0 by exact Nat.dvd_of_mod_eq_zero this
  have h2 := Nat.add_mod a n ψ; rw [h, Nat.mod_eq_of_lt ha] at h2
  have h3 : n % ψ < ψ := Nat.mod_lt _ hψ
  by_cases hcase : a + n % ψ < ψ
  · rw [Nat.mod_eq_of_lt hcase] at h2; omega
  · have hge : ψ ≤ a + n % ψ := by omega
    have hsub : a + n % ψ - ψ < ψ := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsub] at h2; omega

/-- If all edges have consecutive labels, then ψ divides n. -/
private theorem all_consecutive_implies_dvd {n ψ : Nat} (hn : n > 0) (hψ : ψ > 0)
    (C : Fin n → AgentState ψ) (ring : DirectedRing n)
    (hall : ∀ i : Fin n, (C (ring.rightNeighbor i)).label =
      ⟨(((C i).label.val + 1) % ψ), Nat.mod_lt _ hψ⟩) :
    ψ ∣ n := by
  let g : Nat → Nat := fun k => (C ⟨k % n, Nat.mod_lt _ hn⟩).label.val
  have hg_step : ∀ k, g (k + 1) = (g k + 1) % ψ := by
    intro k
    show (C ⟨(k + 1) % n, _⟩).label.val = ((C ⟨k % n, _⟩).label.val + 1) % ψ
    have h := hall ⟨k % n, Nat.mod_lt _ hn⟩
    simp [DirectedRing.rightNeighbor] at h
    exact congrArg Fin.val h
  have hg_ind : ∀ k, g k = (g 0 + k) % ψ := by
    intro k; induction k with
    | zero =>
      show (C ⟨0, hn⟩).label.val = (C ⟨0, hn⟩).label.val % ψ
      exact (Nat.mod_eq_of_lt (C ⟨0, hn⟩).label.isLt).symm
    | succ k ih =>
      rw [hg_step, ih, Nat.add_mod ((g 0 + k) % ψ) 1 ψ, Nat.mod_mod,
          ← Nat.add_mod (g 0 + k) 1 ψ]
      congr 1
  have hg_n : g n = g 0 := by
    show (C ⟨n % n, _⟩).label.val = (C ⟨0 % n, _⟩).label.val
    simp [Nat.mod_self]
  have hg_n' := hg_ind n
  rw [hg_n] at hg_n'
  exact dvd_of_add_mod_eq _ _ _ hψ (C ⟨0, hn⟩).label.isLt hg_n'.symm

/-- If n is not a multiple of ψ, there exists at least one barrier on the ring. -/
theorem barrier_exists_of_not_dvd {n ψ : Nat} (hn : n > 0) (hψ : ψ > 0)
    (hndvd : ¬(ψ ∣ n)) (C : Fin n → AgentState ψ)
    (ring : DirectedRing n) :
    ∃ i : Fin n, (C (ring.rightNeighbor i)).label ≠
      ⟨(((C i).label.val + 1) % ψ), Nat.mod_lt _ hψ⟩ := by
  have hcontra : ¬(∀ i : Fin n, (C (ring.rightNeighbor i)).label =
      ⟨(((C i).label.val + 1) % ψ), Nat.mod_lt _ hψ⟩) :=
    fun hall => hndvd (all_consecutive_implies_dvd hn hψ C ring hall)
  exact Classical.not_forall.mp hcontra
