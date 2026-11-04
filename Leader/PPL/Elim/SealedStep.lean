import Leader.PPL.Elim.TwoLeaderSealedProduct
import Leader.PPL.Elim.CleanReadySweep


namespace PPL.Convergence.LDLocal


set_option autoImplicit false
set_option Elab.async false


private theorem sector_one_lt_n
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) :
    1 < n := by
  have hp := A.gap_pos
  have hn := A.gap_lt_n
  omega


private theorem rightNeighbor_ne_self_local
    {n : Nat} (ring : DirectedRing n)
    (hn : 1 < n) (e : Fin n) :
    ring.rightNeighbor e ≠ e := by
  intro h
  have hv := congrArg Fin.val h
  unfold DirectedRing.rightNeighbor at hv
  dsimp only at hv
  by_cases he : e.val + 1 < n
  · rw [Nat.mod_eq_of_lt he] at hv
    omega
  · have heq : e.val + 1 = n := by omega
    rw [heq, Nat.mod_self] at hv
    omega


private theorem advance_injective_below
    {n : Nat} (ring : DirectedRing n) (i : Fin n)
    {a b : Nat} (ha : a < n) (hb : b < n)
    (h : advance ring i a = advance ring i b) :
    a = b := by
  have hv := congrArg Fin.val h
  unfold advance at hv
  dsimp only at hv
  by_cases hia : i.val + a < n
  · rw [Nat.mod_eq_of_lt hia] at hv
    by_cases hib : i.val + b < n
    · rw [Nat.mod_eq_of_lt hib] at hv
      omega
    · have hge : n ≤ i.val + b := by omega
      have hlt : i.val + b - n < n := by omega
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt] at hv
      omega
  · have hgea : n ≤ i.val + a := by omega
    have hlta : i.val + a - n < n := by omega
    rw [Nat.mod_eq_sub_mod hgea, Nat.mod_eq_of_lt hlta] at hv
    by_cases hib : i.val + b < n
    · rw [Nat.mod_eq_of_lt hib] at hv
      omega
    · have hgeb : n ≤ i.val + b := by omega
      have hltb : i.val + b - n < n := by omega
      rw [Nat.mod_eq_sub_mod hgeb, Nat.mod_eq_of_lt hltb] at hv
      omega


private theorem incoming_responds
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) :
    ring.rightNeighbor (sealedIncomingEdge A) = A.left := by
  exact rightNeighbor_leftNeighbor_twoLeader ring A.left


private theorem body_pos_ne_left
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (q : Nat)
    (hq0 : 0 < q) (hq : q < A.gap) :
    advance ring A.left q ≠ A.left := by
  intro h
  have h0 : advance ring A.left 0 = A.left := by
    simp
  have heq : advance ring A.left q = advance ring A.left 0 := by
    exact h.trans h0.symm
  have hqi : q < n := Nat.lt_trans hq A.gap_lt_n
  have h0i : 0 < n := by
    have hg := A.gap_pos
    have hn := A.gap_lt_n
    omega
  have := advance_injective_below ring A.left hqi h0i heq
  omega


private theorem body_pos_ne_incoming
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (q : Nat)
    (hq : q < A.gap) :
    advance ring A.left q ≠ sealedIncomingEdge A := by
  intro h
  have hr := congrArg ring.rightNeighbor h
  rw [incoming_responds A, advance_succ_twoLeader] at hr
  by_cases hnext : q + 1 < A.gap
  · have hqi : q + 1 < n :=
      Nat.lt_trans hnext A.gap_lt_n
    have h0i : 0 < n := by
      have hg := A.gap_pos
      have hn := A.gap_lt_n
      omega
    have h0 : advance ring A.left 0 = A.left := by
      simp
    have heq :
        advance ring A.left (q + 1) =
          advance ring A.left 0 := by
      exact hr.trans h0.symm
    have := advance_injective_below ring A.left hqi h0i heq
    omega
  · have hlast : q + 1 = A.gap := by omega
    rw [hlast, A.right_eq] at hr
    exact A.left_ne_right hr.symm


private theorem edge_eq_predecessor
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (q : Nat) (e : Fin n)
    (hq0 : 0 < q) (hq : q < A.gap)
    (hresp :
      advance ring A.left q = ring.rightNeighbor e) :
    e = advance ring A.left (q - 1) := by
  apply rightNeighbor_injective_twoLeader ring
  calc
    ring.rightNeighbor e =
        advance ring A.left q := hresp.symm
    _ = advance ring A.left ((q - 1) + 1) := by
      congr 2
      omega
    _ = ring.rightNeighbor
          (advance ring A.left (q - 1)) := by
      exact
        (advance_succ_twoLeader ring A.left (q - 1)).symm


private theorem stepE_initiator
    {n : Nat} (ring : DirectedRing n)
    (C : Config n) (e : Fin n) :
    stepE ring C e e =
      (PPL.Elim.rowE (C e) (C (ring.rightNeighbor e))).1 := by
  simp [stepE, PopulationProtocol.step, PPL.Elim.protocolE]


private theorem stepE_responder
    {n : Nat} (ring : DirectedRing n)
    (C : Config n) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    stepE ring C e (ring.rightNeighbor e) =
      (PPL.Elim.rowE (C e) (C (ring.rightNeighbor e))).2 := by
  simp [stepE, PopulationProtocol.step, PPL.Elim.protocolE,
    hne, Ne.symm hne]


private theorem stepE_other
    {n : Nat} (ring : DirectedRing n)
    (C : Config n) (e k : Fin n)
    (hke : k ≠ e)
    (hkr : k ≠ ring.rightNeighbor e) :
    stepE ring C e k = C k := by
  simp [stepE, PopulationProtocol.step, PPL.Elim.protocolE,
    hke, hkr]


private theorem body_step_eq_of_service_other
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    (a q : Nat) (ha : a < A.gap) (hq : q < A.gap)
    (hqa : q ≠ a) (hqs : q ≠ a + 1) :
    stepE ring C (advance ring A.left a)
        (advance ring A.left q) =
      C (advance ring A.left q) := by
  apply stepE_other
  · intro h
    have heq := advance_injective_below ring A.left
      (Nat.lt_trans hq A.gap_lt_n)
      (Nat.lt_trans ha A.gap_lt_n) h
    exact hqa heq
  · rw [advance_succ_twoLeader]
    intro h
    have ha1 : a + 1 < n := by
      have hn := A.gap_lt_n
      omega
    have heq := advance_injective_below ring A.left
      (Nat.lt_trans hq A.gap_lt_n) ha1 h
    exact hqs heq


private theorem body_step_eq_of_source_other
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    (q : Nat) (hq : q < A.gap)
    (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    stepE ring C A.left (advance ring A.left q) =
      C (advance ring A.left q) := by
  have hq1' : q ≠ 0 + 1 := by
    simpa using hq1
  simpa using
    body_step_eq_of_service_other A C 0 q
      A.gap_pos hq hq0 hq1'


private theorem incoming_body_step_eq
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    (q : Nat) (hq0 : 0 < q) (hq : q < A.gap) :
    stepE ring C (sealedIncomingEdge A)
        (advance ring A.left q) =
      C (advance ring A.left q) := by
  apply stepE_other
  · exact body_pos_ne_incoming A q hq
  · rw [incoming_responds A]
    exact body_pos_ne_left A q hq0 hq


private theorem source_step_eq_other
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    (e : Fin n)
    (hle : e ≠ A.left)
    (hin : e ≠ sealedIncomingEdge A) :
    stepE ring C e A.left = C A.left := by
  apply stepE_other
  · exact Ne.symm hle
  · intro h
    apply hin
    apply rightNeighbor_injective_twoLeader ring
    calc
      ring.rightNeighbor e = A.left := h.symm
      _ = ring.rightNeighbor (sealedIncomingEdge A) :=
        (incoming_responds A).symm


private theorem left_alive_of_not_deleted
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    (h : ¬ EndpointDeleted A C) :
    (C A.left).leader = true := by
  cases hc : (C A.left).leader with
  | false =>
      exact (h (.inl hc)).elim
  | true =>
      rfl


private theorem right_alive_of_not_deleted
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    (h : ¬ EndpointDeleted A C) :
    (C A.right).leader = true := by
  cases hc : (C A.right).leader with
  | false =>
      exact (h (.inr hc)).elim
  | true =>
      rfl


private theorem interiorFollowers_step
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n) (e : Fin n)
    (h : SectorInteriorFollowers A C) :
    SectorInteriorFollowers A (stepE ring C e) := by
  intro q hq0 hq
  exact
    stepE_leader_false_of_false ring C e
      (advance ring A.left q) (h q hq0 hq)


private theorem fin3_cases_local (x : Fin 3) :
    x = (0 : Fin 3) ∨
      x = (1 : Fin 3) ∨
        x = (2 : Fin 3) := by
  have hx := x.isLt
  have hv :
      x.val = 0 ∨ x.val = 1 ∨ x.val = 2 := by
    omega
  rcases hv with h0 | h1 | h2
  · left
    apply Fin.ext
    simpa using h0
  · right
    left
    apply Fin.ext
    simpa using h1
  · right
    right
    apply Fin.ext
    simpa using h2


private theorem rowE_right_signal_false
    (l r : PPL.Elim.Cell4)
    (hrs : r.signalB = false) :
    (PPL.Elim.rowE l r).2.signalB = false := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_local lb with h | h | h <;> subst lb <;>
  rcases fin3_cases_local rb with h | h | h <;> subst rb <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]


private theorem rowE_right_shield_of_signal_false
    (l r : PPL.Elim.Cell4)
    (hrs : r.signalB = false) :
    (PPL.Elim.rowE l r).2.shield = r.shield := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_local lb with h | h | h <;> subst lb <;>
  rcases fin3_cases_local rb with h | h | h <;> subst rb <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]


private theorem rowE_right_bullet_of_leader_signal_false
    (l r : PPL.Elim.Cell4)
    (hrl : r.leader = true)
    (hrs : r.signalB = false) :
    (PPL.Elim.rowE l r).2.bullet = r.bullet := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_local lb with h | h | h <;> subst lb <;>
  rcases fin3_cases_local rb with h | h | h <;> subst rb <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]


private theorem rowE_left_shield_of_signal_false
    (l r : PPL.Elim.Cell4)
    (hls : l.signalB = false) :
    (PPL.Elim.rowE l r).1.shield = l.shield := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_local lb with h | h | h <;> subst lb <;>
  rcases fin3_cases_local rb with h | h | h <;> subst rb <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]


private theorem rowE_left_bullet_zero_of_quiet
    (l r : PPL.Elim.Cell4)
    (hlb : l.bullet = (0 : Fin 3))
    (hquiet : l.leader = false ∨ l.signalB = false) :
    (PPL.Elim.rowE l r).1.bullet = (0 : Fin 3) := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_local lb with h | h | h <;> subst lb <;>
  rcases fin3_cases_local rb with h | h | h <;> subst rb <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]


private theorem rowE_right_bullet_of_left_quiet
    (l r : PPL.Elim.Cell4)
    (hlb : l.bullet = (0 : Fin 3))
    (hquiet : l.leader = false ∨ l.signalB = false)
    (hrl : r.leader = false) :
    (PPL.Elim.rowE l r).2.bullet = r.bullet := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_local lb with h | h | h <;> subst lb <;>
  rcases fin3_cases_local rb with h | h | h <;> subst rb <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]


private theorem rowE_left_signal_false_of_quiet_pair
    (l r : PPL.Elim.Cell4)
    (hls : l.signalB = false)
    (hrs : r.signalB = false)
    (hrl : r.leader = false) :
    (PPL.Elim.rowE l r).1.signalB = false := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_local lb with h | h | h <;> subst lb <;>
  rcases fin3_cases_local rb with h | h | h <;> subst rb <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]


private theorem rowE_left_signal_true_of_follower
    (l r : PPL.Elim.Cell4)
    (hll : l.leader = false)
    (hls : l.signalB = true) :
    (PPL.Elim.rowE l r).1.signalB = true := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_local lb with h | h | h <;> subst lb <;>
  rcases fin3_cases_local rb with h | h | h <;> subst rb <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]


private theorem rowE_move_follower
    (l r : PPL.Elim.Cell4)
    (hls : l.signalB = false)
    (hlb : l.bullet ≠ (0 : Fin 3))
    (hrl : r.leader = false)
    (hrb : r.bullet = (0 : Fin 3)) :
    (PPL.Elim.rowE l r).1.bullet = (0 : Fin 3) ∧
      (PPL.Elim.rowE l r).1.signalB = false ∧
      (PPL.Elim.rowE l r).1.shield = l.shield ∧
      (PPL.Elim.rowE l r).2.bullet = l.bullet ∧
      (PPL.Elim.rowE l r).2.signalB = false := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_local lb with h | h | h <;> subst lb <;>
  rcases fin3_cases_local rb with h | h | h <;> subst rb <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]


private theorem rowE_hit_survive
    (l r : PPL.Elim.Cell4)
    (hls : l.signalB = false)
    (hlb : l.bullet ≠ (0 : Fin 3))
    (hrl : r.leader = true)
    (hout : (PPL.Elim.rowE l r).2.leader = true) :
    (PPL.Elim.rowE l r).1.bullet = (0 : Fin 3) ∧
      (PPL.Elim.rowE l r).1.signalB = true := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_local lb with h | h | h <;> subst lb <;>
  rcases fin3_cases_local rb with h | h | h <;> subst rb <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]


private theorem rowE_ready_incoming_survive
    (l r : PPL.Elim.Cell4)
    (hrl : r.leader = true)
    (hrs : r.signalB = true)
    (hout : (PPL.Elim.rowE l r).2.leader = true) :
    (PPL.Elim.rowE l r).2.bullet = (1 : Fin 3) ∧
      (PPL.Elim.rowE l r).2.shield = false ∧
      (PPL.Elim.rowE l r).2.signalB = false := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_local lb with h | h | h <;> subst lb <;>
  rcases fin3_cases_local rb with h | h | h <;> subst rb <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]


private theorem rowE_ready_outgoing_follower
    (l r : PPL.Elim.Cell4)
    (hll : l.leader = true)
    (hls : l.signalB = true)
    (hlb : l.bullet = (0 : Fin 3))
    (hrl : r.leader = false)
    (hrb : r.bullet = (0 : Fin 3)) :
    (PPL.Elim.rowE l r).1.bullet = (0 : Fin 3) ∧
      (PPL.Elim.rowE l r).1.shield = true ∧
      (PPL.Elim.rowE l r).1.signalB = false ∧
      (PPL.Elim.rowE l r).2.bullet = (2 : Fin 3) ∧
      (PPL.Elim.rowE l r).2.signalB = false := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_local lb with h | h | h <;> subst lb <;>
  rcases fin3_cases_local rb with h | h | h <;> subst rb <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]


private theorem rowE_ready_outgoing_survive
    (l r : PPL.Elim.Cell4)
    (hll : l.leader = true)
    (hls : l.signalB = true)
    (hlb : l.bullet = (0 : Fin 3))
    (hrl : r.leader = true)
    (hout : (PPL.Elim.rowE l r).2.leader = true) :
    (PPL.Elim.rowE l r).1.bullet = (0 : Fin 3) ∧
      (PPL.Elim.rowE l r).1.signalB = true := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_local lb with h | h | h <;> subst lb <;>
  rcases fin3_cases_local rb with h | h | h <;> subst rb <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]


private theorem rowE_return_service
    (l r : PPL.Elim.Cell4)
    (hls : l.signalB = false)
    (hlb : l.bullet = (0 : Fin 3))
    (hrl : r.leader = false)
    (hrb : r.bullet = (0 : Fin 3))
    (hrs : r.signalB = true) :
    (PPL.Elim.rowE l r).1.bullet = (0 : Fin 3) ∧
      (PPL.Elim.rowE l r).1.signalB = true ∧
      (PPL.Elim.rowE l r).2.bullet = (0 : Fin 3) ∧
      (PPL.Elim.rowE l r).2.signalB = true := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_local lb with h | h | h <;> subst lb <;>
  rcases fin3_cases_local rb with h | h | h <;> subst rb <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]


private theorem sourceShield_quiet_step
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n) (e : Fin n)
    (hs : (C A.left).signalB = false) :
    (stepE ring C e A.left).shield = (C A.left).shield := by
  by_cases he : A.left = e
  · rw [he, stepE_initiator]
    exact rowE_left_shield_of_signal_false _ _
      (by simpa [he] using hs)
  · by_cases hr : A.left = ring.rightNeighbor e
    · rw [hr, stepE_responder ring C e
        (rightNeighbor_ne_self_local ring
          (sector_one_lt_n A) e)]
      exact rowE_right_shield_of_signal_false _ _
        (by simpa [hr] using hs)
    · rw [stepE_other ring C e A.left he hr]


private theorem sectorBulletFree_quiet_step
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n) (e : Fin n)
    (hleft : (C A.left).leader = true)
    (hint : SectorInteriorFollowers A C)
    (hfree : SectorBulletFree A C)
    (hs0 : (C A.left).signalB = false) :
    SectorBulletFree A (stepE ring C e) := by
  intro q hq
  have hbq := hfree q hq
  by_cases hqe : advance ring A.left q = e
  · have hquiet :
        (C e).leader = false ∨ (C e).signalB = false := by
      by_cases hq0 : q = 0
      · subst q
        exact .inr (by
          rw [← hqe, advance_zero]
          exact hs0)
      · exact .inl (by
          rw [← hqe]
          exact hint q (by omega) hq)
    rw [hqe, stepE_initiator]
    exact rowE_left_bullet_zero_of_quiet _ _
      (by simpa [← hqe] using hbq) hquiet
  · by_cases hqr :
      advance ring A.left q = ring.rightNeighbor e
    · rw [hqr, stepE_responder ring C e
        (rightNeighbor_ne_self_local ring
          (sector_one_lt_n A) e)]
      by_cases hq0 : q = 0
      · subst q
        have hrl :
            (C (ring.rightNeighbor e)).leader = true := by
          rw [← hqr, advance_zero]
          exact hleft
        have hrs :
            (C (ring.rightNeighbor e)).signalB = false := by
          rw [← hqr, advance_zero]
          exact hs0
        rw [rowE_right_bullet_of_leader_signal_false _ _
          hrl hrs]
        simpa [← hqr] using hbq
      · have hepred :=
          edge_eq_predecessor A q e (by omega) hq hqr
        have hpl : q - 1 < A.gap := by omega
        have hlb : (C e).bullet = (0 : Fin 3) := by
          rw [hepred]
          exact hfree (q - 1) hpl
        have hlq :
            (C e).leader = false ∨
              (C e).signalB = false := by
          by_cases hq1 : q = 1
          · right
            rw [hepred, hq1]
            simp
            exact hs0
          · left
            rw [hepred]
            exact hint (q - 1) (by omega) hpl
        have hrl :
            (C (ring.rightNeighbor e)).leader = false := by
          rw [← hqr]
          exact hint q (by omega) hq
        rw [rowE_right_bullet_of_left_quiet _ _
          hlb hlq hrl]
        simpa [← hqr] using hbq
    · rw [stepE_other ring C e
        (advance ring A.left q) hqe hqr]
      exact hbq


private theorem ready_bulletFree_other
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n) (e : Fin n)
    (hint : SectorInteriorFollowers A C)
    (hfree : SectorBulletFree A C)
    (hle : e ≠ A.left)
    (hin : e ≠ sealedIncomingEdge A) :
    SectorBulletFree A (stepE ring C e) := by
  intro q hq
  have hbq := hfree q hq
  by_cases hqe : advance ring A.left q = e
  · have hq0 : 0 < q := by
      have hn0 : q ≠ 0 := by
        intro hz
        subst q
        rw [advance_zero] at hqe
        exact hle hqe.symm
      omega
    have hll : (C e).leader = false := by
      rw [← hqe]
      exact hint q hq0 hq
    rw [hqe, stepE_initiator]
    exact rowE_left_bullet_zero_of_quiet _ _
      (by simpa [← hqe] using hbq) (.inl hll)
  · by_cases hqr :
      advance ring A.left q = ring.rightNeighbor e
    · have hq0 : 0 < q := by
        have hn0 : q ≠ 0 := by
          intro hz
          subst q
          rw [advance_zero] at hqr
          apply hin
          apply rightNeighbor_injective_twoLeader ring
          calc
            ring.rightNeighbor e = A.left := hqr.symm
            _ = ring.rightNeighbor (sealedIncomingEdge A) :=
              (incoming_responds A).symm
        omega
      have hepred :=
        edge_eq_predecessor A q e hq0 hq hqr
      have hq1 : q ≠ 1 := by
        intro hh
        apply hle
        rw [hepred, hh]
        simp
      have hp0 : 0 < q - 1 := by omega
      have hpl : q - 1 < A.gap := by omega
      have hlb : (C e).bullet = (0 : Fin 3) := by
        rw [hepred]
        exact hfree (q - 1) hpl
      have hll : (C e).leader = false := by
        rw [hepred]
        exact hint (q - 1) hp0 hpl
      have hrl :
          (C (ring.rightNeighbor e)).leader = false := by
        rw [← hqr]
        exact hint q hq0 hq
      rw [hqr, stepE_responder ring C e
        (rightNeighbor_ne_self_local ring
          (sector_one_lt_n A) e)]
      rw [rowE_right_bullet_of_left_quiet _ _
        hlb (.inl hll) hrl]
      simpa [← hqr] using hbq
    · rw [stepE_other ring C e
        (advance ring A.left q) hqe hqr]
      exact hbq


private theorem onlyBullet_stutter
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    (p : Nat) (b : Fin 3) (e : Fin n)
    (hleft : (C A.left).leader = true)
    (hint : SectorInteriorFollowers A C)
    (honly : OnlySectorBullet A C p b)
    (hs0 : (C A.left).signalB = false)
    (hne : e ≠ advance ring A.left p) :
    OnlySectorBullet A (stepE ring C e) p b := by
  rcases honly with ⟨hp, hbp, hother⟩
  refine ⟨hp, ?_, ?_⟩
  · by_cases hpr :
      advance ring A.left p = ring.rightNeighbor e
    · rw [hpr, stepE_responder ring C e
        (rightNeighbor_ne_self_local ring
          (sector_one_lt_n A) e)]
      by_cases hp0 : p = 0
      · subst p
        have hrl :
            (C (ring.rightNeighbor e)).leader = true := by
          rw [← hpr, advance_zero]
          exact hleft
        have hrs :
            (C (ring.rightNeighbor e)).signalB = false := by
          rw [← hpr, advance_zero]
          exact hs0
        rw [rowE_right_bullet_of_leader_signal_false _ _
          hrl hrs]
        simpa [← hpr] using hbp
      · have hepred :=
          edge_eq_predecessor A p e (by omega) hp hpr
        have hpl : p - 1 < A.gap := by omega
        have hlb : (C e).bullet = (0 : Fin 3) := by
          rw [hepred]
          exact hother (p - 1) hpl (by omega)
        have hlq :
            (C e).leader = false ∨
              (C e).signalB = false := by
          by_cases hp1 : p = 1
          · right
            rw [hepred, hp1]
            simp
            exact hs0
          · left
            rw [hepred]
            exact hint (p - 1) (by omega) hpl
        have hrl :
            (C (ring.rightNeighbor e)).leader = false := by
          rw [← hpr]
          exact hint p (by omega) hp
        rw [rowE_right_bullet_of_left_quiet _ _
          hlb hlq hrl]
        simpa [← hpr] using hbp
    · have hpe : advance ring A.left p ≠ e := by
        intro h
        exact hne h.symm
      rw [stepE_other ring C e
        (advance ring A.left p) hpe hpr]
      exact hbp
  · intro q hq hqp
    have hbq := hother q hq hqp
    by_cases hqe : advance ring A.left q = e
    · have hquiet :
          (C e).leader = false ∨
            (C e).signalB = false := by
        by_cases hq0 : q = 0
        · subst q
          exact .inr (by
            rw [← hqe, advance_zero]
            exact hs0)
        · exact .inl (by
            rw [← hqe]
            exact hint q (by omega) hq)
      rw [hqe, stepE_initiator]
      exact rowE_left_bullet_zero_of_quiet _ _
        (by simpa [← hqe] using hbq) hquiet
    · by_cases hqr :
        advance ring A.left q = ring.rightNeighbor e
      · rw [hqr, stepE_responder ring C e
          (rightNeighbor_ne_self_local ring
            (sector_one_lt_n A) e)]
        by_cases hq0 : q = 0
        · subst q
          have hrl :
              (C (ring.rightNeighbor e)).leader = true := by
            rw [← hqr, advance_zero]
            exact hleft
          have hrs :
              (C (ring.rightNeighbor e)).signalB = false := by
            rw [← hqr, advance_zero]
            exact hs0
          rw [rowE_right_bullet_of_leader_signal_false _ _
            hrl hrs]
          simpa [← hqr] using hbq
        · have hepred :=
            edge_eq_predecessor A q e (by omega) hq hqr
          have hpl : q - 1 < A.gap := by omega
          have hpred_ne : q - 1 ≠ p := by
            intro hh
            apply hne
            rw [hepred, hh]
          have hlb : (C e).bullet = (0 : Fin 3) := by
            rw [hepred]
            exact hother (q - 1) hpl hpred_ne
          have hlq :
              (C e).leader = false ∨
                (C e).signalB = false := by
            by_cases hq1 : q = 1
            · right
              rw [hepred, hq1]
              simp
              exact hs0
            · left
              rw [hepred]
              exact hint (q - 1) (by omega) hpl
          have hrl :
              (C (ring.rightNeighbor e)).leader = false := by
            rw [← hqr]
            exact hint q (by omega) hq
          rw [rowE_right_bullet_of_left_quiet _ _
            hlb hlq hrl]
          simpa [← hqr] using hbq
      · rw [stepE_other ring C e
          (advance ring A.left q) hqe hqr]
        exact hbq


private theorem zeroThrough_stutter
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    (p : Nat) (e : Fin n)
    (hp : p < A.gap)
    (hint : SectorInteriorFollowers A C)
    (hz : ZeroSignalThrough A C p)
    (hne : e ≠ advance ring A.left p) :
    ZeroSignalThrough A (stepE ring C e) p := by
  intro q hqp
  have hqgap : q < A.gap := by omega
  have hsq := hz q hqp
  by_cases hqe : advance ring A.left q = e
  · have hqne : q ≠ p := by
      intro hh
      subst q
      exact hne hqe.symm
    have hqnext : q + 1 ≤ p := by omega
    have hrn :
        ring.rightNeighbor e =
          advance ring A.left (q + 1) := by
      rw [← hqe]
      exact advance_succ_twoLeader ring A.left q
    have hrs :
        (C (ring.rightNeighbor e)).signalB = false := by
      rw [hrn]
      exact hz (q + 1) hqnext
    have hrl :
        (C (ring.rightNeighbor e)).leader = false := by
      rw [hrn]
      exact hint (q + 1) (by omega) (by omega)
    rw [hqe, stepE_initiator]
    exact rowE_left_signal_false_of_quiet_pair _ _
      (by simpa [← hqe] using hsq) hrs hrl
  · by_cases hqr :
      advance ring A.left q = ring.rightNeighbor e
    · rw [hqr, stepE_responder ring C e
        (rightNeighbor_ne_self_local ring
          (sector_one_lt_n A) e)]
      exact rowE_right_signal_false _ _
        (by simpa [← hqr] using hsq)
    · rw [stepE_other ring C e
        (advance ring A.left q) hqe hqr]
      exact hsq


private theorem zeroBefore_stutter
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    (q : Nat) (e : Fin n)
    (hq0 : 0 < q) (hq : q < A.gap)
    (hint : SectorInteriorFollowers A C)
    (hz : SignalZeroBefore A C q)
    (hne : e ≠ advance ring A.left (q - 1)) :
    SignalZeroBefore A (stepE ring C e) q := by
  intro r hrq
  have hrgap : r < A.gap := by omega
  have hsr := hz r hrq
  by_cases hre : advance ring A.left r = e
  · have hrne : r ≠ q - 1 := by
      intro hh
      exact hne (by rw [← hre, hh])
    have hrnext : r + 1 < q := by omega
    have hrn :
        ring.rightNeighbor e =
          advance ring A.left (r + 1) := by
      rw [← hre]
      exact advance_succ_twoLeader ring A.left r
    have hrs :
        (C (ring.rightNeighbor e)).signalB = false := by
      rw [hrn]
      exact hz (r + 1) hrnext
    have hrl :
        (C (ring.rightNeighbor e)).leader = false := by
      rw [hrn]
      exact hint (r + 1) (by omega) (by omega)
    rw [hre, stepE_initiator]
    exact rowE_left_signal_false_of_quiet_pair _ _
      (by simpa [← hre] using hsr) hrs hrl
  · by_cases hrr :
      advance ring A.left r = ring.rightNeighbor e
    · rw [hrr, stepE_responder ring C e
        (rightNeighbor_ne_self_local ring
          (sector_one_lt_n A) e)]
      exact rowE_right_signal_false _ _
        (by simpa [← hrr] using hsr)
    · rw [stepE_other ring C e
        (advance ring A.left r) hre hrr]
      exact hsr


private theorem signalFront_stutter
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    (q : Nat) (e : Fin n)
    (hq0 : 0 < q) (hq : q < A.gap)
    (hint : SectorInteriorFollowers A C)
    (hfront :
      (C (advance ring A.left q)).signalB = true)
    (hne : e ≠ advance ring A.left (q - 1)) :
    (stepE ring C e
      (advance ring A.left q)).signalB = true := by
  by_cases hqe : advance ring A.left q = e
  · rw [hqe, stepE_initiator]
    exact rowE_left_signal_true_of_follower _ _
      (by
        rw [← hqe]
        exact hint q hq0 hq)
      (by simpa [← hqe] using hfront)
  · by_cases hqr :
      advance ring A.left q = ring.rightNeighbor e
    · have hepred :=
        edge_eq_predecessor A q e hq0 hq hqr
      exact (hne hepred).elim
    · rw [stepE_other ring C e
        (advance ring A.left q) hqe hqr]
      exact hfront


private theorem moving_stutter_fields
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    (p : Nat) (b : Fin 3) (shieldValue : Bool)
    (e : Fin n)
    (hleft : (C A.left).leader = true)
    (hint : SectorInteriorFollowers A C)
    (honly : OnlySectorBullet A C p b)
    (hshield : (C A.left).shield = shieldValue)
    (hz : ZeroSignalThrough A C p)
    (hne : e ≠ advance ring A.left p) :
    OnlySectorBullet A (stepE ring C e) p b ∧
      (stepE ring C e A.left).shield = shieldValue ∧
      ZeroSignalThrough A (stepE ring C e) p := by
  have hp := honly.1
  have hs0 : (C A.left).signalB = false := by
    have hh := hz 0 (Nat.zero_le p)
    simpa using hh
  refine ⟨
    onlyBullet_stutter A C p b e
      hleft hint honly hs0 hne,
    ?_,
    zeroThrough_stutter A C p e hp hint hz hne
  ⟩
  rw [sourceShield_quiet_step A C e hs0, hshield]


private theorem moving_forward_fields
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    (p : Nat) (b : Fin 3) (shieldValue : Bool)
    (hint : SectorInteriorFollowers A C)
    (honly : OnlySectorBullet A C p b)
    (hshield : (C A.left).shield = shieldValue)
    (hz : ZeroSignalThrough A C p)
    (hb0 : b ≠ (0 : Fin 3))
    (hnext : p + 1 < A.gap) :
    let D := stepE ring C (advance ring A.left p)
    OnlySectorBullet A D (p + 1) b ∧
      (D A.left).shield = shieldValue ∧
      ZeroSignalThrough A D (p + 1) := by
  dsimp only
  rcases honly with ⟨hp, hbp, hother⟩
  let e := advance ring A.left p
  have hrn :
      ring.rightNeighbor e =
        advance ring A.left (p + 1) := by
    dsimp [e]
    exact advance_succ_twoLeader ring A.left p
  have hls : (C e).signalB = false := by
    dsimp [e]
    exact hz p (Nat.le_refl p)
  have hlb : (C e).bullet = b := by
    dsimp [e]
    exact hbp
  have hlbnz : (C e).bullet ≠ (0 : Fin 3) := by
    rw [hlb]
    exact hb0
  have hrl :
      (C (ring.rightNeighbor e)).leader = false := by
    rw [hrn]
    exact hint (p + 1) (by omega) hnext
  have hrb :
      (C (ring.rightNeighbor e)).bullet = (0 : Fin 3) := by
    rw [hrn]
    exact hother (p + 1) hnext (by omega)
  have hm :=
    rowE_move_follower
      (C e) (C (ring.rightNeighbor e))
      hls hlbnz hrl hrb
  rcases hm with
    ⟨hmLB, hmLS, hmSh, hmRB, hmRS⟩
  have hleftStep := stepE_initiator ring C e
  have hrightStep :=
    stepE_responder ring C e
      (rightNeighbor_ne_self_local ring
        (sector_one_lt_n A) e)
  rw [hrn] at hrightStep hmRB hmRS
  have hs0 : (C A.left).signalB = false := by
    have hh := hz 0 (Nat.zero_le p)
    simpa using hh
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨hnext, ?_, ?_⟩
    · rw [hrightStep, hmRB, hlb]
    · intro q hq hqne
      by_cases hqp : q = p
      · subst q
        rw [hleftStep, hmLB]
      · have hqs : q ≠ p + 1 := hqne
        rw [body_step_eq_of_service_other
          A C p q hp hq hqp hqs]
        exact hother q hq hqp
  · rw [sourceShield_quiet_step A C e hs0, hshield]
  · intro q hq
    have hqgap : q < A.gap := by omega
    by_cases hqp : q = p
    · subst q
      rw [hleftStep, hmLS]
    · by_cases hqn : q = p + 1
      · subst q
        rw [hrightStep, hmRS]
      · rw [body_step_eq_of_service_other
          A C p q hp hqgap hqp hqn]
        exact hz q (by omega)


private theorem moving_finish_fields
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    (p : Nat) (b : Fin 3)
    (hright : (C A.right).leader = true)
    (honly : OnlySectorBullet A C p b)
    (hz : ZeroSignalThrough A C p)
    (hb0 : b ≠ (0 : Fin 3))
    (hlast : p + 1 = A.gap)
    (hkeep :
      ¬ EndpointDeleted A
        (stepE ring C (advance ring A.left p))) :
    let D := stepE ring C (advance ring A.left p)
    SectorBulletFree A D ∧
      (D (advance ring A.left p)).signalB = true ∧
      ∀ r, r < p →
        (D (advance ring A.left r)).signalB = false := by
  dsimp only
  rcases honly with ⟨hp, hbp, hother⟩
  let e := advance ring A.left p
  have hrn0 :
      ring.rightNeighbor e =
        advance ring A.left (p + 1) := by
    dsimp [e]
    exact advance_succ_twoLeader ring A.left p
  have hrn : ring.rightNeighbor e = A.right := by
    rw [hrn0, hlast, A.right_eq]
  have hls : (C e).signalB = false := by
    dsimp [e]
    exact hz p (Nat.le_refl p)
  have hlb : (C e).bullet = b := by
    dsimp [e]
    exact hbp
  have hlbnz : (C e).bullet ≠ (0 : Fin 3) := by
    rw [hlb]
    exact hb0
  have hrl :
      (C (ring.rightNeighbor e)).leader = true := by
    rw [hrn]
    exact hright
  have hDright :=
    right_alive_of_not_deleted A
      (stepE ring C e) hkeep
  have hrightStep :=
    stepE_responder ring C e
      (rightNeighbor_ne_self_local ring
        (sector_one_lt_n A) e)
  have hout :
      (PPL.Elim.rowE (C e)
        (C (ring.rightNeighbor e))).2.leader = true := by
    rw [← hrightStep, hrn]
    exact hDright
  have hm :=
    rowE_hit_survive
      (C e) (C (ring.rightNeighbor e))
      hls hlbnz hrl hout
  rcases hm with ⟨hmB, hmS⟩
  have hleftStep := stepE_initiator ring C e
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    by_cases hqp : q = p
    · subst q
      rw [hleftStep, hmB]
    · have hqs : q ≠ p + 1 := by
        intro hh
        have : q = A.gap := by omega
        omega
      rw [body_step_eq_of_service_other
        A C p q hp hq hqp hqs]
      exact hother q hq hqp
  · rw [hleftStep, hmS]
  · intro r hrp
    have hrgap : r < A.gap := by omega
    have hrs : r ≠ p + 1 := by omega
    rw [body_step_eq_of_service_other
      A C p r hp hrgap (by omega) hrs]
    exact hz r (by omega)


private theorem return_stutter_fields
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    (q : Nat) (e : Fin n)
    (hleft : (C A.left).leader = true)
    (hint : SectorInteriorFollowers A C)
    (hq0 : 0 < q) (hq : q < A.gap)
    (hfree : SectorBulletFree A C)
    (hs0 : (C A.left).signalB = false)
    (hz : SignalZeroBefore A C q)
    (hfront :
      (C (advance ring A.left q)).signalB = true)
    (hne : e ≠ advance ring A.left (q - 1)) :
    SectorBulletFree A (stepE ring C e) ∧
      (stepE ring C e A.left).signalB = false ∧
      SignalZeroBefore A (stepE ring C e) q ∧
      (stepE ring C e
        (advance ring A.left q)).signalB = true := by
  have hfreeD :=
    sectorBulletFree_quiet_step
      A C e hleft hint hfree hs0
  have hzD :=
    zeroBefore_stutter A C q e
      hq0 hq hint hz hne
  have hfD :=
    signalFront_stutter A C q e
      hq0 hq hint hfront hne
  have hsD :
      (stepE ring C e A.left).signalB = false := by
    have hh := hzD 0 hq0
    simpa using hh
  exact ⟨hfreeD, hsD, hzD, hfD⟩


private theorem return_service_fields
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    (q : Nat)
    (hint : SectorInteriorFollowers A C)
    (hq0 : 0 < q) (hq : q < A.gap)
    (hfree : SectorBulletFree A C)
    (hz : SignalZeroBefore A C q)
    (hfront :
      (C (advance ring A.left q)).signalB = true) :
    let e := advance ring A.left (q - 1)
    let D := stepE ring C e
    SectorBulletFree A D ∧
      (D (advance ring A.left (q - 1))).signalB = true ∧
      SignalZeroBefore A D (q - 1) := by
  dsimp only
  let e := advance ring A.left (q - 1)
  have hp0 : q - 1 < A.gap := by omega
  have hrn :
      ring.rightNeighbor e =
        advance ring A.left q := by
    dsimp [e]
    calc
      ring.rightNeighbor
          (advance ring A.left (q - 1)) =
          advance ring A.left ((q - 1) + 1) :=
        advance_succ_twoLeader ring A.left (q - 1)
      _ = advance ring A.left q := by
        congr 2
        omega
  have hls : (C e).signalB = false := by
    dsimp [e]
    exact hz (q - 1) (by omega)
  have hlb : (C e).bullet = (0 : Fin 3) := by
    dsimp [e]
    exact hfree (q - 1) hp0
  have hrl :
      (C (ring.rightNeighbor e)).leader = false := by
    rw [hrn]
    exact hint q hq0 hq
  have hrb :
      (C (ring.rightNeighbor e)).bullet = (0 : Fin 3) := by
    rw [hrn]
    exact hfree q hq
  have hrs :
      (C (ring.rightNeighbor e)).signalB = true := by
    rw [hrn]
    exact hfront
  have hm :=
    rowE_return_service
      (C e) (C (ring.rightNeighbor e))
      hls hlb hrl hrb hrs
  rcases hm with ⟨hmLB, hmLS, hmRB, hmRS⟩
  have hleftStep := stepE_initiator ring C e
  have hrightStep :=
    stepE_responder ring C e
      (rightNeighbor_ne_self_local ring
        (sector_one_lt_n A) e)
  rw [hrn] at hrightStep hmRB hmRS
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    by_cases hrL : r = q - 1
    · subst r
      rw [hleftStep, hmLB]
    · by_cases hrR : r = q
      · subst r
        rw [hrightStep, hmRB]
      · rw [body_step_eq_of_service_other
          A C (q - 1) r hp0 hr hrL ?_]
        · exact hfree r hr
        · intro hh
          apply hrR
          omega
  · rw [hleftStep, hmLS]
  · intro r hr
    have hrgap : r < A.gap := by omega
    have hrL : r ≠ q - 1 := by omega
    have hrR : r ≠ (q - 1) + 1 := by omega
    rw [body_step_eq_of_service_other
      A C (q - 1) r hp0 hrgap hrL hrR]
    exact hz r (by omega)


theorem sealedStepSpec : SealedStepSpec := by
  intro n ring C0 A C ph hphase halive e
  by_cases hdel : EndpointDeleted A (stepE ring C e)
  · exact .inl hdel
  · have hleft :=
      left_alive_of_not_deleted A C halive
    have hright :=
      right_alive_of_not_deleted A C halive
    have hleftD :=
      left_alive_of_not_deleted A
        (stepE ring C e) hdel
    have hrightD :=
      right_alive_of_not_deleted A
        (stepE ring C e) hdel
    cases ph with
    | ready =>
        rcases hphase with
          ⟨hint, hsig, hfree⟩
        have hintD :=
          interiorFollowers_step A C e hint
        by_cases hin : e = sealedIncomingEdge A
        · subst e
          have hresp :=
            stepE_responder ring C
              (sealedIncomingEdge A)
              (rightNeighbor_ne_self_local ring
                (sector_one_lt_n A)
                (sealedIncomingEdge A))
          rw [incoming_responds A] at hresp
          have hout :
              (PPL.Elim.rowE
                (C (sealedIncomingEdge A))
                (C A.left)).2.leader = true := by
            rw [← hresp]
            exact hleftD
          have hf :=
            rowE_ready_incoming_survive
              (C (sealedIncomingEdge A))
              (C A.left)
              hleft hsig hout
          rcases hf with ⟨hb1, hsh0, hs0⟩
          have hbD :=
            congrArg PPL.Elim.Cell4.bullet hresp
          have hshD :=
            congrArg PPL.Elim.Cell4.shield hresp
          have hsD :=
            congrArg PPL.Elim.Cell4.signalB hresp
          refine .inr ⟨.dummy 0, ?_, ?_⟩
          · refine ⟨hintD, ?_, ?_, ?_⟩
            · refine ⟨A.gap_pos, ?_, ?_⟩
              · have hh := hbD.trans hb1
                simpa [advance_zero] using hh
              · intro q hq hq0
                have hqpos : 0 < q := by omega
                rw [incoming_body_step_eq
                  A C q hqpos hq]
                exact hfree q hq
            · exact hshD.trans hsh0
            · intro q hq
              have hq0 : q = 0 := by omega
              subst q
              have hh := hsD.trans hs0
              simpa [advance_zero] using hh
          · simp [PhaseTransition, nextSectorPhase]
        · by_cases hout : e = A.left
          · subst e
            have hsrcB : (C A.left).bullet = (0 : Fin 3) := by
              simpa using hfree 0 A.gap_pos
            by_cases hgap : A.gap = 1
            · have hrn :
                  ring.rightNeighbor A.left = A.right := by
                calc
                  ring.rightNeighbor A.left =
                      advance ring A.left (0 + 1) := by
                    simpa using
                      advance_succ_twoLeader
                        ring A.left 0
                  _ = advance ring A.left A.gap := by
                    rw [hgap]
                  _ = A.right := A.right_eq
              have hstepR :=
                stepE_responder ring C A.left
                  (rightNeighbor_ne_self_local ring
                    (sector_one_lt_n A) A.left)
              have houtRow :
                  (PPL.Elim.rowE
                    (C A.left)
                    (C (ring.rightNeighbor A.left))).2.leader =
                    true := by
                rw [← hstepR, hrn]
                exact hrightD
              have hpair :=
                rowE_ready_outgoing_survive
                  (C A.left)
                  (C (ring.rightNeighbor A.left))
                  hleft hsig hsrcB
                  (by
                    rw [hrn]
                    exact hright)
                  houtRow
              rcases hpair with ⟨hb0, hs1⟩
              have hstepL :=
                stepE_initiator ring C A.left
              refine .inr ⟨.ready, ?_, ?_⟩
              · refine ⟨hintD, ?_, ?_⟩
                · rw [hstepL, hs1]
                · intro q hq
                  have hq0 : q = 0 := by omega
                  subst q
                  rw [advance_zero, hstepL, hb0]
              · simp [PhaseTransition, nextSectorPhase,
                  hin, hgap]
            · have hgap2 : 1 < A.gap := by
                exact Nat.lt_of_le_of_ne A.gap_pos (Ne.symm hgap)
              have hrn :
                  ring.rightNeighbor A.left =
                    advance ring A.left 1 := by
                simpa using
                  advance_succ_twoLeader ring A.left 0
              have hrLeader :
                  (C (ring.rightNeighbor A.left)).leader =
                    false := by
                rw [hrn]
                exact hint 1 (by omega) (by omega)
              have hrBullet :
                  (C (ring.rightNeighbor A.left)).bullet =
                    (0 : Fin 3) := by
                rw [hrn]
                exact hfree 1 (by omega)
              have hpair :=
                rowE_ready_outgoing_follower
                  (C A.left)
                  (C (ring.rightNeighbor A.left))
                  hleft hsig hsrcB
                  hrLeader hrBullet
              rcases hpair with
                ⟨hlb, hlsh, hls, hrb, hrs⟩
              have hstepL :=
                stepE_initiator ring C A.left
              have hstepR :=
                stepE_responder ring C A.left
                  (rightNeighbor_ne_self_local ring
                    (sector_one_lt_n A) A.left)
              rw [hrn] at hstepR hrb hrs
              refine .inr ⟨.live 1, ?_, ?_⟩
              · refine ⟨hintD, ?_, ?_, ?_⟩
                · refine ⟨by omega, ?_, ?_⟩
                  · rw [hstepR, hrb]
                  · intro q hq hq1
                    by_cases hq0 : q = 0
                    · subst q
                      rw [advance_zero, hstepL, hlb]
                    · rw [body_step_eq_of_source_other
                        A C q hq hq0 hq1]
                      exact hfree q hq
                · rw [hstepL, hlsh]
                · intro q hq
                  have hcases :
                      q = 0 ∨ q = 1 := by
                    omega
                  rcases hcases with hq0 | hq1
                  · subst q
                    rw [advance_zero, hstepL, hls]
                  · subst q
                    rw [hstepR, hrs]
              · simp [PhaseTransition, nextSectorPhase,
                  hin, hgap]
          · have hsource :=
              source_step_eq_other
                A C e hout hin
            have hfreeD :=
              ready_bulletFree_other
                A C e hint hfree hout hin
            refine .inr ⟨.ready, ?_, ?_⟩
            · refine ⟨hintD, ?_, hfreeD⟩
              rw [hsource]
              exact hsig
            · simp [PhaseTransition, nextSectorPhase,
                hin, hout]
    | dummy p =>
        rcases hphase with
          ⟨hint, honly, hshield, hz⟩
        have hintD :=
          interiorFollowers_step A C e hint
        by_cases hsrv :
            e = advance ring A.left p
        · subst e
          by_cases hnext : p + 1 < A.gap
          · have hf :=
              moving_forward_fields
                A C p (1 : Fin 3) false
                hint honly hshield hz
                (by omega) hnext
            rcases hf with
              ⟨honlyD, hshieldD, hzD⟩
            refine .inr
              ⟨.dummy (p + 1), ?_, ?_⟩
            · exact
                ⟨hintD, honlyD, hshieldD, hzD⟩
            · simp [PhaseTransition, nextSectorPhase,
                hnext]
          · have hlast : p + 1 = A.gap := by
              have hp := honly.1
              omega
            have hf :=
              moving_finish_fields
                A C p (1 : Fin 3)
                hright honly hz
                (by omega) hlast hdel
            rcases hf with
              ⟨hfreeD, hfrontD, hbeforeD⟩
            by_cases hgap : A.gap = 1
            · have hp0 : p = 0 := by omega
              have hpos :
                  advance ring A.left p = A.left := by
                rw [hp0, advance_zero]
              have hs1 :
                  (stepE ring C
                    (advance ring A.left p)
                    A.left).signalB = true := by
                simpa only [hpos] using hfrontD
              refine .inr ⟨.ready, ?_, ?_⟩
              · exact ⟨hintD, hs1, hfreeD⟩
              · simp [PhaseTransition, nextSectorPhase,
                  hnext, hgap]
            · have hp0 : 0 < p := by omega
              have hpEq : p = A.gap - 1 := by
                omega
              have hs0D :
                  (stepE ring C
                    (advance ring A.left p)
                    A.left).signalB = false := by
                have hh := hbeforeD 0 hp0
                simpa using hh
              have hzD :
                  SignalZeroBefore A
                    (stepE ring C
                      (advance ring A.left p))
                    (A.gap - 1) := by
                intro r hr
                apply hbeforeD r
                omega
              have hfD :
                  (stepE ring C
                    (advance ring A.left p)
                    (advance ring A.left
                      (A.gap - 1))).signalB = true := by
                rw [← hpEq]
                exact hfrontD
              refine .inr
                ⟨.ret (A.gap - 1), ?_, ?_⟩
              · exact
                  ⟨hintD, by omega, by omega,
                    hfreeD, hs0D, hzD, hfD⟩
              · simp [PhaseTransition, nextSectorPhase,
                  hnext, hgap]
        · have hleft :=
            left_alive_of_not_deleted A C halive
          have hf :=
            moving_stutter_fields
              A C p (1 : Fin 3) false e
              hleft hint honly hshield hz hsrv
          rcases hf with
            ⟨honlyD, hshieldD, hzD⟩
          refine .inr ⟨.dummy p, ?_, ?_⟩
          · exact
              ⟨hintD, honlyD, hshieldD, hzD⟩
          · simp [PhaseTransition, nextSectorPhase,
              hsrv]
    | live p =>
        rcases hphase with
          ⟨hint, honly, hshield, hz⟩
        have hintD :=
          interiorFollowers_step A C e hint
        by_cases hsrv :
            e = advance ring A.left p
        · subst e
          by_cases hnext : p + 1 < A.gap
          · have hf :=
              moving_forward_fields
                A C p (2 : Fin 3) true
                hint honly hshield hz
                (by omega) hnext
            rcases hf with
              ⟨honlyD, hshieldD, hzD⟩
            refine .inr
              ⟨.live (p + 1), ?_, ?_⟩
            · exact
                ⟨hintD, honlyD, hshieldD, hzD⟩
            · simp [PhaseTransition, nextSectorPhase,
                hnext]
          · have hlast : p + 1 = A.gap := by
              have hp := honly.1
              omega
            have hf :=
              moving_finish_fields
                A C p (2 : Fin 3)
                hright honly hz
                (by omega) hlast hdel
            rcases hf with
              ⟨hfreeD, hfrontD, hbeforeD⟩
            by_cases hgap : A.gap = 1
            · have hp0 : p = 0 := by omega
              have hpos :
                  advance ring A.left p = A.left := by
                rw [hp0, advance_zero]
              have hs1 :
                  (stepE ring C
                    (advance ring A.left p)
                    A.left).signalB = true := by
                simpa only [hpos] using hfrontD
              refine .inr ⟨.ready, ?_, ?_⟩
              · exact ⟨hintD, hs1, hfreeD⟩
              · simp [PhaseTransition, nextSectorPhase,
                  hnext, hgap]
            · have hp0 : 0 < p := by omega
              have hpEq : p = A.gap - 1 := by
                omega
              have hs0D :
                  (stepE ring C
                    (advance ring A.left p)
                    A.left).signalB = false := by
                have hh := hbeforeD 0 hp0
                simpa using hh
              have hzD :
                  SignalZeroBefore A
                    (stepE ring C
                      (advance ring A.left p))
                    (A.gap - 1) := by
                intro r hr
                apply hbeforeD r
                omega
              have hfD :
                  (stepE ring C
                    (advance ring A.left p)
                    (advance ring A.left
                      (A.gap - 1))).signalB = true := by
                rw [← hpEq]
                exact hfrontD
              refine .inr
                ⟨.ret (A.gap - 1), ?_, ?_⟩
              · exact
                  ⟨hintD, by omega, by omega,
                    hfreeD, hs0D, hzD, hfD⟩
              · simp [PhaseTransition, nextSectorPhase,
                  hnext, hgap]
        · have hleft :=
            left_alive_of_not_deleted A C halive
          have hf :=
            moving_stutter_fields
              A C p (2 : Fin 3) true e
              hleft hint honly hshield hz hsrv
          rcases hf with
            ⟨honlyD, hshieldD, hzD⟩
          refine .inr ⟨.live p, ?_, ?_⟩
          · exact
              ⟨hintD, honlyD, hshieldD, hzD⟩
          · simp [PhaseTransition, nextSectorPhase,
              hsrv]
    | ret q =>
        rcases hphase with
          ⟨hint, hq0, hq, hfree, hs0, hz, hfront⟩
        have hintD :=
          interiorFollowers_step A C e hint
        by_cases hsrv :
            e = advance ring A.left (q - 1)
        · subst e
          have hf :=
            return_service_fields
              A C q hint hq0 hq
              hfree hz hfront
          rcases hf with
            ⟨hfreeD, hfrontD, hbeforeD⟩
          by_cases hq1 : q = 1
          · have hpos :
                advance ring A.left (q - 1) =
                  A.left := by
              rw [hq1]
              simp
            have hs1 :
                (stepE ring C
                  (advance ring A.left (q - 1))
                  A.left).signalB = true := by
              simpa only [hpos] using hfrontD
            refine .inr ⟨.ready, ?_, ?_⟩
            · exact ⟨hintD, hs1, hfreeD⟩
            · simp [PhaseTransition, nextSectorPhase,
                hq1]
          · have hqm1 : 0 < q - 1 := by omega
            have hs0D :
                (stepE ring C
                  (advance ring A.left (q - 1))
                  A.left).signalB = false := by
              have hh := hbeforeD 0 hqm1
              simpa using hh
            refine .inr ⟨.ret (q - 1), ?_, ?_⟩
            · exact
                ⟨hintD, hqm1, by omega,
                  hfreeD, hs0D, hbeforeD, hfrontD⟩
            · simp [PhaseTransition, nextSectorPhase,
                hq1]
        · have hf :=
            return_stutter_fields
              A C q e hleft hint hq0 hq
              hfree hs0 hz hfront hsrv
          rcases hf with
            ⟨hfreeD, hs0D, hzD, hfrontD⟩
          refine .inr ⟨.ret q, ?_, ?_⟩
          · exact
              ⟨hintD, hq0, hq,
                hfreeD, hs0D, hzD, hfrontD⟩
          · simp [PhaseTransition, nextSectorPhase,
              hsrv]


#print axioms PPL.Convergence.LDLocal.sealedStepSpec


end PPL.Convergence.LDLocal

