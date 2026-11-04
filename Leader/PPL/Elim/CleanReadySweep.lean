import Leader.PPL.Elim.CleanReadyRank

/-!
# LD(736): clean-ready sweep and return stage obligations

This file proves the two physical row-E obligations for the fresh-front sweep
and nearest-return stages of the corrected clean-ready monitor.
-/

namespace PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

/-! ## Ring and step locality -/

private theorem sector_one_lt_n
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) :
    1 < n := by
  have hp := A.gap_pos
  have hn := A.gap_lt_n
  omega

private theorem rightNeighbor_ne_self_local
    {n : Nat} (ring : DirectedRing n) (hn : 1 < n)
    (e : Fin n) :
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

private theorem rightNeighbor_injective_local
    {n : Nat} (ring : DirectedRing n) :
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

private theorem advance_succ_local
    {n : Nat} (ring : DirectedRing n) (i : Fin n) (q : Nat) :
    ring.rightNeighbor (advance ring i q) =
      advance ring i (q + 1) := by
  apply Fin.ext
  unfold DirectedRing.rightNeighbor advance
  dsimp only
  rw [Nat.mod_add_mod, Nat.add_assoc]

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

private theorem edge_eq_predecessor
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (q : Nat) (e : Fin n)
    (hq0 : 0 < q) (hq : q < A.gap)
    (hresp : advance ring A.left q = ring.rightNeighbor e) :
    e = advance ring A.left (q - 1) := by
  apply rightNeighbor_injective_local ring
  calc
    ring.rightNeighbor e = advance ring A.left q := hresp.symm
    _ = advance ring A.left ((q - 1) + 1) := by
      congr 2
      omega
    _ = ring.rightNeighbor (advance ring A.left (q - 1)) :=
      (advance_succ_local ring A.left (q - 1)).symm

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
  simp [stepE, PopulationProtocol.step, PPL.Elim.protocolE, hne,
    Ne.symm hne]

private theorem stepE_other
    {n : Nat} (ring : DirectedRing n)
    (C : Config n) (e k : Fin n)
    (hke : k ≠ e) (hkr : k ≠ ring.rightNeighbor e) :
    stepE ring C e k = C k := by
  simp [stepE, PopulationProtocol.step, PPL.Elim.protocolE, hke, hkr]

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
  · rw [advance_succ_local]
    intro h
    have ha1 : a + 1 < n := by
      have hn := A.gap_lt_n
      omega
    have heq := advance_injective_below ring A.left
      (Nat.lt_trans hq A.gap_lt_n) ha1 h
    exact hqs heq

private theorem left_alive_of_not_deleted
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    (h : ¬ EndpointDeleted A C) :
    (C A.left).leader = true := by
  cases hc : (C A.left).leader with
  | false => exact (h (Or.inl hc)).elim
  | true => rfl

private theorem right_alive_of_not_deleted
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    (h : ¬ EndpointDeleted A C) :
    (C A.right).leader = true := by
  cases hc : (C A.right).leader with
  | false => exact (h (Or.inr hc)).elim
  | true => rfl

/-! ## Small literal row-E facts -/

private theorem fin3_cases_local (x : Fin 3) :
    x = (0 : Fin 3) ∨
      x = (1 : Fin 3) ∨ x = (2 : Fin 3) := by
  have hx := x.isLt
  have h : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 := by omega
  rcases h with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

private theorem rowE_right_signal_false
    (l r : PPL.Elim.Cell4) (hr : r.signalB = false) :
    (PPL.Elim.rowE l r).2.signalB = false := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_local lb with h | h | h <;> subst lb <;>
  rcases fin3_cases_local rb with h | h | h <;> subst rb <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]

private theorem rowE_right_bullet_of_leader_signal_false
    (l r : PPL.Elim.Cell4)
    (hrl : r.leader = true) (hrs : r.signalB = false) :
    (PPL.Elim.rowE l r).2.bullet = r.bullet := by
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
    (hq : l.leader = false ∨ l.signalB = false) :
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
    (hlq : l.leader = false ∨ l.signalB = false)
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
    (hll : l.leader = false) (hls : l.signalB = true) :
    (PPL.Elim.rowE l r).1.signalB = true := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_local lb with h | h | h <;> subst lb <;>
  rcases fin3_cases_local rb with h | h | h <;> subst rb <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]

private theorem rowE_sweep_move_follower
    (l r : PPL.Elim.Cell4)
    (hls : l.signalB = false)
    (hlb : l.bullet ≠ (0 : Fin 3))
    (hrl : r.leader = false) :
    (PPL.Elim.rowE l r).1.bullet = (0 : Fin 3) ∧
      (PPL.Elim.rowE l r).1.signalB = false ∧
      (PPL.Elim.rowE l r).2.bullet ≠ (0 : Fin 3) ∧
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

private theorem rowE_terminal_quiet
    (l r : PPL.Elim.Cell4)
    (hls : l.signalB = false)
    (hlb : l.bullet = (0 : Fin 3))
    (hrl : r.leader = true) :
    (PPL.Elim.rowE l r).1.bullet = (0 : Fin 3) ∧
      (PPL.Elim.rowE l r).1.signalB = true := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_local lb with h | h | h <;> subst lb <;>
  rcases fin3_cases_local rb with h | h | h <;> subst rb <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]

/-! ## Preservation bricks -/

private theorem sectorBulletFree_quiet_step
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n) (e : Fin n)
    (hleft : (C A.left).leader = true)
    (hint : CRInteriorFollowers A C)
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
        exact Or.inr (by rw [← hqe, advance_zero]; exact hs0)
      · exact Or.inl (by
          rw [← hqe]
          exact hint q (by omega) hq)
    rw [hqe, stepE_initiator]
    exact rowE_left_bullet_zero_of_quiet _ _
      (by simpa [← hqe] using hbq) hquiet
  · by_cases hqr :
      advance ring A.left q = ring.rightNeighbor e
    · rw [hqr, stepE_responder ring C e
        (rightNeighbor_ne_self_local ring (sector_one_lt_n A) e)]
      by_cases hq0 : q = 0
      · subst q
        have hrl : (C (ring.rightNeighbor e)).leader = true := by
          rw [← hqr, advance_zero]
          exact hleft
        have hrs : (C (ring.rightNeighbor e)).signalB = false := by
          rw [← hqr, advance_zero]
          exact hs0
        rw [rowE_right_bullet_of_leader_signal_false _ _ hrl hrs]
        simpa [← hqr] using hbq
      · have hepred :=
          edge_eq_predecessor A q e (by omega) hq hqr
        have hpl : q - 1 < A.gap := by omega
        have hlb : (C e).bullet = (0 : Fin 3) := by
          rw [hepred]
          exact hfree (q - 1) hpl
        have hlq :
            (C e).leader = false ∨ (C e).signalB = false := by
          by_cases hq1 : q = 1
          · right
            rw [hepred]
            have hz : q - 1 = 0 := by omega
            rw [hz, advance_zero]
            exact hs0
          · left
            rw [hepred]
            exact hint (q - 1) (by omega) hpl
        have hrl : (C (ring.rightNeighbor e)).leader = false := by
          rw [← hqr]
          exact hint q (by omega) hq
        rw [rowE_right_bullet_of_left_quiet _ _ hlb hlq hrl]
        simpa [← hqr] using hbq
    · rw [stepE_other ring C e (advance ring A.left q) hqe hqr]
      exact hbq

private theorem leastBullet_stutter
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    (p : Nat) (e : Fin n)
    (hleft : (C A.left).leader = true)
    (hint : CRInteriorFollowers A C)
    (hleast : LeastBulletOffset A C p)
    (hz : ZeroSignalThrough A C p)
    (hne : e ≠ advance ring A.left p) :
    LeastBulletOffset A (stepE ring C e) p := by
  rcases hleast with ⟨hp, hbp, hzero⟩
  have hs0 : (C A.left).signalB = false := by
    have hh := hz 0 (Nat.zero_le p)
    simpa using hh
  refine ⟨hp, ?_, ?_⟩
  · by_cases hpr :
      advance ring A.left p = ring.rightNeighbor e
    · rw [hpr, stepE_responder ring C e
        (rightNeighbor_ne_self_local ring (sector_one_lt_n A) e)]
      by_cases hp0 : p = 0
      · subst p
        have hrl : (C (ring.rightNeighbor e)).leader = true := by
          rw [← hpr, advance_zero]
          exact hleft
        have hrs : (C (ring.rightNeighbor e)).signalB = false := by
          rw [← hpr, advance_zero]
          exact hs0
        rw [rowE_right_bullet_of_leader_signal_false _ _ hrl hrs]
        simpa [← hpr] using hbp
      · have hepred :=
          edge_eq_predecessor A p e (by omega) hp hpr
        have hpl : p - 1 < A.gap := by omega
        have hlb : (C e).bullet = (0 : Fin 3) := by
          rw [hepred]
          exact hzero (p - 1) (by omega)
        have hls : (C e).signalB = false := by
          rw [hepred]
          exact hz (p - 1) (by omega)
        have hrl : (C (ring.rightNeighbor e)).leader = false := by
          rw [← hpr]
          exact hint p (by omega) hp
        rw [rowE_right_bullet_of_left_quiet _ _ hlb (Or.inr hls) hrl]
        simpa [← hpr] using hbp
    · have hpe : advance ring A.left p ≠ e := by
        intro h
        exact hne h.symm
      rw [stepE_other ring C e (advance ring A.left p) hpe hpr]
      exact hbp
  · intro q hqp
    have hqgap : q < A.gap := by omega
    have hbq := hzero q hqp
    by_cases hqe : advance ring A.left q = e
    · have hquiet :
          (C e).leader = false ∨ (C e).signalB = false := by
        by_cases hq0 : q = 0
        · subst q
          exact Or.inr (by
            rw [← hqe, advance_zero]
            exact hs0)
        · exact Or.inl (by
            rw [← hqe]
            exact hint q (by omega) hqgap)
      rw [hqe, stepE_initiator]
      exact rowE_left_bullet_zero_of_quiet _ _
        (by simpa [← hqe] using hbq) hquiet
    · by_cases hqr :
        advance ring A.left q = ring.rightNeighbor e
      · rw [hqr, stepE_responder ring C e
          (rightNeighbor_ne_self_local ring (sector_one_lt_n A) e)]
        by_cases hq0 : q = 0
        · subst q
          have hrl : (C (ring.rightNeighbor e)).leader = true := by
            rw [← hqr, advance_zero]
            exact hleft
          have hrs : (C (ring.rightNeighbor e)).signalB = false := by
            rw [← hqr, advance_zero]
            exact hs0
          rw [rowE_right_bullet_of_leader_signal_false _ _ hrl hrs]
          simpa [← hqr] using hbq
        · have hepred :=
            edge_eq_predecessor A q e (by omega) hqgap hqr
          have hpl : q - 1 < A.gap := by omega
          have hlb : (C e).bullet = (0 : Fin 3) := by
            rw [hepred]
            exact hzero (q - 1) (by omega)
          have hls : (C e).signalB = false := by
            rw [hepred]
            exact hz (q - 1) (by omega)
          have hrl : (C (ring.rightNeighbor e)).leader = false := by
            rw [← hqr]
            exact hint q (by omega) hqgap
          rw [rowE_right_bullet_of_left_quiet _ _ hlb (Or.inr hls) hrl]
          simpa [← hqr] using hbq
      · rw [stepE_other ring C e (advance ring A.left q) hqe hqr]
        exact hbq

private theorem zeroThrough_stutter
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    (p : Nat) (e : Fin n)
    (hp : p < A.gap)
    (hint : CRInteriorFollowers A C)
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
        ring.rightNeighbor e = advance ring A.left (q + 1) := by
      rw [← hqe]
      exact advance_succ_local ring A.left q
    have hrs : (C (ring.rightNeighbor e)).signalB = false := by
      rw [hrn]
      exact hz (q + 1) hqnext
    have hrl : (C (ring.rightNeighbor e)).leader = false := by
      rw [hrn]
      exact hint (q + 1) (by omega) (by omega)
    rw [hqe, stepE_initiator]
    exact rowE_left_signal_false_of_quiet_pair _ _
      (by simpa [← hqe] using hsq) hrs hrl
  · by_cases hqr :
      advance ring A.left q = ring.rightNeighbor e
    · rw [hqr, stepE_responder ring C e
        (rightNeighbor_ne_self_local ring (sector_one_lt_n A) e)]
      exact rowE_right_signal_false _ _
        (by simpa [← hqr] using hsq)
    · rw [stepE_other ring C e (advance ring A.left q) hqe hqr]
      exact hsq

private theorem sweep_forward_fields
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    (p : Nat)
    (hint : CRInteriorFollowers A C)
    (hleast : LeastBulletOffset A C p)
    (hz : ZeroSignalThrough A C p)
    (hnext : p + 1 < A.gap) :
    LeastBulletOffset
        A (stepE ring C (advance ring A.left p)) (p + 1) ∧
      ZeroSignalThrough
        A (stepE ring C (advance ring A.left p)) (p + 1) := by
  rcases hleast with ⟨hp, hbp, hzero⟩
  let e := advance ring A.left p
  have hrn :
      ring.rightNeighbor e = advance ring A.left (p + 1) := by
    dsimp [e]
    exact advance_succ_local ring A.left p
  have hls : (C e).signalB = false := by
    dsimp [e]
    exact hz p (Nat.le_refl p)
  have hlb : (C e).bullet ≠ (0 : Fin 3) := by
    dsimp [e]
    exact hbp
  have hrl : (C (ring.rightNeighbor e)).leader = false := by
    rw [hrn]
    exact hint (p + 1) (by omega) hnext
  have hm := rowE_sweep_move_follower
    (C e) (C (ring.rightNeighbor e)) hls hlb hrl
  rcases hm with ⟨hmLB, hmLS, hmRB, hmRS⟩
  have hleftStep := stepE_initiator ring C e
  have hrightStep := stepE_responder ring C e
    (rightNeighbor_ne_self_local ring (sector_one_lt_n A) e)
  rw [hrn] at hrightStep
  rw [hrn] at hmRB hmRS
  constructor
  · refine ⟨hnext, ?_, ?_⟩
    · rw [hrightStep]
      exact hmRB
    · intro q hq
      by_cases hqp : q = p
      · subst q
        rw [hleftStep, hmLB]
      · have hqgap : q < A.gap := by omega
        have hqs : q ≠ p + 1 := by omega
        rw [body_step_eq_of_service_other A C p q hp hqgap hqp hqs]
        exact hzero q (by omega)
  · intro q hq
    have hqgap : q < A.gap := by omega
    by_cases hqp : q = p
    · subst q
      rw [hleftStep, hmLS]
    · by_cases hqn : q = p + 1
      · subst q
        rw [hrightStep, hmRS]
      · rw [body_step_eq_of_service_other A C p q hp hqgap hqp hqn]
        exact hz q (by omega)

private theorem sweep_finish_fields
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    (p : Nat)
    (hright : (C A.right).leader = true)
    (hleast : LeastBulletOffset A C p)
    (hz : ZeroSignalThrough A C p)
    (hlast : p + 1 = A.gap)
    (hkeep :
      ¬ EndpointDeleted A
        (stepE ring C (advance ring A.left p))) :
    SectorBulletFree
        A (stepE ring C (advance ring A.left p)) ∧
      (stepE ring C (advance ring A.left p)
        (advance ring A.left p)).signalB = true ∧
      (∀ r, r < p →
        (stepE ring C (advance ring A.left p)
          (advance ring A.left r)).signalB = false) := by
  rcases hleast with ⟨hp, hbp, hzero⟩
  let e := advance ring A.left p
  have hrn0 :
      ring.rightNeighbor e = advance ring A.left (p + 1) := by
    dsimp [e]
    exact advance_succ_local ring A.left p
  have hrn : ring.rightNeighbor e = A.right := by
    rw [hrn0, hlast, A.right_eq]
  have hls : (C e).signalB = false := by
    dsimp [e]
    exact hz p (Nat.le_refl p)
  have hlb : (C e).bullet ≠ (0 : Fin 3) := by
    dsimp [e]
    exact hbp
  have hrl : (C (ring.rightNeighbor e)).leader = true := by
    rw [hrn]
    exact hright
  have hDright := right_alive_of_not_deleted A
    (stepE ring C e) hkeep
  have hrightStep := stepE_responder ring C e
    (rightNeighbor_ne_self_local ring (sector_one_lt_n A) e)
  have hout :
      (PPL.Elim.rowE (C e)
        (C (ring.rightNeighbor e))).2.leader = true := by
    rw [← hrightStep, hrn]
    exact hDright
  have hm := rowE_hit_survive
    (C e) (C (ring.rightNeighbor e)) hls hlb hrl hout
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
      rw [body_step_eq_of_service_other A C p q hp hq hqp hqs]
      exact hzero q (by omega)
  · rw [hleftStep, hmS]
  · intro r hrp
    have hrgap : r < A.gap := by omega
    have hrs : r ≠ p + 1 := by omega
    rw [body_step_eq_of_service_other A C p r hp hrgap
      (by omega) hrs]
    exact hz r (by omega)

private theorem zeroBefore_stutter
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    (q : Nat) (e : Fin n)
    (hq0 : 0 < q) (hq : q ≤ A.gap)
    (hint : CRInteriorFollowers A C)
    (hz : ∀ r, r < q →
      (C (advance ring A.left r)).signalB = false)
    (hne : e ≠ advance ring A.left (q - 1)) :
    ∀ r, r < q →
      (stepE ring C e (advance ring A.left r)).signalB = false := by
  intro r hrq
  have hsr := hz r hrq
  by_cases hre : advance ring A.left r = e
  · have hrne : r ≠ q - 1 := by
      intro hh
      exact hne (by rw [← hre, hh])
    have hrnext : r + 1 < q := by omega
    have hrn :
        ring.rightNeighbor e = advance ring A.left (r + 1) := by
      rw [← hre]
      exact advance_succ_local ring A.left r
    have hrs : (C (ring.rightNeighbor e)).signalB = false := by
      rw [hrn]
      exact hz (r + 1) hrnext
    have hrl : (C (ring.rightNeighbor e)).leader = false := by
      rw [hrn]
      exact hint (r + 1) (by omega) (by omega)
    rw [hre, stepE_initiator]
    exact rowE_left_signal_false_of_quiet_pair _ _
      (by simpa [← hre] using hsr) hrs hrl
  · by_cases hrr :
      advance ring A.left r = ring.rightNeighbor e
    · rw [hrr, stepE_responder ring C e
        (rightNeighbor_ne_self_local ring (sector_one_lt_n A) e)]
      exact rowE_right_signal_false _ _
        (by simpa [← hrr] using hsr)
    · rw [stepE_other ring C e (advance ring A.left r) hre hrr]
      exact hsr

private theorem signalFront_stutter
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    (q : Nat) (e : Fin n)
    (hq0 : 0 < q) (hq : q < A.gap)
    (hint : CRInteriorFollowers A C)
    (hfront : (C (advance ring A.left q)).signalB = true)
    (hne : e ≠ advance ring A.left (q - 1)) :
    (stepE ring C e (advance ring A.left q)).signalB = true := by
  by_cases hqe : advance ring A.left q = e
  · rw [hqe, stepE_initiator]
    exact rowE_left_signal_true_of_follower _ _
      (by
        rw [← hqe]
        exact hint q hq0 hq)
      (by simpa [← hqe] using hfront)
  · by_cases hqr :
      advance ring A.left q = ring.rightNeighbor e
    · have hepred := edge_eq_predecessor A q e hq0 hq hqr
      exact (hne hepred).elim
    · rw [stepE_other ring C e (advance ring A.left q) hqe hqr]
      exact hfront

private theorem return_stutter_fields
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    (q : Nat) (e : Fin n)
    (hleft : (C A.left).leader = true)
    (hint : CRInteriorFollowers A C)
    (hfree : SectorBulletFree A C)
    (hs0 : (C A.left).signalB = false)
    (hfront : ReturnFront A C q)
    (hne : e ≠ advance ring A.left (q - 1)) :
    SectorBulletFree A (stepE ring C e) ∧
      (stepE ring C e A.left).signalB = false ∧
      ReturnFront A (stepE ring C e) q := by
  rcases hfront with ⟨hq0, hq, hz, hactual⟩
  have hfreeD :=
    sectorBulletFree_quiet_step A C e hleft hint hfree hs0
  have hzD :=
    zeroBefore_stutter A C q e hq0 hq hint hz hne
  have hs0D : (stepE ring C e A.left).signalB = false := by
    have hh := hzD 0 hq0
    simpa using hh
  refine ⟨hfreeD, hs0D, hq0, hq, hzD, ?_⟩
  intro hqgap
  have hf := hactual hqgap
  exact signalFront_stutter A C q e hq0 hqgap hint hf hne

private theorem return_service_actual_fields
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    (q : Nat)
    (hint : CRInteriorFollowers A C)
    (hq0 : 0 < q) (hq : q < A.gap)
    (hfree : SectorBulletFree A C)
    (hz : ∀ r, r < q →
      (C (advance ring A.left r)).signalB = false)
    (hfront : (C (advance ring A.left q)).signalB = true) :
    SectorBulletFree
        A (stepE ring C (advance ring A.left (q - 1))) ∧
      (stepE ring C (advance ring A.left (q - 1))
        (advance ring A.left (q - 1))).signalB = true ∧
      (∀ r, r < q - 1 →
        (stepE ring C (advance ring A.left (q - 1))
          (advance ring A.left r)).signalB = false) := by
  let e := advance ring A.left (q - 1)
  have hp0 : q - 1 < A.gap := by omega
  have hrn :
      ring.rightNeighbor e = advance ring A.left q := by
    dsimp [e]
    calc
      ring.rightNeighbor (advance ring A.left (q - 1)) =
          advance ring A.left ((q - 1) + 1) :=
            advance_succ_local ring A.left (q - 1)
      _ = advance ring A.left q := by
        congr 2
        omega
  have hls : (C e).signalB = false := by
    dsimp [e]
    exact hz (q - 1) (by omega)
  have hlb : (C e).bullet = (0 : Fin 3) := by
    dsimp [e]
    exact hfree (q - 1) hp0
  have hrl : (C (ring.rightNeighbor e)).leader = false := by
    rw [hrn]
    exact hint q hq0 hq
  have hrb : (C (ring.rightNeighbor e)).bullet = (0 : Fin 3) := by
    rw [hrn]
    exact hfree q hq
  have hrs : (C (ring.rightNeighbor e)).signalB = true := by
    rw [hrn]
    exact hfront
  have hm := rowE_return_service
    (C e) (C (ring.rightNeighbor e)) hls hlb hrl hrb hrs
  rcases hm with ⟨hmLB, hmLS, hmRB, hmRS⟩
  have hleftStep := stepE_initiator ring C e
  have hrightStep := stepE_responder ring C e
    (rightNeighbor_ne_self_local ring (sector_one_lt_n A) e)
  rw [hrn] at hrightStep
  rw [hrn] at hmRB
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    by_cases hrL : r = q - 1
    · subst r
      rw [hleftStep, hmLB]
    · by_cases hrR : r = q
      · subst r
        rw [hrightStep, hmRB]
      · rw [body_step_eq_of_service_other A C (q - 1) r hp0 hr
          hrL ?_]
        · exact hfree r hr
        · intro hh
          apply hrR
          omega
  · rw [hleftStep, hmLS]
  · intro r hr
    have hrgap : r < A.gap := by omega
    have hrL : r ≠ q - 1 := by omega
    have hrR : r ≠ (q - 1) + 1 := by omega
    rw [body_step_eq_of_service_other A C (q - 1) r hp0 hrgap
      hrL hrR]
    exact hz r (by omega)

private theorem return_service_virtual_fields
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    (hright : (C A.right).leader = true)
    (hfree : SectorBulletFree A C)
    (hz : ∀ r, r < A.gap →
      (C (advance ring A.left r)).signalB = false) :
    SectorBulletFree
        A (stepE ring C (advance ring A.left (A.gap - 1))) ∧
      (stepE ring C (advance ring A.left (A.gap - 1))
        (advance ring A.left (A.gap - 1))).signalB = true ∧
      (∀ r, r < A.gap - 1 →
        (stepE ring C (advance ring A.left (A.gap - 1))
          (advance ring A.left r)).signalB = false) := by
  let p := A.gap - 1
  let e := advance ring A.left p
  have hp : p < A.gap := by
    dsimp [p]
    have hpos := A.gap_pos
    omega
  have hp1 : p + 1 = A.gap := by
    dsimp [p]
    omega
  have hrn0 :
      ring.rightNeighbor e = advance ring A.left (p + 1) := by
    dsimp [e]
    exact advance_succ_local ring A.left p
  have hrn : ring.rightNeighbor e = A.right := by
    rw [hrn0, hp1, A.right_eq]
  have hls : (C e).signalB = false := by
    dsimp [e]
    exact hz p hp
  have hlb : (C e).bullet = (0 : Fin 3) := by
    dsimp [e]
    exact hfree p hp
  have hrl : (C (ring.rightNeighbor e)).leader = true := by
    rw [hrn]
    exact hright
  have hm := rowE_terminal_quiet
    (C e) (C (ring.rightNeighbor e)) hls hlb hrl
  rcases hm with ⟨hmB, hmS⟩
  have hleftStep := stepE_initiator ring C e
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    by_cases hrp : r = p
    · subst r
      rw [hleftStep, hmB]
    · have hrs : r ≠ p + 1 := by
        intro hh
        rw [hp1] at hh
        omega
      rw [body_step_eq_of_service_other A C p r hp hr hrp hrs]
      exact hfree r hr
  · change
      (stepE ring C e (advance ring A.left p)).signalB = true
    rw [show advance ring A.left p = e by rfl, hleftStep, hmS]
  · intro r hr
    change
      (stepE ring C e (advance ring A.left r)).signalB = false
    have hrgap : r < A.gap := by omega
    have hrp : r ≠ p := by omega
    have hrs : r ≠ p + 1 := by omega
    rw [body_step_eq_of_service_other A C p r hp hrgap hrp hrs]
    exact hz r hrgap

/-! ## Sweep stage -/

private theorem sweep_other_step
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n) (p : Nat)
    (hint : CRInteriorFollowers A C)
    (hmode : CRModeHolds A C (.sweep p))
    (e : Fin n) (hne : e ≠ advance ring A.left p) :
    CRDone A (stepE ring C e) ∨
      ∃ mode',
        CRModeHolds A (stepE ring C e) mode' ∧
        crRank A mode' ≤ crRank A (.sweep p) := by
  by_cases hdel : EndpointDeleted A (stepE ring C e)
  · exact Or.inl (Or.inl hdel)
  · rcases hmode with ⟨halive, _hs0, hleast, hz⟩
    have hleft := left_alive_of_not_deleted A C halive
    have hleastD :=
      leastBullet_stutter A C p e hleft hint hleast hz hne
    have hp := hleast.1
    have hzD := zeroThrough_stutter A C p e hp hint hz hne
    have hs0D : (stepE ring C e A.left).signalB = false := by
      have hh := hzD 0 (Nat.zero_le p)
      simpa using hh
    refine Or.inr ⟨.sweep p, ?_, Nat.le_refl _⟩
    exact ⟨hdel, hs0D, hleastD, hzD⟩

private theorem sweep_service_step
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n) (p : Nat)
    (hint : CRInteriorFollowers A C)
    (hmode : CRModeHolds A C (.sweep p)) :
    CRDone A (stepE ring C (advance ring A.left p)) ∨
      ∃ mode',
        CRModeHolds
          A (stepE ring C (advance ring A.left p)) mode' ∧
        crRank A mode' < crRank A (.sweep p) := by
  by_cases hdel :
      EndpointDeleted A (stepE ring C (advance ring A.left p))
  · exact Or.inl (Or.inl hdel)
  · rcases hmode with ⟨halive, _hs0, hleast, hz⟩
    have hp := hleast.1
    have hright := right_alive_of_not_deleted A C halive
    by_cases hnext : p + 1 < A.gap
    · have hf := sweep_forward_fields A C p hint hleast hz hnext
      rcases hf with ⟨hleastD, hzD⟩
      have hs0D :
          (stepE ring C (advance ring A.left p) A.left).signalB = false := by
        have hh := hzD 0 (Nat.zero_le (p + 1))
        simpa using hh
      refine Or.inr ⟨.sweep (p + 1), ?_, ?_⟩
      · exact ⟨hdel, hs0D, hleastD, hzD⟩
      · simp only [crRank]
        omega
    · have hlast : p + 1 = A.gap := by omega
      have hf :=
        sweep_finish_fields A C p hright hleast hz hlast hdel
      rcases hf with ⟨hfreeD, hfrontD, hbeforeD⟩
      by_cases hgap : A.gap = 1
      · have hp0 : p = 0 := by omega
        have hpos : advance ring A.left p = A.left := by
          rw [hp0, advance_zero]
        have hs1 :
            (stepE ring C (advance ring A.left p) A.left).signalB = true := by
          simpa only [hpos] using hfrontD
        exact Or.inl (Or.inr ⟨hs1, hfreeD⟩)
      · have hp0 : 0 < p := by omega
        have hpEq : p = A.gap - 1 := by omega
        have hs0D :
            (stepE ring C (advance ring A.left p) A.left).signalB = false := by
          have hh := hbeforeD 0 hp0
          simpa using hh
        have hret :
            ReturnFront A
              (stepE ring C (advance ring A.left p))
              (A.gap - 1) := by
          refine ⟨by omega, by omega, ?_, ?_⟩
          · intro r hr
            exact hbeforeD r (by omega)
          · intro _
            rw [← hpEq]
            exact hfrontD
        refine Or.inr ⟨.ret (A.gap - 1), ?_, ?_⟩
        · exact ⟨hdel, hfreeD, hs0D, hret⟩
        · simp only [crRank]
          omega

theorem crSweepStep : CRSweepStepSpec := by
  intro n ring C0 A C p _hPB hint hmode
  constructor
  · intro e
    by_cases hsrv : e = advance ring A.left p
    · subst e
      rcases sweep_service_step ring A C p hint hmode with
        hdone | ⟨mode', hmode', hrank⟩
      · exact Or.inl hdone
      · exact Or.inr ⟨mode', hmode', Nat.le_of_lt hrank⟩
    · exact sweep_other_step ring A C p hint hmode e hsrv
  · simpa only [crRequiredEdge] using
      sweep_service_step ring A C p hint hmode

/-! ## Return stage -/

private theorem return_other_step
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n) (q : Nat)
    (hint : CRInteriorFollowers A C)
    (hmode : CRModeHolds A C (.ret q))
    (e : Fin n) (hne : e ≠ advance ring A.left (q - 1)) :
    CRDone A (stepE ring C e) ∨
      ∃ mode',
        CRModeHolds A (stepE ring C e) mode' ∧
        crRank A mode' ≤ crRank A (.ret q) := by
  by_cases hdel : EndpointDeleted A (stepE ring C e)
  · exact Or.inl (Or.inl hdel)
  · rcases hmode with ⟨halive, hfree, hs0, hfront⟩
    have hleft := left_alive_of_not_deleted A C halive
    have hf :=
      return_stutter_fields A C q e hleft hint hfree hs0 hfront hne
    rcases hf with ⟨hfreeD, hs0D, hfrontD⟩
    refine Or.inr ⟨.ret q, ?_, Nat.le_refl _⟩
    exact ⟨hdel, hfreeD, hs0D, hfrontD⟩

private theorem return_service_step
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n) (q : Nat)
    (hint : CRInteriorFollowers A C)
    (hmode : CRModeHolds A C (.ret q)) :
    CRDone A (stepE ring C (advance ring A.left (q - 1))) ∨
      ∃ mode',
        CRModeHolds
          A (stepE ring C (advance ring A.left (q - 1))) mode' ∧
        crRank A mode' < crRank A (.ret q) := by
  by_cases hdel :
      EndpointDeleted A
        (stepE ring C (advance ring A.left (q - 1)))
  · exact Or.inl (Or.inl hdel)
  · rcases hmode with ⟨halive, hfree, _hs0, hfront⟩
    rcases hfront with ⟨hq0, hq, hz, hactual⟩
    by_cases hqgap : q < A.gap
    · have hf :=
        return_service_actual_fields A C q hint hq0 hqgap hfree hz
          (hactual hqgap)
      rcases hf with ⟨hfreeD, hfrontD, hbeforeD⟩
      by_cases hq1 : q = 1
      · have hpos :
            advance ring A.left (q - 1) = A.left := by
          rw [hq1]
          simp
        have hs1 :
            (stepE ring C (advance ring A.left (q - 1))
              A.left).signalB = true := by
          simpa only [hpos] using hfrontD
        exact Or.inl (Or.inr ⟨hs1, hfreeD⟩)
      · have hqm1 : 0 < q - 1 := by omega
        have hs0D :
            (stepE ring C (advance ring A.left (q - 1))
              A.left).signalB = false := by
          have hh := hbeforeD 0 hqm1
          simpa using hh
        have hret :
            ReturnFront A
              (stepE ring C (advance ring A.left (q - 1)))
              (q - 1) := by
          refine ⟨hqm1, by omega, hbeforeD, ?_⟩
          intro _
          exact hfrontD
        refine Or.inr ⟨.ret (q - 1), ?_, ?_⟩
        · exact ⟨hdel, hfreeD, hs0D, hret⟩
        · simp only [crRank]
          omega
    · have hqeq : q = A.gap := by omega
      subst q
      have hright := right_alive_of_not_deleted A C halive
      have hf :=
        return_service_virtual_fields A C hright hfree hz
      rcases hf with ⟨hfreeD, hfrontD, hbeforeD⟩
      by_cases hgap : A.gap = 1
      · have hpos :
            advance ring A.left (A.gap - 1) = A.left := by
          rw [hgap]
          simp
        have hs1 :
            (stepE ring C (advance ring A.left (A.gap - 1))
              A.left).signalB = true := by
          simpa only [hpos] using hfrontD
        exact Or.inl (Or.inr ⟨hs1, hfreeD⟩)
      · have hgm1 : 0 < A.gap - 1 := by omega
        have hs0D :
            (stepE ring C (advance ring A.left (A.gap - 1))
              A.left).signalB = false := by
          have hh := hbeforeD 0 hgm1
          simpa using hh
        have hret :
            ReturnFront A
              (stepE ring C (advance ring A.left (A.gap - 1)))
              (A.gap - 1) := by
          refine ⟨hgm1, by omega, hbeforeD, ?_⟩
          intro _
          exact hfrontD
        refine Or.inr ⟨.ret (A.gap - 1), ?_, ?_⟩
        · exact ⟨hdel, hfreeD, hs0D, hret⟩
        · simp only [crRank]
          omega

theorem crReturnStep : CRReturnStepSpec := by
  intro n ring C0 A C q _hPB hint hmode
  constructor
  · intro e
    by_cases hsrv : e = advance ring A.left (q - 1)
    · subst e
      rcases return_service_step ring A C q hint hmode with
        hdone | ⟨mode', hmode', hrank⟩
      · exact Or.inl hdone
      · exact Or.inr ⟨mode', hmode', Nat.le_of_lt hrank⟩
    · exact return_other_step ring A C q hint hmode e hsrv
  · simpa only [crRequiredEdge] using
      return_service_step ring A C q hint hmode

#print axioms sector_one_lt_n
#print axioms rightNeighbor_ne_self_local
#print axioms rightNeighbor_injective_local
#print axioms advance_succ_local
#print axioms advance_injective_below
#print axioms edge_eq_predecessor
#print axioms stepE_initiator
#print axioms stepE_responder
#print axioms stepE_other
#print axioms body_step_eq_of_service_other
#print axioms left_alive_of_not_deleted
#print axioms right_alive_of_not_deleted
#print axioms fin3_cases_local
#print axioms rowE_right_signal_false
#print axioms rowE_right_bullet_of_leader_signal_false
#print axioms rowE_left_bullet_zero_of_quiet
#print axioms rowE_right_bullet_of_left_quiet
#print axioms rowE_left_signal_false_of_quiet_pair
#print axioms rowE_left_signal_true_of_follower
#print axioms rowE_sweep_move_follower
#print axioms rowE_hit_survive
#print axioms rowE_return_service
#print axioms rowE_terminal_quiet
#print axioms sectorBulletFree_quiet_step
#print axioms leastBullet_stutter
#print axioms zeroThrough_stutter
#print axioms sweep_forward_fields
#print axioms sweep_finish_fields
#print axioms zeroBefore_stutter
#print axioms signalFront_stutter
#print axioms return_stutter_fields
#print axioms return_service_actual_fields
#print axioms return_service_virtual_fields
#print axioms sweep_other_step
#print axioms sweep_service_step
#print axioms crSweepStep
#print axioms return_other_step
#print axioms return_service_step
#print axioms crReturnStep

end PPL.Convergence.LDLocal
