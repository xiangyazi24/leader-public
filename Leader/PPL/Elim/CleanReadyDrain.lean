import Leader.PPL.Elim.CleanReadyRank

/-!
# LD(736): clean-ready drain and repair stage obligations

This file proves the two literal row-E obligations for the initial drain stage
and the one-source-firing repair stage.  The only current-state geometric
hypothesis used by the physical arguments is CRInteriorFollowers.
-/

namespace PPL.Convergence.LDLocal

set_option autoImplicit false
set_option Elab.async false

private def crIncomingEdge
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) : Fin n :=
  ring.leftNeighbor A.left

private theorem sector_one_lt_n_crd
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) :
    1 < n := by
  have hp := A.gap_pos
  have hn := A.gap_lt_n
  omega

private theorem rightNeighbor_ne_self_crd
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

private theorem rightNeighbor_injective_crd
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

private theorem rightNeighbor_leftNeighbor_crd
    {n : Nat} (ring : DirectedRing n) (i : Fin n) :
    ring.rightNeighbor (ring.leftNeighbor i) = i := by
  apply Fin.ext
  show ((i.val + n - 1) % n + 1) % n = i.val
  have hn := ring.hn
  have hi := i.isLt
  rcases Nat.eq_zero_or_pos i.val with h0 | hpos
  · have h1 : (i.val + n - 1) % n = n - 1 := by
      rw [h0, Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1, show n - 1 + 1 = n by omega, Nat.mod_self, h0]
  · have h1 : (i.val + n - 1) % n = i.val - 1 := by
      rw [show i.val + n - 1 = (i.val - 1) + n by omega,
        Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1, show i.val - 1 + 1 = i.val by omega]
    exact Nat.mod_eq_of_lt hi

private theorem advance_succ_crd
    {n : Nat} (ring : DirectedRing n) (i : Fin n) (q : Nat) :
    ring.rightNeighbor (advance ring i q) =
      advance ring i (q + 1) := by
  apply Fin.ext
  unfold DirectedRing.rightNeighbor advance
  dsimp only
  rw [Nat.mod_add_mod, Nat.add_assoc]

private theorem advance_injective_below_crd
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

private theorem incoming_responds_crd
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) :
    ring.rightNeighbor (crIncomingEdge A) = A.left := by
  exact rightNeighbor_leftNeighbor_crd ring A.left

private theorem edge_eq_predecessor_crd
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (q : Nat) (e : Fin n)
    (hq0 : 0 < q) (hq : q < A.gap)
    (hresp : advance ring A.left q = ring.rightNeighbor e) :
    e = advance ring A.left (q - 1) := by
  apply rightNeighbor_injective_crd ring
  calc
    ring.rightNeighbor e = advance ring A.left q := hresp.symm
    _ = advance ring A.left ((q - 1) + 1) := by
      congr 2
      omega
    _ = ring.rightNeighbor (advance ring A.left (q - 1)) :=
      (advance_succ_crd ring A.left (q - 1)).symm

private theorem stepE_initiator_crd
    {n : Nat} (ring : DirectedRing n)
    (C : Config n) (e : Fin n) :
    stepE ring C e e =
      (PPL.Elim.rowE (C e) (C (ring.rightNeighbor e))).1 := by
  simp [stepE, PopulationProtocol.step, PPL.Elim.protocolE]

private theorem stepE_responder_crd
    {n : Nat} (ring : DirectedRing n)
    (C : Config n) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    stepE ring C e (ring.rightNeighbor e) =
      (PPL.Elim.rowE (C e) (C (ring.rightNeighbor e))).2 := by
  simp [stepE, PopulationProtocol.step, PPL.Elim.protocolE, hne,
    Ne.symm hne]

private theorem stepE_other_crd
    {n : Nat} (ring : DirectedRing n)
    (C : Config n) (e k : Fin n)
    (hke : k ≠ e) (hkr : k ≠ ring.rightNeighbor e) :
    stepE ring C e k = C k := by
  simp [stepE, PopulationProtocol.step, PPL.Elim.protocolE, hke, hkr]

private theorem source_step_eq_other_crd
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n) (e : Fin n)
    (hle : e ≠ A.left) (hin : e ≠ crIncomingEdge A) :
    stepE ring C e A.left = C A.left := by
  apply stepE_other_crd
  · exact Ne.symm hle
  · intro h
    apply hin
    apply rightNeighbor_injective_crd ring
    calc
      ring.rightNeighbor e = A.left := h.symm
      _ = ring.rightNeighbor (crIncomingEdge A) :=
        (incoming_responds_crd A).symm

private theorem left_alive_crd
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    (h : ¬ EndpointDeleted A C) :
    (C A.left).leader = true := by
  cases hc : (C A.left).leader with
  | false =>
      exact (h (.inl hc)).elim
  | true =>
      rfl

private theorem right_alive_crd
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    (h : ¬ EndpointDeleted A C) :
    (C A.right).leader = true := by
  cases hc : (C A.right).leader with
  | false =>
      exact (h (.inr hc)).elim
  | true =>
      rfl

private theorem fin3_cases_crd (x : Fin 3) :
    x = (0 : Fin 3) ∨
      x = (1 : Fin 3) ∨ x = (2 : Fin 3) := by
  have hx := x.isLt
  have h :
      x.val = 0 ∨ x.val = 1 ∨ x.val = 2 := by
    omega
  rcases h with h | h | h
  · exact .inl (Fin.ext h)
  · exact .inr (.inl (Fin.ext h))
  · exact .inr (.inr (Fin.ext h))

private theorem rowE_left_bullet_zero_crd
    (l r : PPL.Elim.Cell4) :
    (PPL.Elim.rowE l r).1.bullet = (0 : Fin 3) := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_crd lb with h | h | h <;> subst lb <;>
  rcases fin3_cases_crd rb with h | h | h <;> subst rb <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp [PPL.Elim.rowE]

private theorem rowE_left_bullet_zero_of_quiet_crd
    (l r : PPL.Elim.Cell4)
    (hlb : l.bullet = (0 : Fin 3))
    (hq : l.leader = false ∨ l.signalB = false) :
    (PPL.Elim.rowE l r).1.bullet = (0 : Fin 3) := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_crd lb with h | h | h <;> subst lb <;>
  rcases fin3_cases_crd rb with h | h | h <;> subst rb <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]

private theorem rowE_right_bullet_of_leader_signal_false_crd
    (l r : PPL.Elim.Cell4)
    (hrl : r.leader = true) (hrs : r.signalB = false) :
    (PPL.Elim.rowE l r).2.bullet = r.bullet := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_crd lb with h | h | h <;> subst lb <;>
  rcases fin3_cases_crd rb with h | h | h <;> subst rb <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]

private theorem rowE_right_bullet_of_left_quiet_crd
    (l r : PPL.Elim.Cell4)
    (hlb : l.bullet = (0 : Fin 3))
    (hlq : l.leader = false ∨ l.signalB = false)
    (hrl : r.leader = false) :
    (PPL.Elim.rowE l r).2.bullet = r.bullet := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_crd lb with h | h | h <;> subst lb <;>
  rcases fin3_cases_crd rb with h | h | h <;> subst rb <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]

private theorem rowE_ready_incoming_survive_crd
    (l r : PPL.Elim.Cell4)
    (hrl : r.leader = true) (hrs : r.signalB = true)
    (hout : (PPL.Elim.rowE l r).2.leader = true) :
    (PPL.Elim.rowE l r).2.bullet = (1 : Fin 3) ∧
      (PPL.Elim.rowE l r).2.shield = false ∧
      (PPL.Elim.rowE l r).2.signalB = false := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_crd lb with h | h | h <;> subst lb <;>
  rcases fin3_cases_crd rb with h | h | h <;> subst rb <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]

private theorem rowE_fire_out_follower_crd
    (l r : PPL.Elim.Cell4)
    (hll : l.leader = true) (hls : l.signalB = true)
    (hrl : r.leader = false) :
    (PPL.Elim.rowE l r).1.bullet = (0 : Fin 3) ∧
      (PPL.Elim.rowE l r).1.signalB = false ∧
      (PPL.Elim.rowE l r).2.bullet ≠ (0 : Fin 3) ∧
      (PPL.Elim.rowE l r).2.signalB = false := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_crd lb with h | h | h <;> subst lb <;>
  rcases fin3_cases_crd rb with h | h | h <;> subst rb <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]

private theorem rowE_fire_out_leader_survive_signal_crd
    (l r : PPL.Elim.Cell4)
    (hll : l.leader = true) (hls : l.signalB = true)
    (hrl : r.leader = true)
    (hout : (PPL.Elim.rowE l r).2.leader = true) :
    (PPL.Elim.rowE l r).1.signalB = true := by
  rcases l with ⟨ll, lb, lsh, lsb⟩
  rcases r with ⟨rl, rb, rsh, rsb⟩
  rcases fin3_cases_crd lb with h | h | h <;> subst lb <;>
  rcases fin3_cases_crd rb with h | h | h <;> subst rb <;>
  cases ll <;> cases lsh <;> cases lsb <;>
  cases rl <;> cases rsh <;> cases rsb <;>
  simp_all [PPL.Elim.rowE]

private theorem drain_prefix_step_crd
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    (p : Nat) (e : Fin n)
    (hp : p < A.gap)
    (hleft : (C A.left).leader = true)
    (hint : CRInteriorFollowers A C)
    (hs0 : (C A.left).signalB = false)
    (hz : ∀ q, q < p →
      (C (advance ring A.left q)).bullet = (0 : Fin 3)) :
    ∀ q, q < p →
      (stepE ring C e (advance ring A.left q)).bullet =
        (0 : Fin 3) := by
  intro q hqp
  have hqgap : q < A.gap := by omega
  have hbq := hz q hqp
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
          exact hint q (by omega) hqgap)
    rw [hqe, stepE_initiator_crd]
    exact rowE_left_bullet_zero_of_quiet_crd _ _
      (by simpa [← hqe] using hbq) hquiet
  · by_cases hqr :
      advance ring A.left q = ring.rightNeighbor e
    · rw [hqr, stepE_responder_crd ring C e
        (rightNeighbor_ne_self_crd ring (sector_one_lt_n_crd A) e)]
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
        rw [rowE_right_bullet_of_leader_signal_false_crd _ _ hrl hrs]
        simpa [← hqr] using hbq
      · have hepred :=
          edge_eq_predecessor_crd A q e (by omega) hqgap hqr
        have hpl : q - 1 < p := by omega
        have hpredGap : q - 1 < A.gap := by omega
        have hlb : (C e).bullet = (0 : Fin 3) := by
          rw [hepred]
          exact hz (q - 1) hpl
        have hlq :
            (C e).leader = false ∨ (C e).signalB = false := by
          by_cases hq1 : q = 1
          · exact .inr (by
              rw [hepred, hq1]
              simp
              exact hs0)
          · exact .inl (by
              rw [hepred]
              exact hint (q - 1) (by omega) hpredGap)
        have hrl :
            (C (ring.rightNeighbor e)).leader = false := by
          rw [← hqr]
          exact hint q (by omega) hqgap
        rw [rowE_right_bullet_of_left_quiet_crd _ _ hlb hlq hrl]
        simpa [← hqr] using hbq
    · rw [stepE_other_crd ring C e
        (advance ring A.left q) hqe hqr]
      exact hbq

private theorem boundedLeast_crd
    (P : Nat → Prop) (d : Nat)
    (h : ∃ q, q < d ∧ P q) :
    ∃ p, p < d ∧ P p ∧ ∀ q, q < p → ¬ P q := by
  classical
  obtain ⟨q, hqd, hq⟩ := h
  revert hqd hq
  induction q using Nat.strongRecOn with
  | ind q ih =>
      intro hqd hq
      by_cases he : ∃ r, r < q ∧ P r
      · obtain ⟨r, hrq, hr⟩ := he
        exact ih r hrq (Nat.lt_trans hrq hqd) hr
      · exact ⟨q, hqd, hq, by
          intro r hrq hr
          exact he ⟨r, hrq, hr⟩⟩

private theorem leastBulletOffset_exists_crd
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n) (h : SectorHasBullet A C) :
    ∃ p, LeastBulletOffset A C p := by
  obtain ⟨p, hp, hbullet, hmin⟩ :=
    boundedLeast_crd
      (fun q =>
        (C (advance ring A.left q)).bullet ≠ (0 : Fin 3))
      A.gap h
  refine ⟨p, hp, hbullet, ?_⟩
  intro q hq
  by_cases hz :
      (C (advance ring A.left q)).bullet = (0 : Fin 3)
  · exact hz
  · exact False.elim ((hmin q hq) hz)

private theorem sectorBulletFree_of_not_hasBullet_crd
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    (h : ¬ SectorHasBullet A C) :
    SectorBulletFree A C := by
  intro q hq
  by_cases hz :
      (C (advance ring A.left q)).bullet = (0 : Fin 3)
  · exact hz
  · exact False.elim (h ⟨q, hq, hz⟩)

private theorem returnFront_exists_crd
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (C : Config n)
    (hs0 : (C A.left).signalB = false) :
    ∃ q, ReturnFront A C q := by
  classical
  by_cases hsig :
      ∃ q, q < A.gap ∧
        (C (advance ring A.left q)).signalB = true
  · obtain ⟨q, hq, htrue, hmin⟩ :=
      boundedLeast_crd
        (fun r =>
          (C (advance ring A.left r)).signalB = true)
        A.gap hsig
    have hq0 : 0 < q := by
      rcases Nat.eq_zero_or_pos q with hqz | hpos
      · exfalso
        subst q
        have ht0 :
            (C (advance ring A.left 0)).signalB = true := htrue
        simp [advance_zero] at ht0
        rw [hs0] at ht0
        contradiction
      · exact hpos
    refine ⟨q, hq0, Nat.le_of_lt hq, ?_, ?_⟩
    · intro r hr
      cases hrs : (C (advance ring A.left r)).signalB with
      | false =>
          rfl
      | true =>
          exact False.elim ((hmin r hr) hrs)
    · intro _
      exact htrue
  · refine ⟨A.gap, A.gap_pos, Nat.le_refl _, ?_, ?_⟩
    · intro r hr
      cases hrs : (C (advance ring A.left r)).signalB with
      | false =>
          rfl
      | true =>
          exact False.elim (hsig ⟨r, hr, hrs⟩)
    · intro hlt
      omega

private theorem drain_classify_le_crd
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (D : Config n) (p : Nat)
    (hp : p < A.gap)
    (hnotDone : ¬ CRDone A D)
    (hfloor : ∀ q, q < p →
      (D (advance ring A.left q)).bullet = (0 : Fin 3)) :
    ∃ mode',
      CRModeHolds A D mode' ∧
      crRank A mode' ≤ crRank A (.drain p) := by
  classical
  have hnotDeleted : ¬ EndpointDeleted A D := by
    intro h
    exact hnotDone (.inl h)
  by_cases hbullet : SectorHasBullet A D
  · cases hs : (D A.left).signalB with
    | false =>
        obtain ⟨p', hleast⟩ :=
          leastBulletOffset_exists_crd ring A D hbullet
        have hge : p ≤ p' := by
          by_cases hlt : p' < p
          · have hz := hfloor p' hlt
            exact False.elim (hleast.2.1 hz)
          · omega
        refine ⟨.drain p', ⟨hnotDeleted, hs, hleast⟩, ?_⟩
        simp only [crRank]
        omega
    | true =>
        refine ⟨.repair, ⟨hnotDeleted, hs, hbullet⟩, ?_⟩
        simp only [crRank]
        omega
  · have hfree :=
      sectorBulletFree_of_not_hasBullet_crd A D hbullet
    cases hs : (D A.left).signalB with
    | false =>
        obtain ⟨q, hfront⟩ :=
          returnFront_exists_crd ring A D hs
        refine ⟨.ret q, ⟨hnotDeleted, hfree, hs, hfront⟩, ?_⟩
        simp only [crRank]
        have hqle := hfront.2.1
        omega
    | true =>
        exact False.elim
          (hnotDone (.inr ⟨hs, hfree⟩))

private theorem drain_classify_lt_crd
    {n : Nat} (ring : DirectedRing n)
    {C0 : Config n} (A : SectorFrame ring C0)
    (D : Config n) (p : Nat)
    (hp : p < A.gap)
    (hnotDone : ¬ CRDone A D)
    (hfloor : ∀ q, q ≤ p →
      (D (advance ring A.left q)).bullet = (0 : Fin 3)) :
    ∃ mode',
      CRModeHolds A D mode' ∧
      crRank A mode' < crRank A (.drain p) := by
  classical
  have hnotDeleted : ¬ EndpointDeleted A D := by
    intro h
    exact hnotDone (.inl h)
  by_cases hbullet : SectorHasBullet A D
  · cases hs : (D A.left).signalB with
    | false =>
        obtain ⟨p', hleast⟩ :=
          leastBulletOffset_exists_crd ring A D hbullet
        have hgt : p < p' := by
          by_cases hle : p' ≤ p
          · have hz := hfloor p' hle
            exact False.elim (hleast.2.1 hz)
          · omega
        refine ⟨.drain p', ⟨hnotDeleted, hs, hleast⟩, ?_⟩
        simp only [crRank]
        omega
    | true =>
        refine ⟨.repair, ⟨hnotDeleted, hs, hbullet⟩, ?_⟩
        simp only [crRank]
        omega
  · have hfree :=
      sectorBulletFree_of_not_hasBullet_crd A D hbullet
    cases hs : (D A.left).signalB with
    | false =>
        obtain ⟨q, hfront⟩ :=
          returnFront_exists_crd ring A D hs
        refine ⟨.ret q, ⟨hnotDeleted, hfree, hs, hfront⟩, ?_⟩
        simp only [crRank]
        have hqle := hfront.2.1
        omega
    | true =>
        exact False.elim
          (hnotDone (.inr ⟨hs, hfree⟩))

private theorem repair_outgoing_step_crd
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    (hint : CRInteriorFollowers A C)
    (hmode : CRModeHolds A C .repair) :
    CRDone A (stepE ring C A.left) ∨
      ∃ p,
        CRModeHolds A (stepE ring C A.left) (.sweep p) := by
  have hleft := left_alive_crd A C hmode.1
  have hright := right_alive_crd A C hmode.1
  have hsig := hmode.2.1
  by_cases hdel :
      EndpointDeleted A (stepE ring C A.left)
  · exact .inl (.inl hdel)
  · have hrightD :=
      right_alive_crd A (stepE ring C A.left) hdel
    have hstepL := stepE_initiator_crd ring C A.left
    by_cases hgap : A.gap = 1
    · have hrn :
          ring.rightNeighbor A.left = A.right := by
        calc
          ring.rightNeighbor A.left =
              advance ring A.left (0 + 1) := by
                simpa using advance_succ_crd ring A.left 0
          _ = advance ring A.left A.gap := by rw [hgap]
          _ = A.right := A.right_eq
      have hstepR := stepE_responder_crd ring C A.left
        (rightNeighbor_ne_self_crd ring
          (sector_one_lt_n_crd A) A.left)
      have hout :
          (PPL.Elim.rowE
            (C A.left) (C (ring.rightNeighbor A.left))).2.leader =
              true := by
        rw [← hstepR, hrn]
        exact hrightD
      have hrightRn :
          (C (ring.rightNeighbor A.left)).leader = true := by
        rw [hrn]
        exact hright
      have hsRow :=
        rowE_fire_out_leader_survive_signal_crd
          (C A.left) (C (ring.rightNeighbor A.left))
          hleft hsig hrightRn hout
      have hsD :
          (stepE ring C A.left A.left).signalB = true := by
        rw [hstepL]
        exact hsRow
      have hbD :
          (stepE ring C A.left A.left).bullet = (0 : Fin 3) := by
        rw [hstepL]
        exact rowE_left_bullet_zero_crd _ _
      have hfreeD :
          SectorBulletFree A (stepE ring C A.left) := by
        unfold SectorBulletFree
        intro q hq
        have hq1 : q < 1 := by rw [← hgap]; exact hq
        have hq0 : q = 0 := by omega
        subst q
        simpa using hbD
      exact .inl (.inr ⟨hsD, hfreeD⟩)
    · have hgap2 : 1 < A.gap := by
        have := A.gap_pos
        omega
      have hrn :
          ring.rightNeighbor A.left =
            advance ring A.left 1 := by
        simpa using advance_succ_crd ring A.left 0
      have hrl :
          (C (ring.rightNeighbor A.left)).leader = false := by
        rw [hrn]
        exact hint 1 (by omega) hgap2
      have hp :=
        rowE_fire_out_follower_crd
          (C A.left) (C (ring.rightNeighbor A.left))
          hleft hsig hrl
      have hstepR := stepE_responder_crd ring C A.left
        (rightNeighbor_ne_self_crd ring
          (sector_one_lt_n_crd A) A.left)
      rw [hrn] at hstepR
      have hb0 :
          (stepE ring C A.left A.left).bullet = (0 : Fin 3) := by
        rw [hstepL]
        exact hp.1
      have hs0 :
          (stepE ring C A.left A.left).signalB = false := by
        rw [hstepL]
        exact hp.2.1
      have hb1 :
          (stepE ring C A.left
            (advance ring A.left 1)).bullet ≠ (0 : Fin 3) := by
        rw [hstepR]
        exact hp.2.2.1
      have hs1 :
          (stepE ring C A.left
            (advance ring A.left 1)).signalB = false := by
        rw [hstepR]
        exact hp.2.2.2
      have hleast :
          LeastBulletOffset A (stepE ring C A.left) 1 := by
        refine ⟨hgap2, hb1, ?_⟩
        intro q hq
        have hq0 : q = 0 := by omega
        subst q
        simpa using hb0
      have hz :
          ZeroSignalThrough A (stepE ring C A.left) 1 := by
        intro q hq
        have hcases : q = 0 ∨ q = 1 := by omega
        rcases hcases with hq0 | hq1
        · subst q
          simpa using hs0
        · subst q
          exact hs1
      exact .inr ⟨1, ⟨hdel, hs0, hleast, hz⟩⟩

private theorem repair_incoming_step_crd
    {n : Nat} {ring : DirectedRing n} {C0 : Config n}
    (A : SectorFrame ring C0) (C : Config n)
    (hmode : CRModeHolds A C .repair) :
    CRDone A (stepE ring C (crIncomingEdge A)) ∨
      ∃ p,
        CRModeHolds
          A (stepE ring C (crIncomingEdge A)) (.sweep p) := by
  have hleft := left_alive_crd A C hmode.1
  have hsig := hmode.2.1
  by_cases hdel :
      EndpointDeleted A (stepE ring C (crIncomingEdge A))
  · exact .inl (.inl hdel)
  · have hleftD :=
      left_alive_crd A
        (stepE ring C (crIncomingEdge A)) hdel
    have hresp := stepE_responder_crd ring C (crIncomingEdge A)
      (rightNeighbor_ne_self_crd ring
        (sector_one_lt_n_crd A) (crIncomingEdge A))
    rw [incoming_responds_crd A] at hresp
    have hout :
        (PPL.Elim.rowE
          (C (crIncomingEdge A)) (C A.left)).2.leader = true := by
      rw [← hresp]
      exact hleftD
    have hp :=
      rowE_ready_incoming_survive_crd
        (C (crIncomingEdge A)) (C A.left)
        hleft hsig hout
    have hb0 :
        (stepE ring C (crIncomingEdge A) A.left).bullet =
          (1 : Fin 3) := by
      rw [hresp]
      exact hp.1
    have hs0 :
        (stepE ring C (crIncomingEdge A) A.left).signalB =
          false := by
      rw [hresp]
      exact hp.2.2
    have hb0ne :
        (stepE ring C (crIncomingEdge A) A.left).bullet ≠
          (0 : Fin 3) := by
      rw [hb0]
      decide
    have hleast :
        LeastBulletOffset
          A (stepE ring C (crIncomingEdge A)) 0 := by
      refine ⟨A.gap_pos, ?_, ?_⟩
      · simpa using hb0ne
      · intro q hq
        omega
    have hz :
        ZeroSignalThrough
          A (stepE ring C (crIncomingEdge A)) 0 := by
      intro q hq
      have hq0 : q = 0 := by omega
      subst q
      simpa using hs0
    exact .inr ⟨0, ⟨hdel, hs0, hleast, hz⟩⟩

/-- The arbitrary initial drain stage satisfies the corrected one-step CR law. -/
theorem crDrainStep : CRDrainStepSpec := by
  classical
  intro n ring C0 A C p _hPB hInterior hmode
  have hleft := left_alive_crd A C hmode.1
  have hs0 := hmode.2.1
  have hleast := hmode.2.2
  have hp := hleast.1
  have hzero := hleast.2.2
  constructor
  · intro e
    have hfloor :=
      drain_prefix_step_crd
        A C p e hp hleft hInterior hs0 hzero
    by_cases hdone : CRDone A (stepE ring C e)
    · exact .inl hdone
    · exact .inr
        (drain_classify_le_crd
          ring A (stepE ring C e) p hp hdone hfloor)
  · let e := advance ring A.left p
    have hfloor0 :=
      drain_prefix_step_crd
        A C p e hp hleft hInterior hs0 hzero
    have hpzero :
        (stepE ring C e (advance ring A.left p)).bullet =
          (0 : Fin 3) := by
      dsimp [e]
      rw [stepE_initiator_crd]
      exact rowE_left_bullet_zero_crd _ _
    have hfloor :
        ∀ q, q ≤ p →
          (stepE ring C e
            (advance ring A.left q)).bullet = (0 : Fin 3) := by
      intro q hqp
      by_cases hq : q = p
      · subst q
        exact hpzero
      · apply hfloor0 q
        omega
    by_cases hdone : CRDone A (stepE ring C e)
    · exact .inl hdone
    · exact .inr
        (drain_classify_lt_crd
          ring A (stepE ring C e) p hp hdone hfloor)

/-- The one-source-firing repair stage satisfies the corrected one-step CR law. -/
theorem crRepairStep : CRRepairStepSpec := by
  classical
  intro n ring C0 A C _hPB hInterior hmode
  constructor
  · intro e
    by_cases hout : e = A.left
    · subst e
      rcases repair_outgoing_step_crd A C hInterior hmode with
        hdone | ⟨p, hsweep⟩
      · exact .inl hdone
      · refine .inr ⟨.sweep p, hsweep, ?_⟩
        have hp : p < A.gap := hsweep.2.2.1.1
        simp only [crRank]
        omega
    · by_cases hin : e = crIncomingEdge A
      · subst e
        rcases repair_incoming_step_crd A C hmode with
          hdone | ⟨p, hsweep⟩
        · exact .inl hdone
        · refine .inr ⟨.sweep p, hsweep, ?_⟩
          have hp : p < A.gap := hsweep.2.2.1.1
          simp only [crRank]
          omega
      · have hsource :=
          source_step_eq_other_crd A C e hout hin
        have hs :
            (stepE ring C e A.left).signalB = true := by
          rw [hsource]
          exact hmode.2.1
        by_cases hdel :
            EndpointDeleted A (stepE ring C e)
        · exact .inl (.inl hdel)
        · by_cases hbullet :
            SectorHasBullet A (stepE ring C e)
          · refine .inr
              ⟨.repair, ⟨hdel, hs, hbullet⟩, ?_⟩
            simp only [crRank]
            exact Nat.le_refl _
          · have hfree :=
              sectorBulletFree_of_not_hasBullet_crd
                A (stepE ring C e) hbullet
            exact .inl (.inr ⟨hs, hfree⟩)
  · rcases repair_outgoing_step_crd A C hInterior hmode with
      hdone | ⟨p, hsweep⟩
    · exact .inl hdone
    · refine .inr ⟨.sweep p, hsweep, ?_⟩
      have hp : p < A.gap := hsweep.2.2.1.1
      simp only [crRank]
      omega

end PPL.Convergence.LDLocal

#print axioms PPL.Convergence.LDLocal.crDrainStep
#print axioms PPL.Convergence.LDLocal.crRepairStep
