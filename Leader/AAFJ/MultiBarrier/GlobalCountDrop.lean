import Leader.AAFJ.MultiBarrier.PushSuccessorFree
import Leader.Wu.Safety.NoCheckBirthConditionTwoGeometry

set_option autoImplicit false

namespace AAFJPK.GlobalBarrierCountDrop

open BarrierAlgebra
open OriginalNonbarrierWord
open OriginalPushOne
open PPLLNoCheckBirthConditionTwoGeometry

abbrev Supp {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) :=
  barrierSupport hk ring (labelsOf C)

def Rest {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (q : Fin n) : List (Fin n) :=
  (Supp hk ring C).erase q

structure ConsecutiveCharged {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k)
    (q r : Fin n) : Prop where
  q_charged : BarrierAt hk ring (labelsOf C) q
  r_charged : BarrierAt hk ring (labelsOf C) r
  ne : q ≠ r
  no_between :
    ∀ e, BarrierAt hk ring (labelsOf C) e →
      0 < cwDist ring q e →
      cwDist ring q e < cwDist ring q r → False

/-- Invariant carried by the iteration.  The support permutation is real,
not just a cardinality equality. -/
structure MovingFrame {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C0 : Fin n → State k) (q0 : Fin n)
    (D : Fin n → State k) (a r : Fin n) : Prop where
  consecutive : ConsecutiveCharged hk ring D a r
  fresh : a ∉ Rest hk ring C0 q0
  support_iff :
    ∀ e, e ∈ Supp hk ring D ↔
      e = a ∨ e ∈ Rest hk ring C0 q0
  support_perm :
    (Supp hk ring D).Perm (a :: Rest hk ring C0 q0)

private theorem rawRun_append
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (u v : List (Fin n)) :
    rawRun hk ring C (u ++ v) =
      rawRun hk ring (rawRun hk ring C u) v := by
  induction u generalizing C with
  | nil => rfl
  | cons e es ih =>
      simp only [List.cons_append, rawRun]
      exact ih ((protocol k hk).step ring C e)

private theorem cwDist_self
    {n : Nat} (ring : DirectedRing n) (a : Fin n) :
    cwDist ring a a = 0 := by
  exact (cwPos_bounded_unique ring a a 0 ring.hn
    (cwPos_zero ring a)).symm

private theorem cwDist_right_one
    {n : Nat} (ring : DirectedRing n) (hn2 : 1 < n) (a : Fin n) :
    cwDist ring a (ring.rightNeighbor a) = 1 := by
  have hp : cwPos ring a 1 = ring.rightNeighbor a := by
    simpa using cwPos_succ ring a 0
  exact (cwPos_bounded_unique ring a (ring.rightNeighbor a)
    1 (by omega) hp).symm

private theorem dist_drop
    {n : Nat} (ring : DirectedRing n) {a r : Fin n}
    (hd : 1 < cwDist ring a r) :
    cwDist ring (ring.rightNeighbor a) r + 1 =
      cwDist ring a r := by
  let d := cwDist ring a r
  have hpos := cwPos_cwDist ring a r
  have hw : cwPos ring (ring.rightNeighbor a) (d - 1) = r := by
    rw [cwPos_rightNeighbor]
    simpa [d, show d - 1 + 1 = d by omega] using hpos
  have hc := cwPos_bounded_unique ring (ring.rightNeighbor a) r
    (d - 1) (by have := cwDist_lt ring a r; omega) hw
  dsimp [d] at hc ⊢
  omega

private theorem initialFrame
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (q r : Fin n)
    (hc : ConsecutiveCharged hk ring C q r) :
    MovingFrame hk ring C q C q r := by
  have hS := barrierSupport_nodup hk ring (labelsOf C)
  have hq : q ∈ Supp hk ring C :=
    (mem_barrierSupport_iff hk ring (labelsOf C) q).2 hc.q_charged
  have hfresh : q ∉ Rest hk ring C q := by
    simpa [Rest] using (List.Nodup.not_mem_erase hS)
  have hiff : ∀ e, e ∈ Supp hk ring C ↔
      e = q ∨ e ∈ Rest hk ring C q := by
    intro e
    constructor
    · intro he
      by_cases heq : e = q
      · exact Or.inl heq
      · exact Or.inr <| by
          simpa [Rest] using
            (List.Nodup.mem_erase_iff hS).2 ⟨heq, he⟩
    · rintro (rfl | he)
      · exact hq
      · exact List.mem_of_mem_erase he
  have hcand : (q :: Rest hk ring C q).Nodup := by
    rw [List.nodup_cons]
    exact ⟨hfresh, by simpa [Rest] using hS.erase q⟩
  refine ⟨hc, hfresh, hiff, ?_⟩
  apply (List.perm_ext_iff_of_nodup hS hcand).2
  intro e
  simpa using hiff e

private theorem moveOne
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn2 : 1 < n)
    (C0 : Fin n → State k) (q0 : Fin n)
    (C : Fin n → State k) (q r : Fin n)
    (F : MovingFrame hk ring C0 q0 C q r)
    (hgap : 1 < cwDist ring q r) :
    let p := pushWord hk ring C q
    let D := rawRun hk ring C p
    p.length ≤ 4 ∧
      MovingFrame hk ring C0 q0 D (ring.rightNeighbor q) r := by
  let q1 := ring.rightNeighbor q
  have hd1 := cwDist_right_one ring hn2 q
  have hfree : ¬ BarrierAt hk ring (labelsOf C) q1 := by
    intro h
    exact F.consecutive.no_between q1 h
      (by simpa [q1, hd1])
      (by simpa [q1, hd1] using hgap)
  let p := pushWord hk ring C q
  let D := rawRun hk ring C p
  have hp := OriginalPushOne.push_one_of_successor_free
    hk ring hn2 C q F.consecutive.q_charged (by simpa [q1] using hfree)
  change p.length ≤ 4 ∧
    ∀ j, j ∈ Supp hk ring D ↔
      ∃ i, i ∈ Supp hk ring C ∧ redirectEdge ring q i = j at hp

  have hiff : ∀ j, j ∈ Supp hk ring D ↔
      j = q1 ∨ j ∈ Rest hk ring C0 q0 := by
    intro j
    constructor
    · intro hj
      obtain ⟨i, hi, hij⟩ := (hp.2 j).1 hj
      rcases (F.support_iff i).1 hi with rfl | hir
      · left
        simpa [redirectEdge, q1] using hij.symm
      · right
        have hiq : i ≠ q := by
          intro h; subst i; exact F.fresh hir
        have hie : i = j := by
          simpa [redirectEdge, hiq] using hij
        rw [← hie]
        exact hir
    · rintro (rfl | hj)
      · apply (hp.2 q1).2
        exact ⟨q, (F.support_iff q).2 (Or.inl rfl),
          by simp [redirectEdge, q1]⟩
      · have hjq : j ≠ q := by
          intro h; subst j; exact F.fresh hj
        apply (hp.2 j).2
        exact ⟨j, (F.support_iff j).2 (Or.inr hj),
          by simp [redirectEdge, hjq]⟩

  have hfresh : q1 ∉ Rest hk ring C0 q0 := by
    intro h
    have hm := (F.support_iff q1).2 (Or.inr h)
    exact hfree ((mem_barrierSupport_iff hk ring (labelsOf C) q1).1 hm)

  have hqr : q1 ≠ r := by
    intro h
    have hd1' : cwDist ring q r = 1 := by
      simpa [q1, h] using hd1
    rw [hd1'] at hgap
    omega

  have hq1 : BarrierAt hk ring (labelsOf D) q1 :=
    (mem_barrierSupport_iff hk ring (labelsOf D) q1).1
      ((hiff q1).2 (Or.inl rfl))
  have hrRest : r ∈ Rest hk ring C0 q0 := by
    have hm := (F.support_iff r).1
      ((mem_barrierSupport_iff hk ring (labelsOf C) r).2
        F.consecutive.r_charged)
    rcases hm with h | h
    · exact (F.consecutive.ne h.symm).elim
    · exact h
  have hr : BarrierAt hk ring (labelsOf D) r :=
    (mem_barrierSupport_iff hk ring (labelsOf D) r).1
      ((hiff r).2 (Or.inr hrRest))

  have hcons : ConsecutiveCharged hk ring D q1 r := by
    refine ⟨hq1, hr, hqr, ?_⟩
    intro e he hepos helt
    have hem := (mem_barrierSupport_iff hk ring (labelsOf D) e).2 he
    rcases (hiff e).1 hem with rfl | herest
    · rw [cwDist_self] at hepos
      omega
    · have heOld := (mem_barrierSupport_iff hk ring (labelsOf C) e).1
        ((F.support_iff e).2 (Or.inr herest))
      let t := cwDist ring q1 e
      have ht : t < cwDist ring q1 r := by simpa [t] using helt
      have hwalk : cwPos ring q (t + 1) = e := by
        calc
          cwPos ring q (t + 1) = cwPos ring q1 t := by
            simpa [q1] using (cwPos_rightNeighbor ring q t).symm
          _ = e := cwPos_cwDist ring q1 e
      have hcanon := cwPos_bounded_unique ring q e (t + 1)
        (by have := cwDist_lt ring q1 r; omega) hwalk
      have hdec := dist_drop ring hgap
      have hepos : 0 < cwDist ring q e := by
        rw [← hcanon]
        omega
      have helt' : cwDist ring q e < cwDist ring q r := by
        calc
          cwDist ring q e = t + 1 := hcanon.symm
          _ < cwDist ring q1 r + 1 := Nat.add_lt_add_right ht 1
          _ = cwDist ring q r := hdec
      exact F.consecutive.no_between e heOld hepos helt'

  have hrestN : (Rest hk ring C0 q0).Nodup := by
    simpa [Rest] using
      (barrierSupport_nodup hk ring (labelsOf C0)).erase q0
  have hcand : (q1 :: Rest hk ring C0 q0).Nodup := by
    rw [List.nodup_cons]
    exact ⟨hfresh, hrestN⟩
  have hperm : (Supp hk ring D).Perm
      (q1 :: Rest hk ring C0 q0) := by
    apply (List.perm_ext_iff_of_nodup
      (barrierSupport_nodup hk ring (labelsOf D)) hcand).2
    intro e
    simpa using hiff e
  exact ⟨hp.1, ⟨hcons, hfresh, hiff, hperm⟩⟩

private theorem reachAux
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn2 : 1 < n)
    (C0 : Fin n → State k) (q0 : Fin n)
    (C : Fin n → State k) (q r : Fin n) (d : Nat)
    (hd : cwDist ring q r = d)
    (F : MovingFrame hk ring C0 q0 C q r) :
    ∃ w a,
      w.length ≤ 4 * (d - 1) ∧
      ring.rightNeighbor a = r ∧
      MovingFrame hk ring C0 q0 (rawRun hk ring C w) a r := by
  induction d generalizing C q with
  | zero =>
      have hp := cwPos_cwDist ring q r
      rw [hd, cwPos_zero] at hp
      exact (F.consecutive.ne hp).elim
  | succ d ih =>
      by_cases h0 : d = 0
      · subst d
        have hp := cwPos_cwDist ring q r
        rw [hd] at hp
        have hqr : ring.rightNeighbor q = r := by
          calc
            ring.rightNeighbor q = cwPos ring q 1 := by
              simpa using (cwPos_succ ring q 0).symm
            _ = r := by simpa using hp
        exact ⟨[], q, by simp, hqr, by simpa [rawRun] using F⟩
      · have hgap : 1 < cwDist ring q r := by rw [hd]; omega
        have hm := moveOne hk ring hn2 C0 q0 C q r F hgap
        let p := pushWord hk ring C q
        let D := rawRun hk ring C p
        have hpLen : p.length ≤ 4 := by simpa [p, D] using hm.1
        have FD : MovingFrame hk ring C0 q0 D
            (ring.rightNeighbor q) r := by simpa [p, D] using hm.2
        have hdec := dist_drop ring hgap
        have hdD : cwDist ring (ring.rightNeighbor q) r = d := by
          rw [hd] at hdec
          omega
        obtain ⟨w, a, hw, ha, FA⟩ :=
          ih D (ring.rightNeighbor q) hdD FD
        refine ⟨p ++ w, a, ?_, ha, ?_⟩
        · simp only [List.length_append]
          omega
        · rw [rawRun_append]
          simpa [D, p] using FA

theorem consecutive_reach_adjacent
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn2 : 1 < n)
    (C : Fin n → State k) (q r : Fin n)
    (hc : ConsecutiveCharged hk ring C q r) :
    ∃ w a,
      w.length ≤ 4 * (cwDist ring q r - 1) ∧
      ring.rightNeighbor a = r ∧
      ConsecutiveCharged hk ring (rawRun hk ring C w) a r ∧
      (Supp hk ring (rawRun hk ring C w)).Perm
        (a :: Rest hk ring C q) ∧
      barrierCount hk ring (labelsOf (rawRun hk ring C w)) =
        barrierCount hk ring (labelsOf C) := by
  have F0 := initialFrame hk ring C q r hc
  obtain ⟨w, a, hw, ha, F⟩ :=
    reachAux hk ring hn2 C q C q r
      (cwDist ring q r) rfl F0
  refine ⟨w, a, hw, ha, F.consecutive, F.support_perm, ?_⟩
  have hq : q ∈ Supp hk ring C :=
    (mem_barrierSupport_iff hk ring (labelsOf C) q).2 hc.q_charged
  have hlen := F.support_perm.length_eq
  change (Supp hk ring (rawRun hk ring C w)).length =
    (Supp hk ring C).length
  rw [hlen]
  simp only [List.length_cons, Rest]
  rw [List.length_erase_of_mem hq]
  have hp : 0 < (Supp hk ring C).length := List.length_pos_of_mem hq
  omega

#print axioms consecutive_reach_adjacent

end AAFJPK.GlobalBarrierCountDrop
