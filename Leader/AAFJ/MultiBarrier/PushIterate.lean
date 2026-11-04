import Leader.AAFJ.MultiBarrier.PushOne
import Leader.AAFJ.MultiBarrier.GappedSixHit
import Leader.Wu.Safety.NoCheckBirthConditionTwoGeometry

set_option autoImplicit false

namespace AAFJPK.OriginalPushIter

open BarrierAlgebra
open OriginalNonbarrierWord
open PPLLNoCheckBirthConditionTwoGeometry

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

private theorem cwDist_pos_of_ne
    {n : Nat} (ring : DirectedRing n) {a b : Fin n} (hne : a ≠ b) :
    0 < cwDist ring a b := by
  apply Nat.pos_of_ne_zero
  intro hd
  have hp := cwPos_cwDist ring a b
  rw [hd, cwPos_zero] at hp
  exact hne hp

private theorem cwDist_rightNeighbor_left
    {n : Nat} (ring : DirectedRing n) {a b : Fin n}
    (hd : 1 < cwDist ring a b) :
    cwDist ring (ring.rightNeighbor a) b + 1 = cwDist ring a b := by
  let d := cwDist ring a b
  have hdlt : d < n := cwDist_lt ring a b
  have hpos : cwPos ring a d = b := cwPos_cwDist ring a b
  have hgt : 1 < d := by simpa [d] using hd
  have hw : cwPos ring (ring.rightNeighbor a) (d - 1) = b := by
    rw [cwPos_rightNeighbor]
    have h : d - 1 + 1 = d := by omega
    simpa [h] using hpos
  have hc := cwPos_bounded_unique ring (ring.rightNeighbor a) b
    (d - 1) (by omega) hw
  dsimp [d] at hc ⊢
  omega

private theorem exactTwo_count
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (a b : Fin n)
    (hs : ExactTwoBarrierSupport hk ring C a b) :
    barrierCount hk ring (labelsOf C) = 2 := by
  have hp :
      (barrierSupport hk ring (labelsOf C)).Perm [a, b] := by
    apply (List.perm_ext_iff_of_nodup
      (barrierSupport_nodup hk ring (labelsOf C))
      (by simp [hs.1])).2
    intro e
    rw [mem_barrierSupport_iff]
    simpa using hs.2 e
  change (barrierSupport hk ring (labelsOf C)).length = 2
  simpa using hp.length_eq

private theorem reach_aux
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (C : Fin n → State k) (q r : Fin n) (d : Nat)
    (hd : cwDist ring q r = d)
    (hs : ExactTwoBarrierSupport hk ring C q r) :
    ∃ w a,
      w.length ≤ 4 * (d - 1) ∧
      ring.rightNeighbor a = r ∧
      ExactTwoBarrierSupport hk ring (rawRun hk ring C w) a r := by
  induction d generalizing C q with
  | zero =>
      have hp := cwPos_cwDist ring q r
      rw [hd, cwPos_zero] at hp
      exact (hs.1 hp).elim
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
        refine ⟨[], q, ?_, hqr, ?_⟩
        · simp
        · simpa [rawRun] using hs
      · have hgt : 1 < cwDist ring q r := by
          rw [hd]
          omega
        have hsep : ring.rightNeighbor q ≠ r := by
          intro h
          have hpos : cwPos ring q 1 = r := by
            calc
              cwPos ring q 1 = ring.rightNeighbor q := by
                simpa using (cwPos_succ ring q 0)
              _ = r := h
          have hu := cwPos_bounded_unique ring q r 1 (by omega) hpos
          rw [hd] at hu
          omega
        have hp :=
          AAFJPK.OriginalPushOne.exactTwo_push_one
            hk ring hn3 C q r hs hsep
        let p := AAFJPK.OriginalPushOne.pushWord hk ring C q
        let D := rawRun hk ring C p
        have hpLen : p.length ≤ 4 := by simpa [p] using hp.1
        have hsD :
            ExactTwoBarrierSupport hk ring D (ring.rightNeighbor q) r := by
          simpa [D, p] using hp.2
        have hdec := cwDist_rightNeighbor_left ring hgt
        have hdD : cwDist ring (ring.rightNeighbor q) r = d := by
          rw [hd] at hdec
          omega
        obtain ⟨w, a, hw, ha, hsA⟩ :=
          ih D (ring.rightNeighbor q) hdD hsD
        refine ⟨p ++ w, a, ?_, ha, ?_⟩
        · simp only [List.length_append]
          omega
        · rw [rawRun_append]
          simpa [D, p] using hsA

private theorem reach_adjacent
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (C : Fin n → State k) (q r : Fin n)
    (hs : ExactTwoBarrierSupport hk ring C q r) :
    ∃ w a,
      w.length ≤ 4 * (n - 2) ∧
      ring.rightNeighbor a = r ∧
      ExactTwoBarrierSupport hk ring (rawRun hk ring C w) a r := by
  have hdlt := cwDist_lt ring q r
  have hdpos := cwDist_pos_of_ne ring hs.1
  obtain ⟨w, a, hw, ha, hsA⟩ :=
    reach_aux hk ring hn3 C q r (cwDist ring q r) rfl hs
  refine ⟨w, a, ?_, ha, hsA⟩
  omega

theorem exactTwo_eventual_gappedSix_drop
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (C : Fin n → State k) (q r : Fin n)
    (hs : ExactTwoBarrierSupport hk ring C q r) :
    ∃ pre a b c,
      pre.length ≤ 4 * (n - 2) ∧
      ring.rightNeighbor a = b ∧
      ring.rightNeighbor b = c ∧
      ExactTwoBarrierSupport hk ring (rawRun hk ring C pre) a b ∧
      (pre ++ [a, b, a, b, c, b]).length ≤ 4 * (n - 2) + 6 ∧
      barrierCount hk ring
          (labelsOf (rawRun hk ring C (pre ++ [a, b, a, b, c, b]))) <
        barrierCount hk ring (labelsOf C) := by
  obtain ⟨pre, a, hpre, har, hsA⟩ :=
    reach_adjacent hk ring hn3 C q r hs
  let D := rawRun hk ring C pre
  let b := r
  let c := ring.rightNeighbor b
  have hab : ring.rightNeighbor a = b := by simpa [b] using har
  have hbc : ring.rightNeighbor b = c := rfl
  have hsD : ExactTwoBarrierSupport hk ring D a b := by
    simpa [D, b] using hsA
  have hg :=
    AAFJPK.OriginalGappedSix.gapped_six_hit_drops_of_exact_adjacent
      hk ring hn3 D a b c [] [] [] [] [] []
      hab hbc hsD.2 (by trivial) (by trivial) (by trivial)
      (by trivial) (by trivial) (by trivial)
  have hdrop :
      barrierCount hk ring
          (labelsOf (rawRun hk ring D [a, b, a, b, c, b])) <
        barrierCount hk ring (labelsOf D) := by
    simpa [AAFJPK.OriginalGappedSix.gappedService6,
      AAFJPK.OriginalGappedThree.gapHit, rawRun] using hg
  have hcount :
      barrierCount hk ring (labelsOf D) =
        barrierCount hk ring (labelsOf C) :=
    (exactTwo_count hk ring D a b hsD).trans
      (exactTwo_count hk ring C q r hs).symm
  have hdropC :
      barrierCount hk ring
          (labelsOf (rawRun hk ring D [a, b, a, b, c, b])) <
        barrierCount hk ring (labelsOf C) := by
    rw [← hcount]
    exact hdrop
  refine ⟨pre, a, b, c, hpre, hab, hbc, hsD, ?_, ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · rw [rawRun_append]
    simpa [D] using hdropC

/-- A literal deterministic word of the advertised total length strictly
decreases the charged-barrier count from every exact-two configuration. -/
theorem exactTwo_strict_drop_word
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n) (hn3 : 2 < n)
    (C : Fin n → State k) (q r : Fin n)
    (hs : ExactTwoBarrierSupport hk ring C q r) :
    ∃ word : List (Fin n),
      word.length ≤ 4 * (n - 2) + 6 ∧
      barrierCount hk ring (labelsOf (rawRun hk ring C word)) <
        barrierCount hk ring (labelsOf C) := by
  obtain ⟨pre, a, b, c, _, _, _, _, hlen, hdrop⟩ :=
    exactTwo_eventual_gappedSix_drop hk ring hn3 C q r hs
  exact ⟨pre ++ [a, b, a, b, c, b], hlen, hdrop⟩

#print axioms exactTwo_eventual_gappedSix_drop
#print axioms exactTwo_strict_drop_word

end AAFJPK.OriginalPushIter
