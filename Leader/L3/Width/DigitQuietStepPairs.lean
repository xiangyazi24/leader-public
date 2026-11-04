import Leader.L3.Width.DigitQuietStepPairsPosition
import Leader.L3.Width.DigitQuietStepLayout
import Leader.L3.Width.DigitQuietStepRootLayout
import Leader.L3.Width.DigitQuietStepDigits

/-!
# The pairs clause of the quiet class is closed under every letter

`pairs_step`: for a state `S` of the class with `WFixedRoot` and `QWord`, every pair of complete
blocks of `phiD ring S e` satisfies the pair scan.  The machine enters through the glue lemmas
(`glue_left`, `glue_right`, `glue_other`), the digits through `digits_kept`, the leader through the
closure of `WFixedRoot`; the combinatorics is `pq_after_letter`.

Consumer: `WidthDigitQuietStepLaw` (`quietStepLawProved`).
-/

namespace L3.DigitQuiet

open L3
open L3.AcceptedReceipts

set_option autoImplicit false

variable {c : Compiled} {n : Nat}

/-- Two lane views with the same leader, marker, digit and lane fields are equal.  Consumer:
`pairs_step`. -/
theorem view_ext {v w : DigitLaneView c} (h1 : v.leader = w.leader) (h2 : v.marker = w.marker)
    (h3 : v.digit = w.digit) (h4 : LaneFieldsEq v w) : v = w := by
  cases v
  cases w
  obtain ⟨a1, a2, a3, a4, a5⟩ := h4
  simp_all

/-- The leader flag of the site at position `q`, from the root hypothesis alone.  Consumer:
`pairs_step`. -/
theorem leader_of_rootFixed (ring : DirectedRing n) (root : Fin n) (T : Fin n → ProjD c)
    (h : ∀ i : Fin n, (T i).word.native.l = true ↔ i = root) {q : Nat} (hq : q < n) :
    (T (digitSite ring root q)).word.native.l = decide (q = 0) := by
  by_cases h0 : q = 0
  · subst h0
    have := (h (digitSite ring root 0)).mpr rfl
    simp [this]
  · have hne : ¬ (digitSite ring root q = root) := by
      intro he
      have : digitSite ring root q = digitSite ring root 0 := he
      exact h0 (digitSite_inj ring root hq (by omega) this)
    cases hl : (T (digitSite ring root q)).word.native.l
    · simp [h0]
    · exact absurd ((h _).mp hl) hne

/-- The lane views read the record fields (both lanes).  Consumer: `pairs_step`. -/
theorem view_leader (ring : DirectedRing n) (root : Fin n) (S : Fin n → ProjD c) (lane : DigitLane)
    (q : Nat) : (view ring root S lane q).leader = (S (digitSite ring root q)).word.native.l := by
  cases lane <;> rfl

/-- Consumer: `pairs_step`. -/
theorem view_marker (ring : DirectedRing n) (root : Fin n) (S : Fin n → ProjD c) (lane : DigitLane)
    (q : Nat) : (view ring root S lane q).marker = (S (digitSite ring root q)).word.beta := by
  cases lane <;> rfl

/-- Consumer: `pairs_step`. -/
theorem view_digit (ring : DirectedRing n) (root : Fin n) (S : Fin n → ProjD c) (lane : DigitLane)
    (q : Nat) : (view ring root S lane q).digit = (S (digitSite ring root q)).top.d := by
  cases lane <;> rfl

/-- **The pairs clause is closed under every letter.**  Consumer: `quietStepLawProved`. -/
theorem pairs_step (hn : 5 ≤ n) (ring : DirectedRing n) (root : Fin n) (first : Nat)
    (S : Fin n → ProjD (compileAdvice (ceilLogTwo n)))
    (hQ : WidthDigitQuiet ring root first S) (hF : WFixedRoot ring root (wordProjection S))
    (hW : QWord ring (wordProjection S)) (e : Fin n) :
    QuietPairs ring root first (phiD ring S e) := by
  intro lane j hj
  have hR2 := digitSpan_ge_two hn
  have hne : ring.rightNeighbor e ≠ e := rightNeighbor_ne ring (by omega) e
  have hdig := digits_kept hn ring root first S hQ hF hW e
  have hroot' := quiet_rootFixed_step hn ring root first S hF e
  obtain ⟨p, hp, hpe⟩ := digitSite_surj ring root e
  subst hpe
  have hpq := hQ.pairs lane j hj
  rw [pairQuiet_eq_PQ] at hpq ⊢
  have hD : (fun h => ((phiD ring S (digitSite ring root p))
      (digitSite ring root (first + j * digitSpan (compileAdvice (ceilLogTwo n)) + h))).top.d) =
      (fun h => (S (digitSite ring root (first + j * digitSpan (compileAdvice (ceilLogTwo n)) + h))).top.d) :=
    funext (fun h => hdig _)
  rw [hD]
  have hf2 := hQ.layout.1
  -- block facts
  have e2 : (j + 2) * digitSpan (compileAdvice (ceilLogTwo n)) =
      (j + 1) * digitSpan (compileAdvice (ceilLogTwo n)) + digitSpan (compileAdvice (ceilLogTwo n)) := by
    rw [show j + 2 = (j + 1) + 1 from rfl, Nat.succ_mul]
  have hblkA := block_complete ring root first S hQ (by omega) j (by omega)
  have hblkB := block_complete ring root first S hQ (by omega) (j + 1) hj
  have hdw := values_digitwise ring root S hQ.values (first + j * digitSpan (compileAdvice (ceilLogTwo n)))
    (first + (j + 1) * digitSpan (compileAdvice (ceilLogTwo n))) hblkA (by
      rw [Nat.add_mul, Nat.one_mul]; omega) hblkB
  refine pq_after_letter lane (digitSpan (compileAdvice (ceilLogTwo n))) first n j hR2 hf2 hj
    (fun q => view ring root S lane q) (fun q => view ring root (phiD ring S (digitSite ring root p)) lane q)
    _ p hp ?_ ?_ ?_ ?_ ?_ ?_ ?_ hpq
  · intro q hq
    rw [view_leader]; exact leader_at ring root first S hQ hq
  · intro q h0 hq
    rw [view_marker]; exact marker_at ring root first S hQ h0 hq
  · intro h hh
    rw [view_digit]
  · intro h hh
    rw [view_digit]; exact hdw h hh
  · intro q h0 hq hqp hqp1
    have hie : digitSite ring root q ≠ digitSite ring root p := fun he =>
      hqp (digitSite_inj ring root hq hp he)
    have hij : digitSite ring root q ≠ ring.rightNeighbor (digitSite ring root p) := by
      intro he
      have h1 : ring.rightNeighbor (digitSite ring root p) = digitSite ring root (p + 1) := rfl
      rw [h1] at he
      by_cases hp1 : p + 1 < n
      · exact hqp1 (digitSite_inj ring root hq hp1 he)
      · have hpn : p + 1 = n := by omega
        rw [hpn, digitSite_n] at he
        have : digitSite ring root q = digitSite ring root 0 := he
        exact absurd (digitSite_inj ring root hq (by omega) this) (by omega)
    exact glue_other ring S (digitSite ring root p) _ hie hij lane
  · intro hp1
    obtain ⟨hf, hm⟩ := glue_left ring S hW (digitSite ring root p) hne lane
    refine view_ext ?_ ?_ ?_ hf
    · show _ = (view ring root S lane p).leader
      rw [view_leader, view_leader, leader_of_rootFixed ring root _ hroot' hp,
        leader_of_rootFixed ring root S (fun i => hQ.rootFixed i) hp]
    · exact hm
    · show _ = (view ring root S lane p).digit
      rw [view_digit, view_digit]
      exact hdig _
  · intro hp1
    obtain ⟨hf, hm⟩ := glue_right ring S hW (digitSite ring root p) hne lane
    refine view_ext ?_ ?_ ?_ hf
    · show _ = (view ring root S lane (p + 1)).leader
      rw [view_leader, view_leader, leader_of_rootFixed ring root _ hroot' hp1,
        leader_of_rootFixed ring root S (fun i => hQ.rootFixed i) hp1]
    · exact hm
    · show _ = (view ring root S lane (p + 1)).digit
      rw [view_digit, view_digit]
      exact hdig _

end L3.DigitQuiet

#print axioms L3.DigitQuiet.pairs_step
