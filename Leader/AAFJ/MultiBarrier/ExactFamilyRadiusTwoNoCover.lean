import Leader.AAFJ.Protocol
import Leader.AAFJ.BarrierAlgebra
import Leader.AAFJ.NonbarrierWord

set_option autoImplicit false
set_option Elab.async false

namespace AAFJPK.ExactFamilyRadiusTwoNoCover

open AAFJPK
open AAFJPK.BarrierAlgebra
open AAFJPK.OriginalNonbarrierWord

/-!
The accepted adjacent-contact cylinder starts only after a charged edge and
its immediate successor are both barriers.  This file records a smaller
provider-searched exact-family counterfamily for the radius-two version of
that proposed cover.  Every configuration below has two barriers, but no
charged edge has another charged edge at distance one or two.  The displayed
words are still literal `rawRun` words and strictly lower barrier count.

The configurations use all control bits false.  Thus the one-letter words
`[1]`, `[1]`, and `[0]` are actual provider-replayed stutters for `n=6,8,10`
respectively; they witness nonempty exact-source traces without changing the
counterpattern.  The endpoint and no-cover claims below are kernel reductions.
-/

private def q {k : Nat} (label : Fin k) : State k :=
  { bullet := false, leader := false, label := label,
    probe := false, phase := false }

private def labels6 (i : Fin 6) : Fin 4 :=
  if i = 0 then 0 else if i = 1 then 0 else if i = 2 then 1 else
  if i = 3 then 2 else if i = 4 then 2 else 3

private def labels8 (i : Fin 8) : Fin 3 :=
  if i = 0 then 0 else if i = 1 then 0 else if i = 2 then 1 else
  if i = 3 then 2 else if i = 4 then 0 else if i = 5 then 0 else
  if i = 6 then 1 else 2

private def labels10 (i : Fin 10) : Fin 3 :=
  if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 0 else
  if i = 3 then 1 else if i = 4 then 2 else if i = 5 then 0 else
  if i = 6 then 1 else if i = 7 then 0 else if i = 8 then 1 else 2

def C6 : Fin 6 → State 4 := fun i => q (labels6 i)
def C8 : Fin 8 → State 3 := fun i => q (labels8 i)
def C10 : Fin 10 → State 3 := fun i => q (labels10 i)

def ring6 : DirectedRing 6 := ⟨by decide⟩
def ring8 : DirectedRing 8 := ⟨by decide⟩
def ring10 : DirectedRing 10 := ⟨by decide⟩

private theorem hk3 : 0 < 3 := by decide
private theorem hk4 : 0 < 4 := by decide

private theorem selector6 : AAFJExactN.leastNonDivisor 6 = 4 := by
  decide

private theorem selector8 : AAFJExactN.leastNonDivisor 8 = 3 := by
  decide

private theorem selector10 : AAFJExactN.leastNonDivisor 10 = 3 := by
  decide

theorem exactFamily6_protocol :
    AAFJExactFamily.protocolFor 6 (by decide) =
      AAFJPK.protocol 4 hk4 := by
  have h := AAFJExactFamily.protocolFor_large
    (n := 6) (by decide) (by decide) (by decide)
  simpa only [selector6] using h

theorem exactFamily8_protocol :
    AAFJExactFamily.protocolFor 8 (by decide) =
      AAFJPK.protocol 3 hk3 := by
  have h := AAFJExactFamily.protocolFor_large
    (n := 8) (by decide) (by decide) (by decide)
  simpa only [selector8] using h

theorem exactFamily10_protocol :
    AAFJExactFamily.protocolFor 10 (by decide) =
      AAFJPK.protocol 3 hk3 := by
  have h := AAFJExactFamily.protocolFor_large
    (n := 10) (by decide) (by decide) (by decide)
  simpa only [selector10] using h

def RadiusTwoChargedPair {n k : Nat} (hk : 0 < k)
    (ring : DirectedRing n) (C : Fin n → State k) : Prop :=
  ∃ a, BarrierAt hk ring (labelsOf C) a ∧
    (BarrierAt hk ring (labelsOf C) (ring.rightNeighbor a) ∨
      BarrierAt hk ring (labelsOf C)
        (ring.rightNeighbor (ring.rightNeighbor a)))

theorem C6_two_barriers :
    barrierCount hk4 ring6 (labelsOf C6) = 2 := by
  decide +kernel

theorem C8_two_barriers :
    barrierCount hk3 ring8 (labelsOf C8) = 2 := by
  decide +kernel

theorem C10_two_barriers :
    barrierCount hk3 ring10 (labelsOf C10) = 2 := by
  decide +kernel

theorem C6_no_radius_two_pair :
    ¬ RadiusTwoChargedPair hk4 ring6 C6 := by
  have h1 : ¬ BarrierAt hk4 ring6 (labelsOf C6) (1 : Fin 6) := by
    decide +kernel
  have h2 : ¬ BarrierAt hk4 ring6 (labelsOf C6) (2 : Fin 6) := by
    decide +kernel
  have h4 : ¬ BarrierAt hk4 ring6 (labelsOf C6) (4 : Fin 6) := by
    decide +kernel
  have h5 : ¬ BarrierAt hk4 ring6 (labelsOf C6) (5 : Fin 6) := by
    decide +kernel
  have hr3 : ring6.rightNeighbor (3 : Fin 6) = 4 := by
    decide +kernel
  have hr4 : ring6.rightNeighbor (4 : Fin 6) = 5 := by
    decide +kernel
  rintro ⟨a, ha, hnear⟩
  have hc : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 := by
    omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · have hn : BarrierAt hk4 ring6 (labelsOf C6) (1 : Fin 6) ∨
        BarrierAt hk4 ring6 (labelsOf C6) (2 : Fin 6) := by
      simpa [ring6, DirectedRing.rightNeighbor] using hnear
    exact hn.elim h1 h2
  · exact h1 ha
  · exact h2 ha
  · have hn : BarrierAt hk4 ring6 (labelsOf C6) (4 : Fin 6) ∨
        BarrierAt hk4 ring6 (labelsOf C6) (5 : Fin 6) := by
      simpa [hr3, hr4] using hnear
    exact hn.elim h4 h5
  · exact h4 ha
  · exact h5 ha

theorem C8_no_radius_two_pair :
    ¬ RadiusTwoChargedPair hk3 ring8 C8 := by
  have h1 : ¬ BarrierAt hk3 ring8 (labelsOf C8) (1 : Fin 8) := by
    decide +kernel
  have h2 : ¬ BarrierAt hk3 ring8 (labelsOf C8) (2 : Fin 8) := by
    decide +kernel
  have h3 : ¬ BarrierAt hk3 ring8 (labelsOf C8) (3 : Fin 8) := by
    decide +kernel
  have h5 : ¬ BarrierAt hk3 ring8 (labelsOf C8) (5 : Fin 8) := by
    decide +kernel
  have h6 : ¬ BarrierAt hk3 ring8 (labelsOf C8) (6 : Fin 8) := by
    decide +kernel
  have h7 : ¬ BarrierAt hk3 ring8 (labelsOf C8) (7 : Fin 8) := by
    decide +kernel
  have hr4 : ring8.rightNeighbor (4 : Fin 8) = 5 := by
    decide +kernel
  have hr5 : ring8.rightNeighbor (5 : Fin 8) = 6 := by
    decide +kernel
  rintro ⟨a, ha, hnear⟩
  have hc : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨
      a = 6 ∨ a = 7 := by
    omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hn : BarrierAt hk3 ring8 (labelsOf C8) (1 : Fin 8) ∨
        BarrierAt hk3 ring8 (labelsOf C8) (2 : Fin 8) := by
      simpa [ring8, DirectedRing.rightNeighbor] using hnear
    exact hn.elim h1 h2
  · exact h1 ha
  · exact h2 ha
  · exact h3 ha
  · have hn : BarrierAt hk3 ring8 (labelsOf C8) (5 : Fin 8) ∨
        BarrierAt hk3 ring8 (labelsOf C8) (6 : Fin 8) := by
      simpa [hr4, hr5] using hnear
    exact hn.elim h5 h6
  · exact h5 ha
  · exact h6 ha
  · exact h7 ha

theorem C10_no_radius_two_pair :
    ¬ RadiusTwoChargedPair hk3 ring10 C10 := by
  have h0 : ¬ BarrierAt hk3 ring10 (labelsOf C10) (0 : Fin 10) := by
    decide +kernel
  have h2 : ¬ BarrierAt hk3 ring10 (labelsOf C10) (2 : Fin 10) := by
    decide +kernel
  have h3 : ¬ BarrierAt hk3 ring10 (labelsOf C10) (3 : Fin 10) := by
    decide +kernel
  have h4 : ¬ BarrierAt hk3 ring10 (labelsOf C10) (4 : Fin 10) := by
    decide +kernel
  have h5 : ¬ BarrierAt hk3 ring10 (labelsOf C10) (5 : Fin 10) := by
    decide +kernel
  have h7 : ¬ BarrierAt hk3 ring10 (labelsOf C10) (7 : Fin 10) := by
    decide +kernel
  have h8 : ¬ BarrierAt hk3 ring10 (labelsOf C10) (8 : Fin 10) := by
    decide +kernel
  have h9 : ¬ BarrierAt hk3 ring10 (labelsOf C10) (9 : Fin 10) := by
    decide +kernel
  have hr6 : ring10.rightNeighbor (6 : Fin 10) = 7 := by
    decide +kernel
  have hr7 : ring10.rightNeighbor (7 : Fin 10) = 8 := by
    decide +kernel
  rintro ⟨a, ha, hnear⟩
  have hc : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨
      a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 := by
    omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0 ha
  · have hn : BarrierAt hk3 ring10 (labelsOf C10) (2 : Fin 10) ∨
        BarrierAt hk3 ring10 (labelsOf C10) (3 : Fin 10) := by
      simpa [ring10, DirectedRing.rightNeighbor] using hnear
    exact hn.elim h2 h3
  · exact h2 ha
  · exact h3 ha
  · exact h4 ha
  · exact h5 ha
  · have hn : BarrierAt hk3 ring10 (labelsOf C10) (7 : Fin 10) ∨
        BarrierAt hk3 ring10 (labelsOf C10) (8 : Fin 10) := by
      simpa [hr6, hr7] using hnear
    exact hn.elim h7 h8
  · exact h7 ha
  · exact h8 ha
  · exact h9 ha

def drop6 : List (Fin 6) := [0, 1, 0, 1, 2, 1, 2, 3, 2]
def drop8 : List (Fin 8) :=
  [0, 1, 0, 1, 2, 1, 2, 3, 2, 3, 4, 3]
def drop10 : List (Fin 10) :=
  [1, 2, 1, 2, 3, 2, 3, 4, 3, 4, 5, 4, 5, 6, 5]

theorem C6_drop_word_actual :
    barrierCount hk4 ring6
        (labelsOf (rawRun hk4 ring6 C6 drop6)) <
      barrierCount hk4 ring6 (labelsOf C6) := by
  decide +kernel

theorem C8_drop_word_actual :
    barrierCount hk3 ring8
        (labelsOf (rawRun hk3 ring8 C8 drop8)) <
      barrierCount hk3 ring8 (labelsOf C8) := by
  decide +kernel

theorem C10_drop_word_actual :
    barrierCount hk3 ring10
        (labelsOf (rawRun hk3 ring10 C10 drop10)) <
      barrierCount hk3 ring10 (labelsOf C10) := by
  decide +kernel

theorem C6_replayed_stutter_word :
    rawRun hk4 ring6 C6 [1] = C6 := by
  funext i
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
    omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem C8_replayed_stutter_word :
    rawRun hk3 ring8 C8 [1] = C8 := by
  funext i
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
      i = 6 ∨ i = 7 := by
    omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

theorem C10_replayed_stutter_word :
    rawRun hk3 ring10 C10 [0] = C10 := by
  funext i
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
      i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by
    omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

theorem radius_two_counterfamily :
    (barrierCount hk4 ring6 (labelsOf C6) = 2 ∧
      ¬ RadiusTwoChargedPair hk4 ring6 C6 ∧
      barrierCount hk4 ring6
          (labelsOf (rawRun hk4 ring6 C6 drop6)) < 2) ∧
    (barrierCount hk3 ring8 (labelsOf C8) = 2 ∧
      ¬ RadiusTwoChargedPair hk3 ring8 C8 ∧
      barrierCount hk3 ring8
          (labelsOf (rawRun hk3 ring8 C8 drop8)) < 2) ∧
    (barrierCount hk3 ring10 (labelsOf C10) = 2 ∧
      ¬ RadiusTwoChargedPair hk3 ring10 C10 ∧
      barrierCount hk3 ring10
          (labelsOf (rawRun hk3 ring10 C10 drop10)) < 2) := by
  exact ⟨⟨C6_two_barriers, C6_no_radius_two_pair, C6_drop_word_actual⟩,
    ⟨C8_two_barriers, C8_no_radius_two_pair, C8_drop_word_actual⟩,
    ⟨C10_two_barriers, C10_no_radius_two_pair, C10_drop_word_actual⟩⟩

#print axioms exactFamily6_protocol
#print axioms exactFamily8_protocol
#print axioms exactFamily10_protocol
#print axioms C6_two_barriers
#print axioms C8_two_barriers
#print axioms C10_two_barriers
#print axioms C6_no_radius_two_pair
#print axioms C8_no_radius_two_pair
#print axioms C10_no_radius_two_pair
#print axioms C6_drop_word_actual
#print axioms C8_drop_word_actual
#print axioms C10_drop_word_actual
#print axioms C6_replayed_stutter_word
#print axioms C8_replayed_stutter_word
#print axioms C10_replayed_stutter_word
#print axioms radius_two_counterfamily

end AAFJPK.ExactFamilyRadiusTwoNoCover
