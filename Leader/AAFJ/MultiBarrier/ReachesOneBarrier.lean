import Leader.AAFJ.MultiBarrier.GlobalCountDropAssembly

set_option autoImplicit false

namespace AAFJPK
namespace OriginalQualitative

open BarrierAlgebra
open SingleBarrierSanitation
open OriginalNonbarrierWord
open GlobalBarrierCountDropAssembly

/-! The finite qualitative bridge for the multi-barrier part of AAFJ Lemma 9.2.

The imported strict-drop theorem supplies a literal scheduler word whenever
more than one charged barrier is present. Strong induction packages those
words into an actual finite execution to one physical barrier. This file
does not claim the separate one-barrier sanitation route to `Clean`.
-/

/-- Every literal original-Protocol-6 word endpoint is reachable from its
starting configuration. -/
theorem rawRun_reachable
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k) (word : List (Fin n)) :
    PopulationProtocol.Reachable (protocol k hk) ring C
      (rawRun hk ring C word) := by
  induction word generalizing C with
  | nil =>
      exact PopulationProtocol.Reachable.refl
        (P := protocol k hk) (ring := ring) C
  | cons e es ih =>
      change
        PopulationProtocol.Reachable (protocol k hk) ring C
          (rawRun hk ring ((protocol k hk).step ring C e) es)
      exact
        (PopulationProtocol.OneStep.to_reachable
          (P := protocol k hk) (ring := ring)
          ⟨e, rfl⟩).trans
        (ih ((protocol k hk).step ring C e))

/-- Barrier count one contains a unique physical barrier edge, packaged in the
witness-carrying `OneBarrierAt` form needed by the sanitation stack. -/
theorem exists_oneBarrierAt_of_barrierCount_eq_one
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (C : Fin n → State k)
    (hcount : barrierCount hk ring (labelsOf C) = 1) :
    ∃ b : Fin n, OneBarrierAt hk ring C b := by
  unfold barrierCount at hcount
  rw [List.length_eq_one_iff] at hcount
  obtain ⟨b, hb⟩ := hcount
  refine ⟨b, ?_⟩
  intro e
  constructor
  · intro he
    have hemem :
        e ∈ barrierSupport hk ring (labelsOf C) :=
      (mem_barrierSupport_iff hk ring (labelsOf C) e).2 he
    rw [hb] at hemem
    simpa using hemem
  · intro heb
    subst e
    apply (mem_barrierSupport_iff hk ring (labelsOf C) b).1
    rw [hb]
    simp

/-- Strong-induction engine. The numeric parameter is only an induction
ceiling; the exported theorem contains no accumulated length bound. -/
private theorem reaches_oneBarrierAt_aux
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 2 < n) (hndvd : ¬ k ∣ n)
    (m : Nat) (C : Fin n → State k)
    (hcount_le : barrierCount hk ring (labelsOf C) ≤ m) :
    ∃ D : Fin n → State k, ∃ b : Fin n,
      PopulationProtocol.Reachable (protocol k hk) ring C D ∧
      OneBarrierAt hk ring D b := by
  induction m using Nat.strongRecOn generalizing C with
  | ind m ih =>
      have hpos :
          0 < barrierCount hk ring (labelsOf C) :=
        barrierCount_pos_of_not_dvd hk ring C hndvd

      by_cases hcount1 :
          barrierCount hk ring (labelsOf C) = 1
      · obtain ⟨b, hb⟩ :=
          exists_oneBarrierAt_of_barrierCount_eq_one
            hk ring C hcount1
        exact ⟨C, b,
          PopulationProtocol.Reachable.refl
            (P := protocol k hk) (ring := ring) C, hb⟩
      · have hcount_gt_one :
            1 < barrierCount hk ring (labelsOf C) := by
          omega

        obtain ⟨word, _hlen, hdrop⟩ :=
          barrierCount_gt_one_strict_drop_word
            hk ring hn3 C hcount_gt_one

        let D : Fin n → State k := rawRun hk ring C word

        have hdropD :
            barrierCount hk ring (labelsOf D) <
              barrierCount hk ring (labelsOf C) := by
          simpa [D] using hdrop

        have hDm :
            barrierCount hk ring (labelsOf D) < m :=
          Nat.lt_of_lt_of_le hdropD hcount_le

        obtain ⟨E, b, hDE, hb⟩ :=
          ih (barrierCount hk ring (labelsOf D)) hDm
            D (Nat.le_refl _)

        have hCD :
            PopulationProtocol.Reachable (protocol k hk) ring C D := by
          dsimp [D]
          exact rawRun_reachable hk ring C word

        exact ⟨E, b, hCD.trans hDE, hb⟩

/-- Qualitative coalescence: every original `P_k` configuration on a ring of
at least three agents reaches an exactly-one-barrier configuration when
`k ∤ n`. -/
theorem reaches_oneBarrierAt
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 2 < n) (hndvd : ¬ k ∣ n)
    (C : Fin n → State k) :
    ∃ D : Fin n → State k, ∃ b : Fin n,
      PopulationProtocol.Reachable (protocol k hk) ring C D ∧
      OneBarrierAt hk ring D b := by
  exact reaches_oneBarrierAt_aux
    hk ring hn3 hndvd
    (barrierCount hk ring (labelsOf C))
    C
    (Nat.le_refl _)

/-- Existential-predicate wrapper for consumers that do not need to retain the
physical barrier witness. -/
theorem reaches_oneBarrier
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 2 < n) (hndvd : ¬ k ∣ n)
    (C : Fin n → State k) :
    ∃ D : Fin n → State k,
      PopulationProtocol.Reachable (protocol k hk) ring C D ∧
      OneBarrier hk ring D := by
  obtain ⟨D, b, hCD, hb⟩ :=
    reaches_oneBarrierAt hk ring hn3 hndvd C
  exact ⟨D, hCD, ⟨b, hb⟩⟩

#print axioms rawRun_reachable
#print axioms exists_oneBarrierAt_of_barrierCount_eq_one
#print axioms reaches_oneBarrierAt
#print axioms reaches_oneBarrier

end OriginalQualitative
end AAFJPK
