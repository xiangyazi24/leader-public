import Leader.PPL.Elim.TransferCandidateHit

/-!
# YSM21 repair transfer: one-block 23/24 contraction

The imported File-2 module already reserves the parent-namespace name
`PPL.Convergence.LDTransfer.one_block_contract_mass` as a `def ... : Prop`.
Because this task forbids editing existing files, this file cannot redeclare a
theorem at that exact fully-qualified name.  The proved headline is therefore
`PPL.Convergence.LDTransfer.Lemma3.one_block_contract_mass`, with the same
conclusion as the plan.

Exactly one structural obligation is isolated below.  It is the piece the
plan itself identifies as genuinely new: a cyclic enumeration of the current
leaders, its positive gap vector, the corresponding frozen candidate
`TripleFrame`s, and the pathwise multiplicity-three incidence estimate.
Everything after that producer is proved here by finite natural-number double
counting on one common scheduler block.  No independence premise occurs.
-/

namespace PPL.Convergence.LDTransfer

open PPL.Convergence.LDLocal
open PPL.Convergence.LDTransferArith
open K2ArbitraryElimination.FiniteAccounting
open LeaderCountDyadicTail
open FiniteUniformStoppingTree
open Classical

set_option autoImplicit false
set_option Elab.async false

def candidateBit {s : Nat} (n : Nat)
    (g : Fin s → Nat) (r : Fin s) : Nat :=
  if shortCandidate n g r = true then 1 else 0

noncomputable def candidateHitBit
    {n s : Nat} {ring : DirectedRing n}
    {C : PPL.Convergence.LDLocal.Config n}
    (g : Fin s → Nat)
    (frames : Fin s → TripleFrame ring C)
    (r : Fin s)
    (D : PPL.Convergence.LDLocal.Config n) : Nat := by
  classical
  exact
    if shortCandidate n g r = true then
      if TaggedDeleted (frames r) D then 1 else 0
    else 0

noncomputable def candidateHitCount
    {n s : Nat} {ring : DirectedRing n}
    {C : PPL.Convergence.LDLocal.Config n}
    (g : Fin s → Nat)
    (frames : Fin s → TripleFrame ring C)
    (D : PPL.Convergence.LDLocal.Config n) : Nat :=
  (List.ofFn (fun r => candidateHitBit g frames r D)).sum

noncomputable def contractionGoodBit
    {n s : Nat} {ring : DirectedRing n}
    {C : PPL.Convergence.LDLocal.Config n}
    (g : Fin s → Nat)
    (frames : Fin s → TripleFrame ring C)
    (D : PPL.Convergence.LDLocal.Config n) : Nat := by
  classical
  exact
    if candidateCount n g ≤ 4 * candidateHitCount g frames D
    then 1 else 0

/-- The only isolated obligation.

It packages the block-start cyclic leader list:
positive gaps summing to n, one frozen TripleFrame for each cyclic anchor, the
two frame gaps matching the two successive entries of the gap vector, and the
pathwise fact that successful candidate indicators charge deleted block-start
leaders with multiplicity at most three.

The last clause is exactly X(D) ≤ 3*(s-leaderCount D), restricted to endpoints
whose leader count has not increased.  Row E supplies that restriction during
the common block. -/
def CandidateGeometrySpec
    {n s : Nat} (ring : DirectedRing n)
    (C : PPL.Convergence.LDLocal.Config n) : Prop :=
  ∃ g : Fin s → Nat,
    ∃ frames : Fin s → TripleFrame ring C,
      (∀ r, 1 ≤ g r) ∧
      (List.ofFn g).sum = n ∧
      (∀ r,
        (frames r).a = g r ∧
        (frames r).b = g (cyclicNext r)) ∧
      ∀ D : PPL.Convergence.LDLocal.Config n,
        PPL.Elim.leaderCount D ≤ s →
          candidateHitCount g frames D ≤
            3 * (s - PPL.Elim.leaderCount D)

theorem wordSum_ofFn_sum
    {S : Type} {n k : Nat}
    (next : S → Fin n → S)
    (f : Fin k → S → Nat)
    (x : S) (T : Nat) :
    wordSum next
        (fun y => (List.ofFn (fun i => f i y)).sum) x T =
      (List.ofFn (fun i => wordSum next (f i) x T)).sum := by
  induction k with
  | zero =>
      simp [wordSum_const]
  | succ k ih =>
      simp only [List.ofFn_succ, List.sum_cons]
      rw [wordSum_add]
      exact congrArg (wordSum next (f 0) x T + ·)
        (ih (fun i => f i.succ))

theorem candidateBit_sum_eq_candidateCount
    {s n : Nat} (g : Fin s → Nat) :
    (List.ofFn (fun r => candidateBit n g r)).sum =
      candidateCount n g := by
  unfold candidateCount
  apply ofFn_sum_eq
  intro r
  cases h : shortCandidate n g r <;>
    simp [candidateBit, h]

theorem candidateHitCount_le_candidateCount
    {n s : Nat} {ring : DirectedRing n}
    {C : PPL.Convergence.LDLocal.Config n}
    (g : Fin s → Nat)
    (frames : Fin s → TripleFrame ring C)
    (D : PPL.Convergence.LDLocal.Config n) :
    candidateHitCount g frames D ≤ candidateCount n g := by
  rw [← candidateBit_sum_eq_candidateCount g]
  unfold candidateHitCount
  apply ofFn_sum_le
  intro r
  cases h : shortCandidate n g r with
  | false =>
      simp [candidateHitBit, candidateBit, h]
  | true =>
      by_cases hd : TaggedDeleted (frames r) D
      · simp [candidateHitBit, candidateBit, h, hd]
      · simp [candidateHitBit, candidateBit, h, hd]

theorem candidateHit_wordSum_eq
    {S : Type} {n s : Nat}
    {ring : DirectedRing n}
    {C0 : PPL.Convergence.LDLocal.Config n}
    (next : S → Fin n → S)
    (project : S → PPL.Convergence.LDLocal.Config n)
    (g : Fin s → Nat)
    (frames : Fin s → TripleFrame ring C0)
    (x : S) (T : Nat) :
    wordSum next
        (fun y => candidateHitCount g frames (project y)) x T =
      (List.ofFn (fun r =>
        if shortCandidate n g r = true then
          wordSum next
            (fun y =>
              if TaggedDeleted (frames r) (project y)
              then 1 else 0) x T
        else 0)).sum := by
  classical
  unfold candidateHitCount
  rw [wordSum_ofFn_sum]
  apply ofFn_sum_eq
  intro r
  cases h : shortCandidate n g r with
  | false =>
      simp [candidateHitBit, h, wordSum_const]
  | true =>
      simp [candidateHitBit, h]

theorem candidate_hit_total_lower
    {c n s H : Nat}
    (hLD : LDStatement c) (hc : 1 ≤ c)
    (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : PPL.Convergence.LDLocal.Config n)
    (hPB : PPL.Elim.PB ring C)
    (hcount : PPL.Elim.leaderCount C = s)
    (hs : 2 ≤ s)
    (g : Fin s → Nat)
    (frames : Fin s → TripleFrame ring C)
    (hframe :
      ∀ r,
        (frames r).a = g r ∧
        (frames r).b = g (cyclicNext r))
    (hH : 16 * c * n * n ≤ s * H) :
    candidateCount n g * n ^ H ≤
      2 * wordSum (stepE ring)
        (candidateHitCount g frames) C H := by
  classical
  have hpoint :
      ∀ r : Fin s,
        n ^ H * candidateBit n g r ≤
          2 *
            (if shortCandidate n g r = true then
              hitMass (stepE ring)
                (TaggedDeleted (frames r)) C H
            else 0) := by
    intro r
    cases hr : shortCandidate n g r with
    | false =>
        simp [candidateBit, hr]
    | true =>
        have hspan0 :=
          lemma1_candidate_span g r hr
        rcases hframe r with ⟨ha, hb⟩
        have hspan :
            s * ((frames r).a + (frames r).b) ≤ 8 * n := by
          simpa [ha, hb] using hspan0
        have hh :=
          candidate_hit_common_block
            hLD hc hn ring C hPB hcount hs
            (frames r) hspan hH
        simpa [candidateBit, hr] using hh
  have hsum :=
    ofFn_sum_le
      (fun r : Fin s => n ^ H * candidateBit n g r)
      (fun r : Fin s =>
        2 *
          (if shortCandidate n g r = true then
            hitMass (stepE ring)
              (TaggedDeleted (frames r)) C H
          else 0))
      hpoint
  rw [ofFn_sum_mul_left, ofFn_sum_mul_left] at hsum
  rw [candidateBit_sum_eq_candidateCount] at hsum
  have hword :=
    candidateHit_wordSum_eq
      (stepE ring) (fun D => D) g frames C H
  unfold hitMass at hword
  calc
    candidateCount n g * n ^ H =
        n ^ H * candidateCount n g := Nat.mul_comm _ _
    _ ≤
        2 *
          (List.ofFn (fun r =>
            if shortCandidate n g r = true then
              wordSum (stepE ring)
                (fun D =>
                  if TaggedDeleted (frames r) D
                  then 1 else 0) C H
            else 0)).sum := hsum
    _ = 2 * wordSum (stepE ring)
          (candidateHitCount g frames) C H := by
      rw [hword]

theorem candidateHit_good_pathwise
    {n s : Nat} {ring : DirectedRing n}
    {C : PPL.Convergence.LDLocal.Config n}
    (g : Fin s → Nat)
    (frames : Fin s → TripleFrame ring C)
    (D : PPL.Convergence.LDLocal.Config n) :
    4 * candidateHitCount g frames D ≤
      candidateCount n g +
        3 * candidateCount n g *
          contractionGoodBit g frames D := by
  have hx :=
    candidateHitCount_le_candidateCount g frames D
  by_cases hg :
      candidateCount n g ≤
        4 * candidateHitCount g frames D
  · simp [contractionGoodBit, hg]
    omega
  · simp [contractionGoodBit, hg]
    omega

theorem contractionGood_mass
    {n s H : Nat} {ring : DirectedRing n}
    {C : PPL.Convergence.LDLocal.Config n}
    (g : Fin s → Nat)
    (frames : Fin s → TripleFrame ring C)
    (htotal :
      candidateCount n g * n ^ H ≤
        2 * wordSum (stepE ring)
          (candidateHitCount g frames) C H)
    (hmpos : 0 < candidateCount n g) :
    n ^ H ≤
      3 * wordSum (stepE ring)
        (contractionGoodBit g frames) C H := by
  have hpath :=
    K2ArbitraryElimination.FiniteAccounting.wordSum_mono
      (stepE ring)
      (fun D => 4 * candidateHitCount g frames D)
      (fun D =>
        candidateCount n g +
          3 * candidateCount n g *
            contractionGoodBit g frames D)
      (candidateHit_good_pathwise g frames) C H
  rw [wordSum_mul, wordSum_add,
      wordSum_const, wordSum_mul] at hpath
  have hpath' :
      4 * wordSum (stepE ring)
          (candidateHitCount g frames) C H ≤
        candidateCount n g * n ^ H +
          3 * (candidateCount n g *
            wordSum (stepE ring)
              (contractionGoodBit g frames) C H) := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      using hpath
  have hdouble :
      2 * (candidateCount n g * n ^ H) ≤
        4 * wordSum (stepE ring)
          (candidateHitCount g frames) C H := by
    calc
      2 * (candidateCount n g * n ^ H) ≤
          2 *
            (2 * wordSum (stepE ring)
              (candidateHitCount g frames) C H) :=
        Nat.mul_le_mul_left 2 htotal
      _ = 4 * wordSum (stepE ring)
          (candidateHitCount g frames) C H := by
        rw [← Nat.mul_assoc]
  have hcancel :
      candidateCount n g * n ^ H ≤
        3 * (candidateCount n g *
          wordSum (stepE ring)
            (contractionGoodBit g frames) C H) := by
    omega
  have hcancel' :
      candidateCount n g * n ^ H ≤
        candidateCount n g *
          (3 * wordSum (stepE ring)
            (contractionGoodBit g frames) C H) := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      using hcancel
  exact Nat.le_of_mul_le_mul_left hcancel' hmpos

theorem contractionGood_implies_contract
    {n s : Nat} {ring : DirectedRing n}
    {C : PPL.Convergence.LDLocal.Config n}
    (g : Fin s → Nat)
    (frames : Fin s → TripleFrame ring C)
    (D : PPL.Convergence.LDLocal.Config n)
    (hmhalf : s < 2 * candidateCount n g)
    (hinc :
      candidateHitCount g frames D ≤
        3 * (s - PPL.Elim.leaderCount D))
    (hcountD : PPL.Elim.leaderCount D ≤ s)
    (hgood :
      candidateCount n g ≤
        4 * candidateHitCount g frames D) :
    24 * PPL.Elim.leaderCount D < 23 * s := by
  omega

theorem contractionGood_mass_le_target
    {n s H : Nat} (ring : DirectedRing n)
    (C : PPL.Convergence.LDLocal.Config n)
    (hcount : PPL.Elim.leaderCount C = s)
    (g : Fin s → Nat)
    (frames : Fin s → TripleFrame ring C)
    (hmhalf : s < 2 * candidateCount n g)
    (hinc :
      ∀ D : PPL.Convergence.LDLocal.Config n,
        PPL.Elim.leaderCount D ≤ s →
          candidateHitCount g frames D ≤
            3 * (s - PPL.Elim.leaderCount D)) :
    wordSum (stepE ring)
        (contractionGoodBit g frames) C H ≤
      hitMass (stepE ring)
        (fun D => 24 * PPL.Elim.leaderCount D < 23 * s)
        C H := by
  classical
  have hclosed :
      ∀ D : PPL.Convergence.LDLocal.Config n, ∀ e : Fin n,
        PPL.Elim.leaderCount D ≤ s →
          PPL.Elim.leaderCount (stepE ring D e) ≤ s := by
    intro D e hD
    have hs0 := PPL.Elim.leaderCount_step_le ring D e
    have hs1 :
        PPL.Elim.leaderCount (stepE ring D e) ≤
          PPL.Elim.leaderCount D := by
      simpa [stepE] using hs0
    exact Nat.le_trans hs1 hD
  let targetBit :
      PPL.Convergence.LDLocal.Config n → Nat :=
    fun D =>
      @ite Nat
        (24 * PPL.Elim.leaderCount D < 23 * s)
        (Classical.propDecidable _)
        1 0
  have hpoint :
      ∀ D : PPL.Convergence.LDLocal.Config n,
        PPL.Elim.leaderCount D ≤ s →
          contractionGoodBit g frames D ≤ targetBit D := by
    intro D hD
    by_cases hg :
        candidateCount n g ≤
          4 * candidateHitCount g frames D
    · have ht :=
        contractionGood_implies_contract
          g frames D hmhalf (hinc D hD) hD hg
      simp [targetBit, contractionGoodBit, hg, ht]
    · simp [targetBit, contractionGoodBit, hg]
  have hmono :=
    LeaderCountDyadicTail.wordSum_mono_on
      (stepE ring)
      (fun D => PPL.Elim.leaderCount D ≤ s)
      hclosed
      (contractionGoodBit g frames)
      targetBit
      hpoint H C (by simpa [hcount])
  unfold hitMass
  exact hmono

namespace Lemma3

/-- Finite one-block 23/24 contraction, with the single currently unexported
cyclic-geometry/incidence producer made explicit. -/
theorem one_block_contract_mass
    {c : Nat}
    (hLD : LDStatement c) (hc : 1 ≤ c)
    {n s H : Nat} (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : PPL.Convergence.LDLocal.Config n)
    (hPB : PPL.Elim.PB ring C)
    (hcount : PPL.Elim.leaderCount C = s)
    (hs : 2 ≤ s)
    (hGeom : CandidateGeometrySpec (s := s) ring C)
    (hH : 16 * c * n * n ≤ s * H) :
    n ^ H ≤
      3 * hitMass (stepE ring)
        (fun D => 24 * PPL.Elim.leaderCount D < 23 * s)
        C H := by
  rcases hGeom with
    ⟨g, frames, hgpos, hsum, hframe, hinc⟩
  have hmhalf :
      s < 2 * candidateCount n g :=
    lemma1_candidates_gt_half g hs hgpos hsum
  have hmpos : 0 < candidateCount n g := by
    omega
  have htotal :=
    candidate_hit_total_lower
      hLD hc hn ring C hPB hcount hs
      g frames hframe hH
  have hgood :=
    contractionGood_mass
      g frames htotal hmpos
  have htarget :=
    contractionGood_mass_le_target
      (H := H) ring C hcount g frames hmhalf hinc
  exact Nat.le_trans hgood
    (Nat.mul_le_mul_left 3 htarget)

end Lemma3

/-- Adapter proving the Prop placeholder already exported by
LDTransferLemma2.lean. -/
theorem one_block_contract_mass_proved
    {c : Nat}
    (hLD : LDStatement c) (hc : 1 ≤ c)
    {n s H : Nat} (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : PPL.Convergence.LDLocal.Config n)
    (hPB : PPL.Elim.PB ring C)
    (hcount : PPL.Elim.leaderCount C = s)
    (hs : 2 ≤ s)
    (hGeom : CandidateGeometrySpec (s := s) ring C)
    (hH : 16 * c * n * n ≤ s * H) :
    PPL.Convergence.LDTransfer.one_block_contract_mass
      hLD hc hn ring C hPB hcount hs hH := by
  unfold PPL.Convergence.LDTransfer.one_block_contract_mass
  exact
    Lemma3.one_block_contract_mass
      hLD hc hn ring C hPB hcount hs hGeom hH

#print axioms PPL.Convergence.LDTransfer.wordSum_ofFn_sum
#print axioms PPL.Convergence.LDTransfer.candidateBit_sum_eq_candidateCount
#print axioms PPL.Convergence.LDTransfer.candidateHitCount_le_candidateCount
#print axioms PPL.Convergence.LDTransfer.candidateHit_wordSum_eq
#print axioms PPL.Convergence.LDTransfer.candidate_hit_total_lower
#print axioms PPL.Convergence.LDTransfer.candidateHit_good_pathwise
#print axioms PPL.Convergence.LDTransfer.contractionGood_mass
#print axioms PPL.Convergence.LDTransfer.contractionGood_implies_contract
#print axioms PPL.Convergence.LDTransfer.contractionGood_mass_le_target
#print axioms PPL.Convergence.LDTransfer.Lemma3.one_block_contract_mass
#print axioms PPL.Convergence.LDTransfer.one_block_contract_mass_proved

end PPL.Convergence.LDTransfer

