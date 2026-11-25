import Leader.L4.Height.Trial
import Leader.L4.Height.Model

namespace L4.Height

open Classical
open L4.Compiler.Native

/-- Raw execution of the logical chain is exactly `runRounds` on the
bit-vectors encoded by the scheduler letters. -/
theorem runWord_heightChain {m : Nat} (B : Nat) (hm : 0 < m)
    (s : Fin m → Snapshot) (w : List (Fin (2 ^ m))) :
    runWord (heightChain B hm) s w =
      runRounds B hm (w.map bitsOf) s := by
  induction w generalizing s with
  | nil =>
      rfl
  | cons e w ih =>
      change
        runWord (heightChain B hm)
            (logicalRound B hm (bitsOf e) s) w =
          runRounds B hm (w.map bitsOf)
            (logicalRound B hm (bitsOf e) s)
      exact ih (logicalRound B hm (bitsOf e) s)

/-- The generic stopped/raw bridge for a forward-closed target. -/
theorem stoppedRun_closed_iff_runWord_closed {α : Type} {n : Nat}
    (next : α → Fin n → α) (T : α → Prop)
    (hclosed : ∀ x e, T x → T (next x e))
    (x : α) (w : List (Fin n)) :
    T (stoppedRun next T x w) ↔ T (runWord next x w) := by
  exact stoppedRun_mem_iff_runWord_mem next T hclosed x w

/-- A target that is closed while an invariant holds remains true along a
raw word started inside that invariant. -/
theorem runWord_of_closed_under_invariant {α : Type} {n : Nat}
    (next : α → Fin n → α) (G T : α → Prop)
    (hG : ∀ x e, G x → G (next x e))
    (hT : ∀ x e, G x → T x → T (next x e)) :
    ∀ (x : α) (w : List (Fin n)),
      G x → T x → T (runWord next x w) := by
  intro x w
  induction w generalizing x with
  | nil =>
      intro hxG hxT
      simpa [runWord] using hxT
  | cons e w ih =>
      intro hxG hxT
      simpa [runWord] using
        (ih (next x e) (hG x e hxG) (hT x e hxG hxT))

/-- Stopped and raw endpoints agree on target membership when an invariant
is closed and the target is closed on invariant states. -/
theorem stoppedRun_mem_iff_runWord_mem_of_invariant
    {α : Type} {n : Nat}
    (next : α → Fin n → α) (G T : α → Prop)
    (hG : ∀ x e, G x → G (next x e))
    (hT : ∀ x e, G x → T x → T (next x e)) :
    ∀ (x : α) (w : List (Fin n)),
      G x →
        (T (stoppedRun next T x w) ↔ T (runWord next x w)) := by
  intro x w
  induction w generalizing x with
  | nil =>
      intro hxG
      rfl
  | cons e w ih =>
      intro hxG
      by_cases hxT : T x
      · have hrun : T (runWord next x (e :: w)) :=
          runWord_of_closed_under_invariant next G T hG hT
            x (e :: w) hxG hxT
        constructor
        · intro h
          exact hrun
        · intro h
          simpa [stoppedRun, hxT] using hxT
      · simpa [stoppedRun, runWord, hxT] using
          (ih (next x e) (hG x e hxG))

/-- Boundedness is closed under one letter of the logical chain. -/
theorem bounded_heightChain {m : Nat} (B : Nat) (hm : 0 < m)
    (hB : 0 < B) :
    ∀ (s : Fin m → Snapshot) (e : Fin (2 ^ m)),
      Bounded B s → Bounded B (heightChain B hm s e) := by
  intro s e hs
  change Bounded B (logicalRound B hm (bitsOf e) s)
  exact bounded_round B hm hB (bitsOf e) s hs

/-- Boundedness is preserved along every raw logical word. -/
theorem bounded_runWord_heightChain {m : Nat} (B : Nat)
    (hm : 0 < m) (hB : 0 < B)
    (s : Fin m → Snapshot) (w : List (Fin (2 ^ m)))
    (hs : Bounded B s) :
    Bounded B (runWord (heightChain B hm) s w) := by
  exact runWord_of_closed (heightChain B hm) (Bounded B)
    (bounded_heightChain B hm hB) s w hs

/-- Every positive cycle has at least one anchor. -/
theorem anchorCount_pos {m : Nat} (hm : 0 < m)
    (s : Fin m → Snapshot) :
    0 < anchorCount hm s := by
  obtain ⟨i, hi⟩ := anchor_exists hm s
  unfold anchorCount
  apply List.countP_pos_iff.mpr
  exact ⟨i, by simp, decide_eq_true hi⟩

/-- On bounded states, one anchor remains one anchor after one logical
letter. -/
theorem anchorCount_one_heightChain {m : Nat} (B : Nat)
    (hm : 0 < m) (hmb : m < B)
    (s : Fin m → Snapshot) (e : Fin (2 ^ m))
    (hs : Bounded B s) (hone : anchorCount hm s = 1) :
    anchorCount hm (heightChain B hm s e) = 1 := by
  change anchorCount hm (logicalRound B hm (bitsOf e) s) = 1
  have hmono := anchorCount_mono B hm hmb (bitsOf e) s hs
  have hpos := anchorCount_pos hm (logicalRound B hm (bitsOf e) s)
  omega

/-- From a bounded initial state, stopped and raw logical execution agree on
whether the endpoint has exactly one anchor. -/
theorem stoppedRun_single_anchor_iff_runWord_single_anchor
    {m : Nat} (B : Nat) (hm : 0 < m) (hmb : m < B)
    (s : Fin m → Snapshot) (hs : Bounded B s)
    (w : List (Fin (2 ^ m))) :
    anchorCount hm
        (stoppedRun (heightChain B hm)
          (fun y => anchorCount hm y = 1) s w) = 1 ↔
      anchorCount hm (runWord (heightChain B hm) s w) = 1 := by
  have hB : 0 < B := by omega
  exact stoppedRun_mem_iff_runWord_mem_of_invariant
    (heightChain B hm)
    (Bounded B)
    (fun y => anchorCount hm y = 1)
    (bounded_heightChain B hm hB)
    (fun y e hy hone =>
      anchorCount_one_heightChain B hm hmb y e hy hone)
    s w hs

/-- If a Boolean predicate has count one in a list, any two satisfying
members are equal. -/
theorem eq_of_countP_eq_one_of_mem {α : Type}
    (l : List α) (p : α → Bool) {a b : α}
    (ha : a ∈ l) (hb : b ∈ l)
    (hpa : p a) (hpb : p b)
    (hcount : l.countP p = 1) :
    a = b := by
  induction l generalizing a b with
  | nil =>
      simp at ha
  | cons c l ih =>
      simp only [List.mem_cons] at ha hb
      by_cases hpc : p c
      · have htail : l.countP p = 0 := by
          rw [List.countP_cons_of_pos hpc] at hcount
          omega
        have hnone : ∀ z ∈ l, ¬ p z :=
          List.countP_eq_zero.mp htail
        rcases ha with hca | ha
        · subst a
          rcases hb with hbc | hb
          · exact hbc.symm
          · exact False.elim ((hnone b hb) hpb)
        · exact False.elim ((hnone a ha) hpa)
      · rw [List.countP_cons_of_neg hpc] at hcount
        rcases ha with hca | ha
        · subst a
          exact False.elim (hpc hpa)
        · rcases hb with hbc | hb
          · subst b
            exact False.elim (hpc hpb)
          · exact ih ha hb hpa hpb hcount

/-- A named anchor is the unique anchor when the anchor count is one. -/
theorem only_anchor_of_count_one {m : Nat} (hm : 0 < m)
    (s : Fin m → Snapshot) (i : Fin m)
    (hone : anchorCount hm s = 1)
    (hi : IsAnchor hm s i) :
    ∀ j, IsAnchor hm s j ↔ j = i := by
  intro j
  constructor
  · intro hj
    have hc := hone
    unfold anchorCount at hc
    exact eq_of_countP_eq_one_of_mem
      (List.finRange m)
      (fun k => decide (IsAnchor hm s k))
      (a := j) (b := i)
      (by simp) (by simp)
      (decide_eq_true hj) (decide_eq_true hi) hc
  · intro hji
    subst j
    exact hi

/-- If the prefix endpoint has exactly one anchor, named `i`, then every
extension has the same unique anchor `i`. -/
theorem single_anchor_runWord_extension {m : Nat} (B : Nat)
    (hm : 0 < m) (hmb : m < B)
    (s : Fin m → Snapshot) (u : List (Fin (2 ^ m))) (i : Fin m)
    (hs : Bounded B s)
    (hone : anchorCount hm (runWord (heightChain B hm) s u) = 1)
    (hi : IsAnchor hm (runWord (heightChain B hm) s u) i) :
    ∀ (v : List (Fin (2 ^ m))) (j : Fin m),
      IsAnchor hm
          (runWord (heightChain B hm) s (u ++ v)) j ↔
        j = i := by
  have hB : 0 < B := by omega
  have hsu :
      Bounded B (runWord (heightChain B hm) s u) :=
    bounded_runWord_heightChain B hm hB s u hs
  have honly :
      ∀ j, IsAnchor hm (runWord (heightChain B hm) s u) j ↔ j = i :=
    only_anchor_of_count_one hm
      (runWord (heightChain B hm) s u) i hone hi
  intro v j
  rw [runWord_append]
  rw [runWord_heightChain]
  exact single_anchor_runRounds B hm hmb
    (v.map bitsOf)
    (runWord (heightChain B hm) s u) i hsu honly j

/-- At depth `2^19 * m`, logical singleton failure has word mass at most
one quarter of all scheduler words. -/
theorem logical_quarter {m B : Nat}
    (hm : 0 < m) (hmb : m < B)
    (s : Fin m → Snapshot) (hs : Bounded B s)
    (hcon : IIDExpectedHittingTimeAtMost
      (heightChain B hm)
      (fun y => anchorCount hm y = 1)
      s (122880 * m)) :
    4 * wordSum
        (fun u => if anchorCount hm
          (runWord (heightChain B hm) s u) = 1 then 0 else 1)
        (2 ^ 19 * m) ≤
      (2 ^ m) ^ (2 ^ 19 * m) := by
  let Q : Nat := 2 ^ 19 * m
  let bad : Nat :=
    wordSum
      (fun u => if anchorCount hm
        (runWord (heightChain B hm) s u) = 1 then 0 else 1) Q
  let stoppedBad : Nat :=
    wordSum
      (fun u =>
        @ite Nat
          (anchorCount hm
            (stoppedRun (heightChain B hm)
              (fun y => anchorCount hm y = 1) s u) = 1)
          (Classical.propDecidable _)
          0 1) Q
  let total : Nat := (2 ^ m) ^ Q
  change 4 * bad ≤ total
  have hsum : stoppedBad = bad := by
    unfold stoppedBad bad
    apply wordSum_congr_fun
    intro u
    have hiff :=
      stoppedRun_single_anchor_iff_runWord_single_anchor
        B hm hmb s hs u
    by_cases hr :
        anchorCount hm (runWord (heightChain B hm) s u) = 1
    · have hstop := hiff.mpr hr
      simp [hr, hstop]
    · have hstop :
          ¬ anchorCount hm
            (stoppedRun (heightChain B hm)
              (fun y => anchorCount hm y = 1) s u) = 1 := by
        intro h
        exact hr (hiff.mp h)
      simp [hr, hstop]
  have hmark :
      Q * stoppedBad ≤ (122880 * m) * (2 ^ m) ^ Q := by
    unfold stoppedBad
    exact markov_survivors
      (heightChain B hm)
      (fun y => anchorCount hm y = 1)
      s (122880 * m) Q hcon
  have hmarkBad :
      Q * bad ≤ (122880 * m) * total := by
    calc
      Q * bad = Q * stoppedBad :=
        congrArg (fun z : Nat => Q * z) hsum.symm
      _ ≤ (122880 * m) * total := by
        simpa [total] using hmark
  have hcoefBase :
      4 * 122880 ≤ (2 : Nat) ^ 19 := by
    decide
  have hcoef : 4 * (122880 * m) ≤ Q := by
    dsimp [Q]
    calc
      4 * (122880 * m) = (4 * 122880) * m :=
        (Nat.mul_assoc 4 122880 m).symm
      _ ≤ ((2 : Nat) ^ 19) * m :=
        Nat.mul_le_mul_right m hcoefBase
  have htwo : 0 < (2 : Nat) ^ 19 := by
    decide
  have hQ : 0 < Q := by
    dsimp [Q]
    exact Nat.mul_pos htwo hm
  have hscaled :
      (4 * bad) * Q ≤ (4 * (122880 * m)) * total := by
    calc
      (4 * bad) * Q = 4 * (Q * bad) := by
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ 4 * ((122880 * m) * total) :=
        Nat.mul_le_mul_left 4 hmarkBad
      _ = (4 * (122880 * m)) * total := by
        simp [Nat.mul_assoc]
  have hproduct : (4 * bad) * Q ≤ total * Q := by
    calc
      (4 * bad) * Q ≤ (4 * (122880 * m)) * total := hscaled
      _ ≤ Q * total := Nat.mul_le_mul_right total hcoef
      _ = total * Q := Nat.mul_comm _ _
  exact Nat.le_of_mul_le_mul_right hproduct hQ

#print axioms runWord_heightChain
#print axioms stoppedRun_closed_iff_runWord_closed
#print axioms runWord_of_closed_under_invariant
#print axioms stoppedRun_mem_iff_runWord_mem_of_invariant
#print axioms bounded_heightChain
#print axioms bounded_runWord_heightChain
#print axioms anchorCount_pos
#print axioms anchorCount_one_heightChain
#print axioms stoppedRun_single_anchor_iff_runWord_single_anchor
#print axioms eq_of_countP_eq_one_of_mem
#print axioms only_anchor_of_count_one
#print axioms single_anchor_runWord_extension
#print axioms logical_quarter

end L4.Height
