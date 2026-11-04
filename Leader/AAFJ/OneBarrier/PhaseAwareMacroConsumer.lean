import Leader.AAFJ.OneBarrier.PhaseAwareMacroRank

set_option autoImplicit false
set_option Elab.async false

namespace AAFJPK.OriginalPhaseAwareMacroConsumerV2

open BarrierAlgebra
open SingleBarrierSanitation
open OriginalNonbarrierWord
open OriginalUniqueLeaderCleanup
open OriginalMultipleLeaderOneBarrier
open OriginalOneBarrierComposition
open OriginalPhaseAwareMacroRank

/-!  The endpoint evidence is stored in the branch that consumes a public
reduction.  There is deliberately no standalone `EndpointMode D` alternative:
the relation below cannot be inhabited merely by classifying an arbitrary D. -/

inductive EndpointModeWitness {n k : Nat} (D : Fin n → State k) : Prop
  | zero (hzero : ZeroLeaders D)
  | unique (ell : Fin n) (hunique : UniqueLeaderAt D ell)
  | multiple (hmultiple : MultipleLeaders D)

theorem endpoint_mode_witness {n k : Nat} (D : Fin n → State k) :
    EndpointModeWitness D := by
  rcases one_barrier_mode_classification D with hz | hu | hm
  · exact EndpointModeWitness.zero hz
  · rcases hu with ⟨ell, hell⟩
    exact EndpointModeWitness.unique ell hell
  · exact EndpointModeWitness.multiple hm

inductive ClassifiedReduction {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n)
    (b : Fin n) (C : Fin n → State k)
    (b' : Fin n) (D : Fin n → State k) : Prop where
  | clean (mode : EndpointModeWitness D) (hclean : Clean hk ring D)
  | unique (mode : EndpointModeWitness D)
      (ell : Fin n) (hunique : UniqueLeaderAt D ell)
  | multiple (mode : EndpointModeWitness D)
      (hmultiple : MultipleLeaders D)
  | phi (mode : EndpointModeWitness D)
      (hphi : PhiAt ring b' D < PhiAt ring b C)
  | terminal (mode : EndpointModeWitness D)
      (hterm : ∃ ell,
        terminalRank ring b' ell D < terminalRank ring b ell C)
  | strict (mode : EndpointModeWitness D)
      (hlex : StrictLexDrop ring b C b' D)

theorem classified_of_public_reduction {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n)
    (b : Fin n) (C : Fin n → State k)
    (b' : Fin n) (D : Fin n → State k)
    (hred : OneBarrierReduction hk ring b C b' D) :
    ClassifiedReduction hk ring b C b' D := by
  have hmode : EndpointModeWitness D := endpoint_mode_witness D
  rcases hred with hclean | hu | hm | hphi | hterm | hlex
  · exact ClassifiedReduction.clean hmode hclean
  · rcases hu with ⟨ell, hell⟩
    exact ClassifiedReduction.unique hmode ell hell
  · exact ClassifiedReduction.multiple hmode hm
  · exact ClassifiedReduction.phi hmode hphi
  · exact ClassifiedReduction.terminal hmode hterm
  · exact ClassifiedReduction.strict hmode hlex

theorem classified_to_public_reduction {n k : Nat}
    (hk : 0 < k) (ring : DirectedRing n)
    (b : Fin n) (C : Fin n → State k)
    (b' : Fin n) (D : Fin n → State k)
    (hclassified : ClassifiedReduction hk ring b C b' D) :
    OneBarrierReduction hk ring b C b' D := by
  cases hclassified with
  | clean _ hclean => exact Or.inl hclean
  | unique _ ell hell => exact Or.inr (Or.inl ⟨ell, hell⟩)
  | multiple _ hmultiple => exact Or.inr (Or.inr (Or.inl hmultiple))
  | phi _ hphi => exact Or.inr (Or.inr (Or.inr (Or.inl hphi)))
  | terminal _ hterm =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hterm))))
  | strict _ hlex =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hlex))))

theorem terminal_rank_mode_split {n k : Nat}
    (ring : DirectedRing n) (b b' : Fin n)
    (C D : Fin n → State k)
    (mode : EndpointModeWitness D)
    (hterm : ∃ ell,
      terminalRank ring b' ell D < terminalRank ring b ell C) :
    (ZeroLeaders D ∧
        ∃ ell, terminalRank ring b' ell D < terminalRank ring b ell C) ∨
      ((∃ ell, UniqueLeaderAt D ell) ∧
        ∃ ell, terminalRank ring b' ell D < terminalRank ring b ell C) ∨
      (MultipleLeaders D ∧
        ∃ ell, terminalRank ring b' ell D < terminalRank ring b ell C) := by
  cases mode with
  | zero hzero =>
      exact Or.inl ⟨hzero, hterm⟩
  | unique ell hunique =>
      exact Or.inr (Or.inl ⟨⟨ell, hunique⟩, hterm⟩)
  | multiple hmultiple =>
      exact Or.inr (Or.inr ⟨hmultiple, hterm⟩)

theorem one_barrier_mode_step_classified
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (C : Fin n → State k) (b : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (hmode : OneBarrierMode C) :
    ∃ w b',
      w.length ≤ 8 * n ∧
      OneBarrierAt hk ring (rawRun hk ring C w) b' ∧
      ClassifiedReduction hk ring b C b'
        (rawRun hk ring C w) := by
  obtain ⟨w, b', hw, hB', hred⟩ :=
    one_barrier_mode_step hk ring hn3 hndvd C b hB hmode
  exact ⟨w, b', hw, hB', classified_of_public_reduction
    hk ring b C b' (rawRun hk ring C w) hred⟩

theorem classified_step_projects_to_public
    {n k : Nat} (hk : 0 < k) (ring : DirectedRing n)
    (hn3 : 3 ≤ n) (hndvd : ¬ k ∣ n)
    (C : Fin n → State k) (b : Fin n)
    (hB : OneBarrierAt hk ring C b)
    (hmode : OneBarrierMode C) :
    ∃ w b',
      w.length ≤ 8 * n ∧
      OneBarrierAt hk ring (rawRun hk ring C w) b' ∧
      OneBarrierReduction hk ring b C b' (rawRun hk ring C w) := by
  obtain ⟨w, b', hw, hB', hclassified⟩ :=
    one_barrier_mode_step_classified hk ring hn3 hndvd C b hB hmode
  exact ⟨w, b', hw, hB', classified_to_public_reduction
    hk ring b C b' (rawRun hk ring C w) hclassified⟩

instance instDecidableMultipleLeaders
    {n k : Nat} (C : Fin n → State k) :
    Decidable (MultipleLeaders C) := by
  unfold MultipleLeaders
  infer_instance

theorem strictlex_interface_counterexample :
    OneBarrierAt hk2 ring3 U1 2 ∧
      OneBarrierAt hk2 ring3 U2 2 ∧
      StrictLexDrop ring3 2 U1 2 U2 ∧
      ¬ AAFJPK.OriginalPhaseAwareMacroRank.Lex8
        (AAFJPK.OriginalPhaseAwareMacroRank.phaseAwareTuple8 U2)
        (AAFJPK.OriginalPhaseAwareMacroRank.phaseAwareTuple8 U1) := by
  have hphi :
      PhiAt ring3 (2 : Fin 3) U2 = PhiAt ring3 (2 : Fin 3) U1 := by
    decide +kernel
  have hM1 : MultipleLeaders U1 := by
    decide +kernel
  have hM2 : ¬ MultipleLeaders U2 := by
    decide +kernel
  have hlex : StrictLexDrop ring3 2 U1 2 U2 := by
    right
    refine ⟨hphi, ?_⟩
    simp [multiLeaderBit, hM1, hM2]
  exact ⟨by decide +kernel, by decide +kernel, hlex, by
    unfold AAFJPK.OriginalPhaseAwareMacroRank.Lex8
      AAFJPK.OriginalPhaseAwareMacroRank.tuple8List
    decide +kernel⟩

#print axioms endpoint_mode_witness
#print axioms classified_of_public_reduction
#print axioms classified_to_public_reduction
#print axioms terminal_rank_mode_split
#print axioms one_barrier_mode_step_classified
#print axioms classified_step_projects_to_public
#print axioms strictlex_interface_counterexample

end AAFJPK.OriginalPhaseAwareMacroConsumerV2
