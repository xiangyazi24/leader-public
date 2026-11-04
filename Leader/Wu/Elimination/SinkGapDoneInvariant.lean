import Leader.Wu.Elimination.SinkAbsorbStepShape


open LDSinkGapCleanup LDSinkKernelC LDSinkProtectedAbsorption PPLLRepair


namespace LDSinkGapDoneInvariant


set_option autoImplicit false


variable {n ψ : Nat}


/-- K2 completion omits the old R7 parked-bullet stopping case. -/
def GapDoneC (F : GapFrame n) (C : Fin n → AgentState ψ) : Prop :=
  CleanReady F C ∨ EndpointDeleted F C


/-- Removing the blocked disjunct from an R7 done state leaves exactly K2 done. -/
theorem GapDoneC_of_GapDone_not_blocked (F : GapFrame n)
    (C : Fin n → AgentState ψ) :
    GapDone F C → ¬ GapBlocked F C → GapDoneC F C := by
  intro hdone hnotBlocked
  rcases hdone with hclean | hrest
  · exact Or.inl hclean
  · rcases hrest with hdeleted | hblocked
    · exact Or.inr hdeleted
    · exact False.elim (hnotBlocked hblocked)


/-- `GapBlocked` alone does not state this tail.  If the old invariant is also
available, its live bullet at position one forces every sector signal to zero. -/
theorem gapBlocked_signal_tail (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ)
    (hblocked : GapBlocked F C) (hinv : GapInvariant hψ F C) :
    ∀ j, 1 ≤ j → j ≤ F.d →
      (C (F.pos j)).signal_B = (0 : Fin 2) := by
  intro j hj hjd
  have h1d : 1 ≤ F.d := Nat.le_trans hj hjd
  have hbullet :
      (C (F.pos 1)).bullet ≠ (0 : Fin 3) := by
    rw [hblocked.1]
    decide
  exact hinv.2.2.2 1 j (Nat.le_refl 1) h1d hbullet hj hjd


/-- A blocked invariant gap is neither clean-ready nor endpoint-deleted. -/
theorem gapBlocked_not_doneC (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) :
    GapBlocked F C → GapInvariant hψ F C → ¬ GapDoneC F C := by
  intro hblocked hinv hdoneC
  rcases hdoneC with hclean | hdeleted
  · have h1d : 1 ≤ F.d := by
      have hd := F.hd
      omega
    have hzero := hclean.2 1 (Nat.le_refl 1) h1d
    have hne : (2 : Fin 3) ≠ (0 : Fin 3) := by decide
    exact hne (hblocked.1.symm.trans hzero)
  · rcases hdeleted with hleft | hright
    · have hbad : (true : Bool) = false :=
        hinv.1.1.symm.trans hleft
      cases hbad
    · have hbad : (true : Bool) = false :=
        hinv.1.2.symm.trans hright
      cases hbad


/-- Exact R7 transport on the branch where C agrees with the old kernel.
Because `GapBlocked` does not itself include the four invariant conjuncts,
it remains an explicit third successor rather than being coerced to invariant. -/
theorem sinkStepC_off_guard_invariant_or_done (hψ : ψ > 0)
    (F : GapFrame n) (C : Fin n → AgentState ψ) (e : Fin n)
    (hinv : GapInvariant hψ F C) (hdoneC : ¬ GapDoneC F C)
    (hnotBlocked : ¬ GapBlocked F C)
    (hnotGuard :
      ¬ ProtectedGuard hψ (C e) (C (F.ring.rightNeighbor e))) :
    GapDoneC F (sinkStepC hψ F C e) ∨
      GapInvariant hψ F (sinkStepC hψ F C e) ∨
      GapBlocked F (sinkStepC hψ F C e) := by
  have hnotDone : ¬ GapDone F C := by
    intro hdone
    apply hdoneC
    exact GapDoneC_of_GapDone_not_blocked F C hdone hnotBlocked
  have heq := sinkStepC_eq_of_not_guard hψ F C e hnotGuard
  rcases sinkStep_invariant_or_done hψ F C hinv hnotDone e with
    hdone' | hinv'
  · rcases hdone' with hclean | hrest
    · exact Or.inl (Or.inl (by simpa only [heq] using hclean))
    · rcases hrest with hdeleted | hblocked
      · exact Or.inl (Or.inr (by simpa only [heq] using hdeleted))
      · exact Or.inr (Or.inr (by simpa only [heq] using hblocked))
  · exact Or.inr (Or.inl (by simpa only [heq] using hinv'))


/-- Exhaustive C-step invariant interface supported by C1 plus the checked R7
closure theorem.


The desired two-way theorem will follow once the last three alternatives are
discharged by transition-level C lemmas:
* an already-blocked invariant state is C-closed (or reaches `GapDoneC`),
* an R7 blocked successor still has the invariant signal tail, and
* a protected interaction touching this gap is the victim edge, so C1's exact
  protected shape preserves all four invariant conjuncts.


No `bulletTop = 1` hypothesis is introduced here. -/
theorem sinkStepC_invariant_or_done (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n) :
    GapInvariant hψ F C → ¬ GapDoneC F C →
      GapDoneC F (sinkStepC hψ F C e) ∨
      GapInvariant hψ F (sinkStepC hψ F C e) ∨
      GapBlocked F C ∨
      GapBlocked F (sinkStepC hψ F C e) ∨
      (ProtectedGuard hψ (C e) (C (F.ring.rightNeighbor e)) ∧
        ProtectedAbsorbShape (C e) (C (F.ring.rightNeighbor e))
          (sinkStepC hψ F C e e,
            sinkStepC hψ F C e (F.ring.rightNeighbor e)) ∧
        (∀ k : Fin n, k ≠ e → k ≠ F.ring.rightNeighbor e →
          sinkStepC hψ F C e k = C k)) := by
  intro hinv hdoneC
  by_cases hblocked : GapBlocked F C
  · exact Or.inr (Or.inr (Or.inl hblocked))
  by_cases hguard :
      ProtectedGuard hψ (C e) (C (F.ring.rightNeighbor e))
  · have hshape := sinkStepC_protected_shape hψ F C e hguard
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hguard, hshape⟩)))
  · have hoff := sinkStepC_off_guard_invariant_or_done hψ F C e
      hinv hdoneC hblocked hguard
    rcases hoff with hdone' | hrest
    · exact Or.inl hdone'
    · rcases hrest with hinv' | hblocked'
      · exact Or.inr (Or.inl hinv')
      · exact Or.inr (Or.inr (Or.inr (Or.inl hblocked')))


end LDSinkGapDoneInvariant


#print axioms LDSinkGapDoneInvariant.GapDoneC_of_GapDone_not_blocked
#print axioms LDSinkGapDoneInvariant.gapBlocked_signal_tail
#print axioms LDSinkGapDoneInvariant.gapBlocked_not_doneC
#print axioms LDSinkGapDoneInvariant.sinkStepC_off_guard_invariant_or_done
#print axioms LDSinkGapDoneInvariant.sinkStepC_invariant_or_done
