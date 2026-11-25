import Leader.L4.RootedWindows

namespace L4.WindowForeignWitness
open RankPhysical RootedAssembly SevenTagCharge

/-- A raw edge can stop G6 without rewarding G7.
The size is deliberately divisible by the modulus. -/
def tape : Config 2 12 40 := fun i => {
  residue := ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩
  mark := i.val ≤ 14 && i.val % 2 == 0
  leader := i.val ≤ 15 && i.val % 2 == 1
  bullet := if i.val = 14 then .live else .none
  shield := i.val ≤ 13 && i.val % 2 == 1
  signal := .zero
  stock := false
  source := .off
  rail := .e
}

theorem quiet : QuietEntrance tape := by
  refine ⟨?_,?_,⟨0,rfl⟩,?_⟩
  · unfold MCOV
    decide
  · unfold COV
    decide
  · intro b hb
    have heq : b = 14 := by
      by_cases h : b = 14
      · exact h
      have hn : b.val ≠ 14 := fun h' => h (Fin.ext h')
      simp [tape,hn] at hb
    subst b
    refine ⟨12,1,by decide,rfl,rfl,rfl,rfl,?_,?_⟩
    · intro j hj
      have : j = 0 := by omega
      subst j
      rfl
    · intro j hj
      rfl

theorem rank_exact : rank tape = 8 := by decide

def first : Fin (rank tape) := ⟨0, by rw [rank_exact]; decide⟩

theorem local_stop_is_not_global :
    WindowSpan.span tape first = 12 ∧
    window7 (WindowRoster.roster tape) first = [0,2,4,6,8,10,12] ∧
    TripleResidual.death tape 14 = true ∧
    (TripleResidual.advance (TripleResidual.init tape) 14).stopped = true ∧
    reward tape (window7 (WindowRoster.roster tape) first) [14] = 0 := by
  decide

#print axioms quiet
#print axioms rank_exact
#print axioms local_stop_is_not_global
end L4.WindowForeignWitness
