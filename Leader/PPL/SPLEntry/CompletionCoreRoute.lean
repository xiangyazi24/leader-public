import Leader.PPL.SPLEntry.BuildBlockAdvance


namespace PPL.Convergence.L18


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


open PPL


/-- Schedule-wide frame half of L18PrimeLemma4Core. -/
def L18PrimeLemma4FrameRow : Prop :=
  PPL.lemma4_deterministic_core →
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (C : Config n psi kappa)
    (schedule : DetSchedule n),
    b < l18BlockCount n psi →
    L18BuildPrefixAt ring root b C →
    (PPL.lemma4Word ring
      (shiftRight ring root (b * psi)) psi).Sublist schedule →
    let D := runPPrime ring C schedule
    l18HitsSPL ring root C schedule = true ∨
      L18BuildPrefixAt ring root b D


/-- Current-pair construction half of L18PrimeLemma4Core. -/
def L18PrimeLemma4PairRow : Prop :=
  PPL.lemma4_deterministic_core →
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (C : Config n psi kappa)
    (schedule : DetSchedule n),
    b < l18BlockCount n psi →
    L18BuildPrefixAt ring root b C →
    (PPL.lemma4Word ring
      (shiftRight ring root (b * psi)) psi).Sublist schedule →
    let D := runPPrime ring C schedule
    l18HitsSPL ring root C schedule = true ∨
      L18BuildPairOK ring root D b


theorem l18PrimeLemma4Core_of_rows
    (hframe : L18PrimeLemma4FrameRow)
    (hpair : L18PrimeLemma4PairRow) :
    L18PrimeLemma4Core := by
  unfold L18PrimeLemma4Core
  intro hlemma4
  intro n psi kappa
  intro hn3 hpsi ring root b C schedule
  intro hb hprefix hsub
  have hf :=
    hframe hlemma4 hn3 hpsi ring root b C schedule
      hb hprefix hsub
  have hp :=
    hpair hlemma4 hn3 hpsi ring root b C schedule
      hb hprefix hsub
  dsimp only at hf hp ⊢
  rcases hf with hhit | hkeep
  · exact Or.inl hhit
  · rcases hp with hhit | hpairD
    · exact Or.inl hhit
    · exact Or.inr ⟨hkeep, hpairD⟩


end PPL.Convergence.L18


#print axioms PPL.Convergence.L18.l18PrimeLemma4Core_of_rows
