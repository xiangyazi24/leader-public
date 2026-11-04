import Leader.PPL.SPLEntry.WhiteTokenHalf
import Leader.PPL.SPLEntry.WhiteFrame
import Leader.PPL.Safety.SPLWhiteCorrectness

/-!
P_PL Theorem 1 cleanup, phase 2: the declarations of this file that served only the old
psi <= log2 n + 1 route to `theorem1Statement_proved` moved to
`Leader/Superseded/Theorem1LogWindow/Theorem1PPLFromHalves.lean`, namespace `PPL.Superseded.LogWindow`: `theorem1Statement_of_halves_upto12`.
-/

/-!
# P_PL Theorem 1 from the two halves of the establishment cut

The establishment cut `L18PrimeLemma4EstablishmentCutRow` is
split into its two halves:

* token half: `L18PrimeHalfWordTokenHalfRow` (the token half after the
  first-half purge), turned into the cut's token half by
  `l18PrimeLemma4EstablishmentTokensAtCut_of_halfRow`;
* ID half: `L18PrimeLemma4EstablishmentIdAtCutRow`, the statement of
  `l18PrimeLemma4EstablishmentIdAtCut`, universally quantified.

`L18BuildPairOK ring root E b` is exactly `ID equation ∧ token half`, so the
cut follows from the two halves.
-/

namespace PPL.Convergence.L18

set_option autoImplicit false
set_option linter.defProp false

open PPL

/-- `l18PrimeLemma4EstablishmentIdAtCut`, verbatim, as a
proposition: the first physical construction of the successor segment ID at
the establishment cut.  Open. -/
def L18PrimeLemma4EstablishmentIdAtCutRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (C : Config n psi kappa)
    (cut : DetSchedule n)
    (hb : b < l18BlockCount n psi)
    (hPrefix : L18BuildPrefixAt ring root b C)
    (hsub :
      (PPL.lemma4Word ring
        (shiftRight ring root (b * psi)) psi).Sublist cut)
    (hminimal :
      ∀ (cut0 tail : DetSchedule n),
        cut = cut0 ++ tail →
        tail ≠ [] →
        Not
          ((PPL.lemma4Word ring
            (shiftRight ring root (b * psi)) psi).Sublist cut0)),
    let E := runPPrime ring C cut
    Or
      (l18HitsSPL ring root C cut = true)
      (rootedSegmentId ring root E (b + 1) =
        (rootedSegmentId ring root E b + 1) % (2 ^ psi))

/-- The establishment cut from its token half and its ID half. -/
theorem l18PrimeLemma4EstablishmentCutRow_of_halves
    (hHalf : L18PrimeHalfWordTokenHalfRow)
    (hId : L18PrimeLemma4EstablishmentIdAtCutRow) :
    L18PrimeLemma4EstablishmentCutRow := by
  intro n psi kappa hn3 hpsi ring root b C cut hb hPrefix hsub hminimal
  have hT :=
    l18PrimeLemma4EstablishmentTokensAtCut_of_halfRow
      hHalf hn3 hpsi ring root b C cut hb hPrefix hsub
  have hI :=
    hId hn3 hpsi ring root b C cut hb hPrefix hsub hminimal
  dsimp only at hT hI ⊢
  rcases hI with hhit | hid
  · exact Or.inl hhit
  · rcases hT with hhit | htok
    · exact Or.inl hhit
    · exact Or.inr ⟨hid, htok⟩

end PPL.Convergence.L18

#print axioms PPL.Convergence.L18.l18PrimeLemma4EstablishmentCutRow_of_halves
