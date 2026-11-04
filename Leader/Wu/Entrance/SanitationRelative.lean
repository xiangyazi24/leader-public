import Leader.Wu.Entrance.LargeRingLaws
import Leader.Wu.Entrance.LocalRulerWord
import Leader.Wu.Entrance.RelativeRulerContract

set_option autoImplicit false
set_option Elab.async false

namespace B6SanitationRelative

open PPLL PPLLResearchFormulation
open BirthCheckPermitRepairLeaf BirthCheckChainR1Ring
open B6LocalReverseFill
open B6PreparedRelativeContract

variable {n psi kappa tau : Nat} {P : Type}
variable {ring : DirectedRing n}

/-- Replacement C4 law 6, with an explicit budget for the new `0 -> 1` leaf. -/
def RulerPreparationWithinCoreBoundRel
    {n psi : Nat} (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n)
    (_hdom : B6EntranceLargeRingPackage.LargeRingDomain psi n)
    (zeroOneL : Nat) : Prop :=
  B6EntranceV2.HostCoreStageWord
    (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
    (fun q : B6EntranceV2.Phys psi psi (16 * psi) => q)
    ring (B6EntranceLawsWiring2.WPfinal (psi := psi) ring)
    (B6EntranceV2K2.K2DrainedAt
      (fun q : B6EntranceV2.Phys psi psi (16 * psi) => q)
      (B6EntranceLawsWiring2.WPfinal (psi := psi) ring))
    (B6EntranceV2K2.CorePreparedRel hpsi
      (fun q : B6EntranceV2.Phys psi psi (16 * psi) => q)
      (B6EntranceLawsWiring2.WPfinal (psi := psi) ring))
    (B6EntranceStageLengths.rulerTargetL psi + zeroOneL)

/-- Replacement C4 law 7: same route target and bound, new prepared source. -/
def RouteExitWithinCoreSweepRel
    {n psi : Nat} (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n)
    (_hdom : B6EntranceLargeRingPackage.LargeRingDomain psi n) : Prop :=
  B6EntranceV2.HostCoreStageWord
    (B9Host.r1Host (kappa := psi) (tau := 16 * psi) hpsi h2)
    (fun q : B6EntranceV2.Phys psi psi (16 * psi) => q)
    ring (B6EntranceLawsWiring2.WPfinal (psi := psi) ring)
    (B6EntranceV2K2.CorePreparedRel hpsi
      (fun q : B6EntranceV2.Phys psi psi (16 * psi) => q)
      (B6EntranceLawsWiring2.WPfinal (psi := psi) ring))
    (fun _ _ => False)
    (B6EntranceStageLengths.routeTargetL psi)

/--
The existing sharp ruler word proves all relative ruler edges with left offset
at least 1.  On the leaderless branch, adding exactly `ZeroOneRulerLeaf`
upgrades that tail to the full `RulerNFRel`.
-/
theorem local_ruler_word_sharp_rel_range
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (ring : DirectedRing n) (I : Interval ring) (hW : 2 ≤ I.size)
    (C : BirthCheckPermitRepairLeaf.FC n psi kappa tau) :
    ∃ w : List (Fin n), InternalWord I w ∧
      w.length ≤ (I.size - 2) * I.size ∧
      (B6LocalRuler.WorkspaceLeader ring I
          (runR hpsi h2 ring w C) ∨
       (ZeroOneRulerLeaf hpsi ring I (runR hpsi h2 ring w C) ->
        RulerNFRel hpsi ring I (runR hpsi h2 ring w C))) := by
  obtain ⟨w, hwI, hwL, hwS⟩ :=
    B6LocalRulerWord.local_ruler_word_sharp hpsi h2 ring I hW C
  refine ⟨w, hwI, hwL, ?_⟩
  rcases hwS with hleader | htail
  · exact Or.inl hleader
  · refine Or.inr ?_
    intro h01 k hk
    by_cases hk0 : k = 0
    · subst k
      simpa [ZeroOneRulerLeaf] using h01
    · have hk1 : 1 ≤ k := by omega
      exact htail k hk1 hk

end B6SanitationRelative
