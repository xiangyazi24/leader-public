import Leader.PPL.SPLEntry.GappedRiskyScopedRoute
import Leader.PPL.SPLEntry.CPBUniqueStepRow
import Leader.PPL.SPLEntry.GappedPhases
import Leader.PPL.SPLEntry.RiskySweepLetterInductive
import Init.Omega

namespace PPL.Convergence.L18

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL

/-
The only remaining hard point is responder-site token provenance.
Everything else in L18GappedRiskyInsertedStepRow is already a consequence
of public landed geometry/frame lemmas.
-/

/-- Arbitrary P_PL-prime letters preserve the full rooted CDL frame. -/
private theorem q20218_cdl_step
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n)
    (hC : CDLAt ring root C) :
    CDLAt ring root (pprimeStep ring C e) := by
  have hUnique :
      L18UniqueLeaderAt C root := by
    exact hC.2.1

  have hDist :
      L18CanonicalDistanceAt ring root C := by
    intro i
    exact (hC.2.2 i).1

  have hCU :=
    PPL.Convergence.L18Bridge.l18CPBUniqueStepRow_proved
      hn3 hpsi ring root C e
      hC.1 hUnique

  have hDistAfter :
      L18CanonicalDistanceAt ring root
        (pprimeStep ring C e) :=
    l18Gapped_canonicalDistance_step
      hn3 hpsi ring root C e
      hUnique hDist

  have hLast :
      L18LastPrefixAt ring root n C := by
    intro i _hi
    have h := (hC.2.2 i).2
    simpa [l18GappedLastThreshold] using h

  have hLastAfter :
      L18LastPrefixAt ring root n
        (pprimeStep ring C e) :=
    l18LastPrefixStepRow_proved
      hn3 hpsi ring root n C e
      hUnique hDist hLast

  refine
    And.intro hCU.1
      (And.intro hCU.2 ?_)
  intro i
  refine
    And.intro
      (hDistAfter i)
      ?_
  have hl :=
    hLastAfter i (by omega)
  simpa [l18GappedLastThreshold] using hl

/-- Off the selected pair, the token-bearing state is pointwise framed. -/
private theorem q20218_nonincident_not_risky
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (j : Nat)
    (C : Config n psi kappa)
    (e i : Fin n)
    (hPrefix : L18RiskySweepPrefix2 ring root j C)
    (hi : cyclicOffset ring root i < j)
    (hie : i != e)
    (hir : i != ring.rightNeighbor e) :
    Not
      (Risky ring root
        (pprimeStep ring C e) i) := by
  have hframe :
      pprimeStep ring C e i = C i :=
    l18Risk2UntouchedFrame
      ring C e i (bne_iff_ne.mp hie) (bne_iff_ne.mp hir)

  have hpre :
      Not (Risky ring root C i) :=
    hPrefix.2 i hi

  intro hpost
  apply hpre
  unfold Risky PPL.tokenRisky at hpost ⊢
  rw [hframe] at hpost
  exact hpost

/--
If the cleared-prefix site is the initiator, it is itself one of the
canonical rooted S_0 sweep sites.  Re-index by its cyclic offset and reuse
the already-proved selected-site theorem.
-/
private theorem q20218_initiator_not_risky
    {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (j : Nat)
    (C : Config n psi kappa)
    (e i : Fin n)
    (hje : j <= psi)
    (hPrefix : L18RiskySweepPrefix2 ring root j C)
    (hi : cyclicOffset ring root i < j)
    (hie : i = e) :
    Not
      (Risky ring root
        (pprimeStep ring C e) i) := by
  subst i

  let k : Nat :=
    cyclicOffset ring root e

  have hk : k < psi := by
    dsimp only [k]
    omega

  have he :
      shiftRight ring root k = e := by
    dsimp only [k]
    exact
      l18Risk2ShiftRight_cyclicOffset
        ring root e

  have hnr :=
    l18Risk2Current_not_risky
      hn3 hpsi hlt
      ring root C k hk
      hPrefix.1

  rw [he] at hnr
  exact hnr

/--
Remaining wrap responder row.

The responder is root.  Since it lies in the cleared prefix, j > 0.
The predecessor is the final rooted site and canonical last=true closes
the move gate, so no positive token can wrap into root.  Clearing an invalid
root token can only remove risky mass.
-/
def L18GappedRiskyInsertedResponderWrapRow : Prop :=
  forall {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (j : Nat)
    (C : Config n psi kappa)
    (e : Fin n),
    j <= psi ->
    L18RiskySweepPrefix2 ring root j C ->
    ring.rightNeighbor e = root ->
    0 < j ->
    Not
      (Risky ring root
        (pprimeStep ring C e)
        (ring.rightNeighbor e))

/--
Remaining non-wrap responder row.

Here the responder is in the cleared prefix but is not root, hence its
predecessor e is also in the cleared prefix.  Therefore both possible old
token sources are non-risky before the step.  The branch proof only has to
show:
* same-token responder outputs preserve non-risk;
* a positive token moved from e preserves its physical target, so post-risk
  would imply pre-risk at e;
* negative and fresh/turn outputs are non-risky, with the fresh path leaving
  S_0 because psi < n.
-/
def L18GappedRiskyInsertedResponderNonwrapRow : Prop :=
  forall {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (j : Nat)
    (C : Config n psi kappa)
    (e : Fin n),
    j <= psi ->
    L18RiskySweepPrefix2 ring root j C ->
    ring.rightNeighbor e != root ->
    cyclicOffset ring root
        (ring.rightNeighbor e) < j ->
    Not
      (Risky ring root
        (pprimeStep ring C e)
        (ring.rightNeighbor e))

/--
Adapter: the two responder rows close the exact landed
L18GappedRiskyInsertedStepRow.  Non-incident and initiator cases are already
proved above.
-/
theorem l18GappedRiskyInsertedStepRow_of_responderRows
    (hWrap : L18GappedRiskyInsertedResponderWrapRow)
    (hNonwrap : L18GappedRiskyInsertedResponderNonwrapRow) :
    L18GappedRiskyInsertedStepRow := by
  unfold L18GappedRiskyInsertedResponderWrapRow at hWrap
  unfold L18GappedRiskyInsertedResponderNonwrapRow at hNonwrap
  unfold L18GappedRiskyInsertedStepRow

  intro n psi kappa
  intro hn3 hpsi hlt
  intro ring root j C e
  intro hj hPrefix

  have hCDL :
      CDLAt ring root
        (pprimeStep ring C e) :=
    q20218_cdl_step
      hn3 hpsi ring root C e
      hPrefix.1

  refine And.intro hCDL ?_
  intro i hi

  by_cases hie : i = e
  · exact
      q20218_initiator_not_risky
        hn3 hpsi hlt
        ring root j C e i
        hj hPrefix hi hie

  · by_cases hir :
        i = ring.rightNeighbor e
    · subst i
      by_cases hroot :
          ring.rightNeighbor e = root
      · have hoff :
            cyclicOffset ring root
                (ring.rightNeighbor e) = 0 := by
          rw [hroot]
          exact
            l18Risk2CyclicOffset_self
              ring root

        have hjpos : 0 < j := by
          rw [hoff] at hi
          omega

        exact
          hWrap
            hn3 hpsi hlt
            ring root j C e
            hj hPrefix hroot hjpos

      · exact
          hNonwrap
            hn3 hpsi hlt
            ring root j C e
            hj hPrefix (bne_iff_ne.mpr hroot) hi

    · exact
        q20218_nonincident_not_risky
          ring root j C e i
          hPrefix hi (bne_iff_ne.mpr hie) (bne_iff_ne.mpr hir)

end PPL.Convergence.L18

#print axioms
  PPL.Convergence.L18.l18GappedRiskyInsertedStepRow_of_responderRows
