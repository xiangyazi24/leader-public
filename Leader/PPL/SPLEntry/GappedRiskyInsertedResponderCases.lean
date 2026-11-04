import Leader.PPL.SPLEntry.GappedRiskyInsertedStepRoute

namespace PPL.Convergence.L18

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL

/--
Literal wrap case, black selected token only.

At rightNeighbor e = root, the predecessor is the final rooted site.  CDLAt
therefore makes the initiator last bit true, so the selected-color move gate
is closed.  Any surviving responder black token can only be an old cleared
root token.
-/
def L18GappedRiskyInsertedResponderWrapBlackCase : Prop :=
  forall {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n),
    CDLAt ring root C ->
    ring.rightNeighbor e = root ->
    Not
      (PPL.tokenRisky ring root C
        (ring.rightNeighbor e) .black) ->
    Not
      (PPL.tokenRisky ring root
        (pprimeStep ring C e)
        (ring.rightNeighbor e) .black)

/--
Literal wrap case, white selected token only.

The same closed-gate argument applies after the preceding black pass because
pprimeMoveToken frames dist/last and never lets the black pass create a white
token.
-/
def L18GappedRiskyInsertedResponderWrapWhiteCase : Prop :=
  forall {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n),
    CDLAt ring root C ->
    ring.rightNeighbor e = root ->
    Not
      (PPL.tokenRisky ring root C
        (ring.rightNeighbor e) .white) ->
    Not
      (PPL.tokenRisky ring root
        (pprimeStep ring C e)
        (ring.rightNeighbor e) .white)

/--
Literal non-wrap case, black selected token only.

Both old physical sources are assumed non-risky.  The responder is in the
proper rooted S0.  The remaining local Algorithm-3 split is: old responder
stay; positive left move with preserved target; c=1 negative turn; or the
fresh black birth at the root, whose psi-1 responder path exits S0.
-/
def L18GappedRiskyInsertedResponderNonwrapBlackCase : Prop :=
  forall {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n),
    CDLAt ring root C ->
    Not (ring.rightNeighbor e = root) ->
    cyclicOffset ring root
        (ring.rightNeighbor e) < psi ->
    Not
      (PPL.tokenRisky ring root C e .black) ->
    Not
      (PPL.tokenRisky ring root C
        (ring.rightNeighbor e) .black) ->
    Not
      (PPL.tokenRisky ring root
        (pprimeStep ring C e)
        (ring.rightNeighbor e) .black)

/--
Literal non-wrap case, white selected token only.

The preceding black pass frames white token data and dist/last.  Under CDLAt,
a white fresh birth guard cannot fire at an initiator strictly inside rooted
S0, while ordinary right motion and the c=1 turn have the same safety shapes
as in the black row.
-/
def L18GappedRiskyInsertedResponderNonwrapWhiteCase : Prop :=
  forall {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n),
    CDLAt ring root C ->
    Not (ring.rightNeighbor e = root) ->
    cyclicOffset ring root
        (ring.rightNeighbor e) < psi ->
    Not
      (PPL.tokenRisky ring root C e .white) ->
    Not
      (PPL.tokenRisky ring root C
        (ring.rightNeighbor e) .white) ->
    Not
      (PPL.tokenRisky ring root
        (pprimeStep ring C e)
        (ring.rightNeighbor e) .white)

theorem l18GappedRiskyInsertedResponderWrapRow_of_cases
    (hBlack : L18GappedRiskyInsertedResponderWrapBlackCase)
    (hWhite : L18GappedRiskyInsertedResponderWrapWhiteCase) :
    L18GappedRiskyInsertedResponderWrapRow := by
  unfold L18GappedRiskyInsertedResponderWrapBlackCase at hBlack
  unfold L18GappedRiskyInsertedResponderWrapWhiteCase at hWhite
  unfold L18GappedRiskyInsertedResponderWrapRow

  intro n psi kappa
  intro hn3 hpsi hlt
  intro ring root j C e
  intro _hj hPrefix hroot hjpos

  have hoff :
      cyclicOffset ring root
          (ring.rightNeighbor e) = 0 := by
    rw [hroot]
    exact l18Risk2CyclicOffset_self ring root

  have hpre :
      Not
        (Risky ring root C
          (ring.rightNeighbor e)) :=
    hPrefix.2
      (ring.rightNeighbor e)
      (by
        rw [hoff]
        exact hjpos)

  have hpreBlack :
      Not
        (PPL.tokenRisky ring root C
          (ring.rightNeighbor e) .black) := by
    intro hb
    exact hpre (Or.inl hb)

  have hpreWhite :
      Not
        (PPL.tokenRisky ring root C
          (ring.rightNeighbor e) .white) := by
    intro hw
    exact hpre (Or.inr hw)

  intro hpost
  rcases hpost with hb | hw
  · exact
      (hBlack
        hn3 hpsi hlt
        ring root C e
        hPrefix.1 hroot hpreBlack) hb
  · exact
      (hWhite
        hn3 hpsi hlt
        ring root C e
        hPrefix.1 hroot hpreWhite) hw

theorem l18GappedRiskyInsertedResponderNonwrapRow_of_cases
    (hBlack : L18GappedRiskyInsertedResponderNonwrapBlackCase)
    (hWhite : L18GappedRiskyInsertedResponderNonwrapWhiteCase) :
    L18GappedRiskyInsertedResponderNonwrapRow := by
  unfold L18GappedRiskyInsertedResponderNonwrapBlackCase at hBlack
  unfold L18GappedRiskyInsertedResponderNonwrapWhiteCase at hWhite
  unfold L18GappedRiskyInsertedResponderNonwrapRow

  intro n psi kappa
  intro hn3 hpsi hlt
  intro ring root j C e
  intro hj hPrefix hrootB hroff

  have hroot :
      Not (ring.rightNeighbor e = root) :=
    bne_iff_ne.mp hrootB

  have hstepOff :
      cyclicOffset ring root
          (ring.rightNeighbor e) =
        cyclicOffset ring root e + 1 :=
    l18Gapped_rightNeighbor_offset_of_ne_root
      ring root e hroot

  have heoff :
      cyclicOffset ring root e < j := by
    have h := hroff
    rw [hstepOff] at h
    omega

  have hroffPsi :
      cyclicOffset ring root
          (ring.rightNeighbor e) < psi := by
    omega

  have hpreE :
      Not (Risky ring root C e) :=
    hPrefix.2 e heoff

  have hpreR :
      Not
        (Risky ring root C
          (ring.rightNeighbor e)) :=
    hPrefix.2
      (ring.rightNeighbor e) hroff

  have hpreEBlack :
      Not (PPL.tokenRisky ring root C e .black) := by
    intro hb
    exact hpreE (Or.inl hb)

  have hpreEWhite :
      Not (PPL.tokenRisky ring root C e .white) := by
    intro hw
    exact hpreE (Or.inr hw)

  have hpreRBlack :
      Not
        (PPL.tokenRisky ring root C
          (ring.rightNeighbor e) .black) := by
    intro hb
    exact hpreR (Or.inl hb)

  have hpreRWhite :
      Not
        (PPL.tokenRisky ring root C
          (ring.rightNeighbor e) .white) := by
    intro hw
    exact hpreR (Or.inr hw)

  intro hpost
  rcases hpost with hb | hw
  · exact
      (hBlack
        hn3 hpsi hlt
        ring root C e
        hPrefix.1 hroot hroffPsi
        hpreEBlack hpreRBlack) hb
  · exact
      (hWhite
        hn3 hpsi hlt
        ring root C e
        hPrefix.1 hroot hroffPsi
        hpreEWhite hpreRWhite) hw

theorem l18GappedRiskyInsertedStepRow_of_responderCases
    (hWrapBlack : L18GappedRiskyInsertedResponderWrapBlackCase)
    (hWrapWhite : L18GappedRiskyInsertedResponderWrapWhiteCase)
    (hNonwrapBlack :
      L18GappedRiskyInsertedResponderNonwrapBlackCase)
    (hNonwrapWhite :
      L18GappedRiskyInsertedResponderNonwrapWhiteCase) :
    L18GappedRiskyInsertedStepRow := by
  exact
    l18GappedRiskyInsertedStepRow_of_responderRows
      (l18GappedRiskyInsertedResponderWrapRow_of_cases
        hWrapBlack hWrapWhite)
      (l18GappedRiskyInsertedResponderNonwrapRow_of_cases
        hNonwrapBlack hNonwrapWhite)

end PPL.Convergence.L18

#print axioms
  PPL.Convergence.L18.l18GappedRiskyInsertedResponderWrapRow_of_cases
#print axioms
  PPL.Convergence.L18.l18GappedRiskyInsertedResponderNonwrapRow_of_cases
#print axioms
  PPL.Convergence.L18.l18GappedRiskyInsertedStepRow_of_responderCases
