import Leader.PPL.Safety.SPLBlackCorrectnessRoute

namespace PPL.Safety.SPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/--
Selected initiator old-image branch.

Provenance has already fixed the old source to e, exposed the cleared live
black token, and exposed the exact selected black MoveToken output.
-/
def SPLBlackOldImageInitiatorBranch : Prop :=
  PPL.remark2_one_step_unique ->
  forall {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n),
    SPLAt ring root C ->
    forall
      (seg : Fin (segmentCount n psi - 2))
      (i : Fin n)
      (t t' : TokenData psi),
      let rsite := ring.rightNeighbor e
      let p :=
        PPL.Safety.PeacefulProps.preTokenPair
          hpsi (C e) (C rsite)
      let l0 := PPL.sourceClear .black p.1
      let r0 := PPL.sourceClear .black p.2
      let q := PPL.moveToken hpsi .black p.1 p.2
      let gate := l0.last = false /\ r0.last = false
      tokenAt .black (C e) = some t ->
      tokenAt .black l0 = some t ->
      ((Not gate /\
          i = e /\
          tokenAt .black q.1 = some t') \/
        (gate /\
          tokenAt .black r0 = none /\
          ((i = e /\
              tokenAt .black q.1 = some t') \/
            (i = rsite /\
              tokenAt .black q.2 = some t')))) ->
      tokenAt .black
          (nextConfig ring C e i) =
        some t' ->
      (ValidToken .black
          (nextConfig ring C e) i /\
        WorkingFor ring root
          (nextConfig ring C e)
          i .black seg.val) ->
      CorrectToken ring root
        (nextConfig ring C e)
        i .black seg.val

/--
Selected responder old-image branch.

Provenance has already fixed the old source to rightNeighbor e, exposed the
cleared responder token, and exposed the selected black MoveToken output.
-/
def SPLBlackOldImageResponderBranch : Prop :=
  PPL.remark2_one_step_unique ->
  forall {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n),
    SPLAt ring root C ->
    forall
      (seg : Fin (segmentCount n psi - 2))
      (i : Fin n)
      (t t' : TokenData psi),
      let rsite := ring.rightNeighbor e
      let p :=
        PPL.Safety.PeacefulProps.preTokenPair
          hpsi (C e) (C rsite)
      let l0 := PPL.sourceClear .black p.1
      let r0 := PPL.sourceClear .black p.2
      let q := PPL.moveToken hpsi .black p.1 p.2
      let gate := l0.last = false /\ r0.last = false
      tokenAt .black (C rsite) = some t ->
      tokenAt .black r0 = some t ->
      ((Not gate /\
          i = rsite /\
          tokenAt .black q.2 = some t') \/
        (gate /\
          ((i = e /\
              tokenAt .black q.1 = some t') \/
            (i = rsite /\
              tokenAt .black q.2 = some t')))) ->
      tokenAt .black
          (nextConfig ring C e i) =
        some t' ->
      (ValidToken .black
          (nextConfig ring C e) i /\
        WorkingFor ring root
          (nextConfig ring C e)
          i .black seg.val) ->
      CorrectToken ring root
        (nextConfig ring C e)
        i .black seg.val

private theorem splBlackOldStep_other
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (e i : Fin n)
    (hie : Not (i = e))
    (hir : Not (i = ring.rightNeighbor e)) :
    nextConfig ring C e i = C i := by
  unfold nextConfig PopulationProtocol.step
  simp [hie, hir]

/--
Off-pair old-image branch.

The token at i is untouched by the step (i is neither endpoint of e), so the
remaining content is that its payload stays correct: `payloadCorrect` reads
id bits at other sites, which the SPL field frame keeps fixed.
-/
def SPLBlackOldImageOffPairBranch : Prop :=
  forall {n psi kappa : Nat}
    (hn3 : 3 <= n)
    (hpsi : 2 <= psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (e : Fin n),
    SPLAt ring root C ->
    forall
      (seg : Fin (segmentCount n psi - 2))
      (i : Fin n),
      Not (i = e) ->
      Not (i = ring.rightNeighbor e) ->
      nextConfig ring C e i = C i ->
      CorrectToken ring root C i .black seg.val ->
      CorrectToken ring root
        (nextConfig ring C e)
        i .black seg.val

/--
Exact adapter from the three case rows.

The off-pair case uses the literal configuration frame to move ValidToken and
WorkingFor back to C, applies the pre-step SPL correctness conjunct, and hands
the payload transfer to SPLBlackOldImageOffPairBranch.
-/
theorem splAlgorithm23BlackOldImageRow_of_branches
    (hInitiator : SPLBlackOldImageInitiatorBranch)
    (hResponder : SPLBlackOldImageResponderBranch)
    (hOff : SPLBlackOldImageOffPairBranch) :
    SPLAlgorithm23BlackOldImageRow := by
  unfold SPLBlackOldImageInitiatorBranch at hInitiator
  unfold SPLBlackOldImageResponderBranch at hResponder
  unfold SPLAlgorithm23BlackOldImageRow

  intro hRemark
  intro n psi kappa
  intro hn3 hpsi ring root C e hSPL
  intro seg i t' hpost hOld hVW

  unfold SPLPostTokenOldImage at hOld
  dsimp only at hOld

  rcases hOld with
    ⟨j, t, _hwhere, hCtok, hshape⟩

  rcases hshape with hleft | hright | hoff
  · rcases hleft with
      ⟨hje, hl0tok, hmove⟩
    subst j
    exact
      hInitiator hRemark
        hn3 hpsi ring root C e hSPL
        seg i t t'
        hCtok
        (by exact hl0tok)
        (by exact hmove)
        hpost hVW

  · rcases hright with
      ⟨hjr, hr0tok, hmove⟩
    subst j
    exact
      hResponder hRemark
        hn3 hpsi ring root C e hSPL
        seg i t t'
        hCtok
        (by exact hr0tok)
        (by exact hmove)
        hpost hVW

  · rcases hoff with
      ⟨hji, hie, hir, _htt⟩
    subst j

    have hsame :
        nextConfig ring C e i = C i :=
      splBlackOldStep_other
        ring C e i hie hir

    have hVW0 :
        ValidToken .black C i /\
          WorkingFor ring root C i
            .black seg.val := by
      unfold ValidToken WorkingFor at hVW
      unfold ValidToken WorkingFor
      rw [hsame] at hVW
      exact hVW

    exact
      hOff hn3 hpsi ring root C e hSPL
        seg i hie hir hsame
        (((hSPL.2.2 seg).2 i).1 hVW0)

end PPL.Safety.SPL

#print axioms PPL.Safety.SPL.splAlgorithm23BlackOldImageRow_of_branches
