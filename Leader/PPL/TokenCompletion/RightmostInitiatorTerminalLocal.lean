import Leader.PPL.TokenCompletion.RightmostInitiatorStateLocal

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/--
Pure selected-pair shape row.

There is no lineage-history premise, no ID-uniqueness premise, no fresh
kinematics premise, and no age premise here.  The conclusion says only that
a tracked rightmost initiator which disappears from both selected ghost
outputs must be the final positive service.

Truth argument:
* GhostSound makes the tracked physical token exactly z.value and valid.
* C_d makes coordinate 2*psi-1 incapable of carrying any valid selected-color
  token, so the tracked valid owner has x < 2*psi-1.
* Its responder is therefore still in the 2*psi window.
* Coverage + rightmostness rules out a valid physical responder blocker.
* c < 0 stays on the left; c >= 2 moves to a live right owner; c = 1 before
  the last service also leaves the advanced owner live on the right.
Thus no same-ID selected output leaves only x = 2*psi-2 and c = 1.
-/
def Lemma4RightmostInitiatorTerminalFinalShapeRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (x : Fin (2 * psi))
    (z : GhostToken n psi),
    Cd ring k kind G.phys →
    Cd ring k kind
      (ghostStep hpsi ring step G e).phys →
    Lemma4GhostCoveredWindow ring k kind G →
    GhostSound G →
    Lemma4RightmostAt ring k kind G x z →
    e = shiftRight ring k x.val →
    (∀ zL : GhostToken n psi,
      (ghostStepSelectedPair
          hpsi ring step G e kind).left =
        some zL →
      zL.lmeta.id ≠ z.lmeta.id) →
    (∀ zR : GhostToken n psi,
      (ghostStepSelectedPair
          hpsi ring step G e kind).right =
        some zR →
      zR.lmeta.id ≠ z.lmeta.id) →
    x.val = 2 * psi - 2 ∧
      decodeOffset psi (tokenCode z.value) = (1 : Int)

/--
Final-service completion row.

This starts after the branch tree has already established
  x = 2*psi-2, c = 1.
Hence there is no negative/stay/right-move classification left.

The remaining proof is:
1. apply Lemma4FreshKinematics to the tracked fresh owner;
2. use moves < tokenTrajectoryMoves to exclude q >= psi in the intrinsic
   trajectory witness;
3. use C_d at the now-bounded unwrapped coordinate and at x to identify the
   two coordinates;
4. apply lemma4FreshTrajectoryPoint_finalPositive, obtaining
   (ghostStepLineageAdvance z.lmeta).moves = tokenTrajectoryMoves psi;
5. in the single c = 1 ghost branch, coverage/rightmostness excludes a
   responder collision, bumpTo emits [ghostStepLineageAdvance z.lmeta], and
   ghostStep appends that selected done list to completed.
-/
def Lemma4RightmostInitiatorTerminalFinalCompletionRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (x : Fin (2 * psi))
    (z : GhostToken n psi),
    Cd ring k kind G.phys →
    Cd ring k kind
      (ghostStep hpsi ring step G e).phys →
    Lemma4GhostCoveredWindow ring k kind G →
    GhostSound G →
    Lemma4FreshKinematics ring k G →
    (FreshAt kind k z.lmeta →
      z.lmeta.moves < tokenTrajectoryMoves psi) →
    Lemma4RightmostAt ring k kind G x z →
    e = shiftRight ring k x.val →
    FreshAt kind k z.lmeta →
    x.val = 2 * psi - 2 →
    decodeOffset psi (tokenCode z.value) = (1 : Int) →
    HasFreshCompletion kind k
      (ghostStep hpsi ring step G e)

/--
Exact residual bundle for this partial reduction.

Both conjuncts are strictly smaller than
Lemma4RightmostInitiatorTerminalStateLocalResidual:
the first has no history arithmetic, while the second is already fixed to the
single final c = 1 branch and has no selected-output exclusion hypotheses.
-/
def Lemma4RightmostInitiatorTerminalLocalResiduals : Prop :=
  Lemma4RightmostInitiatorTerminalFinalShapeRow ∧
    Lemma4RightmostInitiatorTerminalFinalCompletionRow

theorem
    lemma4RightmostInitiatorTerminalStateLocalResidual_of_terminalLocalResiduals
    (hrows :
      Lemma4RightmostInitiatorTerminalLocalResiduals) :
    Lemma4RightmostInitiatorTerminalStateLocalResidual := by
  rcases hrows with ⟨hshape, hfinish⟩
  unfold Lemma4RightmostInitiatorTerminalStateLocalResidual
  intro n psi kappa hpsi
  intro ring k kind step G e x z
  intro hCd hCd' hcovered hsound hkin
  intro hage hright htrack
  intro hleft hrightOut hfresh

  have hfinal :
      x.val = 2 * psi - 2 ∧
        decodeOffset psi (tokenCode z.value) =
          (1 : Int) :=
    hshape
      hpsi ring k kind step G e x z
      hCd hCd' hcovered hsound
      hright htrack hleft hrightOut

  exact
    hfinish
      hpsi ring k kind step G e x z
      hCd hCd' hcovered hsound hkin
      hage hright htrack hfresh
      hfinal.1 hfinal.2

end PPL

#print axioms PPL.lemma4RightmostInitiatorTerminalStateLocalResidual_of_terminalLocalResiduals
