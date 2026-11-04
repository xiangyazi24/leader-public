import Leader.PPL.TokenCompletion.HalfPowerDynamics
import Leader.PPL.TransitionFacts

namespace PPL

set_option autoImplicit false
set_option Elab.async false

/-!
# Lemma 4 rightmost-owner progress: literal row reduction

Truth audit.

The proposed rightmost dynamics is semantically sound.

* If a younger selected-color contender is on the left and the tracked
  rightmost owner is the responder, Algorithm 3 lines 16--17 delete the
  left contender, not the responder.
* If the tracked owner is the initiator, a collision would require a valid
  selected-color token at the responder.  Inside the C_d window,
  Lemma4GhostCoveredWindow gives that token an owner, contradicting
  rightmostness.
* A selected-color birth can occur only where dist = tokenD'.  Under C_d
  that is the source coordinate k.  Hence a younger birth cannot appear to
  the right of a non-source frontier; if the frontier is at k, its valid
  physical token prevents the birth guard lv0 = none.
* A service move cannot leave the 2*psi C_d window: a valid positive owner
  cannot occupy its final coordinate, and a valid negative owner cannot
  occupy its first coordinate.

The only source-level obstruction in this bounded round is that the selected
ghost mover (ghostMoveToken and its liveShadow/bumpTo helpers) is private in
TokenCorrectness.lean.  TransitionFacts proves all non-selected field frames,
but intentionally erases the selected token.  We therefore isolate exactly
two finite one-interaction rows:

1. Lemma4RightmostInteractedRow: the tracked frontier is one of the selected
   pair endpoints;
2. Lemma4RightmostNoOvertakeOffPair: the selected pair is disjoint from the
   frontier and cannot create/move an owner past it.

Everything after those two literal Algorithm-3 rows is proved below.
-/

/-! ## A convenient exact copy of the target outcome -/

private def lemma4RightmostStepOutcome
    {n psi kappa : Nat}
    (hpsi : 2 <= psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind)
    (pre : DetSchedule n)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (x : Fin (2 * psi))
    (z : GhostToken n psi) : Prop :=
  let i := shiftRight ring k x.val
  let G' := ghostStep hpsi ring pre.length G e
  Or
    (And
      (¬ FreshAt kind k z.lmeta)
      (∀ j z',
        ghostTokenAt kind G' j = some z' ->
        z'.lmeta.id ≠ z.lmeta.id))
    (Or
      (HasFreshCompletion kind k G')
      (∃ y z',
        And
          (Lemma4RightmostAt ring k kind G' y z')
          (And
            (z'.lmeta.id = z.lmeta.id)
            (And
              (FreshAt kind k z.lmeta ->
                FreshAt kind k z'.lmeta)
              (And
                (lemma4TokenProgress
                    kind (G.phys i) z.value <=
                  lemma4TokenProgress
                    kind
                    (G'.phys
                      (shiftRight ring k y.val))
                    z'.value)
                (e = lemma4ServiceEdge ring kind G i z ->
                  lemma4TokenProgress
                      kind
                      (G'.phys
                        (shiftRight ring k y.val))
                      z'.value =
                    lemma4TokenProgress
                      kind (G.phys i) z.value + 1))))))

/-!
## Residual 1: interacted-pair selected row

This is strictly one literal Algorithm-3 pair row.  The extra premise says
that the tracked rightmost owner is an endpoint of the selected interaction.
There is no list induction, half-word argument, probability statement, or
coverage-preservation statement here.

The intended proof is the finite expansion of the private selected
ghostMoveToken:
* tracked initiator: collision/delete, stay, c=1, c>=2;
* tracked responder: collision deletes the left contender, stay, c=-1,
  c<=-2.

TransitionFacts supplies the physical selected-token-erased frames around
those branches.
-/
def Lemma4RightmostInteractedRow : Prop :=
  ∀ {n psi kappa : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (x : Fin (2 * psi))
    (z : GhostToken n psi),
    G = ghostRun hpsi ring 0 (initialGhost C0) pre ->
    Cd ring k kind G.phys ->
    Cd ring k kind
      (ghostStep hpsi ring pre.length G e).phys ->
    Lemma4GhostCoveredWindow ring k kind G ->
    Lemma4RightmostAt ring k kind G x z ->
    let i := shiftRight ring k x.val
    Or (e = i) (ring.rightNeighbor e = i) ->
    lemma4RightmostStepOutcome
      hpsi ring k kind pre G e x z

/-!
## Residual 2: disjoint-pair no-overtake row

When neither selected endpoint is the tracked site, the tracked slot itself is
definitionally untouched.  The only nontrivial selected-color fact is that no
new owner appears to its right.

Under C_d, the only fresh birth site is k; a lower owner can move right by at
most one, and if it tries to enter the tracked site the collision removes the
left contender.  This Prop records exactly that no-overtake conclusion.
-/
def Lemma4RightmostNoOvertakeOffPair : Prop :=
  ∀ {n psi kappa : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (x : Fin (2 * psi))
    (z : GhostToken n psi),
    G = ghostRun hpsi ring 0 (initialGhost C0) pre ->
    Cd ring k kind G.phys ->
    Cd ring k kind
      (ghostStep hpsi ring pre.length G e).phys ->
    Lemma4GhostCoveredWindow ring k kind G ->
    Lemma4RightmostAt ring k kind G x z ->
    let i := shiftRight ring k x.val
    e ≠ i ->
    ring.rightNeighbor e ≠ i ->
    Lemma4RightmostAt ring k kind
      (ghostStep hpsi ring pre.length G e) x z

/-! ## Ring arithmetic for the off-pair service contradiction -/

private theorem lemma4RightNeighborLeftNeighbor
    {n : Nat} (ring : DirectedRing n) (i : Fin n) :
    ring.rightNeighbor (ring.leftNeighbor i) = i := by
  apply Fin.ext
  show ((i.val + n - 1) % n + 1) % n = i.val
  have hn := ring.hn
  have hi := i.isLt
  rcases Nat.eq_zero_or_pos i.val with h0 | hpos
  · have h1 :
        (i.val + n - 1) % n = n - 1 := by
      rw [h0, Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1, show n - 1 + 1 = n by omega,
      Nat.mod_self, h0]
  · have h1 :
        (i.val + n - 1) % n = i.val - 1 := by
      rw [show i.val + n - 1 =
          (i.val - 1) + n by omega,
        Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1, show i.val - 1 + 1 = i.val by omega]
    exact Nat.mod_eq_of_lt hi

/-! ## Full reduction -/

/--
Conditional close from exactly the two private-row leaves above.

The off-pair case is completely discharged here:
* the same x,z remains the rightmost owner by the no-overtake row;
* the physical state at its site is unchanged;
* therefore canonical progress is unchanged;
* its current service edge cannot equal e, because a positive service uses i
  and a negative service uses leftNeighbor i, whose responder is i.
-/
theorem lemma4RightmostProgressStep
    (hInteracted : Lemma4RightmostInteractedRow)
    (hOffPair : Lemma4RightmostNoOvertakeOffPair) :
    Lemma4RightmostProgressStep := by
  unfold Lemma4RightmostProgressStep
  intro n psi kappa hpsi
  intro ring k kind C0 pre G e x z
  intro hrun hCd hCd' hCovered hRightmost
  dsimp only

  let i := shiftRight ring k x.val
  let G' := ghostStep hpsi ring pre.length G e

  by_cases hie : e = i
  · have h :=
      hInteracted hpsi ring k kind
        C0 pre G e x z
        hrun hCd hCd' hCovered hRightmost
        (Or.inl hie)
    simpa [lemma4RightmostStepOutcome, i, G'] using h

  · by_cases hir : ring.rightNeighbor e = i
    · have h :=
        hInteracted hpsi ring k kind
          C0 pre G e x z
          hrun hCd hCd' hCovered hRightmost
          (Or.inr hir)
      simpa [lemma4RightmostStepOutcome, i, G'] using h

    · have hRightmost' :
          Lemma4RightmostAt ring k kind G' x z := by
        have h :=
          hOffPair hpsi ring k kind
            C0 pre G e x z
            hrun hCd hCd' hCovered hRightmost
            hie hir
        simpa [i, G'] using h

      have hphysStep :=
        congrFun
          (ghostStep_erases
            hpsi ring pre.length G e) i

      have hphys :
          G'.phys i = G.phys i := by
        have h1 :
            (ghostStep hpsi ring pre.length G e).phys i =
              (PopulationProtocol.step
                (protocol psi kappa)
                ring G.phys e) i :=
          hphysStep
        change
          (ghostStep hpsi ring pre.length G e).phys i =
            G.phys i
        rw [h1]
        simp [PopulationProtocol.step,
          Ne.symm hie, Ne.symm hir]

      refine Or.inr (Or.inr ?_)
      refine ⟨x, z, ?_, rfl, ?_, ?_, ?_⟩
      · exact hRightmost'
      · intro hfresh
        exact hfresh
      · have hsame :
            G'.phys (shiftRight ring k x.val) =
              G.phys i := by
          simpa [i] using hphys
        rw [hsame]
        exact Nat.le_refl _
      · intro hservice
        have hfalse : False := by
          unfold lemma4ServiceEdge at hservice
          by_cases hpos :
              0 <
                decodeOffset psi
                  (tokenCode z.value)
          · have hei : e = i := by
              simpa [hpos] using hservice
            exact hie hei
          · have hel :
                e = ring.leftNeighbor i := by
              simpa [hpos] using hservice
            have hri :
                ring.rightNeighbor e = i := by
              rw [hel]
              exact
                lemma4RightNeighborLeftNeighbor
                  ring i
            exact hir hri
        exact False.elim hfalse

end PPL

#print axioms PPL.lemma4RightNeighborLeftNeighbor
#print axioms PPL.lemma4RightmostProgressStep
#check PPL.Lemma4RightmostInteractedRow
#check PPL.Lemma4RightmostNoOvertakeOffPair
