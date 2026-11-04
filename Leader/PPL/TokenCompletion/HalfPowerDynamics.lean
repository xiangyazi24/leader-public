import Leader.PPL.TokenCompletion.HalfPowerReduction

/-!
# P_PL Lemma 4: repaired half-power dynamics

## Truth verdict for the old Lemma4HalfPowerDynamics

The old Prop is FALSE, specifically its second conjunct.

The hole is not an old *owned* ghost entering the C_d window.  The hole is a
valid *physical* token with no ghost owner.  initialGhost intentionally omits
initially-invalid raw tokens.  But Algorithm 2 runs before Algorithm 3 line 12,
so an arbitrary prefix may change dist and thereby make such a raw token valid
before line 12 tests it.  The physical token then survives while the ghost map
still has no owner for it.  Lemma4FreshWindow quantifies only existing ghost
owners, so it does not exclude this blocker.

Concrete witness:

* n = 4, psi = 2, kappa = 32, k = 0, kind = black.
* Standard directed four-cycle.
* All leaders, ids, last bits, bullets, signals and shields are false/zero;
  all modes are Construct; clocks and hits are zero.
* Distances are [0,0,2,3].
* The only black token is at u1, with signed offset +1 and payload/carry 0.
  It is invalid initially because its target coordinate is 1 < psi.
* Prefix pre = [e0].

At e0, Algorithm 2 line 8 changes u1.dist from 0 to 1.  The old raw token at
u1 is now valid (target coordinate 2), but initialGhost had no owner for it.
The same interaction creates the source-border black token at u0; lines 16-17
immediately delete that left fresh token because the now-valid unowned token
is at u1.  The resulting physical distances are [0,1,2,3], all last bits are
false, and the selected-color ghost window is empty, so the old
Lemma4FreshWindow premise holds vacuously.

Now take the exact second half word for psi=2:

  [e0,e1,e2,e2,e1,e0, e0,e1,e2,e2,e1,e0].

The unowned token blocks the source birth at the first e0 of each block.  In
the first block it goes +1 at u1 -> -1 at u2 -> +2 at u1.  In the second it
goes +2 at u1 -> +1 at u2 -> invalid -1 at u3 and is deleted on the next e2.
Only the final e0 can then create a fresh owned token; that token has made one
move when the half-word ends.  For psi=2 a completion requires
2*psi^2-2*psi+1 = 5 moves.  Hence there is no HasFreshCompletion.

The continuation remains in C_0 throughout: only e0,e1,e2 occur, Construct
line-8 distance writes are idempotent on [0,1,2,3], line-9 keeps last=false,
and kappa=32 keeps the mode away from Detect.

Thus conjunct (2) of Lemma4HalfPowerDynamics is false.
-/

namespace PPL

set_option autoImplicit false
set_option Elab.async false

/-! ## 1. Correct midpoint predicate -/

/--
Every valid physical selected-color token in the local C_d window has a ghost
owner.  This is the missing half of the old Lemma4FreshWindow predicate.
-/
def Lemma4GhostCoveredWindow
    {n psi kappa : Nat}
    (ring : DirectedRing n) (k : Fin n)
    (kind : TokenKind) (G : GhostConfig n psi kappa) : Prop :=
  ∀ i : Fin n,
    Lemma4InWindow ring k psi i ->
    ValidToken kind G.phys i ->
    ∃ z : GhostToken n psi,
      ghostTokenAt kind G i = some z

/--
Correct midpoint invariant for Lemma 4.

The first conjunct is the old freshness assertion.  The second forbids a valid
physical selected-color blocker that is absent from the ghost map.
-/
def Lemma4CoveredFreshWindow
    {n psi kappa : Nat}
    (ring : DirectedRing n) (k : Fin n)
    (kind : TokenKind) (G : GhostConfig n psi kappa) : Prop :=
  Lemma4FreshWindow ring k kind G ∧
    Lemma4GhostCoveredWindow ring k kind G

theorem lemma4CoveredFreshWindow_fresh
    {n psi kappa : Nat}
    {ring : DirectedRing n} {k : Fin n}
    {kind : TokenKind} {G : GhostConfig n psi kappa}
    (h : Lemma4CoveredFreshWindow ring k kind G) :
    Lemma4FreshWindow ring k kind G :=
  h.1

theorem lemma4CoveredFreshWindow_covered
    {n psi kappa : Nat}
    {ring : DirectedRing n} {k : Fin n}
    {kind : TokenKind} {G : GhostConfig n psi kappa}
    (h : Lemma4CoveredFreshWindow ring k kind G) :
    Lemma4GhostCoveredWindow ring k kind G :=
  h.2

/-! ## 2. Corrected half-power statement -/

/--
Corrected replacement for Lemma4HalfPowerDynamics.

The only change is that the midpoint and second-half entry carry
Lemma4CoveredFreshWindow rather than Lemma4FreshWindow.  Clause (1) is still
the source first-half purge, but it now also records ghost coverage of every
valid physical token.  Clause (2) is then protected from the revived-unowned
counterexample above.
-/
def Lemma4HalfPowerDynamicsCovered : Prop :=
  ∀ {n psi kappa : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind),
    (∀ (C : Config n psi kappa)
       (schedule : DetSchedule n),
      CdTrace hpsi ring k kind C schedule ->
      (lemma4HalfWord ring k psi).Sublist schedule ->
      Lemma4CoveredFreshWindow ring k kind
        (ghostRun hpsi ring 0 (initialGhost C) schedule)) ∧
    (∀ (C0 : Config n psi kappa)
       (pre : DetSchedule n)
       (G : GhostConfig n psi kappa)
       (schedule : DetSchedule n),
      G = ghostRun hpsi ring 0 (initialGhost C0) pre ->
      Lemma4CoveredFreshWindow ring k kind G ->
      CdTrace hpsi ring k kind G.phys schedule ->
      (lemma4HalfWord ring k psi).Sublist schedule ->
      HasFreshCompletion kind k
        (ghostRun hpsi ring pre.length G schedule))

/-!
The existing two-half assembly needs no other semantic change.
-/
theorem lemma4_deterministic_core_of_coveredHalfPowerDynamics
    (hdyn : Lemma4HalfPowerDynamicsCovered) :
    lemma4_deterministic_core := by
  intro n psi kappa hpsi ring k kind C schedule hCd hsub

  have hword :
      lemma4Word ring k psi =
        lemma4HalfWord ring k psi ++
          lemma4HalfWord ring k psi :=
    lemma4Word_eq_two_halves ring k
  rw [hword] at hsub

  rcases List.append_sublist_iff.mp hsub with
    ⟨pre, post, hschedule, hpre, hpost⟩
  subst schedule

  rcases
    lemma4_cdTrace_append
      hpsi ring k kind C pre post hCd
    with ⟨hCdPre, hCdPost⟩

  let Gmid : GhostConfig n psi kappa :=
    ghostRun hpsi ring 0 (initialGhost C) pre

  have hFreshCovered :
      Lemma4CoveredFreshWindow ring k kind Gmid := by
    simpa [Gmid] using
      (hdyn hpsi ring k kind).1 C pre hCdPre hpre

  have hmidPhys :
      Gmid.phys =
        PPL.Probability.runPopulationSchedule
          (protocol psi kappa) ring C pre := by
    have h :=
      ghostRun_erases hpsi ring 0 (initialGhost C) pre
    rw [lemma4_erase_initialGhost C] at h
    simpa [Gmid, eraseGhost] using h

  have hCdPost' :
      CdTrace hpsi ring k kind Gmid.phys post := by
    rw [hmidPhys]
    exact hCdPost

  have hfinish :
      HasFreshCompletion kind k
        (ghostRun hpsi ring pre.length Gmid post) := by
    exact
      (hdyn hpsi ring k kind).2
        C pre Gmid post rfl
        hFreshCovered hCdPost' hpost

  rw [lemma4_ghostRun_append
    hpsi ring 0 (initialGhost C) pre post]
  simpa [Gmid] using hfinish

/-! ## 3. Public progress coordinates for the remaining local proof -/

/--
Macro-stage used by the source proof.  For a valid positive-offset token this
is its right target coordinate; for a valid negative-offset token it is the
left target coordinate shifted by psi-1.  Under C_d it lies in
[psi,2*psi-1].
-/
def lemma4TokenStage
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi) : Nat :=
  let target :=
    (tokenTargetCoordinate kind q t).toNat
  if 0 < decodeOffset psi (tokenCode t) then
    target
  else
    target + psi - 1

/--
Number of physical moves already spent in the canonical Lemma-4 trajectory,
measured from a fresh +psi token at stage psi.

For a positive offset c, psi-c right moves of the current stage have been
spent.  For c<0, the right leg is complete and
2*psi-|c|-1 moves of the whole stage have been spent.
-/
def lemma4TokenProgress
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi) : Nat :=
  let c := decodeOffset psi (tokenCode t)
  let stage := lemma4TokenStage kind q t
  let base := (stage - psi) * (2 * psi - 1)
  if 0 < c then
    base + (psi - c.toNat)
  else
    base + (2 * psi - c.natAbs - 1)

/--
The unique scheduler edge that services this token at its present signed leg:
positive offsets move as initiator; negative offsets move as responder.
-/
def lemma4ServiceEdge
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (kind : TokenKind)
    (G : GhostConfig n psi kappa)
    (i : Fin n)
    (z : GhostToken n psi) : Fin n :=
  if 0 < decodeOffset psi (tokenCode z.value) then
    i
  else
    ring.leftNeighbor i

/--
A concrete rightmost owned token, not merely a rightmost runtime slot.
Validity is explicit because the counterexample is exactly about a valid
physical slot with no owner.
-/
def Lemma4RightmostAt
    {n psi kappa : Nat}
    (ring : DirectedRing n) (k : Fin n)
    (kind : TokenKind)
    (G : GhostConfig n psi kappa)
    (x : Fin (2 * psi))
    (z : GhostToken n psi) : Prop :=
  let i := shiftRight ring k x.val
  ghostTokenAt kind G i = some z ∧
    ValidToken kind G.phys i ∧
    ∀ y : Fin (2 * psi),
      x.val < y.val ->
        ghostTokenAt kind G
          (shiftRight ring k y.val) = none

/-! ## 4. The two remaining single-interaction facts -/

/--
STEP FACT 1: ghost coverage and no valid foreign entry.

Base: initialGhost owns every initially valid selected-color physical token in
the C_d window.

Step: between two C_d states, one literal ghostStep preserves that coverage.
Moreover, every post-step in-window owner is either a descendant of an
in-window pre-step owner with the same lineage id, or a fresh birth at k.

This is where the repaired statement uses the literal order
Algorithm 2 -> Algorithm 3 line 12.  Pre/post C_d prevents the
invalid-to-valid revival seen in the counterexample during the second half,
and Definition-3 validity prevents a valid outside token from crossing the
window boundary.
-/
def Lemma4CoverageStep : Prop :=
  ∀ {n psi kappa : Nat} (hpsi : 2 <= psi)
    (ring : DirectedRing n) (k : Fin n) (kind : TokenKind),
    (∀ C : Config n psi kappa,
      Cd ring k kind C ->
      Lemma4GhostCoveredWindow ring k kind
        (initialGhost C)) ∧
    (∀ (C0 : Config n psi kappa)
       (pre : DetSchedule n)
       (G : GhostConfig n psi kappa)
       (e : Fin n),
      G = ghostRun hpsi ring 0 (initialGhost C0) pre ->
      Cd ring k kind G.phys ->
      Cd ring k kind
        (ghostStep hpsi ring pre.length G e).phys ->
      Lemma4GhostCoveredWindow ring k kind G ->
      let G' := ghostStep hpsi ring pre.length G e
      Lemma4GhostCoveredWindow ring k kind G' ∧
        ∀ i z,
          Lemma4InWindow ring k psi i ->
          ghostTokenAt kind G' i = some z ->
          FreshAt kind k z.lmeta ∨
            ∃ j z0,
              Lemma4InWindow ring k psi j ∧
              ghostTokenAt kind G j = some z0 ∧
              z.lmeta.id = z0.lmeta.id)

/--
STEP FACT 2: exact rightmost-owner service dynamics.

Assume physical/ghost coverage, pre/post C_d, and choose an actual rightmost
valid owner.  One literal interaction has exactly three possible semantic
outcomes:

* a non-fresh old owner terminates;
* a fresh completion is logged; or
* the same lineage survives as the rightmost owner, its canonical progress
  never decreases, and selecting its current service edge increases progress
  by exactly one.

Freshness is preserved in the survivor branch.  The first branch is therefore
impossible for a fresh frontier.  This packages precisely the line-12
validity filter, lines 13-17 birth/collision order, and the c=+1, c>=2,
c=-1, c<=-2 movement cases; no multi-interaction or probability assertion is
hidden here.
-/
def Lemma4RightmostProgressStep : Prop :=
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
    let G' := ghostStep hpsi ring pre.length G e
    (¬FreshAt kind k z.lmeta ∧
        ∀ j z',
          ghostTokenAt kind G' j = some z' ->
          z'.lmeta.id ≠ z.lmeta.id) ∨
      HasFreshCompletion kind k G' ∨
      ∃ y z',
        Lemma4RightmostAt ring k kind G' y z' ∧
          z'.lmeta.id = z.lmeta.id ∧
          (FreshAt kind k z.lmeta ->
            FreshAt kind k z'.lmeta) ∧
          lemma4TokenProgress
              kind (G.phys i) z.value <=
            lemma4TokenProgress
              kind
              (G'.phys (shiftRight ring k y.val))
              z'.value ∧
          (e = lemma4ServiceEdge ring kind G i z ->
            lemma4TokenProgress
                kind
                (G'.phys (shiftRight ring k y.val))
                z'.value =
              lemma4TokenProgress
                kind (G.phys i) z.value + 1)

/-!
These are the only two Algorithm-3 branch facts left by this file.

Once they are proved, the remaining half-power proof is the source sweep
induction:

1. CoverageStep starts from initialGhost and forbids valid unowned entries.
2. In each H = seqR ++ seqL block choose the rightmost owner.
3. RightmostProgressStep follows its service edge through the clockwise and
   counterclockwise sweep.  A surviving owner gains one macro-stage per block;
   an old owner may terminate.
4. After psi blocks no initial owner remains.  CoverageStep says every
   remaining owner is a birth at k, yielding Lemma4CoveredFreshWindow.
5. During the second psi blocks choose the rightmost fresh owner.  Its
   termination branch is impossible, so the same service induction reaches
   tokenTrajectoryMoves psi and bumpTo logs FreshCompletion.

No further protocol-semantic fact is required; what remains after the two
step facts is list/Sublist induction over the already-defined
lemma4HalfWord.
-/

end PPL

#print axioms PPL.lemma4CoveredFreshWindow_fresh
#print axioms PPL.lemma4CoveredFreshWindow_covered
#print axioms PPL.lemma4_deterministic_core_of_coveredHalfPowerDynamics

