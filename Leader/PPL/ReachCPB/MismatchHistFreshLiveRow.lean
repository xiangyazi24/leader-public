import Leader.PPL.ReachCPB.MismatchHistFreshLastRewire
import Init.Omega

namespace PPL.Convergence.ReachCPB

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL
open PPL.Probability

/-!
Q1: the arbitrary-G LastReady live row is false.  The extra-lap
witness survives once its physical distance row is repaired from
[0,0,1,2] to the genuine cyclic LastReady row [3,0,1,2].  The selected pair
e=2 -> 3 is unchanged locally: dist 1 -> 2, a black responder token has
c=-1 and moves=5=tokenTrajectoryMoves 2, and the c=-1 branch advances it to
moves=6 with c=+2 while logging no completion.  The post live invariant then
forces q=2, contradicting q<psi=2.

Q2: on canonical ghostRun prefixes that exact state is excluded.
The proof seam is the responder c=-1 clause of ghostMoveToken
(TokenCorrectness.lean, the c=-1 branches around lines 277-285 and 318-326):
bumpTo only logs when the *new* move count equals tokenTrajectoryMoves.
Thus an arbitrary pre-owner already at the terminal count can move to
terminal+1 and remain live without a new completion.

For canonical runs, the minimal history fact needed here is per-LineageId:
a fresh live owner whose own LineageId has no prior completion must still be
strictly below tokenTrajectoryMoves.  The existing
lemma4FreshTerminalProvenance_run is close, but its hypothesis is the stronger
global ¬ HasFreshCompletion kind k G, so it does not directly supply this
per-ID fact when another older lineage born at k has completed.

The definitions at the end isolate that exact missing canonical invariant and
the selected-endpoint aged row.  The final theorem is a kernel-cheap adapter:
those two hypotheses imply Lemma16PostEpochFreshLiveStepGeomLastCanon.
-/

/-! -------------------------------------------------------------------------
    1. LastReady repair of the earlier example
------------------------------------------------------------------------- -/

private theorem q20063Hpsi : 2 ≤ 2 := by
  omega

private theorem q20063Hn3 : 3 ≤ 4 := by
  omega

private def q20063Ring : DirectedRing 4 :=
  ⟨by decide⟩

private def q20063E0 : Fin 4 :=
  ⟨0, by decide⟩

private def q20063E1 : Fin 4 :=
  ⟨1, by decide⟩

private def q20063E2 : Fin 4 :=
  ⟨2, by decide⟩

private def q20063E3 : Fin 4 :=
  ⟨3, by decide⟩

/-- c = -1 at psi=2, payload (bit,carry)=(0,0). -/
private def q20063TokenNegOne : PPL.TokenData 2 :=
  ((PPL.offsetNegPsiPlusOneCode
      2 q20063Hpsi,
      (0 : Fin 2)),
    (0 : Fin 2))

/--
The only change from the earlier example is the distance row:
  site : 0 1 2 3
  dist : 3 0 1 2
which is a genuine +1 mod 4 cycle.

The selected pair 2 -> 3 is still exactly 1 -> 2, so the same literal
responder c=-1 transition fires.
-/
private def q20063State
    (i : Fin 4) : PPL.State 2 1 :=
  {
    leader := false
    id := if i = q20063E2 then true else false
    dist :=
      if i = q20063E0 then
        (3 : Fin 4)
      else if i = q20063E1 then
        (0 : Fin 4)
      else if i = q20063E2 then
        (1 : Fin 4)
      else
        (2 : Fin 4)
    last := false
    tokenB :=
      if i = q20063E3 then
        some q20063TokenNegOne
      else
        none
    tokenW := none
    mode := true
    clock := (1 : Fin 2)
    signalR := 0
    hits := 0
    bullet := 0
    shield := false
    signalB := false
  }

private def q20063Cepoch : Config 4 2 1 :=
  q20063State

private def q20063Z : PPL.GhostToken 4 2 :=
  {
    value := q20063TokenNegOne
    lmeta :=
      {
        id := .born .black 0
        birthSite := q20063E0
        birthStep := 0
        moves := 5
      }
  }

private def q20063G : PPL.GhostConfig 4 2 1 :=
  {
    phys := q20063Cepoch
    black :=
      fun i =>
        if i = q20063E3 then
          some q20063Z
        else
          none
    white := fun _ => none
    completed := []
  }

private def q20063TokenPost : PPL.TokenData 2 :=
  ((PPL.offsetPsiCode
      2 q20063Hpsi,
      (1 : Fin 2)),
    (0 : Fin 2))

private def q20063ZPost : PPL.GhostToken 4 2 :=
  {
    value := q20063TokenPost
    lmeta :=
      {
        id := .born .black 0
        birthSite := q20063E0
        birthStep := 0
        moves := 6
      }
  }

private def q20063GPost : PPL.GhostConfig 4 2 1 :=
  PPL.ghostStep
    q20063Hpsi q20063Ring 1
    q20063G q20063E2

theorem lemma16PostEpochFreshLiveStepGeomLast_refuted :
    ¬ Lemma16PostEpochFreshLiveStepGeomLast := by
  intro hrow

  have hownerShape :
      ∀ (i : Fin 4)
        (z : PPL.GhostToken 4 2),
        PPL.ghostTokenAt .black
            q20063G i =
          some z →
        i = q20063E3 ∧
          z = q20063Z := by
    intro i z h
    by_cases hi : i = q20063E3
    · subst i
      have hz : q20063Z = z := by
        simpa
          [q20063G,
            PPL.ghostTokenAt]
          using h
      exact ⟨rfl, hz.symm⟩
    · have hf : False := by
        simpa
          [q20063G,
            PPL.ghostTokenAt, hi]
          using h
      exact False.elim hf

  have hgeom :
      Lemma16PostEpochFreshBorderGeometry
        q20063Ring
        q20063E2 q20063E0 2 := by
    unfold
      Lemma16PostEpochFreshBorderGeometry
    decide

  have hdetect :
      DetectReadyCapped
        q20063Ring q20063G.phys := by
    unfold DetectReadyCapped DetectReady
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_⟩
      · exact
          @of_decide_eq_true _
            (instDecidableAllLivePeaceful _ _)
            rfl
      · intro i
        revert i
        decide
      · decide
      · decide
    · intro i
      revert i
      decide

  have hready :
      LastReadyCapped
        q20063Ring q20063G.phys := by
    unfold LastReadyCapped DistReadyCapped
    refine ⟨⟨hdetect, ?_⟩, ?_⟩
    · intro i
      revert i
      decide
    · intro i
      revert i
      decide

  have hdecodeOld :
      PPL.decodeOffset 2
          (PPL.tokenCode
            q20063TokenNegOne) =
        (-1 : Int) := by
    simpa
      [q20063TokenNegOne,
        PPL.tokenCode]
      using
        (PPL.decodeOffset_negPsiPlusOne
          2 q20063Hpsi)

  have hinv :
      Lemma16PostEpochFreshStateInvariant
        q20063Ring q20063Cepoch 0
        q20063E2 q20063E0
        .black q20063G := by
    unfold
      Lemma16PostEpochFreshStateInvariant
    refine ⟨(fun _ => rfl), ?_⟩
    unfold
      Lemma16PostEpochFreshLiveInvariant
    intro i z t howner hid _hsite _hepoch _hprior
    rcases hownerShape i z howner with
      ⟨hi, hz⟩
    subst i
    subst z

    have ht : t = 0 := by
      change
        PPL.LineageId.born .black 0 =
          PPL.LineageId.born .black t
        at hid
      cases hid
      rfl
    subst t

    refine
      ⟨1, by omega, ?_, ?_, ?_, ?_⟩

    · unfold Lemma16FreshMacroStageAt
      dsimp only
      rw [show
        q20063Z.value =
          q20063TokenNegOne from rfl,
        hdecodeOld]
      refine
        ⟨3, by decide, Or.inr ?_⟩
      refine
        ⟨by omega, by decide,
          by omega, by decide⟩

    · unfold PPL.payloadCorrect
      decide

    · unfold Lemma16TargetPrefix
      intro x hx
      have hx0 : x = 0 := by
        omega
      subst x
      decide

    · intro _hneg
      decide

  have hpostOwner :
      PPL.ghostTokenAt .black
          q20063GPost q20063E2 =
        some q20063ZPost := by
    decide

  have hpostCompleted :
      q20063GPost.completed = [] := by
    decide

  have hpostLeaderless :
      ∀ i : Fin 4,
        (q20063GPost.phys i).leader =
          false := by
    decide

  have hpostNotCPB :
      ¬ PPL.CPB
          q20063Ring q20063GPost.phys := by
    intro hcpb
    unfold PPL.CPB PPL.CPBCore at hcpb
    rcases hcpb.1 with ⟨i, hi⟩
    have hf := hpostLeaderless i
    dsimp only at hi
    rw [hf] at hi
    cases hi

  have hpostNoPrior :
      Lemma16NoPriorCompletionId
        q20063GPost
        q20063ZPost.lmeta.id := by
    unfold Lemma16NoPriorCompletionId
    intro m hm
    rw [hpostCompleted] at hm
    have hf : False := by
      simpa using hm
    exact hf.elim

  unfold
    Lemma16PostEpochFreshLiveStepGeomLast
    at hrow

  have hlocal :=
    hrow
      (n := 4) (psi := 2) (kappa := 1)
      q20063Hpsi q20063Hn3
      q20063Ring
      q20063Cepoch
      0
      q20063E2 q20063E0
      .black
      1
      q20063G
      q20063E2
      hgeom
      hready
      hinv

  dsimp only at hlocal
  rcases hlocal with hcpb | hlive
  · exact hpostNotCPB hcpb
  · have hout :=
      hlive
        q20063E2
        q20063ZPost
        0
        hpostOwner
        rfl
        rfl
        (by omega)
        hpostNoPrior

    rcases hout with
      ⟨q, hq, hstage,
        _hpay, _hpref, _hlatch⟩

    have hdecodePost :
        PPL.decodeOffset 2
            (PPL.tokenCode
              q20063ZPost.value) =
          (2 : Int) := by
      simpa
        [q20063ZPost,
          q20063TokenPost,
          PPL.tokenCode]
        using
          (PPL.decodeOffset_psi
            2 q20063Hpsi)

    unfold Lemma16FreshMacroStageAt
      at hstage
    dsimp only at hstage
    rw [hdecodePost] at hstage

    rcases hstage with
      ⟨x, _hx, hpos | hneg⟩
    · have hmoves :=
        hpos.2.2.2
      have hmoves6 :
          q20063ZPost.lmeta.moves = 6 := by
        rfl
      rw [hmoves6] at hmoves
      change 6 = q * 3 at hmoves
      omega
    · have hc : (2 : Int) < 0 :=
        hneg.1
      omega

/-! -------------------------------------------------------------------------
    2. Canonical live row and the exact missing history invariant
------------------------------------------------------------------------- -/

/--
Canonical version requested in Q2.

G is definitionally the canonical prefix
  ghostRun hpsi ring 0 (initialGhost C0) pre
and the next ghost step uses step = pre.length.
-/
def Lemma16PostEpochFreshLiveStepGeomLastCanon : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (Cepoch : Config n psi kappa)
    (epoch : Nat)
    (b k : Fin n)
    (kind : PPL.TokenKind)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (e : Fin n),
    let G :=
      PPL.ghostRun hpsi ring 0
        (PPL.initialGhost C0) pre
    Lemma16PostEpochFreshBorderGeometry
      ring b k psi →
    LastReadyCapped ring G.phys →
    Lemma16PostEpochFreshStateInvariant
      ring Cepoch epoch b k kind G →
    let G' :=
      PPL.ghostStep hpsi ring pre.length G e
    PPL.CPB ring G'.phys ∨
      Lemma16PostEpochFreshLiveInvariant
        ring Cepoch epoch b k kind G'

/--
Minimal per-LineageId age fact excluding the extra-lap state.

Unlike lemma4FreshTerminalProvenance_run, the guard is exactly
Lemma16NoPriorCompletionId for this owner's LineageId, not the global
absence of every FreshCompletion born at k.
-/
def Lemma16FreshNoPriorTerminalAge
    {n psi kappa : Nat}
    (kind : PPL.TokenKind)
    (k : Fin n)
    (G : PPL.GhostConfig n psi kappa) : Prop :=
  ∀ (i : Fin n)
    (z : PPL.GhostToken n psi),
    PPL.ghostTokenAt kind G i = some z →
    PPL.FreshAt kind k z.lmeta →
    Lemma16NoPriorCompletionId
      G z.lmeta.id →
    z.lmeta.moves <
      PPL.tokenTrajectoryMoves psi

/--
Canonical producer form of the missing history invariant.

This is the smallest run-history strengthening needed to rule out the
arbitrary-G c=-1 owner with moves already at the terminal count.
-/
def Lemma16FreshNoPriorTerminalAgeCanon : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (k : Fin n)
    (kind : PPL.TokenKind),
    Lemma16FreshNoPriorTerminalAge
      kind k
      (PPL.ghostRun hpsi ring 0
        (PPL.initialGhost C0) pre)

/--
Exact selected-endpoint residual after adding the per-ID age invariant.

The genuinely new blocker relative to the old branch expansion is the
responder c=-1 clause of ghostMoveToken: an arbitrary owner can start with
moves >= tokenTrajectoryMoves and take an unlogged extra lap.  hage excludes
that state.  The remaining literal selected-pair branch expansion is isolated
here rather than claimed proved in this bounded round.
-/
def Lemma16PostEpochFreshSelectedLiveStepGeomLastCanonAged : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (hn3 : 3 ≤ n)
    (ring : DirectedRing n)
    (Cepoch : Config n psi kappa)
    (epoch : Nat)
    (b k : Fin n)
    (kind : PPL.TokenKind)
    (C0 : Config n psi kappa)
    (pre : DetSchedule n)
    (e : Fin n),
    let G :=
      PPL.ghostRun hpsi ring 0
        (PPL.initialGhost C0) pre
    Lemma16PostEpochFreshBorderGeometry
      ring b k psi →
    LastReadyCapped ring G.phys →
    Lemma16PostEpochFreshStateInvariant
      ring Cepoch epoch b k kind G →
    Lemma16FreshNoPriorTerminalAge
      kind k G →
    let G' :=
      PPL.ghostStep hpsi ring pre.length G e
    ¬ PPL.CPB ring G'.phys →
    ∀ (i : Fin n)
      (z : PPL.GhostToken n psi)
      (t : Nat),
      (i = e ∨
        i = ring.rightNeighbor e) →
      PPL.ghostTokenAt kind G' i =
        some z →
      z.lmeta.id = .born kind t →
      z.lmeta.birthSite = k →
      epoch ≤ t →
      Lemma16NoPriorCompletionId
        G' z.lmeta.id →
      ∃ q : Nat,
        q < psi ∧
          Lemma16FreshMacroStageAt
            ring k i z q ∧
          PPL.payloadCorrect
            ring Cepoch k q z.value ∧
          Lemma16TargetPrefix
            ring Cepoch b k q ∧
          (PPL.decodeOffset psi
              (PPL.tokenCode z.value) < 0 →
            (Cepoch
                (PPL.shiftRight
                  ring b q)).id =
              lemma16ExpectedAddOneBit
                ring Cepoch k q)

/--
Kernel-cheap global adapter.

This does not assert the canonical row unconditionally.  It states precisely
what remains after Q1:
  (1) prove the per-ID canonical age invariant, and
  (2) close the selected-pair literal row under that invariant.
Everything off the selected pair is the public ghostTokenAt frame.
-/
theorem
    lemma16PostEpochFreshLiveStepGeomLastCanon_of_selectedAged
    (hAgeCanon :
      Lemma16FreshNoPriorTerminalAgeCanon)
    (hSelected :
      Lemma16PostEpochFreshSelectedLiveStepGeomLastCanonAged) :
    Lemma16PostEpochFreshLiveStepGeomLastCanon := by
  unfold
    Lemma16PostEpochFreshLiveStepGeomLastCanon
  intro n psi kappa hpsi hn3
  intro ring Cepoch epoch b k kind
  intro C0 pre e
  dsimp only
  intro hgeom hready hinv

  let G :=
    PPL.ghostRun hpsi ring 0
      (PPL.initialGhost C0) pre

  change LastReadyCapped ring G.phys
    at hready
  change
    Lemma16PostEpochFreshStateInvariant
      ring Cepoch epoch b k kind G
    at hinv
  change
    PPL.CPB ring
        (PPL.ghostStep
          hpsi ring pre.length G e).phys ∨
      Lemma16PostEpochFreshLiveInvariant
        ring Cepoch epoch b k kind
        (PPL.ghostStep
          hpsi ring pre.length G e)

  by_cases hcpb :
      PPL.CPB ring
        (PPL.ghostStep
          hpsi ring pre.length G e).phys
  · exact Or.inl hcpb
  · apply Or.inr
    unfold
      Lemma16PostEpochFreshLiveInvariant
    intro i z t
    intro howner hid hsite hepoch hprior

    have hage0 :=
      hAgeCanon
        (n := n) (psi := psi)
        (kappa := kappa)
        hpsi ring C0 pre k kind
    have hage :
        Lemma16FreshNoPriorTerminalAge
          kind k G := by
      simpa [G] using hage0

    have hselected0 :=
      hSelected
        (n := n) (psi := psi)
        (kappa := kappa)
        hpsi hn3 ring Cepoch epoch
        b k kind C0 pre e
    dsimp only at hselected0

    have hselected :=
      hselected0
        hgeom
        (by simpa [G] using hready)
        (by simpa [G] using hinv)
        (by simpa [G] using hage)
        (by simpa [G] using hcpb)

    by_cases hie : i = e
    · exact
        hselected
          i z t
          (Or.inl hie)
          (by simpa [G] using howner)
          hid hsite hepoch
          (by simpa [G] using hprior)
    · by_cases hir :
          i = ring.rightNeighbor e
      · exact
          hselected
            i z t
            (Or.inr hir)
            (by simpa [G] using howner)
            hid hsite hepoch
            (by simpa [G] using hprior)
      · have howner0 :
            PPL.ghostTokenAt kind G i =
              some z := by
          exact
            (PPL.ghostTokenAt_ghostStep_frame
              hpsi ring pre.length
              G e i kind hie hir).symm.trans
                howner

        have hprior0 :
            Lemma16NoPriorCompletionId
              G z.lmeta.id := by
          unfold
            Lemma16NoPriorCompletionId
            at hprior ⊢
          intro m hm
          apply hprior m
          simp only
            [PPL.ghostStep,
              List.mem_append]
          exact Or.inl (Or.inl hm)

        exact
          hinv.2 i z t
            howner0 hid hsite
            hepoch hprior0

end PPL.Convergence.ReachCPB

#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshLiveStepGeomLast_refuted
#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshLiveStepGeomLastCanon_of_selectedAged
