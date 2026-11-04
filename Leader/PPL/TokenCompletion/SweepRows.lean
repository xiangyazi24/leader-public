import Leader.PPL.TokenCompletion.Sweep
import Leader.PPL.TokenCompletion.RunFacts
import Leader.PPL.TokenCompletion.GhostStepMirror

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-
The run history is discharged once, exactly as in the rightmost-row adapters:
GhostSound comes from Lemma4CoverageGhostRunSound; live-ID uniqueness and
fresh-lineage kinematics come from TokenCorrectnessLemma4RunFacts.

What remains below is state-local.  The selected-pair rows mention only one
ghostStep, and the global owner conclusion is reconstructed from the three
public site equations in TokenCorrectnessLemma4GhostStepExport.
-/

/-- The exact arbitrary-owner conclusion occurring in Lemma4SweepMissingRows. -/
def Lemma4SweepOwnerOutcome
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e i : Fin n)
    (z : GhostToken n psi) : Prop :=
  (∀ (j : Fin n) (z' : GhostToken n psi),
      ghostTokenAt kind
          (ghostStep hpsi ring step G e) j =
        some z' →
      z'.lmeta.id ≠ z.lmeta.id) ∨
    HasFreshCompletion kind k
      (ghostStep hpsi ring step G e) ∨
    ∃ j : Fin n, ∃ z' : GhostToken n psi,
      Lemma4InWindow ring k psi j ∧
        ghostTokenAt kind
            (ghostStep hpsi ring step G e) j =
          some z' ∧
        z'.lmeta.id = z.lmeta.id ∧
        (FreshAt kind k z.lmeta →
          FreshAt kind k z'.lmeta) ∧
        ValidToken kind
          (ghostStep hpsi ring step G e).phys j ∧
        lemma4TokenProgress
            kind (G.phys i) z.value ≤
          lemma4TokenProgress
            kind
            ((ghostStep hpsi ring step G e).phys j)
            z'.value ∧
        (e = lemma4ServiceEdge ring kind G i z →
          lemma4TokenProgress
              kind
              ((ghostStep hpsi ring step G e).phys j)
              z'.value =
            lemma4TokenProgress
                kind (G.phys i) z.value +
              1)

/--
Pure selected-pair fate of an interacted old owner.

The deletion branch says neither endpoint output carries the old lineage ID.
The survivor branch already records the geometric/progress facts, but records
the owner through ghostStepSelectedPair rather than through ghostTokenAt.
The public site equations are therefore sufficient to lift this to
Lemma4SweepOwnerOutcome.
-/
def Lemma4SweepPairOwnerResult
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e i : Fin n)
    (z : GhostToken n psi) : Prop :=
  ((∀ z' : GhostToken n psi,
      (ghostStepSelectedPair
          hpsi ring step G e kind).left =
        some z' →
      z'.lmeta.id ≠ z.lmeta.id) ∧
    (∀ z' : GhostToken n psi,
      (ghostStepSelectedPair
          hpsi ring step G e kind).right =
        some z' →
      z'.lmeta.id ≠ z.lmeta.id)) ∨
    HasFreshCompletion kind k
      (ghostStep hpsi ring step G e) ∨
    ∃ j : Fin n, ∃ z' : GhostToken n psi,
      Lemma4InWindow ring k psi j ∧
        ((j = e ∧
            (ghostStepSelectedPair
                hpsi ring step G e kind).left =
              some z') ∨
          (j = ring.rightNeighbor e ∧
            (ghostStepSelectedPair
                hpsi ring step G e kind).right =
              some z')) ∧
        z'.lmeta.id = z.lmeta.id ∧
        (FreshAt kind k z.lmeta →
          FreshAt kind k z'.lmeta) ∧
        ValidToken kind
          (ghostStep hpsi ring step G e).phys j ∧
        lemma4TokenProgress
            kind (G.phys i) z.value ≤
          lemma4TokenProgress
            kind
            ((ghostStep hpsi ring step G e).phys j)
            z'.value ∧
        (e = lemma4ServiceEdge ring kind G i z →
          lemma4TokenProgress
              kind
              ((ghostStep hpsi ring step G e).phys j)
              z'.value =
            lemma4TokenProgress
                kind (G.phys i) z.value +
              1)

/-- State-local selected-pair row when the tracked owner is the initiator. -/
def Lemma4SweepInitiatorLiteralCases : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (z : GhostToken n psi),
    Cd ring k kind G.phys →
    Cd ring k kind
      (ghostStep hpsi ring step G e).phys →
    Lemma4GhostCoveredWindow ring k kind G →
    GhostSound G →
    GhostIdsUniqueAt step G →
    Lemma4FreshKinematics ring k G →
    Lemma4InWindow ring k psi e →
    ghostTokenAt kind G e = some z →
    Lemma4SweepPairOwnerResult
      hpsi ring k kind step G e e z

/-- State-local selected-pair row when the tracked owner is the responder. -/
def Lemma4SweepResponderLiteralCases : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (z : GhostToken n psi),
    Cd ring k kind G.phys →
    Cd ring k kind
      (ghostStep hpsi ring step G e).phys →
    Lemma4GhostCoveredWindow ring k kind G →
    GhostSound G →
    GhostIdsUniqueAt step G →
    Lemma4FreshKinematics ring k G →
    Lemma4InWindow ring k psi
      (ring.rightNeighbor e) →
    ghostTokenAt kind G (ring.rightNeighbor e) =
      some z →
    Lemma4SweepPairOwnerResult
      hpsi ring k kind step G e
      (ring.rightNeighbor e) z

/--
State-local empty-window source-birth row.

This is the second semantic residual from the architecture brief.  The run
history has already been converted to GhostSound, uniqueness, and intrinsic
fresh kinematics; no prefix schedule occurs in this interface.
-/
def Lemma4SweepEmptyBirthLiteralCases : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n),
    Cd ring k kind G.phys →
    Cd ring k kind
      (ghostStep hpsi ring step G e).phys →
    Lemma4GhostCoveredWindow ring k kind G →
    GhostSound G →
    GhostIdsUniqueAt step G →
    Lemma4FreshKinematics ring k G →
    (¬ ∃ i : Fin n, ∃ z : GhostToken n psi,
      Lemma4InWindow ring k psi i ∧
        ghostTokenAt kind G i = some z) →
    e = k →
    HasFreshCompletion kind k
        (ghostStep hpsi ring step G e) ∨
      ∃ x : Fin (2 * psi),
        ∃ z : GhostToken n psi,
          Lemma4RightmostAt ring k kind
              (ghostStep hpsi ring step G e) x z ∧
            FreshAt kind k z.lmeta

/-- A C_d window with psi ≥ 2 cannot live on a singleton ring. -/
private theorem lemma4SweepCd_two_le_n
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (C : Config n psi kappa)
    (hCd : Cd ring k kind C) :
    2 ≤ n := by
  by_cases hn2 : 2 ≤ n
  · exact hn2
  · have hn0 : 0 < n := ring.hn
    have hn1 : n = 1 := by
      omega
    subst n

    let x0 : Fin (2 * psi) := ⟨0, by omega⟩
    let x1 : Fin (2 * psi) := ⟨1, by omega⟩

    have h0 := (hCd x0).1
    have h1 := (hCd x1).1
    dsimp only [x0, x1] at h0 h1

    have hs :
        shiftRight ring k 0 =
          shiftRight ring k 1 := by
      apply Fin.ext
      simp [shiftRight]
    rw [hs] at h0

    cases kind with
    | black =>
        have hm1 :
            1 % (2 * psi) = 1 :=
          Nat.mod_eq_of_lt (by omega)
        simp [tokenD', hm1] at h0 h1
        omega
    | white =>
        have hm0 :
            psi % (2 * psi) = psi :=
          Nat.mod_eq_of_lt (by omega)
        have hm1 :
            (1 + psi) % (2 * psi) =
              1 + psi :=
          Nat.mod_eq_of_lt (by omega)
        simp [tokenD', hm0, hm1] at h0 h1
        omega

private theorem lemma4Sweep_rightNeighbor_leftNeighbor
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n) :
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
    rw [h1,
      show n - 1 + 1 = n by omega,
      Nat.mod_self, h0]
  · have h1 :
        (i.val + n - 1) % n = i.val - 1 := by
      rw [show i.val + n - 1 =
          (i.val - 1) + n by omega,
        Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1,
      show i.val - 1 + 1 = i.val by omega,
      Nat.mod_eq_of_lt hi]

private theorem lemma4Sweep_rightNeighbor_ne
    {n : Nat}
    (ring : DirectedRing n)
    (hn2 : 2 ≤ n)
    (i : Fin n) :
    ring.rightNeighbor i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at hv
  by_cases hlt : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have heq : i.val + 1 = n := by
      omega
    rw [heq, Nat.mod_self] at hv
    omega

/-- GhostSound projected to Definition-3 validity, without naming its private helper. -/
private theorem lemma4Sweep_owner_valid
    {n psi kappa : Nat}
    (kind : TokenKind)
    (G : GhostConfig n psi kappa)
    (i : Fin n)
    (z : GhostToken n psi)
    (hsound : GhostSound G)
    (howner : ghostTokenAt kind G i = some z) :
    ValidToken kind G.phys i := by
  cases kind with
  | black =>
      have hs := hsound.1 i z howner
      unfold ValidToken
      rw [hs.1]
      exact hs.2
  | white =>
      have hs := hsound.2 i z howner
      unfold ValidToken
      rw [hs.1]
      exact hs.2

/--
A selected-pair result lifts to the global arbitrary-owner outcome.

The only nonlocal step is the deletion branch: an alleged same-ID owner at an
off-pair post site is a frame owner from the pre-state, so pre-step ID
uniqueness forces that site to be the tracked interacted endpoint.
-/
private theorem lemma4SweepPairResult_to_outcome
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e i : Fin n)
    (z : GhostToken n psi)
    (hn2 : 2 ≤ n)
    (huniq : GhostIdsUniqueAt step G)
    (htouch : i = e ∨ i = ring.rightNeighbor e)
    (howner : ghostTokenAt kind G i = some z)
    (hpair :
      Lemma4SweepPairOwnerResult
        hpsi ring k kind step G e i z) :
    Lemma4SweepOwnerOutcome
      hpsi ring k kind step G e i z := by
  have hne :
      ring.rightNeighbor e ≠ e :=
    lemma4Sweep_rightNeighbor_ne ring hn2 e

  rcases hpair with hdel | hrest
  · refine Or.inl ?_
    intro j z' hpost
    by_cases hje : j = e
    · subst j
      have hout :
          (ghostStepSelectedPair
              hpsi ring step G e kind).left =
            some z' := by
        exact
          (ghostTokenAt_ghostStep_initiator
            hpsi ring step G e kind).symm.trans hpost
      exact hdel.1 z' hout
    · by_cases hjr : j = ring.rightNeighbor e
      · subst j
        have hout :
            (ghostStepSelectedPair
                hpsi ring step G e kind).right =
              some z' := by
          exact
            (ghostTokenAt_ghostStep_responder_of_ne
              hpsi ring step G e kind hne).symm.trans hpost
        exact hdel.2 z' hout
      · have hpre :
            ghostTokenAt kind G j = some z' := by
          have hframe :=
            ghostTokenAt_ghostStep_frame
              hpsi ring step G e j kind hje hjr
          exact hframe.symm.trans hpost
        intro hid
        have hji : j = i :=
          huniq.1 kind j i z' z hpre howner hid
        rcases htouch with hie | hir
        · exact hje (hji.trans hie)
        · exact hjr (hji.trans hir)

  · rcases hrest with hcompletion | hsurvive
    · exact Or.inr (Or.inl hcompletion)
    · rcases hsurvive with
        ⟨j, z', hwin, hsite, hid, hfresh,
          hvalid, hprogress, hservice⟩
      have hpost :
          ghostTokenAt kind
              (ghostStep hpsi ring step G e) j =
            some z' := by
        rcases hsite with hleft | hright
        · rcases hleft with ⟨hje, hout⟩
          subst j
          exact
            (ghostTokenAt_ghostStep_initiator
              hpsi ring step G e kind).trans hout
        · rcases hright with ⟨hjr, hout⟩
          subst j
          exact
            (ghostTokenAt_ghostStep_responder_of_ne
              hpsi ring step G e kind hne).trans hout
      exact
        Or.inr
          (Or.inr
            ⟨j, z', hwin, hpost, hid, hfresh,
              hvalid, hprogress, hservice⟩)

/--
The complete off-pair row.

Both the physical state and selected owner at i are literal frames.  Therefore
progress is unchanged.  If e were the service edge, the signed-offset
definition of lemma4ServiceEdge would force i to be one of the two interaction
endpoints, contradicting the off-pair hypotheses.
-/
private theorem lemma4SweepOwnerFrame
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e i : Fin n)
    (z : GhostToken n psi)
    (hsound : GhostSound G)
    (hwin : Lemma4InWindow ring k psi i)
    (howner : ghostTokenAt kind G i = some z)
    (hie : i ≠ e)
    (hir : i ≠ ring.rightNeighbor e) :
    Lemma4SweepOwnerOutcome
      hpsi ring k kind step G e i z := by
  have hpostOwner :
      ghostTokenAt kind
          (ghostStep hpsi ring step G e) i =
        some z := by
    exact
      (ghostTokenAt_ghostStep_frame
        hpsi ring step G e i kind hie hir).trans
        howner

  have hphys :
      (ghostStep hpsi ring step G e).phys i =
        G.phys i := by
    change
      PopulationProtocol.step
          (protocol psi kappa)
          ring G.phys e i =
        G.phys i
    simp [PopulationProtocol.step, hie, hir]

  have hvalid0 :
      ValidToken kind G.phys i :=
    lemma4Sweep_owner_valid
      kind G i z hsound howner

  have hvalid :
      ValidToken kind
        (ghostStep hpsi ring step G e).phys i := by
    unfold ValidToken at hvalid0 ⊢
    rw [hphys]
    exact hvalid0

  have hprogress :
      lemma4TokenProgress
          kind (G.phys i) z.value ≤
        lemma4TokenProgress
          kind
          ((ghostStep hpsi ring step G e).phys i)
          z.value := by
    rw [hphys]
    exact Nat.le_refl _

  have hservice :
      e = lemma4ServiceEdge ring kind G i z →
        lemma4TokenProgress
            kind
            ((ghostStep hpsi ring step G e).phys i)
            z.value =
          lemma4TokenProgress
              kind (G.phys i) z.value +
            1 := by
    intro hs
    have hfalse : False := by
      unfold lemma4ServiceEdge at hs
      by_cases hpos :
          0 < decodeOffset psi (tokenCode z.value)
      · rw [if_pos hpos] at hs
        exact hie hs.symm
      · rw [if_neg hpos] at hs
        have hr :
            ring.rightNeighbor e = i := by
          rw [hs]
          exact
            lemma4Sweep_rightNeighbor_leftNeighbor
              ring i
        exact hir hr.symm
    exact False.elim hfalse

  exact
    Or.inr
      (Or.inr
        ⟨i, z, hwin, hpostOwner, rfl,
          (fun hfresh => hfresh), hvalid,
          hprogress, hservice⟩)

private theorem lemma4SweepInitiator_of_literal
    {n psi kappa : Nat}
    (hliteral : Lemma4SweepInitiatorLiteralCases)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (z : GhostToken n psi)
    (hn2 : 2 ≤ n)
    (hCd :
      Cd ring k kind G.phys)
    (hCd' :
      Cd ring k kind
        (ghostStep hpsi ring step G e).phys)
    (hcovered :
      Lemma4GhostCoveredWindow ring k kind G)
    (hsound : GhostSound G)
    (huniq : GhostIdsUniqueAt step G)
    (hkin : Lemma4FreshKinematics ring k G)
    (hwin : Lemma4InWindow ring k psi e)
    (howner : ghostTokenAt kind G e = some z) :
    Lemma4SweepOwnerOutcome
      hpsi ring k kind step G e e z := by
  apply
    lemma4SweepPairResult_to_outcome
      hpsi ring k kind step G e e z
      hn2 huniq (Or.inl rfl) howner
  exact
    hliteral
      hpsi ring k kind step G e z
      hCd hCd' hcovered hsound huniq hkin
      hwin howner

private theorem lemma4SweepResponder_of_literal
    {n psi kappa : Nat}
    (hliteral : Lemma4SweepResponderLiteralCases)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (z : GhostToken n psi)
    (hn2 : 2 ≤ n)
    (hCd :
      Cd ring k kind G.phys)
    (hCd' :
      Cd ring k kind
        (ghostStep hpsi ring step G e).phys)
    (hcovered :
      Lemma4GhostCoveredWindow ring k kind G)
    (hsound : GhostSound G)
    (huniq : GhostIdsUniqueAt step G)
    (hkin : Lemma4FreshKinematics ring k G)
    (hwin :
      Lemma4InWindow ring k psi
        (ring.rightNeighbor e))
    (howner :
      ghostTokenAt kind G (ring.rightNeighbor e) =
        some z) :
    Lemma4SweepOwnerOutcome
      hpsi ring k kind step G e
      (ring.rightNeighbor e) z := by
  apply
    lemma4SweepPairResult_to_outcome
      hpsi ring k kind step G e
      (ring.rightNeighbor e) z
      hn2 huniq (Or.inr rfl) howner
  exact
    hliteral
      hpsi ring k kind step G e z
      hCd hCd' hcovered hsound huniq hkin
      hwin howner

/--
Run-history-free reduction of Lemma4SweepMissingRows.

Only three state-local literals remain as hypotheses:
the two selected-pair old-owner rows and the empty-window source-birth row.
The off-pair owner row is closed above.
-/
theorem lemma4SweepMissingRows_of_literal
    (hsound : Lemma4CoverageGhostRunSound)
    (hinitiator : Lemma4SweepInitiatorLiteralCases)
    (hresponder : Lemma4SweepResponderLiteralCases)
    (hbirth : Lemma4SweepEmptyBirthLiteralCases) :
    Lemma4SweepMissingRows := by
  unfold Lemma4SweepMissingRows
  intro n psi kappa hpsi
  intro ring k kind C0 pre G e
  intro hrun hCd hCd' hcovered

  have hsoundG : GhostSound G := by
    rw [hrun]
    exact hsound hpsi ring C0 pre

  have hn2 : 2 ≤ n :=
    lemma4SweepCd_two_le_n
      hpsi ring k kind G.phys hCd

  have huniq :
      GhostIdsUniqueAt pre.length G := by
    rw [hrun]
    exact
      ghostIdsUnique_run
        hpsi hn2 ring C0 pre

  have hkin :
      Lemma4FreshKinematics ring k G := by
    rw [hrun]
    exact
      lemma4FreshKinematics_run
        hpsi ring k C0 pre

  dsimp only
  constructor
  · intro i z hwin howner
    by_cases hie : i = e
    · subst i
      exact
        lemma4SweepInitiator_of_literal
          hinitiator
          hpsi ring k kind pre.length
          G e z hn2
          hCd hCd' hcovered
          hsoundG huniq hkin
          hwin howner

    · by_cases hir : i = ring.rightNeighbor e
      · subst i
        exact
          lemma4SweepResponder_of_literal
            hresponder
            hpsi ring k kind pre.length
            G e z hn2
            hCd hCd' hcovered
            hsoundG huniq hkin
            hwin howner

      · exact
          lemma4SweepOwnerFrame
            hpsi ring k kind pre.length
            G e i z hsoundG
            hwin howner hie hir

  · intro hempty hek
    exact
      hbirth
        hpsi ring k kind pre.length
        G e
        hCd hCd' hcovered
        hsoundG huniq hkin
        hempty hek

end PPL

#print axioms PPL.lemma4SweepMissingRows_of_literal

