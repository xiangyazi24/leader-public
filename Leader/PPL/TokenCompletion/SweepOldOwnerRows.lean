import Leader.PPL.TokenCompletion.SweepOldOwner
import Leader.PPL.TokenCompletion.CoverageLeaves
import Leader.PPL.TokenCompletion.GhostStepMirror
import Leader.PPL.TokenCompletion.RunFacts

namespace PPL

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

/-!
Truth audit.

The old-owner step is consistent with the literal selected-colour transition.

* Off-pair: both the physical state and selected owner are literal frames, so
  lemma4TokenProgress is unchanged.  The selected edge cannot simultaneously
  be the token's service edge.
* Initiator collision/deletion: collision deletes the left contender.  If the
  tracked initiator lineage disappears, that is exactly the deletion disjunct.
  A surviving positive initiator executes c=1 or c>=2 motion; a negative
  initiator is not serviced by the selected edge.
* Responder collision/deletion: collision preserves the right contender.
  For c<=-2, the responder moves left and changes c to c+1.  For c=-1, it
  turns to +psi at the initiator.  Under the pre/post C_d equations these are
  the canonical next trajectory states, so the service move has exact +1
  progress.  Positive responders stay and are not serviced by e.

No counterexample was found.  The file below isolates the two interacted
literal rows and closes the frame row and the role assembly.
-/

/-- Unmasked conclusion required by Lemma4SweepOldOwnerProgressStep. -/
def Lemma4SweepOldOwnerOutcome
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
    ∃ j : Fin n, ∃ z' : GhostToken n psi,
      Lemma4InWindow ring k psi j ∧
        ghostTokenAt kind
            (ghostStep hpsi ring step G e) j =
          some z' ∧
        z'.lmeta.id = z.lmeta.id ∧
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

/-- Interacted-owner residual when the tracked old owner is the initiator. -/
def Lemma4SweepOldOwnerInitiatorRow : Prop :=
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
    Lemma4InWindow ring k psi e →
    ghostTokenAt kind G e = some z →
    ¬ FreshAt kind k z.lmeta →
    Lemma4SweepOldOwnerOutcome
      hpsi ring k kind step G e e z

/-- Interacted-owner residual when the tracked old owner is the responder. -/
def Lemma4SweepOldOwnerResponderRow : Prop :=
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
    Lemma4InWindow ring k psi
      (ring.rightNeighbor e) →
    ghostTokenAt kind G (ring.rightNeighbor e) =
      some z →
    ¬ FreshAt kind k z.lmeta →
    Lemma4SweepOldOwnerOutcome
      hpsi ring k kind step G e
      (ring.rightNeighbor e) z

/-- Off-pair row.  This one is completely closed below. -/
def Lemma4SweepOldOwnerFrameRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e i : Fin n)
    (z : GhostToken n psi),
    Cd ring k kind G.phys →
    Cd ring k kind
      (ghostStep hpsi ring step G e).phys →
    Lemma4GhostCoveredWindow ring k kind G →
    GhostSound G →
    GhostIdsUniqueAt step G →
    Lemma4InWindow ring k psi i →
    ghostTokenAt kind G i = some z →
    ¬ FreshAt kind k z.lmeta →
    i ≠ e →
    i ≠ ring.rightNeighbor e →
    Lemma4SweepOldOwnerOutcome
      hpsi ring k kind step G e i z

private theorem oldOwnerCd_two_le_n
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

private theorem oldOwner_rightNeighbor_leftNeighbor
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

private theorem oldOwner_owner_valid
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
The requested frame row.

The post owner and physical state at i are literal frames.  Hence progress is
equal.  The exact-service implication is vacuous: a positive token is serviced
at i itself, while a nonpositive token is serviced at leftNeighbor i, whose
responder is i.
-/
theorem lemma4SweepOldOwnerFrameRow_proved :
    Lemma4SweepOldOwnerFrameRow := by
  unfold Lemma4SweepOldOwnerFrameRow
  intro n psi kappa hpsi
  intro ring k kind step G e i z
  intro hCd hCd' hcovered hsound huniq
  intro hwin howner hnonfresh hie hir

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
    oldOwner_owner_valid
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
            oldOwner_rightNeighbor_leftNeighbor
              ring i
        exact hir hr.symm
    exact False.elim hfalse

  exact
    Or.inr
      ⟨i, z, hwin, hpostOwner, rfl,
        hvalid, hprogress, hservice⟩

/--
Assembly of the unmasked old-owner step from the three owner-role rows.

The actual-run premise supplies GhostSound from the already-proved coverage
run theorem and ID uniqueness from ghostIdsUnique_run.  The role split then
matches the endpoint split used by the responder and fresh-persistence
reductions: initiator, responder, or literal frame.
-/
theorem lemma4SweepOldOwnerProgressStep_of_rows
    (hinitiator : Lemma4SweepOldOwnerInitiatorRow)
    (hresponder : Lemma4SweepOldOwnerResponderRow)
    (hframe : Lemma4SweepOldOwnerFrameRow) :
    Lemma4SweepOldOwnerProgressStep := by
  unfold Lemma4SweepOldOwnerProgressStep
  intro n psi kappa hpsi
  intro ring k kind C0 pre G e
  intro hrun hCd hCd' hcovered
  intro i z hwin howner hnonfresh
  dsimp only

  have hsound :
      GhostSound G := by
    rw [hrun]
    exact
      lemma4CoverageGhostRunSound_proved
        hpsi ring C0 pre

  have hn2 :
      2 ≤ n :=
    oldOwnerCd_two_le_n
      hpsi ring k kind G.phys hCd

  have huniq :
      GhostIdsUniqueAt pre.length G := by
    rw [hrun]
    exact
      ghostIdsUnique_run
        hpsi hn2 ring C0 pre

  change
    Lemma4SweepOldOwnerOutcome
      hpsi ring k kind pre.length G e i z

  by_cases hie : i = e
  · subst i
    exact
      hinitiator
        hpsi ring k kind pre.length G e z
        hCd hCd' hcovered hsound huniq
        hwin howner hnonfresh

  · by_cases hir : i = ring.rightNeighbor e
    · subst i
      exact
        hresponder
          hpsi ring k kind pre.length G e z
          hCd hCd' hcovered hsound huniq
          hwin howner hnonfresh

    · exact
        hframe
          hpsi ring k kind pre.length
          G e i z
          hCd hCd' hcovered hsound huniq
          hwin howner hnonfresh
          hie hir

/-- Convenience form with the closed frame row discharged. -/
theorem lemma4SweepOldOwnerProgressStep_of_interacted_rows
    (hinitiator : Lemma4SweepOldOwnerInitiatorRow)
    (hresponder : Lemma4SweepOldOwnerResponderRow) :
    Lemma4SweepOldOwnerProgressStep := by
  exact
    lemma4SweepOldOwnerProgressStep_of_rows
      hinitiator hresponder
      lemma4SweepOldOwnerFrameRow_proved

end PPL

#print axioms PPL.lemma4SweepOldOwnerFrameRow_proved
#print axioms PPL.lemma4SweepOldOwnerProgressStep_of_rows
#print axioms PPL.lemma4SweepOldOwnerProgressStep_of_interacted_rows

