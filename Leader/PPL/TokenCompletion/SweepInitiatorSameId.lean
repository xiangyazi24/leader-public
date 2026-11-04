import Leader.PPL.TokenCompletion.SweepInitiator


namespace PPL


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


/-!
Truth audit on current main:
Lemma4SweepInitiatorSameIdBranch has no state-local counterexample found.


The over-aged fresh witness is not a counterexample: its tracked
initiator ID disappears from both selected-pair outputs, so it fails the
same-ID-survivor premise here.


For an initiator owner, decodeOffset_valid leaves exactly three classes:
* c < 0: the initiator is not serviced; a same-ID initiator survivor is a
  stay while the responder may execute its negative turn/move;
* c = 1: positive arrival, moving the tracked lineage to the responder;
* 2 <= c: ordinary positive right move.


The file freezes those three finite rows and proves their assembly. It also
closes the cheap negative-service arithmetic.
-/


/-! ## Shared premise and conclusion packages -/


def Lemma4SweepInitiatorSameIdPremises
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (z : GhostToken n psi) : Prop :=
  Cd ring k kind G.phys ∧
    Cd ring k kind
      (ghostStep hpsi ring step G e).phys ∧
    Lemma4GhostCoveredWindow ring k kind G ∧
    GhostSound G ∧
    GhostIdsUniqueAt step G ∧
    Lemma4FreshKinematics ring k G ∧
    Lemma4InWindow ring k psi e ∧
    ghostTokenAt kind G e = some z ∧
    ((∃ zL : GhostToken n psi,
        (ghostStepSelectedPair
            hpsi ring step G e kind).left =
          some zL ∧
        zL.lmeta.id = z.lmeta.id) ∨
      (∃ zR : GhostToken n psi,
        (ghostStepSelectedPair
            hpsi ring step G e kind).right =
          some zR ∧
        zR.lmeta.id = z.lmeta.id))


def Lemma4SweepInitiatorSameIdConclusion
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (z : GhostToken n psi) : Prop :=
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
            kind (G.phys e) z.value ≤
          lemma4TokenProgress
            kind
            ((ghostStep hpsi ring step G e).phys j)
            z'.value ∧
        (e = lemma4ServiceEdge ring kind G e z →
          lemma4TokenProgress
              kind
              ((ghostStep hpsi ring step G e).phys j)
              z'.value =
            lemma4TokenProgress
                kind (G.phys e) z.value +
              1)


/-! ## Per-offset-class rows -/


def Lemma4SweepInitiatorArrivalRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (z : GhostToken n psi),
    Lemma4SweepInitiatorSameIdPremises
        hpsi ring k kind step G e z →
    decodeOffset psi (tokenCode z.value) = 1 →
    Lemma4SweepInitiatorSameIdConclusion
      hpsi ring k kind step G e z


def Lemma4SweepInitiatorRightMoveRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (z : GhostToken n psi),
    Lemma4SweepInitiatorSameIdPremises
        hpsi ring k kind step G e z →
    2 ≤ decodeOffset psi (tokenCode z.value) →
    Lemma4SweepInitiatorSameIdConclusion
      hpsi ring k kind step G e z


def Lemma4SweepInitiatorTurnRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (z : GhostToken n psi),
    Lemma4SweepInitiatorSameIdPremises
        hpsi ring k kind step G e z →
    decodeOffset psi (tokenCode z.value) < 0 →
    Lemma4SweepInitiatorSameIdConclusion
      hpsi ring k kind step G e z


def Lemma4SweepInitiatorTurnCoreRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (step : Nat)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (z : GhostToken n psi),
    Lemma4SweepInitiatorSameIdPremises
        hpsi ring k kind step G e z →
    decodeOffset psi (tokenCode z.value) < 0 →
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
              kind (G.phys e) z.value ≤
            lemma4TokenProgress
              kind
              ((ghostStep hpsi ring step G e).phys j)
              z'.value


/-! ## Cheap offset and ring arithmetic -/


theorem lemma4SweepInitiatorOffsetCases
    {psi : Nat}
    (hpsi : 2 ≤ psi)
    (t : TokenData psi) :
    decodeOffset psi (tokenCode t) = 1 ∨
      2 ≤ decodeOffset psi (tokenCode t) ∨
      decodeOffset psi (tokenCode t) < 0 := by
  have hv :=
    decodeOffset_valid
      psi (by omega) (tokenCode t)
  rcases hv with hneg | hpos
  · exact Or.inr (Or.inr (by omega))
  · by_cases h1 :
        decodeOffset psi (tokenCode t) = 1
    · exact Or.inl h1
    · exact Or.inr (Or.inl (by omega))


private theorem initiatorSameIdCd_two_le_n
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


private theorem initiatorSameId_rightNeighbor_ne_self
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


private theorem initiatorSameId_rightNeighbor_leftNeighbor
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


private theorem initiatorSameId_leftNeighbor_ne_self
    {n : Nat}
    (ring : DirectedRing n)
    (hn2 : 2 ≤ n)
    (i : Fin n) :
    i ≠ ring.leftNeighbor i := by
  intro h
  have hr := congrArg (ring.rightNeighbor) h
  rw [initiatorSameId_rightNeighbor_leftNeighbor] at hr
  exact
    initiatorSameId_rightNeighbor_ne_self
      ring hn2 i hr


theorem lemma4SweepInitiatorNegative_not_service
    {n psi kappa : Nat}
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (k : Fin n)
    (kind : TokenKind)
    (G : GhostConfig n psi kappa)
    (e : Fin n)
    (z : GhostToken n psi)
    (hCd : Cd ring k kind G.phys)
    (hneg :
      decodeOffset psi (tokenCode z.value) < 0) :
    e ≠ lemma4ServiceEdge ring kind G e z := by
  have hn2 :
      2 ≤ n :=
    initiatorSameIdCd_two_le_n
      hpsi ring k kind G.phys hCd
  have hleft :
      e ≠ ring.leftNeighbor e :=
    initiatorSameId_leftNeighbor_ne_self
      ring hn2 e
  have hpos :
      ¬ 0 <
        decodeOffset psi (tokenCode z.value) := by
    omega
  simpa [lemma4ServiceEdge, hpos] using hleft


/-! ## Cheap negative-row completion -/


theorem lemma4SweepInitiatorTurnRow_of_core
    (hcore : Lemma4SweepInitiatorTurnCoreRow) :
    Lemma4SweepInitiatorTurnRow := by
  unfold Lemma4SweepInitiatorTurnRow
  intro n psi kappa hpsi
  intro ring k kind step G e z
  intro hp hneg


  have hCd :
      Cd ring k kind G.phys :=
    hp.1
  have hnot :
      e ≠ lemma4ServiceEdge ring kind G e z :=
    lemma4SweepInitiatorNegative_not_service
      hpsi ring k kind G e z hCd hneg


  have hc :=
    hcore
      hpsi ring k kind step G e z
      hp hneg
  rcases hc with hdone | hsurvive
  · exact Or.inl hdone
  · rcases hsurvive with
      ⟨j, z', hwin, hsite, hid,
        hfresh, hvalid, hprogress⟩
    exact
      Or.inr
        ⟨j, z', hwin, hsite, hid,
          hfresh, hvalid, hprogress,
          fun hservice =>
            False.elim (hnot hservice)⟩


/-! ## Requested assembly -/


theorem lemma4SweepInitiatorSameIdBranch_of_rows
    (hArrival : Lemma4SweepInitiatorArrivalRow)
    (hRight : Lemma4SweepInitiatorRightMoveRow)
    (hTurn : Lemma4SweepInitiatorTurnRow) :
    Lemma4SweepInitiatorSameIdBranch := by
  unfold Lemma4SweepInitiatorSameIdBranch
  intro n psi kappa hpsi
  intro ring k kind step G e z
  intro hCd hCd' hcovered hsound
  intro huniq hkin hwin howner hsame


  have hp :
      Lemma4SweepInitiatorSameIdPremises
        hpsi ring k kind step G e z := by
    exact
      ⟨hCd, hCd', hcovered, hsound,
        huniq, hkin, hwin, howner, hsame⟩


  have hc :=
    lemma4SweepInitiatorOffsetCases
      hpsi z.value
  rcases hc with h1 | hge | hneg
  · exact
      hArrival
        hpsi ring k kind step G e z
        hp h1
  · exact
      hRight
        hpsi ring k kind step G e z
        hp hge
  · exact
      hTurn
        hpsi ring k kind step G e z
        hp hneg


theorem lemma4SweepInitiatorSameIdBranch_of_positiveRows_and_turnCore
    (hArrival : Lemma4SweepInitiatorArrivalRow)
    (hRight : Lemma4SweepInitiatorRightMoveRow)
    (hTurnCore : Lemma4SweepInitiatorTurnCoreRow) :
    Lemma4SweepInitiatorSameIdBranch := by
  exact
    lemma4SweepInitiatorSameIdBranch_of_rows
      hArrival hRight
      (lemma4SweepInitiatorTurnRow_of_core
        hTurnCore)


end PPL


#print axioms PPL.lemma4SweepInitiatorOffsetCases
#print axioms PPL.lemma4SweepInitiatorNegative_not_service
#print axioms PPL.lemma4SweepInitiatorTurnRow_of_core
#print axioms PPL.lemma4SweepInitiatorSameIdBranch_of_rows
#print axioms PPL.lemma4SweepInitiatorSameIdBranch_of_positiveRows_and_turnCore


