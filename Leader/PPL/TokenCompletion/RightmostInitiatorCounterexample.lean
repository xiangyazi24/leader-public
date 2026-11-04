import Leader.PPL.TokenCompletion.RightmostInitiator
import Leader.PPL.TokenCompletion.GhostStepMirror


namespace PPL


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


private theorem initiatorRefuteHpsi : 2 ≤ 2 := by
  omega


private def initiatorRefuteRing : DirectedRing 4 :=
  ⟨by omega⟩


private def initiatorRefuteK : Fin 4 :=
  ⟨0, by omega⟩


private def initiatorRefuteE0 : Fin 4 :=
  ⟨0, by omega⟩


private def initiatorRefuteE1 : Fin 4 :=
  ⟨1, by omega⟩


private def initiatorRefuteE2 : Fin 4 :=
  ⟨2, by omega⟩


private def initiatorRefuteE3 : Fin 4 :=
  ⟨3, by omega⟩


private def initiatorRefuteX : Fin 4 :=
  ⟨2, by omega⟩


private def initiatorRefuteValue : TokenData 2 :=
  ((offsetOneCode 2 initiatorRefuteHpsi, (0 : Fin 2)),
    (0 : Fin 2))


/-
This is deliberately an over-aged fresh lineage.


For psi=2 and c=+1, q=5 gives the intrinsic trajectory point
  x = q + (psi-1) = 6,
which is physical site 2 on the four-cycle.  Its move count is
  5*(2*psi-1) + (psi-1) = 16.
The genuine terminal count is only 5.
-/
private def initiatorRefuteZ : GhostToken 4 2 where
  value := initiatorRefuteValue
  lmeta :=
    { id := .born .black 0
      birthSite := initiatorRefuteK
      birthStep := 0
      moves := 16 }


private def initiatorRefuteState (i : Fin 4) :
    State 2 32 :=
  { leader := false
    id := false
    dist := ⟨i.val, i.isLt⟩
    last := false
    tokenB :=
      if i = initiatorRefuteE2 then
        some initiatorRefuteValue
      else
        none
    tokenW := none
    mode := false
    clock := (0 : Fin 33)
    signalR := (0 : Fin 33)
    hits := (0 : Fin 3)
    bullet := (0 : Fin 3)
    shield := false
    signalB := false }


private def initiatorRefuteC : Config 4 2 32 :=
  initiatorRefuteState


private def initiatorRefuteG : GhostConfig 4 2 32 :=
  { phys := initiatorRefuteC
    black := fun i =>
      if i = initiatorRefuteE2 then
        some initiatorRefuteZ
      else
        none
    white := fun _ => none
    completed := [] }


private def initiatorRefuteLocalValid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi) : Prop :=
  let c := decodeOffset psi (tokenCode t)
  let target := tokenTargetCoordinate kind q t
  (0 < c ∧
      ((psi : Nat) : Int) ≤ target ∧
        target ≤ (((2 * psi - 1 : Nat)) : Int)) ∨
    (c < 0 ∧
      1 ≤ target ∧
        target ≤ (((psi - 1 : Nat)) : Int))


private instance instDecidableInitiatorRefuteLocalValid
    {psi kappa : Nat}
    (kind : TokenKind)
    (q : State psi kappa)
    (t : TokenData psi) :
    Decidable (initiatorRefuteLocalValid kind q t) := by
  unfold initiatorRefuteLocalValid
  infer_instance


private theorem initiatorRefuteFin4Cases
    (i : Fin 4) :
    i = initiatorRefuteE0 ∨
      i = initiatorRefuteE1 ∨
      i = initiatorRefuteE2 ∨
      i = initiatorRefuteE3 := by
  rcases i with ⟨v, hv⟩
  rcases v with _ | v
  · exact Or.inl rfl
  · rcases v with _ | v
    · exact Or.inr (Or.inl rfl)
    · rcases v with _ | v
      · exact Or.inr (Or.inr (Or.inl rfl))
      · rcases v with _ | v
        · exact Or.inr (Or.inr (Or.inr rfl))
        · omega


private theorem initiatorRefuteCd :
    Cd initiatorRefuteRing initiatorRefuteK
      .black initiatorRefuteC := by
  intro x
  dsimp only
  have hx : x.val < 4 := x.isLt
  simp [initiatorRefuteC, initiatorRefuteState,
    initiatorRefuteRing, initiatorRefuteK,
    shiftRight, tokenD', Nat.mod_eq_of_lt hx]


private theorem initiatorRefuteCdPost :
    Cd initiatorRefuteRing initiatorRefuteK
      .black
      (ghostStep
        initiatorRefuteHpsi
        initiatorRefuteRing
        1
        initiatorRefuteG
        initiatorRefuteE2).phys := by
  intro x
  rcases initiatorRefuteFin4Cases x with
    hx | hx | hx | hx
  · subst x
    set_option maxHeartbeats 12000000 in
      decide
  · subst x
    set_option maxHeartbeats 12000000 in
      decide
  · subst x
    set_option maxHeartbeats 12000000 in
      decide
  · subst x
    set_option maxHeartbeats 12000000 in
      decide


private theorem initiatorRefuteCovered :
    Lemma4GhostCoveredWindow
      initiatorRefuteRing
      initiatorRefuteK
      .black
      initiatorRefuteG := by
  intro i _hwin hvalid
  by_cases hi : i = initiatorRefuteE2
  · subst i
    refine ⟨initiatorRefuteZ, ?_⟩
    simp [initiatorRefuteG, ghostTokenAt]
  · have htok :
        tokenAt .black
            (initiatorRefuteG.phys i) =
          none := by
      simp [initiatorRefuteG,
        initiatorRefuteC,
        initiatorRefuteState,
        tokenAt, hi]
    unfold ValidToken at hvalid
    rw [htok] at hvalid
    exact False.elim hvalid


private theorem initiatorRefuteBlackOwnerShape
    (i : Fin 4)
    (z : GhostToken 4 2)
    (h :
      ghostTokenAt .black initiatorRefuteG i =
        some z) :
    i = initiatorRefuteE2 ∧
      z = initiatorRefuteZ := by
  by_cases hi : i = initiatorRefuteE2
  · subst i
    have hz :
        initiatorRefuteZ = z := by
      simpa [initiatorRefuteG, ghostTokenAt] using h
    exact ⟨rfl, hz.symm⟩
  · have hf : False := by
      simpa [initiatorRefuteG, ghostTokenAt, hi] using h
    exact False.elim hf


private theorem initiatorRefuteWhiteOwnerFalse
    (i : Fin 4)
    (z : GhostToken 4 2)
    (h :
      ghostTokenAt .white initiatorRefuteG i =
        some z) :
    False := by
  simpa [initiatorRefuteG, ghostTokenAt] using h


private theorem initiatorRefuteGhostSound :
    GhostSound initiatorRefuteG := by
  change
    (∀ i z,
      ghostTokenAt .black initiatorRefuteG i =
          some z →
        tokenAt .black
              (initiatorRefuteG.phys i) =
            some z.value ∧
          initiatorRefuteLocalValid
            .black
            (initiatorRefuteG.phys i)
            z.value) ∧
    (∀ i z,
      ghostTokenAt .white initiatorRefuteG i =
          some z →
        tokenAt .white
              (initiatorRefuteG.phys i) =
            some z.value ∧
          initiatorRefuteLocalValid
            .white
            (initiatorRefuteG.phys i)
            z.value)
  constructor
  · intro i z hz
    have hs :=
      initiatorRefuteBlackOwnerShape i z hz
    rcases hs with ⟨rfl, rfl⟩
    constructor
    · decide
    · unfold initiatorRefuteLocalValid
      decide
  · intro i z hz
    exact False.elim
      (initiatorRefuteWhiteOwnerFalse i z hz)


private theorem initiatorRefuteUnique :
    GhostIdsUniqueAt 1 initiatorRefuteG := by
  constructor
  · intro kind i j zi zj hi hj _hid
    cases kind with
    | black =>
        have hsi :=
          initiatorRefuteBlackOwnerShape i zi hi
        have hsj :=
          initiatorRefuteBlackOwnerShape j zj hj
        exact hsi.1.trans hsj.1.symm
    | white =>
        exact False.elim
          (initiatorRefuteWhiteOwnerFalse i zi hi)
  · intro kind i z bornKind s hi hid
    cases kind with
    | black =>
        have hs :=
          initiatorRefuteBlackOwnerShape i z hi
        rw [hs.2] at hid
        cases hid
        omega
    | white =>
        exact False.elim
          (initiatorRefuteWhiteOwnerFalse i z hi)


private theorem initiatorRefuteValueOffset :
    decodeOffset 2
        (tokenCode initiatorRefuteValue) =
      (1 : Int) := by
  change
    decodeOffset 2
        (offsetOneCode 2 initiatorRefuteHpsi) =
      (1 : Int)
  exact decodeOffset_one 2 initiatorRefuteHpsi


private theorem initiatorRefuteKinematics :
    Lemma4FreshKinematics
      initiatorRefuteRing
      initiatorRefuteK
      initiatorRefuteG := by
  intro kind i z howner _hfresh
  cases kind with
  | black =>
      have hs :=
        initiatorRefuteBlackOwnerShape i z howner
      rcases hs with ⟨rfl, rfl⟩
      refine ⟨6, ?_, ?_⟩
      · decide
      · change
          Lemma4FreshTrajectoryPoint
            2 16 6
            (decodeOffset 2
              (tokenCode initiatorRefuteValue))
        rw [initiatorRefuteValueOffset]
        left
        refine ⟨5, ?_, ?_, ?_, ?_⟩
        · omega
        · omega
        · omega
        · omega
  | white =>
      exact False.elim
        (initiatorRefuteWhiteOwnerFalse i z howner)


private theorem initiatorRefuteTrack :
    initiatorRefuteE2 =
      shiftRight
        initiatorRefuteRing
        initiatorRefuteK
        initiatorRefuteX.val := by
  decide


private theorem initiatorRefuteRightmost :
    Lemma4RightmostAt
      initiatorRefuteRing
      initiatorRefuteK
      .black
      initiatorRefuteG
      initiatorRefuteX
      initiatorRefuteZ := by
  unfold Lemma4RightmostAt
  dsimp only
  have hsite :
      shiftRight
          initiatorRefuteRing
          initiatorRefuteK
          initiatorRefuteX.val =
        initiatorRefuteE2 :=
    initiatorRefuteTrack.symm
  rw [hsite]
  refine ⟨?_, ?_, ?_⟩
  · simp [initiatorRefuteG, ghostTokenAt]
  · decide
  · intro y hy
    have hy3 :
        y = initiatorRefuteE3 := by
      apply Fin.ext
      dsimp [initiatorRefuteX] at hy
      have hlt := y.isLt
      dsimp [initiatorRefuteE3]
      omega
    subst y
    have hs3 :
        shiftRight
            initiatorRefuteRing
            initiatorRefuteK
            initiatorRefuteE3.val =
          initiatorRefuteE3 := by
      decide
    rw [hs3]
    simp [initiatorRefuteG, ghostTokenAt,
      initiatorRefuteE2, initiatorRefuteE3]


private theorem initiatorRefuteFresh :
    FreshAt .black
      initiatorRefuteK
      initiatorRefuteZ.lmeta := by
  refine ⟨0, rfl, rfl⟩


private theorem initiatorRefutePostBlackNone
    (i : Fin 4) :
    ghostTokenAt .black
        (ghostStep
          initiatorRefuteHpsi
          initiatorRefuteRing
          1
          initiatorRefuteG
          initiatorRefuteE2)
        i =
      none := by
  rcases initiatorRefuteFin4Cases i with
    hi | hi | hi | hi
  · subst i
    set_option maxHeartbeats 12000000 in
      decide
  · subst i
    set_option maxHeartbeats 12000000 in
      decide
  · subst i
    set_option maxHeartbeats 12000000 in
      decide
  · subst i
    set_option maxHeartbeats 12000000 in
      decide


private theorem initiatorRefutePostCompleted :
    (ghostStep
      initiatorRefuteHpsi
      initiatorRefuteRing
      1
      initiatorRefuteG
      initiatorRefuteE2).completed =
        [] := by
  set_option maxHeartbeats 12000000 in
    decide


private theorem initiatorRefuteNoCompletion :
    ¬ HasFreshCompletion
        .black
        initiatorRefuteK
        (ghostStep
          initiatorRefuteHpsi
          initiatorRefuteRing
          1
          initiatorRefuteG
          initiatorRefuteE2) := by
  intro h
  unfold HasFreshCompletion at h
  rcases h with ⟨m, hm, _hfresh⟩
  rw [initiatorRefutePostCompleted] at hm
  simp at hm


/--
The requested literal row is false as stated.


The local hypotheses admit a fresh owner that satisfies the intrinsic
trajectory equations after an extra full ring lap.  At the final positive
service its metadata advances from 16 to 17.  For psi=2 the terminal count is
5, so bumpTo logs no completion; the destination owner is invalid and is
dropped.  Hence a fresh lineage disappears without satisfying any conclusion
disjunct.
-/
theorem lemma4RightmostInitiatorLiteralCases_false :
    ¬ Lemma4RightmostInitiatorLiteralCases := by
  intro h
  have hout :=
    h
      (n := 4) (psi := 2) (kappa := 32)
      initiatorRefuteHpsi
      initiatorRefuteRing
      initiatorRefuteK
      .black
      1
      initiatorRefuteG
      initiatorRefuteE2
      initiatorRefuteX
      initiatorRefuteZ
      initiatorRefuteCd
      initiatorRefuteCdPost
      initiatorRefuteCovered
      initiatorRefuteGhostSound
      initiatorRefuteUnique
      initiatorRefuteKinematics
      initiatorRefuteRightmost
      initiatorRefuteTrack
  dsimp only at hout
  rcases hout with hdeleted | hrest
  · exact hdeleted.1 initiatorRefuteFresh
  · rcases hrest with hdone | hsurvive
    · exact initiatorRefuteNoCompletion hdone
    · rcases hsurvive with
        ⟨y, z', hright, _hid, _hfresh,
          _hprogress, _hservice⟩
      unfold Lemma4RightmostAt at hright
      have howner := hright.1
      rw [initiatorRefutePostBlackNone
        (shiftRight
          initiatorRefuteRing
          initiatorRefuteK
          y.val)] at howner
      cases howner


end PPL


#print axioms PPL.lemma4RightmostInitiatorLiteralCases_false
