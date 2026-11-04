import Leader.PPL.ReachCPB.MismatchCapped


namespace PPL.Convergence.ReachCPB


set_option autoImplicit false
set_option Elab.async false


/-!
Counterexample to Lemma16MismatchCompletionStepSpec.


n=4, psi=2, kappa=1.


The black lineage is born at site 0.  Its first comparison writes target bit 0.
After its c=-1 turn has already captured source bit 1 = false, an independent
white token writes that source bit to true while the site is still Construct.
Two later hits restore that site to clock=kappa.  Thus immediately before the
black fifth move we have LastReadyCapped and the bad segment equation, but the
black token still carries the stale false bit.  Its final comparison therefore
matches target bit 1, creates no leader, and ghostStep logs FreshCompletion.
-/


private def mismatchStepRing : DirectedRing 4 :=
  ⟨by decide⟩


private def mismatchStep0 : Fin 4 := ⟨0, by decide⟩
private def mismatchStep1 : Fin 4 := ⟨1, by decide⟩
private def mismatchStep2 : Fin 4 := ⟨2, by decide⟩
private def mismatchStep3 : Fin 4 := ⟨3, by decide⟩


/-- A valid white +psi token.  Its c=1 comparison is used only to rewrite
source bit 1 after the black lineage has captured the old value. -/
private def mismatchStepWhiteToken : PPL.TokenData 2 :=
  ((PPL.offsetPsiCode 2 (by decide), (1 : Fin 2)), (0 : Fin 2))


private def mismatchStepState (i : Fin 4) : PPL.State 2 1 :=
  {
    leader := false
    id := false
    dist := ⟨i.val, by omega⟩
    last := false
    tokenB := none
    tokenW :=
      if i = mismatchStep3 then
        some mismatchStepWhiteToken
      else
        none
    mode := true
    clock :=
      if i = mismatchStep1 ∨ i = mismatchStep2 then
        (0 : Fin 2)
      else
        (1 : Fin 2)
    signalR := 0
    hits := 0
    bullet := 0
    shield := false
    signalB := false
  }


private def mismatchStepC0 : Config 4 2 1 :=
  mismatchStepState


/-
Black moves:
  edge 0 : birth at 0, +2 -> +1 at 1                     (move 1)
  edge 1 : +1 comparison writes id(2)=true, bounce       (move 2)
  edge 1 : -1 turn at source site 1, captures id(1)=false (move 3)


Then:
  edge 3 : initial white +2 moves to site 0 with +1
  edge 0 : white +1 comparison writes id(1)=true


Black then:
  edge 1 : +2 -> +1 at site 2                            (move 4)


Finally the two edge-0 interactions cap site 1 without moving black.
At this point source bits are (false,true), target bits are (true,false):
target=1 whereas source+1=3 mod 4, so the bad witness holds.
-/
private def mismatchStepPre : DetSchedule 4 :=
  [ mismatchStep0,
    mismatchStep1,
    mismatchStep1,
    mismatchStep3,
    mismatchStep0,
    mismatchStep1,
    mismatchStep0,
    mismatchStep0 ]


private def mismatchStepMeta : PPL.LineageMeta 4 :=
  {
    id := .born .black 0
    birthSite := mismatchStep0
    birthStep := 0
    moves := 5
  }




/-! ## Concrete initial ghost and physical projection bridges -/


private def mismatchStepLocalValid
    {psi kappa : Nat}
    (kind : PPL.TokenKind)
    (q : PPL.State psi kappa)
    (t : PPL.TokenData psi) : Prop :=
  let c := PPL.decodeOffset psi (PPL.tokenCode t)
  let target := PPL.tokenTargetCoordinate kind q t
  Or
    (And (0 < c)
      (And (((psi : Nat) : Int) <= target)
        (target <= (((2 * psi - 1 : Nat)) : Int))))
    (And (c < 0)
      (And (1 <= target)
        (target <= (((psi - 1 : Nat)) : Int))))


private instance instDecidableMismatchStepLocalValid
    {psi kappa : Nat}
    (kind : PPL.TokenKind)
    (q : PPL.State psi kappa)
    (t : PPL.TokenData psi) :
    Decidable (mismatchStepLocalValid kind q t) := by
  unfold mismatchStepLocalValid
  infer_instance


private noncomputable def mismatchStepInitialOwned
    {n psi kappa : Nat}
    (kind : PPL.TokenKind)
    (C : Config n psi kappa)
    (i : Fin n) :
    Option (PPL.GhostToken n psi) := by
  classical
  exact
    match PPL.tokenAt kind (C i) with
    | none => none
    | some t =>
        if mismatchStepLocalValid kind (C i) t then
          some
            {
              value := t
              lmeta :=
                {
                  id := .initial kind i
                  birthSite := i
                  birthStep := 0
                  moves := 0
                }
            }
        else
          none


private theorem mismatchStepGhostTokenAtInitial
    {n psi kappa : Nat}
    (C : Config n psi kappa)
    (kind : PPL.TokenKind)
    (i : Fin n) :
    PPL.ghostTokenAt kind (PPL.initialGhost C) i =
      mismatchStepInitialOwned kind C i := by
  cases kind <;> rfl


private def mismatchStepInitialWhiteGhost :
    PPL.GhostToken 4 2 :=
  {
    value := mismatchStepWhiteToken
    lmeta :=
      {
        id := .initial .white mismatchStep3
        birthSite := mismatchStep3
        birthStep := 0
        moves := 0
      }
  }


private def mismatchStepInitialExplicit :
    PPL.GhostConfig 4 2 1 :=
  {
    phys := mismatchStepC0
    black := fun _ => none
    white := fun i =>
      if i = mismatchStep3 then
        some mismatchStepInitialWhiteGhost
      else
        none
    completed := []
  }


private theorem mismatchStepGhostConfigExt
    {n psi kappa : Nat}
    {G H : PPL.GhostConfig n psi kappa}
    (hphys : G.phys = H.phys)
    (hblack : forall i, G.black i = H.black i)
    (hwhite : forall i, G.white i = H.white i)
    (hcompleted : G.completed = H.completed) :
    G = H := by
  cases G with
  | mk gphys gblack gwhite gcompleted =>
      cases H with
      | mk hphys' hblack' hwhite' hcompleted' =>
          dsimp only at hphys hblack hwhite hcompleted
          have hb : gblack = hblack' := funext hblack
          have hw : gwhite = hwhite' := funext hwhite
          cases hphys
          cases hb
          cases hw
          cases hcompleted
          rfl


private theorem mismatchStep_initial_black_none
    (i : Fin 4) :
    PPL.ghostTokenAt .black
        (PPL.initialGhost mismatchStepC0) i = none := by
  rw [mismatchStepGhostTokenAtInitial]
  unfold mismatchStepInitialOwned
  simp [mismatchStepC0, mismatchStepState, PPL.tokenAt]


private theorem mismatchStep_initial_white_valid :
    mismatchStepLocalValid .white
      (mismatchStepC0 mismatchStep3)
      mismatchStepWhiteToken := by
  unfold mismatchStepLocalValid
  decide


private theorem mismatchStep_initial_white_some :
    PPL.ghostTokenAt .white
        (PPL.initialGhost mismatchStepC0)
        mismatchStep3 =
      some mismatchStepInitialWhiteGhost := by
  rw [mismatchStepGhostTokenAtInitial]
  unfold mismatchStepInitialOwned
  have htok :
      PPL.tokenAt .white
          (mismatchStepC0 mismatchStep3) =
        some mismatchStepWhiteToken := by
    simp
      [mismatchStepC0, mismatchStepState,
        mismatchStep3, PPL.tokenAt]
  simp only
    [htok, mismatchStep_initial_white_valid,
      if_true, ite_true]
  all_goals rfl


private theorem mismatchStep_initial_white_none
    (i : Fin 4)
    (hi : i ≠ mismatchStep3) :
    PPL.ghostTokenAt .white
        (PPL.initialGhost mismatchStepC0) i = none := by
  rw [mismatchStepGhostTokenAtInitial]
  unfold mismatchStepInitialOwned
  simp
    [mismatchStepC0, mismatchStepState,
      PPL.tokenAt, hi]


private theorem mismatchStep_initialGhost_eq :
    PPL.initialGhost mismatchStepC0 =
      mismatchStepInitialExplicit := by
  apply mismatchStepGhostConfigExt
  · rfl
  · intro i
    simpa
      [PPL.ghostTokenAt, mismatchStepInitialExplicit]
      using mismatchStep_initial_black_none i
  · intro i
    by_cases hi : i = mismatchStep3
    · subst i
      simpa
        [PPL.ghostTokenAt, mismatchStepInitialExplicit]
        using mismatchStep_initial_white_some
    · simpa
        [PPL.ghostTokenAt, mismatchStepInitialExplicit, hi]
        using mismatchStep_initial_white_none i hi
  · rfl


private theorem mismatchStep_pre_phys :
    (PPL.ghostRun
        (by decide : 2 <= 2)
        mismatchStepRing 0
        (PPL.initialGhost mismatchStepC0)
        mismatchStepPre).phys =
      PPL.Probability.runPPL
        mismatchStepRing mismatchStepC0 mismatchStepPre := by
  have h :=
    PPL.ghostRun_erases
      (by decide : 2 <= 2)
      mismatchStepRing 0
      (PPL.initialGhost mismatchStepC0)
      mismatchStepPre
  simpa
    [PPL.eraseGhost, PPL.Probability.runPPL,
      PPL.initialGhost]
    using h


private theorem mismatchStep_final_phys :
    (PPL.ghostStep
        (by decide : 2 <= 2)
        mismatchStepRing
        mismatchStepPre.length
        (PPL.ghostRun
          (by decide : 2 <= 2)
          mismatchStepRing 0
          (PPL.initialGhost mismatchStepC0)
          mismatchStepPre)
        mismatchStep2).phys =
      PopulationProtocol.step
        (PPL.protocol 2 1)
        mismatchStepRing
        (PPL.Probability.runPPL
          mismatchStepRing mismatchStepC0 mismatchStepPre)
        mismatchStep2 := by
  have h :=
    PPL.ghostStep_erases
      (by decide : 2 <= 2)
      mismatchStepRing
      mismatchStepPre.length
      (PPL.ghostRun
        (by decide : 2 <= 2)
        mismatchStepRing 0
        (PPL.initialGhost mismatchStepC0)
        mismatchStepPre)
      mismatchStep2
  simpa
    [PPL.eraseGhost, mismatchStep_pre_phys]
    using h


private theorem mismatchStep_pre_completed_eq :
    (PPL.ghostRun
        (by decide : 2 <= 2)
        mismatchStepRing 0
        (PPL.initialGhost mismatchStepC0)
        mismatchStepPre).completed = [] := by
  rw [mismatchStep_initialGhost_eq]
  rfl


private theorem mismatchStep_final_completed_eq :
    (PPL.ghostStep
        (by decide : 2 <= 2)
        mismatchStepRing
        mismatchStepPre.length
        (PPL.ghostRun
          (by decide : 2 <= 2)
          mismatchStepRing 0
          (PPL.initialGhost mismatchStepC0)
          mismatchStepPre)
        mismatchStep2).completed =
      [mismatchStepMeta] := by
  rw [mismatchStep_initialGhost_eq]
  rfl


set_option maxRecDepth 200000 in
set_option maxHeartbeats 12000000 in
private theorem mismatchStep_ready :
    LastReadyCapped mismatchStepRing
      (PPL.ghostRun
        (by decide : 2 <= 2)
        mismatchStepRing 0
        (PPL.initialGhost mismatchStepC0)
        mismatchStepPre).phys := by
  rw [mismatchStep_pre_phys]
  unfold LastReadyCapped DistReadyCapped DetectReadyCapped
    DetectReady
  refine ⟨⟨⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact @of_decide_eq_true _
      (instDecidableAllLivePeaceful _ _) rfl
  all_goals decide


set_option maxRecDepth 200000 in
set_option maxHeartbeats 12000000 in
private theorem mismatchStep_bad :
    Lemma16BadBorderWitness
      mismatchStepRing
      (PPL.ghostRun
        (by decide : 2 <= 2)
        mismatchStepRing 0
        (PPL.initialGhost mismatchStepC0)
        mismatchStepPre).phys
      mismatchStep2 mismatchStep0 .black := by
  rw [mismatchStep_pre_phys]
  unfold Lemma16BadBorderWitness PPL.IsBorder PPL.Cd
  dsimp only
  decide


private theorem mismatchStep_fresh :
    PPL.FreshCompletion
      (psi := 2) .black mismatchStep0 mismatchStepMeta := by
  constructor
  · exact ⟨0, rfl, rfl⟩
  · decide


private theorem mismatchStep_new_member :
    mismatchStepMeta ∈
      (PPL.ghostStep
        (by decide : 2 <= 2)
        mismatchStepRing
        mismatchStepPre.length
        (PPL.ghostRun
          (by decide : 2 <= 2)
          mismatchStepRing 0
          (PPL.initialGhost mismatchStepC0)
          mismatchStepPre)
        mismatchStep2).completed := by
  rw [mismatchStep_final_completed_eq]
  simp


private theorem mismatchStep_not_old_member :
    mismatchStepMeta ∉
      (PPL.ghostRun
        (by decide : 2 <= 2)
        mismatchStepRing 0
        (PPL.initialGhost mismatchStepC0)
        mismatchStepPre).completed := by
  rw [mismatchStep_pre_completed_eq]
  simp


set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
private theorem mismatchStep_final_leaderless :
    forall i : Fin 4,
      ((PPL.ghostStep
        (by decide : 2 <= 2)
        mismatchStepRing
        mismatchStepPre.length
        (PPL.ghostRun
          (by decide : 2 <= 2)
          mismatchStepRing 0
          (PPL.initialGhost mismatchStepC0)
          mismatchStepPre)
        mismatchStep2).phys i).leader = false := by
  rw [mismatchStep_final_phys]
  decide


set_option maxRecDepth 200000 in
private theorem mismatchStep_final_not_cpb :
    ¬ PPL.CPB mismatchStepRing
      (PPL.ghostStep
        (by decide : 2 <= 2)
        mismatchStepRing
        mismatchStepPre.length
        (PPL.ghostRun
          (by decide : 2 <= 2)
          mismatchStepRing 0
          (PPL.initialGhost mismatchStepC0)
          mismatchStepPre)
        mismatchStep2).phys := by
  intro hcpb
  unfold PPL.CPB PPL.CPBCore at hcpb
  rcases hcpb.1 with ⟨i, hi⟩
  dsimp only at hi
  rw [mismatchStep_final_leaderless i] at hi
  contradiction


theorem lemma16MismatchCompletionStepSpec_refuted :
    ¬ Lemma16MismatchCompletionStepSpec := by
  intro hspec
  have hs :=
    hspec
      (n := 4) (psi := 2) (kappa := 1)
      (by decide) (by decide)
      mismatchStepRing
      mismatchStepC0
      mismatchStepPre
      mismatchStep2
      mismatchStep0
      .black
      mismatchStep2
      mismatchStep_ready
      mismatchStep_bad
  dsimp only at hs
  rcases hs with hcpb | hkeep
  · exact mismatchStep_final_not_cpb hcpb
  · have hold :=
      hkeep.2.2
        mismatchStepMeta
        mismatchStep_new_member
        mismatchStep_fresh
    exact mismatchStep_not_old_member hold


end PPL.Convergence.ReachCPB


#print axioms PPL.Convergence.ReachCPB.lemma16MismatchCompletionStepSpec_refuted


