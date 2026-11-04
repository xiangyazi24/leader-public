import Leader.PPL.ReachCPB.MismatchHistFreshLiteralRows


namespace PPL.Convergence.ReachCPB


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


open PPL


/-!
Counterexample to `Lemma16AgedC1OwnerRow` as stated.

n=4, psi=2, kappa=1, k=0, b=2 (= k+psi), e=1, i=2, kind=black, epoch=0.

Physical configuration: all agents Detect, clock=kappa, dist=i, last=false,
leaderless, id=false everywhere, no physical tokens.  This is LastReadyCapped.

Ghost layer: a single black ghost at site 1 with c=+1, bit=1, carry=0,
id=born black 0, birthSite 0, moves 1.  This satisfies the live invariant
at q=0 (payloadCorrect at bit zero: j=firstZeroBit=0, expected bit !id(0)=1,
expected carry 0).  The physical agent at site 1 carries no token, so the
physical step performs no Detect comparison, creates no leader and the post
state is not CPB.

`Lemma16AgedC1Data` only relates `z` to the *ghost* source; it records no
link between the ghost value and the physical token.  With the post token
z (c=-1, bit=1, moves=2), the macro stage forces q=0, and the goal's
negative latch demands id(b)=id(2)=false = expectedAddOneBit(0) = !id(0) =
true, which fails.
-/


private def c1rRing : DirectedRing 4 :=
  ⟨by decide⟩

private def c1r0 : Fin 4 := ⟨0, by decide⟩
private def c1r1 : Fin 4 := ⟨1, by decide⟩
private def c1r2 : Fin 4 := ⟨2, by decide⟩


private def c1rState (i : Fin 4) : PPL.State 2 1 :=
  {
    leader := false
    id := false
    dist := ⟨i.val, by omega⟩
    last := false
    tokenB := none
    tokenW := none
    mode := true
    clock := (1 : Fin 2)
    signalR := 0
    hits := 0
    bullet := 0
    shield := false
    signalB := false
  }


private def c1rC : Config 4 2 1 :=
  c1rState


/-- c=+1 (code 1), bit 1, carry 0. -/
private def c1rSourceValue : TokenData 2 :=
  ((⟨1, by decide⟩, (1 : Fin 2)), (0 : Fin 2))


/-- c=-1 = 1-psi (code 0), bit 1, carry 0. -/
private def c1rPostValue : TokenData 2 :=
  ((⟨0, by decide⟩, (1 : Fin 2)), (0 : Fin 2))


private def c1rSourceMeta : LineageMeta 4 :=
  {
    id := .born .black 0
    birthSite := c1r0
    birthStep := 0
    moves := 1
  }


private def c1rSource : GhostToken 4 2 :=
  {
    value := c1rSourceValue
    lmeta := c1rSourceMeta
  }


private def c1rZ : GhostToken 4 2 :=
  {
    value := c1rPostValue
    lmeta := ghostStepLineageAdvance c1rSourceMeta
  }


private def c1rG : GhostConfig 4 2 1 :=
  {
    phys := c1rC
    black := fun i =>
      if i = c1r1 then some c1rSource else none
    white := fun _ => none
    completed := []
  }


private theorem c1r_ready :
    LastReadyCapped c1rRing c1rG.phys := by
  show LastReadyCapped c1rRing c1rC
  unfold LastReadyCapped DistReadyCapped DetectReadyCapped
    DetectReady
  refine ⟨⟨⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact @of_decide_eq_true _
      (instDecidableAllLivePeaceful _ _) rfl
  all_goals decide


private theorem c1r_geom :
    Lemma16PostEpochFreshBorderGeometry
      c1rRing c1r2 c1r0 2 := by
  unfold Lemma16PostEpochFreshBorderGeometry
  decide


private theorem c1r_inv :
    Lemma16PostEpochFreshStateInvariant
      c1rRing c1rC 0 c1r2 c1r0 .black c1rG := by
  refine ⟨fun _ => rfl, ?_⟩
  unfold Lemma16PostEpochFreshLiveInvariant
  intro i z t howner _hid _hbs _hepoch _hprior
  have hz :
      ghostTokenAt .black c1rG i =
        if i = c1r1 then some c1rSource else none :=
    rfl
  rw [hz] at howner
  by_cases hi : i = c1r1
  · rw [if_pos hi] at howner
    cases howner
    subst hi
    refine ⟨0, by decide, ?_, ?_, ?_, ?_⟩
    · unfold Lemma16FreshMacroStageAt
      dsimp only
      exact ⟨1, by decide, Or.inl (by decide)⟩
    · decide
    · intro x hx
      exact absurd hx (Nat.not_lt_zero x)
    · intro h
      exact absurd h (by decide)
  · rw [if_neg hi] at howner
    cases howner


private theorem c1r_leaderless :
    ∀ j : Fin 4,
      ((PopulationProtocol.step
        (protocol 2 1) c1rRing c1rC c1r1) j).leader =
        false := by
  decide


private theorem c1r_not_cpb :
    ¬ CPB c1rRing
      (ghostStep (by decide : 2 ≤ 2) c1rRing 0 c1rG c1r1).phys := by
  rw [ghostStep_phys_export]
  intro hcpb
  unfold PPL.CPB PPL.CPBCore at hcpb
  rcases hcpb.1 with ⟨j, hj⟩
  dsimp only at hj
  have hf := c1r_leaderless j
  have hj' :
      ((PopulationProtocol.step
        (protocol 2 1) c1rRing c1rC c1r1) j).leader = true :=
    hj
  rw [hf] at hj'
  cases hj'


private theorem c1r_completed :
    (ghostStep (by decide : 2 ≤ 2) c1rRing 0 c1rG c1r1).completed =
      [] := by
  decide


private theorem c1r_prior :
    Lemma16NoPriorCompletionId
      (ghostStep (by decide : 2 ≤ 2) c1rRing 0 c1rG c1r1)
      c1rZ.lmeta.id := by
  intro m hm
  rw [c1r_completed] at hm
  cases hm


private def c1r_data :
    Lemma16AgedC1Data c1rRing .black c1rG c1r1 c1r2 c1rZ :=
  {
    source := c1rSource
    howner := by decide
    hsite := by decide
    hmeta := rfl
    hbit := rfl
    hcarry := rfl
    hsourceOffset := by decide
    hpostOffset := by decide
  }


theorem lemma16AgedC1OwnerRow_false :
    ¬ Lemma16AgedC1OwnerRow := by
  intro hrow
  unfold Lemma16AgedC1OwnerRow at hrow
  have hgoal :=
    hrow
      (n := 4) (psi := 2) (kappa := 1)
      (by decide) (by decide)
      c1rRing c1rC 0 c1r2 c1r0 .black 0 c1rG c1r1
      c1r_geom c1r_ready c1r_inv c1r_not_cpb
      c1r2 c1rZ 0 rfl rfl (Nat.le_refl 0)
      c1r_prior c1r_data
  unfold Lemma16AgedLiveGoal at hgoal
  rcases hgoal with ⟨q, _hq, hstage, _hpay, _hprefix, hlatch⟩
  have hc :
      decodeOffset 2 (tokenCode c1rZ.value) = -1 := by
    decide
  have hm : c1rZ.lmeta.moves = 2 := rfl
  unfold Lemma16FreshMacroStageAt at hstage
  dsimp only at hstage
  rw [hc, hm] at hstage
  rcases hstage with ⟨x, _hx, hp | hn⟩
  · omega
  · have hq0 : q = 0 := by
      omega
    subst hq0
    have hl := hlatch (by rw [hc]; decide)
    exact absurd hl (by decide)


end PPL.Convergence.ReachCPB


#print axioms PPL.Convergence.ReachCPB.lemma16AgedC1OwnerRow_false
