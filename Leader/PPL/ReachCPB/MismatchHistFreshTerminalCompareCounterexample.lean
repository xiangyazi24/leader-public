import Leader.PPL.ReachCPB.MismatchHistFreshDistCanonLocal
import Init.Omega


namespace PPL.Convergence.ReachCPB


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


open PPL
open PPL.Probability


/-!
The collision alias is impossible under the row's Cd premise:
a terminal-stage c=+1 owner is at displacement 2*psi-2, and every legal
negative token at its responder has target coordinate in the positive band,
so liveShadow clears it before collision.


The standalone terminal-compare row is nevertheless false because it has no
GhostSound/source-link premise.  The witness below uses a stale named
terminal-stage ghost at the responder and a distinct, physically aligned
same-metadata c=+2 ghost at the initiator.  The latter performs the actual
terminal bump.
-/


private theorem q20144Hpsi : 2 ≤ 2 := by
  omega


private theorem q20144Hn3 : 3 ≤ 4 := by
  omega


private def q20144Ring : DirectedRing 4 :=
  ⟨by decide⟩


private def q20144E0 : Fin 4 := ⟨0, by decide⟩
private def q20144E1 : Fin 4 := ⟨1, by decide⟩
private def q20144E2 : Fin 4 := ⟨2, by decide⟩
private def q20144E3 : Fin 4 := ⟨3, by decide⟩


private def q20144Dist (i : Fin 4) : Fin 4 :=
  if i = q20144E0 then
    (1 : Fin 4)
  else if i = q20144E1 then
    (2 : Fin 4)
  else if i = q20144E2 then
    (3 : Fin 4)
  else
    (0 : Fin 4)


private def q20144TokenOne : PPL.TokenData 2 :=
  ((PPL.offsetOneCode 2 q20144Hpsi, (0 : Fin 2)),
    (0 : Fin 2))


private def q20144TokenTwo : PPL.TokenData 2 :=
  ((PPL.offsetPsiCode 2 q20144Hpsi, (0 : Fin 2)),
    (0 : Fin 2))


private def q20144State (i : Fin 4) : PPL.State 2 1 :=
  {
    leader := false
    id :=
      if i = q20144E1 ∨ i = q20144E2 then
        true
      else
        false
    dist := q20144Dist i
    last := false
    tokenB :=
      if i = q20144E0 then
        some q20144TokenTwo
      else
        none
    tokenW := none
    mode := true
    clock := (1 : Fin 2)
    signalR := (0 : Fin 2)
    hits := (0 : Fin 3)
    bullet := (0 : Fin 3)
    shield := false
    signalB := false
  }


private def q20144C : Config 4 2 1 :=
  q20144State


private def q20144Meta : PPL.LineageMeta 4 :=
  {
    id := .born .black 0
    birthSite := q20144E3
    birthStep := 0
    moves := 4
  }


/-- Actual physically aligned source: c=+2 at u0. -/
private def q20144ZMove : PPL.GhostToken 4 2 :=
  {
    value := q20144TokenTwo
    lmeta := q20144Meta
  }


/--
Named row witness: terminal-stage c=+1 at u1, but deliberately stale because
the physical black slot at u1 is empty.
-/
private def q20144ZNamed : PPL.GhostToken 4 2 :=
  {
    value := q20144TokenOne
    lmeta := q20144Meta
  }


private def q20144M : PPL.LineageMeta 4 :=
  PPL.ghostStepLineageAdvance q20144Meta


private def q20144G : PPL.GhostConfig 4 2 1 :=
  {
    phys := q20144C
    black := fun i =>
      if i = q20144E0 then
        some q20144ZMove
      else if i = q20144E1 then
        some q20144ZNamed
      else
        none
    white := fun _ => none
    completed := []
  }


private theorem q20144OwnerMove :
    PPL.ghostTokenAt .black q20144G q20144E0 =
      some q20144ZMove := by
  decide


private theorem q20144OwnerNamed :
    PPL.ghostTokenAt .black q20144G q20144E1 =
      some q20144ZNamed := by
  decide


/-- The witness deliberately violates live-ID uniqueness. -/
theorem q20144Witness_not_GhostIdsUnique :
    ¬ PPL.GhostIdsUnique q20144G := by
  intro hU
  have hsites :=
    hU .black
      q20144E0 q20144E1
      q20144ZMove q20144ZNamed
      q20144OwnerMove q20144OwnerNamed
      (by rfl)
  have hne : q20144E0 ≠ q20144E1 := by
    decide
  exact hne hsites


private theorem q20144Geometry :
    Lemma16PostEpochFreshBorderGeometry
      q20144Ring q20144E1 q20144E3 2 := by
  unfold Lemma16PostEpochFreshBorderGeometry
  decide


private theorem q20144Ready :
    DetectReadyCapped q20144Ring q20144G.phys := by
  unfold DetectReadyCapped DetectReady
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact
      @of_decide_eq_true _
        (instDecidableAllLivePeaceful _ _)
        rfl
  all_goals decide


private def q20144DistanceEquationBool : Bool :=
  decide
    (∀ i : Fin 4,
      (q20144G.phys
          (q20144Ring.rightNeighbor i)).dist.val =
        ((q20144G.phys i).dist.val + 1) % 4)


private theorem q20144DistanceEquationBool_true :
    q20144DistanceEquationBool = true := by
  decide


private theorem q20144DistanceEquation :
    ∀ i : Fin 4,
      (q20144G.phys
          (q20144Ring.rightNeighbor i)).dist.val =
        ((q20144G.phys i).dist.val + 1) % (2 * 2) := by
  have h :
      ∀ i : Fin 4,
        (q20144G.phys
            (q20144Ring.rightNeighbor i)).dist.val =
          ((q20144G.phys i).dist.val + 1) % 4 := by
    apply of_decide_eq_true
    exact q20144DistanceEquationBool_true
  simpa using h


private theorem q20144DistReady :
    DistReadyCapped q20144Ring q20144G.phys := by
  unfold DistReadyCapped
  exact ⟨q20144Ready, q20144DistanceEquation⟩


private theorem q20144Frozen :
    ∀ j : Fin 4,
      (q20144G.phys j).id = (q20144C j).id := by
  intro j
  rfl


private theorem q20144Pair :
    q20144E1 = q20144E0 ∨
      q20144E1 = q20144Ring.rightNeighbor q20144E0 := by
  right
  decide


private theorem q20144FreshNamed :
    PPL.FreshAt .black q20144E3 q20144ZNamed.lmeta := by
  unfold PPL.FreshAt
  exact ⟨0, rfl, rfl⟩


private theorem q20144Advance :
    q20144M =
      PPL.ghostStepLineageAdvance q20144ZNamed.lmeta := by
  rfl


private theorem q20144Done :
    q20144M ∈
      (PPL.ghostStepSelectedPair
        q20144Hpsi q20144Ring 0
        q20144G q20144E0 .black).done := by
  decide


private theorem q20144FreshCompletion :
    PPL.FreshCompletion
      (psi := 2) .black q20144E3 q20144M := by
  unfold PPL.FreshCompletion PPL.FreshAt
  refine ⟨⟨0, rfl, rfl⟩, ?_⟩
  decide


private theorem q20144TokenOneOffset :
    PPL.decodeOffset 2
        (PPL.tokenCode q20144TokenOne) =
      (1 : Int) := by
  decide


private theorem q20144Macro :
    Lemma16FreshMacroStageAt
      q20144Ring q20144E3 q20144E1
      q20144ZNamed 1 := by
  unfold Lemma16FreshMacroStageAt
  dsimp only
  refine ⟨2, ?_, ?_⟩
  · decide
  · have hoff :
        PPL.decodeOffset 2
            (PPL.tokenCode q20144ZNamed.value) =
          (1 : Int) := by
      simpa [q20144ZNamed] using q20144TokenOneOffset
    rw [hoff]
    left
    simp [q20144ZNamed, q20144Meta]


private theorem q20144Payload :
    PPL.payloadCorrect
      q20144Ring q20144C q20144E3
      1 q20144ZNamed.value := by
  decide


private theorem q20144Prefix :
    Lemma16TargetPrefix
      q20144Ring q20144C
      q20144E1 q20144E3 1 := by
  unfold Lemma16TargetPrefix
  intro x hx
  have hx0 : x = 0 := by
    omega
  subst x
  decide


private theorem q20144Bad :
    Lemma16BadBorderWitness
      q20144Ring q20144G.phys
      q20144E1 q20144E3 .black := by
  unfold Lemma16BadBorderWitness PPL.IsBorder PPL.Cd
  dsimp only
  decide


/--
The actual black transition is c=+2 at u0, so it only moves to c=+1 at u1.
No c=1 comparison is executed on this interaction.
-/
private def q20144PostLeaderlessBool : Bool :=
  decide
    (∀ i : Fin 4,
      ((PPL.ghostStep
        q20144Hpsi q20144Ring 0
        q20144G q20144E0).phys i).leader = false)


private theorem q20144PostLeaderlessBool_true :
    q20144PostLeaderlessBool = true := by
  decide


private theorem q20144PostLeaderless :
    ∀ i : Fin 4,
      ((PPL.ghostStep
        q20144Hpsi q20144Ring 0
        q20144G q20144E0).phys i).leader = false := by
  apply of_decide_eq_true
  exact q20144PostLeaderlessBool_true


private theorem q20144PostNotCPB :
    ¬ PPL.CPB q20144Ring
        (PPL.ghostStep
          q20144Hpsi q20144Ring 0
          q20144G q20144E0).phys := by
  intro hcpb
  unfold PPL.CPB PPL.CPBCore at hcpb
  rcases hcpb.1 with ⟨i, hi⟩
  dsimp only at hi
  rw [q20144PostLeaderless i] at hi
  contradiction


/--
The terminal-compare row is false as stated.


The named endpoint is the stale c=+1 ghost at u1.  The selected-pair done
entry is produced instead by the same-metadata, physically aligned c=+2
initiator at u0.
-/
theorem lemma16PostEpochFreshTerminalCompareLiteralRow_refuted :
    ¬ Lemma16PostEpochFreshTerminalCompareLiteralRow := by
  intro hrow
  unfold Lemma16PostEpochFreshTerminalCompareLiteralRow at hrow


  have hcpb :=
    hrow
      (n := 4) (psi := 2) (kappa := 1)
      q20144Hpsi q20144Hn3
      q20144Ring
      q20144C
      q20144E1 q20144E3
      .black
      0
      q20144G
      q20144E0 q20144E1
      q20144ZNamed
      q20144M
      1
      q20144Geometry
      q20144DistReady
      q20144Frozen
      q20144Pair
      q20144OwnerNamed
      q20144FreshNamed
      q20144Advance
      q20144Done
      q20144FreshCompletion
      (by omega)
      q20144Macro
      q20144Payload
      q20144Prefix
      q20144Bad


  exact q20144PostNotCPB hcpb


end PPL.Convergence.ReachCPB


#print axioms PPL.Convergence.ReachCPB.q20144Witness_not_GhostIdsUnique
#print axioms PPL.Convergence.ReachCPB.lemma16PostEpochFreshTerminalCompareLiteralRow_refuted
