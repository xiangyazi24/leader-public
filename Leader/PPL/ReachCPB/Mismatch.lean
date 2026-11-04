import Leader.PPL.ReachCPB.WordBound


namespace PPL.Convergence.ReachCPB


set_option autoImplicit false
set_option Elab.async false


/-!
The requested residual is false on the current literal carrier.


The missing invariant is a clock/mode coherence condition.  `LastReady`
requires every `mode` bit to be Detect, but it does not require the clocks to
be at `kappa`.  Algorithm 4 recomputes the mode from the clock at every
interaction.  Thus an arbitrary LastReady configuration may enter Construct
on the very first edge.  A fresh comparison trajectory can then repair the
mismatching segment ID through Algorithm 3 line 22 instead of creating a
leader through line 20.


The counterexample below uses n=4, psi=2, kappa=32.  Distances are 0,1,2,3,
all `last` bits are false, all modes are initially Detect, but every clock is
0.  Both possible C_d witnesses admit a five-move fresh completion with no
leader at the endpoint.
-/


private def mismatchRing : DirectedRing 4 :=
  ⟨by omega⟩


private def mismatch0 : Fin 4 := ⟨0, by omega⟩
private def mismatch1 : Fin 4 := ⟨1, by omega⟩
private def mismatch2 : Fin 4 := ⟨2, by omega⟩
private def mismatch3 : Fin 4 := ⟨3, by omega⟩


private def mismatchState (i : Fin 4) : PPL.State 2 32 :=
  { leader := false
    id := false
    dist := ⟨i.val, by omega⟩
    last := false
    tokenB := none
    tokenW := none
    mode := true
    clock := (0 : Fin 33)
    signalR := (0 : Fin 33)
    hits := (0 : Fin 3)
    bullet := (0 : Fin 3)
    shield := false
    signalB := false }


private def mismatchC : Config 4 2 32 :=
  mismatchState


/-
Black starts at the dist=0 border.  After the first edge, the touched modes
are Construct because clock=0<kappa.  The five token moves are:
  +2 -> +1, compare/bounce, -1 -> +2, +2 -> +1, compare/bounce.
The first comparison writes the missing low bit; the second already agrees.
-/
private def mismatchBlackWord : DetSchedule 4 :=
  [mismatch0, mismatch1, mismatch1, mismatch1, mismatch2]


/-- The white witness is the same trace rotated by two sites. -/
private def mismatchWhiteWord : DetSchedule 4 :=
  [mismatch2, mismatch3, mismatch3, mismatch3, mismatch0]


private def mismatchBlackMeta : PPL.LineageMeta 4 :=
  { id := .born .black 0
    birthSite := mismatch0
    birthStep := 0
    moves := 5 }


private def mismatchWhiteMeta : PPL.LineageMeta 4 :=
  { id := .born .white 0
    birthSite := mismatch2
    birthStep := 0
    moves := 5 }


private theorem mismatch_lastReady :
    LastReady mismatchRing mismatchC := by
  decide


private theorem mismatch_notPerfect :
    ¬ PPL.Perfect mismatchRing mismatchC := by
  exact
    PPL.leaderless_not_perfect
      (by decide : 3 ≤ 4)
      (by decide : 4 ≤ 2 ^ 2)
      mismatchRing mismatchC
      (by
        intro i
        rfl)


private theorem mismatch_shiftRight_zero (k : Fin 4) :
    PPL.shiftRight mismatchRing k 0 = k := by
  apply Fin.ext
  simp [PPL.shiftRight, Nat.mod_eq_of_lt k.isLt]


/-- In this distance pattern, any black C_d source is necessarily site 0. -/
private theorem mismatch_blackCd_forces_zero
    (k : Fin 4)
    (hCd : PPL.Cd mismatchRing k .black mismatchC) :
    k = mismatch0 := by
  have hx := hCd (⟨0, by omega⟩ : Fin (2 * 2))
  dsimp only at hx
  rw [mismatch_shiftRight_zero k] at hx
  have hk : k.val = 0 := by
    simpa [mismatchC, mismatchState, PPL.tokenD'] using hx.1
  apply Fin.ext
  exact hk


/-- In this distance pattern, any white C_d source is necessarily site 2. -/
private theorem mismatch_whiteCd_forces_two
    (k : Fin 4)
    (hCd : PPL.Cd mismatchRing k .white mismatchC) :
    k = mismatch2 := by
  have hx := hCd (⟨0, by omega⟩ : Fin (2 * 2))
  dsimp only at hx
  rw [mismatch_shiftRight_zero k] at hx
  have hk : k.val = 2 := by
    simpa [mismatchC, mismatchState, PPL.tokenD'] using hx.1
  apply Fin.ext
  exact hk


/-
These are closed, finite reductions of the literal ghost machine.  They use
ordinary `decide` only on propositions with synthesized Decidable instances:
List membership of a concrete LineageMeta, and a finite Fin-quantifier over
the concrete endpoint.  No native_decide is used.
-/


private theorem mismatch_black_completed_member :
    mismatchBlackMeta ∈
      (PPL.ghostRun
        (by decide : 2 ≤ 2)
        mismatchRing 0
        (PPL.initialGhost mismatchC)
        mismatchBlackWord).completed := by
  decide


private theorem mismatch_white_completed_member :
    mismatchWhiteMeta ∈
      (PPL.ghostRun
        (by decide : 2 ≤ 2)
        mismatchRing 0
        (PPL.initialGhost mismatchC)
        mismatchWhiteWord).completed := by
  decide


private theorem mismatch_black_freshCompletion :
    PPL.HasFreshCompletion .black mismatch0
      (PPL.ghostRun
        (by decide : 2 ≤ 2)
        mismatchRing 0
        (PPL.initialGhost mismatchC)
        mismatchBlackWord) := by
  refine ⟨mismatchBlackMeta, mismatch_black_completed_member, ?_⟩
  constructor
  · exact ⟨0, rfl, rfl⟩
  · decide


private theorem mismatch_white_freshCompletion :
    PPL.HasFreshCompletion .white mismatch2
      (PPL.ghostRun
        (by decide : 2 ≤ 2)
        mismatchRing 0
        (PPL.initialGhost mismatchC)
        mismatchWhiteWord) := by
  refine ⟨mismatchWhiteMeta, mismatch_white_completed_member, ?_⟩
  constructor
  · exact ⟨0, rfl, rfl⟩
  · decide


private theorem mismatch_black_endpoint_leaderless :
    ∀ i : Fin 4,
      ((PPL.Probability.runPPL
          mismatchRing mismatchC mismatchBlackWord) i).leader = false := by
  decide


set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem mismatch_white_endpoint_leaderless :
    ∀ i : Fin 4,
      ((PPL.Probability.runPPL
          mismatchRing mismatchC mismatchWhiteWord) i).leader = false := by
  decide


private theorem cpb_false_of_leaderless
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (C : Config n psi kappa)
    (hzero : ∀ i : Fin n, (C i).leader = false) :
    ¬ PPL.CPB ring C := by
  intro hcpb
  unfold PPL.CPB PPL.CPBCore at hcpb
  rcases hcpb.1 with ⟨i, hi⟩
  have h0 : (C i).leader = false := hzero i
  simp only [] at hi
  rw [h0] at hi
  contradiction


private theorem mismatch_black_endpoint_not_cpb :
    ¬ PPL.CPB mismatchRing
      (PPL.Probability.runPPL
        mismatchRing mismatchC mismatchBlackWord) := by
  exact
    cpb_false_of_leaderless
      mismatchRing
      (PPL.Probability.runPPL
        mismatchRing mismatchC mismatchBlackWord)
      mismatch_black_endpoint_leaderless


private theorem mismatch_white_endpoint_not_cpb :
    ¬ PPL.CPB mismatchRing
      (PPL.Probability.runPPL
        mismatchRing mismatchC mismatchWhiteWord) := by
  exact
    cpb_false_of_leaderless
      mismatchRing
      (PPL.Probability.runPPL
        mismatchRing mismatchC mismatchWhiteWord)
      mismatch_white_endpoint_leaderless


/--
Concrete refutation of the current residual.


Any witness returned by Lemma16MismatchWitnessSpec is forced by C_d to be
either black at site 0 or white at site 2.  The corresponding five-edge word
has a fresh completed trajectory but its endpoint is leaderless, contradicting
the universal CPB conclusion.
-/
theorem lemma16MismatchWitnessSpec_false :
    ¬ Lemma16MismatchWitnessSpec := by
  intro hspec
  have hw :=
    hspec
      (by decide : 3 ≤ 4)
      (by decide : 2 ≤ 2)
      (by decide : 4 ≤ 2 ^ 2)
      mismatchRing mismatchC
      mismatch_lastReady
      mismatch_notPerfect
  rcases hw with ⟨k, kind, hCd, hforces⟩
  cases kind with
  | black =>
      have hk : k = mismatch0 :=
        mismatch_blackCd_forces_zero k hCd
      subst k
      have hcpb :=
        hforces mismatchBlackWord
          mismatch_black_freshCompletion
      exact mismatch_black_endpoint_not_cpb hcpb
  | white =>
      have hk : k = mismatch2 :=
        mismatch_whiteCd_forces_two k hCd
      subst k
      have hcpb :=
        hforces mismatchWhiteWord
          mismatch_white_freshCompletion
      exact mismatch_white_endpoint_not_cpb hcpb


end PPL.Convergence.ReachCPB


#print axioms PPL.Convergence.ReachCPB.lemma16MismatchWitnessSpec_false
