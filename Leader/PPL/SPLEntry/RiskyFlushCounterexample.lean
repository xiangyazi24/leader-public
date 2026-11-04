import Leader.PPL.SPLEntry.ForcingWord


namespace PPL.Convergence.L18


set_option autoImplicit false
set_option Elab.async false


open PPL

instance instDecidableL18NoRiskyAtRefute {n psi kappa : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config n psi kappa) :
    Decidable (L18NoRiskyAt ring root C) := by
  unfold L18NoRiskyAt
  infer_instance


/-!
Truth audit for L18RiskyFlushPhase.

The phase is false as currently quantified.  The missing case is zeta = 1:
when n = psi, CDLAt makes every site a last-segment site.  Hence Algorithm 3's
line-13 gate is closed on every interaction.  Nevertheless Risky still permits
a positive token whose whole path lies in S_0, because S_0 is then the whole
ring.

The requested n=3, psi=2 shape is also audited below.  In that two-segment
case the analogous white c=+1 token at the root is serviced by the first edge
of seqR(root,2), so it is not a counterexample.
-/


/-! ## n = 3, psi = 2: the suggested shape is flushed -/


private theorem riskyFlushPsi2Hpsi : 2 ≤ 2 := by
  omega


private def riskyFlushPsi2Ring : DirectedRing 3 :=
  ⟨by omega⟩


private def riskyFlushPsi2Root : Fin 3 :=
  ⟨0, by omega⟩


private def riskyFlushPsi2E2 : Fin 3 :=
  ⟨2, by omega⟩


private def riskyFlushPsi2Token : TokenData 2 :=
  ((offsetOneCode 2 riskyFlushPsi2Hpsi, (0 : Fin 2)),
    (0 : Fin 2))


private def riskyFlushPsi2State (i : Fin 3) : State 2 0 :=
  { leader :=
      if i = riskyFlushPsi2Root then true else false
    id := false
    dist := ⟨i.val, by omega⟩
    last :=
      if i = riskyFlushPsi2E2 then true else false
    tokenB := none
    tokenW :=
      if i = riskyFlushPsi2Root then
        some riskyFlushPsi2Token
      else
        none
    mode := false
    clock := 0
    signalR := 0
    hits := 0
    bullet := 0
    shield := false
    signalB := false }


private def riskyFlushPsi2C : Config 3 2 0 :=
  riskyFlushPsi2State


private theorem riskyFlushPsi2_cdl :
    CDLAt riskyFlushPsi2Ring
      riskyFlushPsi2Root riskyFlushPsi2C := by
  decide +kernel


private theorem riskyFlushPsi2_initial_risky :
    Risky riskyFlushPsi2Ring
      riskyFlushPsi2Root riskyFlushPsi2C
      riskyFlushPsi2Root := by
  decide +kernel


private theorem riskyFlushPsi2_one_sweep_no_risky :
    L18NoRiskyAt riskyFlushPsi2Ring
      riskyFlushPsi2Root
      (runPPrime riskyFlushPsi2Ring riskyFlushPsi2C
        (PPL.seqR riskyFlushPsi2Ring riskyFlushPsi2Root 2)) := by
  decide +kernel


/-! ## Actual counterexample: n = 3, psi = 3 -/


private theorem riskyFlushFalseHpsi : 2 ≤ 3 := by
  omega


private def riskyFlushFalseRing : DirectedRing 3 :=
  ⟨by omega⟩


private def riskyFlushFalseRoot : Fin 3 :=
  ⟨0, by omega⟩


/--
A white c=+1 token at the root.

For psi=3 its white target coordinate is
  0 + 1 + tokenD'(white) = 4 mod 6,
so it is locally valid.  Since S_0 contains the whole three-agent ring when
n=psi=3, its two-site positive path lies entirely in S_0 and the token is
Risky.
-/
private def riskyFlushFalseToken : TokenData 3 :=
  ((offsetOneCode 3 riskyFlushFalseHpsi, (0 : Fin 2)),
    (0 : Fin 2))


private def riskyFlushFalseState (i : Fin 3) : State 3 0 :=
  { leader :=
      if i = riskyFlushFalseRoot then true else false
    id := false
    dist := ⟨i.val, by omega⟩
    last := true
    tokenB := none
    tokenW :=
      if i = riskyFlushFalseRoot then
        some riskyFlushFalseToken
      else
        none
    mode := false
    clock := 0
    signalR := 0
    hits := 0
    bullet := 0
    shield := false
    signalB := false }


private def riskyFlushFalseC : Config 3 3 0 :=
  riskyFlushFalseState


private def riskyFlushFalseAfterOne : Config 3 3 0 :=
  runPPrime riskyFlushFalseRing riskyFlushFalseC
    (PPL.seqR riskyFlushFalseRing riskyFlushFalseRoot 3)


private def riskyFlushFalseAfterTwo : Config 3 3 0 :=
  runPPrime riskyFlushFalseRing riskyFlushFalseC
    (l18RiskyFlushWord
      riskyFlushFalseRing riskyFlushFalseRoot 3)


private theorem riskyFlushFalse_cdl :
    CDLAt riskyFlushFalseRing
      riskyFlushFalseRoot riskyFlushFalseC := by
  decide +kernel


private theorem riskyFlushFalse_initial_risky :
    Risky riskyFlushFalseRing
      riskyFlushFalseRoot riskyFlushFalseC
      riskyFlushFalseRoot := by
  decide +kernel


/--
One complete seqR(root,psi) sweep does not move the token: zeta=1 makes
last=true at both endpoints of every interaction, so the line-13 movement
guard is false after invalid-token clearing.
-/
private theorem riskyFlushFalse_after_one_risky :
    Risky riskyFlushFalseRing
      riskyFlushFalseRoot riskyFlushFalseAfterOne
      riskyFlushFalseRoot := by
  decide +kernel


/-- The second sweep still cannot move the token. -/
private theorem riskyFlushFalse_after_two_risky :
    Risky riskyFlushFalseRing
      riskyFlushFalseRoot riskyFlushFalseAfterTwo
      riskyFlushFalseRoot := by
  decide +kernel


/--
The geometry/leader half is not the failure in this witness: CDLAt itself
survives the two sweeps.
-/
private theorem riskyFlushFalse_after_two_cdl :
    CDLAt riskyFlushFalseRing
      riskyFlushFalseRoot riskyFlushFalseAfterTwo := by
  decide +kernel


theorem l18RiskyFlushPhase_false :
    ¬ L18RiskyFlushPhase := by
  intro hphase
  have hout :=
    hphase
      (n := 3) (psi := 3) (kappa := 0)
      (by omega) riskyFlushFalseHpsi
      riskyFlushFalseRing
      riskyFlushFalseRoot
      riskyFlushFalseC
      riskyFlushFalse_cdl
  dsimp only at hout
  have hno := hout.2
  unfold L18NoRiskyAt at hno
  exact
    (hno riskyFlushFalseRoot)
      riskyFlushFalse_after_two_risky


end PPL.Convergence.L18


#print axioms PPL.Convergence.L18.riskyFlushPsi2_one_sweep_no_risky
#print axioms PPL.Convergence.L18.l18RiskyFlushPhase_false
