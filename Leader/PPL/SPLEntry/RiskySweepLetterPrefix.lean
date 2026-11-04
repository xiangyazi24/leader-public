import Leader.PPL.SPLEntry.RiskyFlushScoped

namespace PPL.Convergence.L18

set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false

open PPL

/-!
The requested letter row is intentionally stated with the prefix hypothesis
needed by a sweep induction.  Its third clause is the literal requested
"no new risky site at offsets at or beyond j+1" condition.

That third clause is false: a valid risky positive token can move from the
current host j to j+1 while remaining risky.  The finite witness below is
n=4, psi=3, j=0.

The first two clauses are nevertheless exactly the clauses needed by the
conditional sweep assembler proved below.
-/

def L18RiskySweepLetterRow : Prop :=
  ∀ {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (j : Nat),
    j < psi →
    CDLAt ring root C →
    (∀ i : Fin n,
      cyclicOffset ring root i < j →
        ¬ Risky ring root C i) →
    let D :=
      pprimeStep ring C
        (PPL.shiftRight ring root j)
    CDLAt ring root D ∧
      (∀ i : Fin n,
        cyclicOffset ring root i < j + 1 →
          ¬ Risky ring root D i) ∧
      (∀ i : Fin n,
        j + 1 ≤ cyclicOffset ring root i →
        ¬ Risky ring root C i →
          ¬ Risky ring root D i)

/-! ## Sweep-prefix assembly, conditional on the requested row -/

private theorem riskySweepSeqR_succ
    {n : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (j : Nat) :
    PPL.seqR ring root (j + 1) =
      PPL.seqR ring root j ++
        [PPL.shiftRight ring root j] := by
  unfold PPL.seqR
  rw [List.ofFn_succ_last]
  rfl

private theorem riskySweepRun_seqR_succ
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (j : Nat) :
    runPPrime ring C
        (PPL.seqR ring root (j + 1)) =
      pprimeStep ring
        (runPPrime ring C
          (PPL.seqR ring root j))
        (PPL.shiftRight ring root j) := by
  rw [riskySweepSeqR_succ, runPPrime_append]
  rfl

private def L18RiskySweepPrefix
    {n psi kappa : Nat}
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (j : Nat) : Prop :=
  let D :=
    runPPrime ring C
      (PPL.seqR ring root j)
  CDLAt ring root D ∧
    ∀ i : Fin n,
      cyclicOffset ring root i < j →
        ¬ Risky ring root D i

private theorem riskySweep_shiftRight_zero
    {n : Nat}
    (ring : DirectedRing n)
    (i : Fin n) :
    PPL.shiftRight ring i 0 = i := by
  apply Fin.ext
  simp [PPL.shiftRight,
    Nat.mod_eq_of_lt i.isLt]

private theorem riskySweep_risky_host_offset_lt_psi
    {n psi kappa : Nat}
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (i : Fin n)
    (hrisky : Risky ring root C i) :
    cyclicOffset ring root i < psi := by
  have hkind :
      ∀ kind : PPL.TokenKind,
        PPL.tokenRisky ring root C i kind →
          cyclicOffset ring root i < psi := by
    intro kind hk
    unfold PPL.tokenRisky at hk
    cases ht : PPL.tokenAt kind (C i) with
    | none =>
        simp [ht] at hk
    | some t =>
        rw [ht] at hk
        dsimp only at hk
        let h0 :
            Fin
              ((PPL.decodeOffset psi
                  (PPL.tokenCode t)).natAbs + 1) :=
          ⟨0, by omega⟩
        have hin :=
          hk.2 h0
        have hz :
            PPL.shiftRight ring i h0.val = i := by
          dsimp only [h0]
          exact riskySweep_shiftRight_zero ring i
        rw [hz] at hin
        unfold PPL.InSegment at hin
        dsimp only at hin
        have hmin :
            Nat.min psi n = psi :=
          Nat.min_eq_left (Nat.le_of_lt hlt)
        simpa [hmin] using hin.2
  unfold PPL.Risky at hrisky
  rcases hrisky with hb | hw
  · exact hkind .black hb
  · exact hkind .white hw

private theorem riskySweepPrefix_run
    (hletter : L18RiskySweepLetterRow)
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (hlt : psi < n)
    (ring : DirectedRing n)
    (root : Fin n)
    (C : Config n psi kappa)
    (hC : CDLAt ring root C) :
    ∀ j : Nat,
      j ≤ psi →
        L18RiskySweepPrefix
          ring root C j := by
  intro j
  induction j with
  | zero =>
      intro _hj
      unfold L18RiskySweepPrefix
      dsimp only
      constructor
      · simpa [PPL.seqR, runPPrime] using hC
      · intro i hi
        omega
  | succ j ih =>
      intro hj
      have hjlt : j < psi := by
        omega
      have hprev :=
        ih (by omega)
      unfold L18RiskySweepPrefix at hprev ⊢
      dsimp only at hprev ⊢
      have hstep :=
        hletter
          hn3 hpsi hlt ring root
          (runPPrime ring C
            (PPL.seqR ring root j))
          j
          hjlt
          hprev.1
          hprev.2
      dsimp only at hstep
      rw [riskySweepRun_seqR_succ]
      exact
        ⟨hstep.1, hstep.2.1⟩

theorem l18RiskySingleSweepScopedRow_of_letterRow
    (hletter : L18RiskySweepLetterRow) :
    L18RiskySingleSweepScopedRow := by
  unfold L18RiskySingleSweepScopedRow
  intro n psi kappa
  intro hn3 hpsi hlt ring root C hC
  have hp :=
    riskySweepPrefix_run
      hletter
      hn3 hpsi hlt
      ring root C hC
      psi (Nat.le_refl psi)
  unfold L18RiskySweepPrefix at hp
  dsimp only at hp
  refine ⟨hp.1, ?_⟩
  unfold L18NoRiskyAt
  intro i
  intro hrisky
  have hoff :
      cyclicOffset ring root i < psi :=
    riskySweep_risky_host_offset_lt_psi
      hlt ring root
      (runPPrime ring C
        (PPL.seqR ring root psi))
      i hrisky
  exact
    (hp.2 i hoff) hrisky

/-! ## Smallest scoped case: n=3, psi=2

Here S_0 is offsets 0 and 1 and the final segment is offset 2.

A risky positive token at offset 1 is impossible, because every positive path
takes at least one clockwise step and immediately reaches offset 2 outside
S_0.  At offset 0, a locally valid risky token that can survive line 12 has
only the unit-hit shape in the relevant selected colour; its first sweep
letter turns it negative.  Fresh +psi and c=-1-return +psi tokens have a
psi+1-site path and therefore leave S_0.  The second letter has a final-segment
responder with last=true, but by then there is no risky host left to service.

So the n=3, psi=2 case does not expose the defect below.
-/

/-! ## Counterexample to the requested no-new-site clause: n=4, psi=3 -/

private theorem riskySweepCounterHpsi :
    2 ≤ 3 := by
  omega

private def riskySweepCounterRing :
    DirectedRing 4 :=
  ⟨by omega⟩

private def riskySweepCounterRoot :
    Fin 4 :=
  ⟨0, by omega⟩

private def riskySweepCounterE1 :
    Fin 4 :=
  ⟨1, by omega⟩

/--
Code 3 in Fin 5 decodes to +2 when psi=3.

At the root the white validity coordinate is
  0 + 2 + 3 = 5 mod 6,
which lies in the positive validity interval [3,5].
Its physical target is rooted offset 2, so the token is Risky in S_0.
-/
private def riskySweepCounterToken :
    TokenData 3 :=
  (((⟨3, by omega⟩ : Fin (2 * 3 - 1)),
    (0 : Fin 2)),
    (0 : Fin 2))

private def riskySweepCounterState
    (i : Fin 4) :
    State 3 0 :=
  { leader :=
      if i = riskySweepCounterRoot then
        true
      else
        false
    id := false
    dist := ⟨i.val, by omega⟩
    last :=
      if i.val = 3 then true else false
    tokenB := none
    tokenW :=
      if i = riskySweepCounterRoot then
        some riskySweepCounterToken
      else
        none
    mode := false
    clock := 0
    signalR := 0
    hits := 0
    bullet := 0
    shield := false
    signalB := false }

private def riskySweepCounterC :
    Config 4 3 0 :=
  riskySweepCounterState

private def riskySweepCounterAfter :
    Config 4 3 0 :=
  pprimeStep
    riskySweepCounterRing
    riskySweepCounterC
    (PPL.shiftRight
      riskySweepCounterRing
      riskySweepCounterRoot 0)

private theorem riskySweepCounter_cdl :
    CDLAt
      riskySweepCounterRing
      riskySweepCounterRoot
      riskySweepCounterC := by
  decide +kernel

private theorem riskySweepCounter_pre_clear :
    ∀ i : Fin 4,
      cyclicOffset
          riskySweepCounterRing
          riskySweepCounterRoot i < 0 →
        ¬ Risky
          riskySweepCounterRing
          riskySweepCounterRoot
          riskySweepCounterC i := by
  intro i hi
  omega

private theorem riskySweepCounter_e1_offset :
    1 ≤
      cyclicOffset
        riskySweepCounterRing
        riskySweepCounterRoot
        riskySweepCounterE1 := by
  decide +kernel

private theorem riskySweepCounter_e1_not_risky_before :
    ¬ Risky
      riskySweepCounterRing
      riskySweepCounterRoot
      riskySweepCounterC
      riskySweepCounterE1 := by
  decide +kernel

/--
The first letter moves the white c=+2 token from offset 0 to offset 1 and
decrements it to c=+1.  Its physical target remains offset 2, so it is still
Risky.  Thus a new risky *site* appears at offset 1, even though the risky
lineage itself is old.
-/
private theorem riskySweepCounter_e1_risky_after :
    Risky
      riskySweepCounterRing
      riskySweepCounterRoot
      riskySweepCounterAfter
      riskySweepCounterE1 := by
  decide +kernel

/--
The structural half is not the problem: rooted CDL survives this letter.
-/
private theorem riskySweepCounter_after_cdl :
    CDLAt
      riskySweepCounterRing
      riskySweepCounterRoot
      riskySweepCounterAfter := by
  decide +kernel

theorem l18RiskySweepLetterRow_refuted :
    ¬ L18RiskySweepLetterRow := by
  intro hrow
  have hout :=
    hrow
      (n := 4) (psi := 3) (kappa := 0)
      (by omega : 3 ≤ 4)
      riskySweepCounterHpsi
      (by omega : 3 < 4)
      riskySweepCounterRing
      riskySweepCounterRoot
      riskySweepCounterC
      0
      (by omega)
      riskySweepCounter_cdl
      riskySweepCounter_pre_clear
  dsimp only at hout
  have hno :=
    hout.2.2
      riskySweepCounterE1
      riskySweepCounter_e1_offset
      riskySweepCounter_e1_not_risky_before
  exact
    hno
      riskySweepCounter_e1_risky_after

end PPL.Convergence.L18

#print axioms PPL.Convergence.L18.l18RiskySingleSweepScopedRow_of_letterRow
#print axioms PPL.Convergence.L18.l18RiskySweepLetterRow_refuted
