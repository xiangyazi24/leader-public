import Leader.PPL.SPLEntry.CompletionCoreRoute
import Leader.PPL.SPLEntry.GappedRiskyFlushPhaseScoped
import Init.Omega


namespace PPL.Convergence.L18


set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false


open PPL


/-
BLOCKED LEAF AT c813242f.


The agenda-mentioned theorem `l18PrimeStepPreservesBuildPrefix` is not
present in the pinned tree.  The newly landed gapped-risky machinery closes
its CDLAt and no-risky components.  The only unproved component left is the
already-built pair frame:


theorem l18PrimeStepPreservesBuiltPairPrefix
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (C : Config n psi kappa)
    (e : Fin n)
    (hb : b < l18BlockCount n psi)
    (hPrefix : L18BuildPrefixAt ring root b C) :
    ∀ seg : Fin (l18BlockCount n psi),
      seg.val < b →
      L18BuildPairOK ring root
        (pprimeStep ring C e) seg.val


Once that lemma is available, the rest of L18PrimeLemma4FrameRow is the
schedule induction below.  No use of the refuted full-P_PL -> P_PL-prime
transfer is made.
-/


private theorem q20245_psi_lt_n
    {n psi : Nat}
    (hpsi : 2 ≤ psi)
    (b : Nat)
    (hb : b < l18BlockCount n psi) :
    psi < n := by
  have hseg2 : 2 ≤ PPL.segmentCount n psi := by
    unfold l18BlockCount at hb
    omega
  exact
    (two_le_segmentCount_iff_psi_lt_n hpsi).1 hseg2


private theorem q20245_cdlNoRisky_step
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (C : Config n psi kappa)
    (e : Fin n)
    (hb : b < l18BlockCount n psi)
    (hPrefix : L18BuildPrefixAt ring root b C) :
    CDLAt ring root (pprimeStep ring C e) ∧
      L18NoRiskyAt ring root (pprimeStep ring C e) := by
  have hlt : psi < n :=
    q20245_psi_lt_n hpsi b hb


  have hSweep :
      L18RiskySweepPrefix2 ring root psi C := by
    unfold L18RiskySweepPrefix2
    exact
      ⟨hPrefix.1,
        fun i _hi => hPrefix.2.1 i⟩


  have hPost :=
    l18GappedRiskyInsertedStepRow_proved
      hn3 hpsi hlt ring root psi C e
      (Nat.le_refl psi) hSweep
  unfold L18RiskySweepPrefix2 at hPost


  refine ⟨hPost.1, ?_⟩
  unfold L18NoRiskyAt
  intro i hRisk
  have hoff :
      PPL.cyclicOffset ring root i < psi :=
    l18Risk2RiskyHostOffset_lt_psi
      hlt ring root
      (pprimeStep ring C e) i hRisk
  exact hPost.2 i hoff hRisk


theorem l18PrimeStepPreservesBuildPrefix_of_builtPairs
    (hPairs :
      ∀ {n psi kappa : Nat}
        (hn3 : 3 ≤ n)
        (hpsi : 2 ≤ psi)
        (ring : DirectedRing n)
        (root : Fin n)
        (b : Nat)
        (C : Config n psi kappa)
        (e : Fin n),
        b < l18BlockCount n psi →
        L18BuildPrefixAt ring root b C →
        ∀ seg : Fin (l18BlockCount n psi),
          seg.val < b →
          L18BuildPairOK ring root
            (pprimeStep ring C e) seg.val) :
    ∀ {n psi kappa : Nat}
      (hn3 : 3 ≤ n)
      (hpsi : 2 ≤ psi)
      (ring : DirectedRing n)
      (root : Fin n)
      (b : Nat)
      (C : Config n psi kappa)
      (e : Fin n),
      b < l18BlockCount n psi →
      L18BuildPrefixAt ring root b C →
      L18BuildPrefixAt ring root b
        (pprimeStep ring C e) := by
  intro n psi kappa
  intro hn3 hpsi ring root b C e
  intro hb hPrefix


  have hSafe :=
    q20245_cdlNoRisky_step
      hn3 hpsi ring root b C e hb hPrefix


  have hBuilt :=
    hPairs
      hn3 hpsi ring root b C e
      hb hPrefix


  unfold L18BuildPrefixAt
  exact
    ⟨hSafe.1,
      ⟨hSafe.2, hBuilt⟩⟩


private theorem q20245_runPrefix_of_stepFrame
    (hStep :
      ∀ {n psi kappa : Nat}
        (hn3 : 3 ≤ n)
        (hpsi : 2 ≤ psi)
        (ring : DirectedRing n)
        (root : Fin n)
        (b : Nat)
        (C : Config n psi kappa)
        (e : Fin n),
        b < l18BlockCount n psi →
        L18BuildPrefixAt ring root b C →
        L18BuildPrefixAt ring root b
          (pprimeStep ring C e))
    {n psi kappa : Nat}
    (hn3 : 3 ≤ n)
    (hpsi : 2 ≤ psi)
    (ring : DirectedRing n)
    (root : Fin n)
    (b : Nat)
    (C : Config n psi kappa)
    (schedule : DetSchedule n)
    (hb : b < l18BlockCount n psi)
    (hPrefix : L18BuildPrefixAt ring root b C) :
    L18BuildPrefixAt ring root b
      (runPPrime ring C schedule) := by
  induction schedule generalizing C with
  | nil =>
      simpa [runPPrime] using hPrefix
  | cons e rest ih =>
      have hOne :
          L18BuildPrefixAt ring root b
            (pprimeStep ring C e) :=
        hStep
          hn3 hpsi ring root b C e
          hb hPrefix
      have hTail :=
        ih
          (C := pprimeStep ring C e)
          hOne
      simpa [runPPrime] using hTail


theorem l18PrimeLemma4FrameRow_of_stepFrame
    (hStep :
      ∀ {n psi kappa : Nat}
        (hn3 : 3 ≤ n)
        (hpsi : 2 ≤ psi)
        (ring : DirectedRing n)
        (root : Fin n)
        (b : Nat)
        (C : Config n psi kappa)
        (e : Fin n),
        b < l18BlockCount n psi →
        L18BuildPrefixAt ring root b C →
        L18BuildPrefixAt ring root b
          (pprimeStep ring C e)) :
    L18PrimeLemma4FrameRow := by
  unfold L18PrimeLemma4FrameRow
  intro _hlemma4
  intro n psi kappa
  intro hn3 hpsi ring root b C schedule
  intro hb hPrefix _hsub
  dsimp only
  exact
    Or.inr
      (q20245_runPrefix_of_stepFrame
        hStep
        hn3 hpsi ring root b C schedule
        hb hPrefix)


theorem l18PrimeLemma4FrameRow_of_builtPairStep
    (hPairs :
      ∀ {n psi kappa : Nat}
        (hn3 : 3 ≤ n)
        (hpsi : 2 ≤ psi)
        (ring : DirectedRing n)
        (root : Fin n)
        (b : Nat)
        (C : Config n psi kappa)
        (e : Fin n),
        b < l18BlockCount n psi →
        L18BuildPrefixAt ring root b C →
        ∀ seg : Fin (l18BlockCount n psi),
          seg.val < b →
          L18BuildPairOK ring root
            (pprimeStep ring C e) seg.val) :
    L18PrimeLemma4FrameRow :=
  l18PrimeLemma4FrameRow_of_stepFrame
    (l18PrimeStepPreservesBuildPrefix_of_builtPairs
      hPairs)


end PPL.Convergence.L18


#print axioms
  PPL.Convergence.L18.l18PrimeStepPreservesBuildPrefix_of_builtPairs
#print axioms
  PPL.Convergence.L18.l18PrimeLemma4FrameRow_of_stepFrame
#print axioms
  PPL.Convergence.L18.l18PrimeLemma4FrameRow_of_builtPairStep


