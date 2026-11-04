import Leader.L3.DefectCrossing

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
The physical configuration at the cold entrance is x.val:
Counter.resetClockBankColdStartPhysical is the exact projection.
This module bridges authentic OLD-edge defect exits to G14 entry
events. No fabricated observer states or stochastic independence.
-/

/-- A crossing witness persists under right extension of the same
actual edge word. -/
private theorem coldDefectCrossingAppend
    {n q : Nat} (ring : DirectedRing n)
    (C : Counter.Config q n) (root : Fin n)
    (word suffix : List (Fin n))
    (h : DefectCrossingEntryWithin ring C root word) :
    DefectCrossingEntryWithin ring C root (word ++ suffix) := by
  obtain ⟨pre, e, after, hw, he⟩ := h
  refine ⟨pre, e, after ++ suffix, ?_, he⟩
  calc
    word ++ suffix = (pre ++ e :: after) ++ suffix :=
      congrArg (fun w => w ++ suffix) hw
    _ = pre ++ e :: (after ++ suffix) := by
      simp only [List.append_assoc, List.cons_append]

/-- Transport of a true OLD-edge witness across one preceding
physical protocol interaction. -/
private theorem coldDefectCrossingCons
    {n q : Nat} (ring : DirectedRing n)
    (C : Counter.Config q n) (root e : Fin n)
    (tail : List (Fin n))
    (h : DefectCrossingEntryWithin ring
      ((protocol q).step ring C e) root tail) :
    DefectCrossingEntryWithin ring C root (e :: tail) := by
  obtain ⟨pre, edge, suffix, hw, he⟩ := h
  refine ⟨e :: pre, edge, suffix, ?_, ?_⟩
  · rw [hw]
    simp only [List.cons_append]
  · change Counter.ResetClockBankDefectEntry ring
      (densityRealAfter ring ((protocol q).step ring C e) pre)
      root edge
    exact he

private theorem coldDefectNextHasOldEntry
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : Counter.ResetClockBankColdState
      (q := ceilLogTwo n) ring root)
    (hz : ¬ Counter.resetClockBankColdTerminal ring root z)
    (e : Fin n) (D : Counter.Config (ceilLogTwo n) n)
    (hdef :
      Counter.resetClockBankColdNext ring root hsp z e =
        .inr (.inr (D, .defect))) :
    Counter.ResetClockBankDefectEntry ring
      (Counter.resetClockBankColdConfig ring root z) root e := by
  cases z with
  | inl x =>
      change Counter.ResetClockBankDefectEntry ring x.val root e
      by_cases hd : Counter.ResetClockBankDefectEntry ring x.val root e
      · exact hd
      · by_cases hg :
          Counter.GrantFree
            ((protocol (ceilLogTwo n)).step ring x.val e) root
        · rw [Counter.resetClockBankColdNextContinue
              ring root hsp x e hd hg] at hdef
          unfold Counter.resetClockBankColdLift at hdef
          split at hdef <;> cases hdef
        · rw [Counter.resetClockBankColdNextGrant
              ring root hsp x e hd hg] at hdef
          cases hdef
  | inr y =>
      cases y with
      | inl a =>
          change
            (Sum.inr (Counter.resetClockBankResultObserve ring root
              (Counter.resetClockBankAttemptService
                ring root hsp a e)) :
              Counter.ResetClockBankColdState
                (q := ceilLogTwo n) ring root) =
              .inr (.inr (D, .defect)) at hdef
          cases hs : Counter.resetClockBankAttemptService
              ring root hsp a e with
          | active a' =>
              rw [hs] at hdef
              cases hdef
          | retry seed =>
              rw [hs] at hdef
              cases hdef
          | stop D' reason =>
              rw [hs] at hdef
              cases reason with
              | clean =>
                  cases hdef
              | grant =>
                  cases hdef
              | defect =>
                  cases hdef
                  exact Counter.resetClockBankServiceStopSound
                    ring root hsp a e _ .defect hs
      | inr outcome =>
          exact False.elim (hz True.intro)


/-- Terminal observer records are absorbing on real scheduler
letters. -/
private theorem coldDefectTerminalNextFixed
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : Counter.ResetClockBankColdState
      (q := ceilLogTwo n) ring root)
    (hz : Counter.resetClockBankColdTerminal ring root z)
    (e : Fin n) :
    Counter.resetClockBankColdNext ring root hsp z e = z := by
  cases z with
  | inl x =>
      exact False.elim hz
  | inr y =>
      cases y with
      | inl a =>
          exact False.elim hz
      | inr outcome =>
          rfl

private theorem coldDefectTerminalRunFixed
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ∀ (word : List (Fin n))
      (z : Counter.ResetClockBankColdState
        (q := ceilLogTwo n) ring root),
      Counter.resetClockBankColdTerminal ring root z →
      Prob.stoppedTapeRun
        (Counter.resetClockBankColdNext ring root hsp) word z = z := by
  intro word
  induction word with
  | nil =>
      intro z hz
      rfl
  | cons e tail ih =>
      intro z hz
      change Prob.stoppedTapeRun
          (Counter.resetClockBankColdNext ring root hsp)
          tail (Counter.resetClockBankColdNext ring root hsp z e) =
        z
      rw [coldDefectTerminalNextFixed ring root hsp z hz e]
      exact ih z hz

/-- A terminal DEFECT reached from a nonterminal observer state
is witnessed by a real OLD-edge event inside that exact word.
No observer-soundness existential is misused as a location. -/
private theorem coldDefectTraceHasEntry
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ∀ (word : List (Fin n))
      (z : Counter.ResetClockBankColdState
        (q := ceilLogTwo n) ring root)
      (D : Counter.Config (ceilLogTwo n) n),
      ¬ Counter.resetClockBankColdTerminal ring root z →
      Prob.stoppedTapeRun
        (Counter.resetClockBankColdNext ring root hsp) word z =
        .inr (.inr (D, .defect)) →
      DefectCrossingEntryWithin ring
        (Counter.resetClockBankColdConfig ring root z) root word := by
  intro word
  induction word with
  | nil =>
      intro z D hn hdef
      change z = .inr (.inr (D, .defect)) at hdef
      have ht : Counter.resetClockBankColdTerminal ring root z := by
        rw [hdef]
        exact True.intro
      exact False.elim (hn ht)
  | cons e tail ih =>
      intro z D hn hdef
      have htail :
          Prob.stoppedTapeRun
            (Counter.resetClockBankColdNext ring root hsp)
            tail (Counter.resetClockBankColdNext ring root hsp z e) =
              .inr (.inr (D, .defect)) := by
        simpa only [Prob.stoppedTapeRun] using hdef
      by_cases hnext :
          Counter.resetClockBankColdTerminal ring root
            (Counter.resetClockBankColdNext ring root hsp z e)
      · have hfixed := coldDefectTerminalRunFixed
          ring root hsp tail
          (Counter.resetClockBankColdNext ring root hsp z e) hnext
        rw [hfixed] at htail
        have hentry := coldDefectNextHasOldEntry
          ring root hsp z hn e D htail
        refine ⟨[], e, tail, rfl, ?_⟩
        simpa only [densityRealAfter] using hentry
      · have hchild := ih
          (Counter.resetClockBankColdNext ring root hsp z e)
          D hnext htail
        rw [Counter.resetClockBankColdPhysical
          ring root hsp z hn e] at hchild
        exact coldDefectCrossingCons ring
          (Counter.resetClockBankColdConfig ring root z)
          root e tail hchild

/-- Initial cold observer is not yet a terminal labelled outcome,
including the RESET-start injection. -/
private theorem coldDefectStartNonterminal
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root) :
    ¬ Counter.resetClockBankColdTerminal ring root
      (Counter.resetClockBankColdStart ring root x) := by
  unfold Counter.resetClockBankColdStart
    Counter.resetClockBankColdLift
  split <;> simp [Counter.resetClockBankColdTerminal,
    Counter.resetClockBankRenewalTarget]

/-- Wordwise G13/G14 bridge at any fixed prefix length.
The initial physical configuration is exactly x.val. -/
theorem bankTrialColdDefectRunImpliesCrossing
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (word : List (Fin n))
    (D : Counter.Config (ceilLogTwo n) n)
    (hdef :
      Prob.stoppedTapeRun
        (Counter.resetClockBankColdNext ring root hsp)
        word (Counter.resetClockBankColdStart ring root x) =
          .inr (.inr (D, .defect))) :
    DefectCrossingEntryWithin ring x.val root word := by
  have h := coldDefectTraceHasEntry
    ring root hsp word (Counter.resetClockBankColdStart ring root x)
    D (coldDefectStartNonterminal ring root x) hdef
  rw [Counter.resetClockBankColdStartPhysical ring root x] at h
  exact h

/-- The DEFECT exit is the only state whose Boolean flag is true. -/
private def coldDefectTerminalFlag
    {n : Nat} (ring : DirectedRing n) (root : Fin n) :
    Counter.ResetClockBankColdState
      (q := ceilLogTwo n) ring root → Bool
  | .inr (.inr (_, .defect)) => true
  | _ => false

private theorem coldDefectFlagWitness
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (z : Counter.ResetClockBankColdState
      (q := ceilLogTwo n) ring root)
    (hz : coldDefectTerminalFlag ring root z = true) :
    ∃ D : Counter.Config (ceilLogTwo n) n,
      z = .inr (.inr (D, .defect)) := by
  cases z with
  | inl a =>
      simp [coldDefectTerminalFlag] at hz
  | inr y =>
      cases y with
      | inl a =>
          simp [coldDefectTerminalFlag] at hz
      | inr output =>
          cases output with
          | mk D reason =>
              cases reason with
              | clean =>
                  simp [coldDefectTerminalFlag] at hz
              | grant =>
                  simp [coldDefectTerminalFlag] at hz
              | defect =>
                  exact ⟨D, rfl⟩

/-- Wordwise first-stop cylinders use the same terminal flag as
the DEFECT label. -/
private theorem coldDefectFlagCylinder
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (z : Counter.ResetClockBankColdState
      (q := ceilLogTwo n) ring root)
    (k : Nat) :
    n ^ k * Prob.indicator (coldDefectTerminalFlag ring root z) =
      match z with
      | .inr (.inr (_, .defect)) => n ^ k
      | _ => 0 := by
  cases z with
  | inl a =>
      simp [coldDefectTerminalFlag, Prob.indicator]
  | inr y =>
      cases y with
      | inl a =>
          simp [coldDefectTerminalFlag, Prob.indicator]
      | inr output =>
          cases output with
          | mk D reason =>
              cases reason with
              | clean =>
                  simp [coldDefectTerminalFlag, Prob.indicator]
              | grant =>
                  simp [coldDefectTerminalFlag, Prob.indicator]
              | defect =>
                  simp [coldDefectTerminalFlag, Prob.indicator]

/-- The actual prefix of length W still begins with any already
consumed prefix whose length is at most W. -/
private theorem coldDefectPrefixTakeShape
    {α : Type} :
    ∀ (pre suffix : List α) (W : Nat),
      pre.length ≤ W →
      ∃ rest : List α,
        (pre ++ suffix).take W = pre ++ rest := by
  intro pre
  induction pre with
  | nil =>
      intro suffix W _
      exact ⟨suffix.take W, rfl⟩
  | cons e pre ih =>
      intro suffix W hlength
      cases W with
      | zero =>
          simp only [List.length_cons] at hlength
          omega
      | succ W =>
          have htail : pre.length ≤ W := by
            simp only [List.length_cons] at hlength
            omega
          obtain ⟨rest, hrest⟩ := ih suffix W htail
          refine ⟨rest, ?_⟩
          simp only [List.cons_append, List.take_succ_cons]
          exact congrArg (List.cons e) hrest

private theorem coldDefectRunAppendOne
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ∀ (pre : List (Fin n))
      (z : Counter.ResetClockBankColdState
        (q := ceilLogTwo n) ring root) (e : Fin n),
      Prob.stoppedTapeRun
        (Counter.resetClockBankColdNext ring root hsp)
        (pre ++ [e]) z =
      Counter.resetClockBankColdNext ring root hsp
        (Prob.stoppedTapeRun
          (Counter.resetClockBankColdNext ring root hsp) pre z) e := by
  intro pre
  induction pre with
  | nil =>
      intro z e
      rfl
  | cons a tail ih =>
      intro z e
      change Prob.stoppedTapeRun
          (Counter.resetClockBankColdNext ring root hsp)
          (tail ++ [e])
          (Counter.resetClockBankColdNext ring root hsp z a) =
        Counter.resetClockBankColdNext ring root hsp
          (Prob.stoppedTapeRun
            (Counter.resetClockBankColdNext ring root hsp)
            tail (Counter.resetClockBankColdNext ring root hsp z a)) e
      exact ih _ e

/-- Any successful stopped-word DEFECT flag has a physical
crossing witness within its consumed prefix, hence within the
first W scheduler letters. -/
private theorem coldDefectFlagAtConsumedPrefix
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (pre suffix : List (Fin n)) (W : Nat)
    (z : Counter.ResetClockBankColdState
      (q := ceilLogTwo n) ring root)
    (hstate : z =
      Prob.stoppedTapeRun
        (Counter.resetClockBankColdNext ring root hsp)
        pre (Counter.resetClockBankColdStart ring root x))
    (hpre : pre.length ≤ W)
    (hflag : coldDefectTerminalFlag ring root z = true) :
    DefectCrossingEntryWithin ring x.val root
      ((pre ++ suffix).take W) := by
  obtain ⟨D, hdef⟩ :=
    coldDefectFlagWitness ring root z hflag
  have hrun :
      Prob.stoppedTapeRun
          (Counter.resetClockBankColdNext ring root hsp)
          pre (Counter.resetClockBankColdStart ring root x) =
        .inr (.inr (D, .defect)) := by
    rw [← hstate, hdef]
  have hentry :=
    bankTrialColdDefectRunImpliesCrossing
      ring root hsp x pre D hrun
  obtain ⟨rest, htake⟩ :=
    coldDefectPrefixTakeShape pre suffix W hpre
  rw [htake]
  exact coldDefectCrossingAppend
    ring x.val root pre rest hentry

private theorem coldDefectStoppedWordLeCrossing
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (W : Nat) :
    ∀ (word pre : List (Fin n))
      (z : Counter.ResetClockBankColdState
        (q := ceilLogTwo n) ring root) (T : Nat),
      z = Prob.stoppedTapeRun
        (Counter.resetClockBankColdNext ring root hsp)
        pre (Counter.resetClockBankColdStart ring root x) →
      bankTrialSuccessNatStoppedWord
        (Counter.resetClockBankColdNext ring root hsp)
        (bankTrialRenewalColdStop ring root)
        (fun cut y _ _ =>
          if cut.length ≤ W then
            Prob.indicator (coldDefectTerminalFlag ring root y)
          else 0)
        T pre z word ≤
      (if DefectCrossingEntryWithin ring x.val root
        ((pre ++ word).take W) then 1 else 0) := by
  intro word
  induction word with
  | nil =>
      intro pre z T hstate
      cases hs : bankTrialRenewalColdStop ring root pre z with
      | false =>
          simp [bankTrialSuccessNatStoppedWord, hs]
      | true =>
          by_cases hpre : pre.length ≤ W
          · by_cases hflag :
              coldDefectTerminalFlag ring root z = true
            · have hentry := coldDefectFlagAtConsumedPrefix
                ring root hsp x pre [] W z hstate hpre hflag
              have hentryBase :
                  DefectCrossingEntryWithin ring x.val root
                    (List.take W pre) := by
                simpa only [List.append_nil] using hentry
              simp [bankTrialSuccessNatStoppedWord, hs,
                hpre, Prob.indicator, hflag, hentryBase]
            · simp [bankTrialSuccessNatStoppedWord, hs,
                hpre, Prob.indicator, hflag]
          · simp [bankTrialSuccessNatStoppedWord, hs, hpre]
  | cons e tail ih =>
      intro pre z T hstate
      cases hs : bankTrialRenewalColdStop ring root pre z with
      | true =>
          by_cases hpre : pre.length ≤ W
          · by_cases hflag :
              coldDefectTerminalFlag ring root z = true
            · have hentry := coldDefectFlagAtConsumedPrefix
                ring root hsp x pre (e :: tail) W z
                hstate hpre hflag
              simp [bankTrialSuccessNatStoppedWord, hs,
                hpre, Prob.indicator, hflag, hentry]
            · simp [bankTrialSuccessNatStoppedWord, hs,
                hpre, Prob.indicator, hflag]
          · simp [bankTrialSuccessNatStoppedWord, hs, hpre]
      | false =>
          have hnext :
              Counter.resetClockBankColdNext ring root hsp z e =
                Prob.stoppedTapeRun
                  (Counter.resetClockBankColdNext ring root hsp)
                  (pre ++ [e])
                  (Counter.resetClockBankColdStart ring root x) := by
            rw [coldDefectRunAppendOne, ← hstate]
          have hchild := ih (pre ++ [e])
            (Counter.resetClockBankColdNext ring root hsp z e)
            (T - 1) hnext
          simpa only [bankTrialSuccessNatStoppedWord,
            hs, Bool.false_eq_true, if_false,
            List.append_assoc, List.singleton_append] using hchild


private theorem coldDefectMassStoppedFactor
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T W : Nat) :
    bankTrialRenewalColdDefectMass ring root hsp x T W =
    Prob.scheduleSum n T (fun word =>
      bankTrialSuccessNatStoppedWord
        (Counter.resetClockBankColdNext ring root hsp)
        (bankTrialRenewalColdStop ring root)
        (fun cut y _ _ =>
          if cut.length ≤ W then
            Prob.indicator (coldDefectTerminalFlag ring root y)
          else 0)
        T [] (Counter.resetClockBankColdStart ring root x) word) := by
  rw [bankTrialSuccessNatStoppedFactorization]
  unfold bankTrialRenewalColdDefectMass
  apply congrArg List.sum
  apply List.map_congr_left
  intro cut _
  by_cases hc : cut.length ≤ W
  · simp only [if_pos hc]
    rw [bankTrialProbabilityScheduleSumConst]
    exact (coldDefectFlagCylinder ring root
      (Prob.stoppedTapeRun
        (Counter.resetClockBankColdNext ring root hsp)
        cut (Counter.resetClockBankColdStart ring root x))
      (T - cut.length)).symm
  · simp only [if_neg hc]
    rw [bankTrialProbabilityScheduleSumConst]
    simp only [Nat.mul_zero]


/-- The desired first-stop-to-crossing injection on the original
length-T scheduler. This is the missing G13/G14 event bridge. -/
theorem bankTrialRenewalColdDefectMassLeCrossing
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T W : Nat) :
    bankTrialRenewalColdDefectMass ring root hsp x T W ≤
    Prob.scheduleSum n T (fun word =>
      if DefectCrossingEntryWithin ring x.val root
        (word.take W) then 1 else 0) := by
  rw [coldDefectMassStoppedFactor]
  apply Density.schedule_sum_mono
  intro word
  simpa only [List.nil_append] using
    (coldDefectStoppedWordLeCrossing
      ring root hsp x W word []
      (Counter.resetClockBankColdStart ring root x)
      T rfl)

/-- The C.11 crossing estimate pays the entire authentic cold
DEFECT stopped-prefix mass, with C exactly x.val. -/
theorem bankTrialRenewalColdDefectCrossingBound
    {n : Nat} (hn : 5 ≤ n)
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (radius W T : Nat)
    (hBuffered : HeadlineGrantBufferedCounter
      ring x.val radius root)
    (hWT : W ≤ T)
    (hwindow : W ≤ radius * n / 8) :
    8 ^ radius *
      bankTrialRenewalColdDefectMass ring root hsp x T W ≤
    Density.N (badSet ring x.val) * 3 ^ radius * n ^ T := by
  exact Nat.le_trans
    (Nat.mul_le_mul_left (8 ^ radius)
      (bankTrialRenewalColdDefectMassLeCrossing
        ring root hsp x T W))
    (defectCrossingMass (by omega : 2 ≤ n)
      ring x.val root radius W T hBuffered hWT hwindow)

/-- All multiplication is performed over opaque natural numbers;
the two probabilistic inequalities are fed to this arithmetic
lemma without opening compiler powers. -/
private theorem coldDefectProxySubtractionArithmetic
    (A B D C N W P E : Nat)
    (hbase : A * W * N ≤ B * (P + E))
    (hcross : D * E ≤ C * N)
    (hsmall : B * C ≤ A * W * D) :
    (A * W * D - B * C) * N ≤ B * D * P := by
  have hscaled := Nat.mul_le_mul_left D hbase
  have hcrossScaled := Nat.mul_le_mul_left B hcross
  have htotal :
      (A * W * D) * N ≤ B * D * P + (B * C) * N := by
    calc
      (A * W * D) * N = D * (A * W * N) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ D * (B * (P + E)) := hscaled
      _ = B * D * P + B * (D * E) := by
        simp only [Nat.mul_add, Nat.mul_assoc,
          Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ B * D * P + B * (C * N) :=
        Nat.add_le_add_left hcrossScaled _
      _ = B * D * P + (B * C) * N := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hsub : (A * W * D - B * C) + B * C = A * W * D :=
    Nat.sub_add_cancel hsmall
  have hscaledSub := congrArg (fun v : Nat => v * N) hsub
  rw [Nat.add_mul] at hscaledSub
  omega

/-- Explicit sparse-defect correction to G13. The smallness
condition is B*C ≤ 51279921*W*8^radius, with B exactly the
C.16 coefficient and C exactly the C.11 bad-particle weight.
No additional physical-success coupling is asserted. -/
theorem bankTrialRenewalColdProxyMassSparseLower
    {n : Nat} (hn : 5 ≤ n)
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (hlarge :
      2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (R L T W radius : Nat)
    (hradius : (256 * R) ^ 2 ≤ n ∧
      n < (256 * (R + 1)) ^ 2)
    (hW : W = R * n / 8)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold
      n (ceilLogTwo n) ≤ L)
    (hWT : W ≤ T)
    (hbudgetCold :
      W + bankTrialRenewalIndexWindowCount
        n (ceilLogTwo n) W * L ≤ T)
    (hBuffered : HeadlineGrantBufferedCounter
      ring x.val radius root)
    (hcrossWindow : W ≤ radius * n / 8)
    (hsmall :
      (104857600 * (8 * (compileAdvice (ceilLogTwo n)).b + 13) *
        n * 2 ^ (compileAdvice (ceilLogTwo n)).K) *
        (Density.N (badSet ring x.val) * 3 ^ radius) ≤
      51279921 * W * 8 ^ radius) :
    (51279921 * W * 8 ^ radius -
      (104857600 * (8 * (compileAdvice (ceilLogTwo n)).b + 13) *
        n * 2 ^ (compileAdvice (ceilLogTwo n)).K) *
        (Density.N (badSet ring x.val) * 3 ^ radius)) * n ^ T ≤
    (104857600 * (8 * (compileAdvice (ceilLogTwo n)).b + 13) *
      n * 2 ^ (compileAdvice (ceilLogTwo n)).K) *
      8 ^ radius *
      bankTrialRenewalColdProxyMass ring root hsp x T W := by
  have hbase := bankTrialRenewalColdSuccessMassLower
    ring root hn hsp hw hlarge x R L T W
    hradius hW hL hWT hbudgetCold
  have hcross := bankTrialRenewalColdDefectCrossingBound
    hn ring root hsp x radius W T hBuffered hWT hcrossWindow
  exact coldDefectProxySubtractionArithmetic
    51279921
    (104857600 * (8 * (compileAdvice (ceilLogTwo n)).b + 13) *
      n * 2 ^ (compileAdvice (ceilLogTwo n)).K)
    (8 ^ radius)
    (Density.N (badSet ring x.val) * 3 ^ radius)
    (n ^ T) W
    (bankTrialRenewalColdProxyMass ring root hsp x T W)
    (bankTrialRenewalColdDefectMass ring root hsp x T W)
    (by simpa only [Nat.mul_assoc] using hbase)
    (by simpa only [Nat.mul_assoc] using hcross)
    hsmall

end L3

#print axioms L3.bankTrialColdDefectRunImpliesCrossing
#print axioms L3.bankTrialRenewalColdDefectMassLeCrossing
#print axioms L3.bankTrialRenewalColdDefectCrossingBound
#print axioms L3.bankTrialRenewalColdProxyMassSparseLower
