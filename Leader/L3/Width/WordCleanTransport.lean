import Leader.L3.Width.WordCleanPass

/-!
# Width W clean clock, part 5: the completion future and the clean target

Ported BankWordCleanWord and BankWordCleanTransport declarations.
Every declaration is the width port of the BANK declaration named in its
docstring (via SmallWordClean*): band premise `5 ≤ n`, start class
`WidthWordSerializerRootClass` (the fixed physical root), renewal
constants in the compiled width t; see WidthWordCleanBand.
-/

namespace L3.RenewalReferenceClock

open Classical

set_option autoImplicit false
set_option Elab.async false

section
open Classical
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3.AcceptedReceipts
open L3.AcceptedReceipts.WordEntrance
open L3.AcceptedReceipts.WordEntrance.CleanWorker
open L3.WordCertificate

/-- Width port of `generatedControlOfAllFree`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordCompletionGeneratedControl`.
 All SI free at BANK width is a GeneratedControl state: empty
shape, and the acceptance scrub holds because every site is free.
Consumer: `widthWordCompletionGeneratedControl`. -/
theorem widthGeneratedControlOfAllFree {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsmallFive : 5 ≤ n)
    (p : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hfree : ∀ i : Fin n, freeSI (p i).si = true) :
    GeneratedControl ring root p := by
  have hw := widthWordPassWidth hsmallFive
  exact generatedControlOfEmpty ring root p
    ⟨hw.1, by omega⟩ hfree
    (fun _ _ i _ _ => hfree i)

end

section
open Classical
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3.AcceptedReceipts
open L3.AcceptedReceipts.WordEntrance
open L3.AcceptedReceipts.WordEntrance.CleanWorker
open L3.WordCertificate

/-- Width port of `bankWordCompletionGeneratedControl`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordCompletionFutureInvariant`.
 Group 4 base: at every reachable completed epoch state the
physical word is a GeneratedControl state.  Consumer:
`widthWordCompletionFutureInvariant`. -/
theorem widthWordCompletionGeneratedControl {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hcomp : BankWordRenewalCompleted z) :
    GeneratedControl ring root z.2.1 :=
  widthGeneratedControlOfAllFree ring root hsmallFive z.2.1
    (widthWordEpochCompletedClean ring hn hsmallFive root s hs z hz hcomp).2

end

section
open Classical
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3.AcceptedReceipts
open L3.AcceptedReceipts.WordEntrance
open L3.AcceptedReceipts.WordEntrance.CleanWorker
open L3.WordCertificate

/-- Width port of `GeneratedControlTransport`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthCleanWorkerCompletionQWord`, `widthGeneratedControlTransportOfRows`, `widthWordCompletionCleanWordTarget`.
 The GeneratedControl transport that QWord at a completion needs,
stated on the future of reachable completions (both fields of
`qwordOfGeneratedControl`: selected quietness and the forward step,
whose acceptClean clause is the successor's GeneratedControl field).
Consumer: `widthCleanWorkerCompletionQWord`; its proof is the open
WordGeneratedStep lane. -/
structure WidthGeneratedControlTransport {n : Nat}
    (ring : DirectedRing n)
    (hsmallFive : 5 ≤ n) : Prop where
  selected : ∀ root : Fin n,
    ∀ s : Fin n → ProjW (compileAdvice (ceilLogTwo n)),
      WidthWordSerializerRootClass ring hsmallFive root s →
      ∀ y : BankWordEpochState n,
        BankWordCompletionFuture ring root s y →
        GeneratedControl ring root y.2.1 →
        CleanWorkerWordValues ring root y.2.1 →
        ∀ e : Fin n,
          SelectedWordQuiet (y.2.1 e) (y.2.1 (ring.rightNeighbor e))
  step : ∀ root : Fin n,
    ∀ s : Fin n → ProjW (compileAdvice (ceilLogTwo n)),
      WidthWordSerializerRootClass ring hsmallFive root s →
      ∀ y : BankWordEpochState n,
        BankWordCompletionFuture ring root s y →
        GeneratedControl ring root y.2.1 →
        CleanWorkerWordValues ring root y.2.1 →
        ∀ e : Fin n,
          GeneratedControl ring root (phiW ring y.2.1 e)

end

section
open Classical
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3.AcceptedReceipts
open L3.AcceptedReceipts.WordEntrance
open L3.AcceptedReceipts.WordEntrance.CleanWorker
open L3.WordCertificate

/-- Width port of `bankWordCompletionFutureInvariant`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthCleanWorkerCompletionQWord`.
 On the completion future every state is a GeneratedControl state
with the clean word values.  Consumer: `widthCleanWorkerCompletionQWord`. -/
theorem widthWordCompletionFutureInvariant {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (htrans : WidthGeneratedControlTransport ring hsmallFive)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (y : BankWordEpochState n)
    (hy : BankWordCompletionFuture ring root s y) :
    GeneratedControl ring root y.2.1 ∧
      CleanWorkerWordValues ring root y.2.1 := by
  obtain ⟨z, hz, hc, word, hw⟩ := hy
  subst hw
  have key : ∀ (w : List (Fin n)) (y0 : BankWordEpochState n),
      BankWordCompletionFuture ring root s y0 →
      GeneratedControl ring root y0.2.1 →
      CleanWorkerWordValues ring root y0.2.1 →
      GeneratedControl ring root (bankWordEpochRun ring root y0 w).2.1 ∧
        CleanWorkerWordValues ring root
          (bankWordEpochRun ring root y0 w).2.1 := by
    intro w
    induction w with
    | nil =>
        intro y0 _ hg hcl
        exact ⟨hg, hcl⟩
    | cons e rest ih =>
        intro y0 hf hg hcl
        have hne : ring.rightNeighbor e ≠ e :=
          clockNeighborDifferent ring (by omega : 2 ≤ n) e
        have hg' : GeneratedControl ring root
            (bankWordEpochNext ring root y0 e).2.1 :=
          htrans.step root s hs y0 hf hg hcl e
        have hcl' : CleanWorkerWordValues ring root
            (bankWordEpochNext ring root y0 e).2.1 :=
          (generatedControlSelectedWordStep ring root y0.2.1 e hne hcl
            (htrans.selected root s hs y0 hf hg hcl e)).2
        exact ih (bankWordEpochNext ring root y0 e)
          (bankWordCompletionFutureNext ring root s y0 hf e) hg' hcl'
  exact key word z ⟨z, hz, hc, [], rfl⟩
    (widthWordCompletionGeneratedControl ring hn hsmallFive root s hs z hz hc)
    (widthWordEpochCompletedClean ring hn hsmallFive root s hs z hz hc).1

end

section
open Classical
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3.AcceptedReceipts
open L3.AcceptedReceipts.WordEntrance
open L3.AcceptedReceipts.WordEntrance.CleanWorker
open L3.WordCertificate

/-- Width port of `cleanWorkerCompletionQWord`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordCompletionCleanWordTarget`.
 Group 4: QWord at every reachable completion, from the transport
premise and the green clean completion.  Consumer:
`widthWordCompletionCleanWordTarget`. -/
theorem widthCleanWorkerCompletionQWord {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (htrans : WidthGeneratedControlTransport ring hsmallFive)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hcomp : BankWordRenewalCompleted z) :
    QWord ring z.2.1 := by
  change SafeAll (phiW ring) (badWord ring) z.2.1
  apply safe_inclusion (phiW ring) (badWord ring)
    (fun q => ∃ y : BankWordEpochState n,
      BankWordCompletionFuture ring root s y ∧ y.2.1 = q)
  · intro q hq e
    obtain ⟨y, hy, hyq⟩ := hq
    subst hyq
    obtain ⟨hg, hcl⟩ := widthWordCompletionFutureInvariant
      ring hn hsmallFive htrans root s hs y hy
    have hne : ring.rightNeighbor e ≠ e :=
      clockNeighborDifferent ring (by omega : 2 ≤ n) e
    have hv := (selectedWordQuiet_iff_edge ring y.2.1 e hne).mp
      (htrans.selected root s hs y hy hg hcl e)
    refine ⟨?_, ⟨bankWordEpochNext ring root y e,
      bankWordCompletionFutureNext ring root s y hy e, rfl⟩⟩
    intro hbad
    obtain ⟨i, hi⟩ := hbad
    exact hi (hv i)
  · exact ⟨z, ⟨z, hz, hcomp, [], rfl⟩, rfl⟩

end

section
open Classical
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3.AcceptedReceipts
open L3.AcceptedReceipts.WordEntrance
open L3.AcceptedReceipts.WordEntrance.CleanWorker
open L3.WordCertificate

/-- Width port of `bankWordCompletionCleanWordTarget`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: the SMALL clean W clock.
 Every reachable completion is a clean-word entrance state.
Consumer: `bankWordCleanWordClockOfTransport`. -/
theorem widthWordCompletionCleanWordTarget {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (htrans : WidthGeneratedControlTransport ring hsmallFive)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hcomp : BankWordRenewalCompleted z) :
    BankWordCleanWordTarget ring z.2.1 := by
  have hclean :=
    widthWordEpochCompletedClean ring hn hsmallFive root s hs z hz hcomp
  exact ⟨root,
    ⟨widthWordEpochFixedRoot ring hn hsmallFive root s hs z hz,
      hclean.1,
      widthCleanWorkerCompletionQWord ring hn hsmallFive htrans root s hs z hz hcomp⟩,
    hclean.2⟩

end

section
open Classical
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3.AcceptedReceipts
open L3.AcceptedReceipts.WordEntrance
open L3.AcceptedReceipts.WordEntrance.CleanWorker
open L3.WordCertificate

/-- Width port of `bankWordEpochCompletedRetired`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordCompletionFutureWave`.
 The retired pass state at every reachable completion (same proof as
`widthWordEpochCompletedClean`, keeping the retirement record).
Consumer: `widthWordCompletionFutureWave` (root not VALIDATING). -/
theorem widthWordEpochCompletedRetired {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hcomp : BankWordRenewalCompleted z) :
    BankWordPassRetired ring root z := by
  obtain ⟨word, hword⟩ := hz
  obtain ⟨r, hr⟩ := hcomp
  cases hrev : word.reverse with
  | nil =>
      have hnil : word = [] := List.reverse_eq_nil_iff.mp hrev
      subst hnil
      rw [← hword] at hr
      cases hr
  | cons e rest =>
      have hsplit : word = rest.reverse ++ [e] := by
        have := congrArg List.reverse hrev
        simpa using this
      subst hsplit
      rw [bankWordEpochRunAppend] at hword
      let y := bankWordEpochRun ring root (bankWordEpochStart s)
        rest.reverse
      have hy : BankWordEpochReachable ring root s y :=
        ⟨rest.reverse, rfl⟩
      have hzy : bankWordEpochNext ring root y e = z := hword
      have hr' :
          (wWorkerReceiptStep root e (ring.rightNeighbor e)
            (y.2.2.clock + 1)
            (y.2.1 e) (y.2.1 (ring.rightNeighbor e))
            (wGenuineAcceptance root e
              (y.2.1 e) (y.2.1 (ring.rightNeighbor e))
              (y.2.2.validation e)
              (y.2.2.validation (ring.rightNeighbor e)))
            y.2.2.worker).2 = some r := by
        have h2 : (bankWordEpochNext ring root y e).2.2.completion =
            some r := by
          rw [hzy]
          exact hr
        exact h2
      obtain ⟨hnone, hno, w, hw⟩ :=
        bankWordPassGhostCompletionCases _ _ _ _ _ _ _ _ r hr'
      obtain ⟨seed, word0, hrun, hnh, hl⟩ :=
        widthWordEpochLiveFromSeedReachable ring hn hsmallFive root s hs y hy
          w hw
      have hnh' : BankWordPassNoHardStart ring root seed.1.1
          (word0 ++ [e]) := by
        apply bankWordPassNoHardStartSnoc ring root word0 seed.1.1 e hnh
        rw [hrun]
        exact hno
      have hend :
          bankWordEpochRun ring root seed.1.1 (word0 ++ [e]) = z := by
        rw [bankWordEpochRunAppend, hrun]
        exact hzy
      have hworkerNone : z.2.2.worker = none := by
        have h2 : (bankWordEpochNext ring root y e).2.2.worker = none :=
          hnone
        rw [hzy] at h2
        exact h2
      rcases widthWordPassValuesRun ring hn hsmallFive root s hs
          (word0 ++ [e]) seed.1.1 seed.1.2.1
          (widthWordPassShapeAtFreshSeed ring hn hsmallFive root s hs seed)
          (widthWordPassValuesBase ring hn hsmallFive root s hs seed) hnh' with
        ⟨hshape, _, _⟩ | hclean
      · exfalso
        rw [bankWordPassLabelRunEq, hend] at hshape
        obtain ⟨v, hv, _⟩ := hshape.2.1
        rw [hworkerNone] at hv
        cases hv
      · obtain ⟨hret, _⟩ :=
          bankWordPassCleanAtLastLetter ring root word0 seed.1.1 e hl hclean
        rw [hend] at hret
        exact hret

end

section
open Classical
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3.AcceptedReceipts
open L3.AcceptedReceipts.WordEntrance
open L3.AcceptedReceipts.WordEntrance.CleanWorker
open L3.WordCertificate

/-- Width port of `bankWordCompletionFutureWave`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthGeneratedControlTransportOfRows`.
 The wave scrub holds on the whole completion future.  Consumer:
`widthGeneratedControlTransportOfRows`. -/
theorem widthWordCompletionFutureWave {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (y : BankWordEpochState n)
    (hy : BankWordCompletionFuture ring root s y) :
    BankWordFutureWave ring root y.2.1 := by
  obtain ⟨z, hz, hc, word, hw⟩ := hy
  subst hw
  have key : ∀ (w : List (Fin n)) (y0 : BankWordEpochState n),
      BankWordCompletionFuture ring root s y0 →
      BankWordFutureWave ring root y0.2.1 →
      BankWordFutureWave ring root (bankWordEpochRun ring root y0 w).2.1 := by
    intro w
    induction w with
    | nil => intro y0 _ h; exact h
    | cons e rest ih =>
        intro y0 hf h
        have hr := bankWordCompletionFutureReachable ring root s y0 hf
        apply ih (bankWordEpochNext ring root y0 e)
          (bankWordCompletionFutureNext ring root s y0 hf e)
        exact bankWordFutureWaveStep (by omega) ring root y0.2.1 e
          (widthWordEpochFixedRoot ring hn hsmallFive root s hs y0 hr)
          (widthWordEpochFixedRootNext ring hn hsmallFive root s hs y0 hr e) h
  apply key word z ⟨z, hz, hc, [], rfl⟩
  exact Or.inl ((widthWordEpochCompletedRetired ring hn hsmallFive root s hs
    z hz hc).1 root)

end

section
open Classical
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3.AcceptedReceipts
open L3.AcceptedReceipts.WordEntrance
open L3.AcceptedReceipts.WordEntrance.CleanWorker
open L3.WordCertificate

/-- Width port of `generatedControlTransportOfRows`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: the SMALL clean W clock.
 WidthGeneratedControlTransport from the row transport and the wave scrub.
Consumer: `bankWordCleanWordClockOfRows`. -/
theorem widthGeneratedControlTransportOfRows {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hrows : GeneratedControlRowTransport ring) :
    WidthGeneratedControlTransport ring hsmallFive := by
  have core : ∀ root : Fin n,
      ∀ s : Fin n → ProjW (compileAdvice (ceilLogTwo n)),
        WidthWordSerializerRootClass ring hsmallFive root s →
        ∀ y : BankWordEpochState n,
          BankWordCompletionFuture ring root s y →
          GeneratedControl ring root y.2.1 →
          CleanWorkerWordValues ring root y.2.1 →
          ∀ e : Fin n,
            GeneratedControl ring root (phiW ring y.2.1 e) ∧
              SelectedWordQuiet (y.2.1 e) (y.2.1 (ring.rightNeighbor e)) := by
    intro root s hs y hy hg hcl e
    have hr := bankWordCompletionFutureReachable ring root s y hy
    have hfix := widthWordEpochFixedRoot ring hn hsmallFive root s hs y hr
    have hwave := widthWordCompletionFutureWave ring hn hsmallFive root s hs y hy
    have hy' := bankWordCompletionFutureNext ring root s y hy e
    have hfix' := widthWordEpochFixedRoot ring hn hsmallFive root s hs _
      (bankWordCompletionFutureReachable ring root s _ hy')
    have hwave' := widthWordCompletionFutureWave ring hn hsmallFive root s hs _ hy'
    exact hrows root y.2.1 hfix hg hcl e
      ((bankWordFutureAcceptPair (by omega) ring root y.2.1 hfix hwave).2 e)
      (bankWordFutureAcceptPair (by omega) ring root _ hfix' hwave').1
  exact ⟨fun root s hs y hy hg hcl e => (core root s hs y hy hg hcl e).2,
    fun root s hs y hy hg hcl e => (core root s hs y hy hg hcl e).1⟩

end

section
open Classical
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3.AcceptedReceipts
open L3.AcceptedReceipts.WordEntrance
open L3.AcceptedReceipts.WordEntrance.CleanWorker
open L3.WordCertificate

/-- Width port of `bankWordRowTransport`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: the SMALL clean W clock.
 The Cartesian GeneratedControl row transport on BANK rings
(n ≥ 5).  Consumer: `bankWordCleanWordClockOfBank`. -/
theorem widthWordRowTransport {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n) :
    GeneratedControlRowTransport ring := by
  intro root q hfix hgen hword e hresp hnext
  have hne := clockNeighborDifferent ring (by omega) e
  have hroom := (widthWordPassWidth hsmallFive).2
  cases ha : (serW (q e) (q (ring.rightNeighbor e))).hard.hardAccept
  · cases herase : ((serW (q e) (q (ring.rightNeighbor e))).hard.hardLeft ||
        (serW (q e) (q (ring.rightNeighbor e))).hard.hardRight)
    · have hlr := Bool.or_eq_false_iff.mp herase
      exact bankWordRowQuiet ring root q e (by omega) hroom hne hfix hgen
        hword ha hlr.1 hlr.2 hnext
    · exact bankWordRowIone ring root q e hne hgen hword ha herase hnext
  · exact bankWordRowIzero ring root q e hne hfix hgen hword ha
      (hresp ha) hnext

end

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.widthGeneratedControlOfAllFree
#print axioms L3.RenewalReferenceClock.widthWordCompletionGeneratedControl
#print axioms L3.RenewalReferenceClock.widthWordCompletionFutureInvariant
#print axioms L3.RenewalReferenceClock.widthCleanWorkerCompletionQWord
#print axioms L3.RenewalReferenceClock.widthWordCompletionCleanWordTarget
#print axioms L3.RenewalReferenceClock.widthWordEpochCompletedRetired
#print axioms L3.RenewalReferenceClock.widthWordCompletionFutureWave
#print axioms L3.RenewalReferenceClock.widthGeneratedControlTransportOfRows
#print axioms L3.RenewalReferenceClock.widthWordRowTransport
