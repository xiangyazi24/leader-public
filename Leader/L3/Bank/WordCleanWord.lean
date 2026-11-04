import Leader.L3.Bank.WordPassMonitor
import Leader.L3.WordGeneratedStep
import Leader.L3.Bank.RepairDigit

/-!
# R10 W: the clean-word closed class (route (a))

The W stage no longer targets the monitored `AcceptedWord`.  Its
persistent class is `CleanWordAtRoot ring r p`: fixed physical root,
the five clean-worker word equations, and the all-future quiescence
certificate `QWord`.  At the W completion cut every SI is also free;
that clause is an entrance clause only (`BankWordCleanWordTarget`).

* Group 4 base: `GeneratedControl` at every reachable completion
  (`bankWordCompletionGeneratedControl`).
* Group 4: `QWord` at every reachable completion
  (`cleanWorkerCompletionQWord`), from the transport premise
  `GeneratedControlTransport`, which is stated on the future set of
  reachable completions (the Cartesian transport is false: the I0
  countermodel in WordGeneratedStep and `frontierInterferenceProjection`
  in WordCertificate).
* Group 5: `cleanWordRootPhiStep`, closure of `CleanWordAtRoot` under
  every phiW step.
* The W clock to `BankWordCleanWordTarget` with no AcceptedWord
  premise (`bankWordCleanWordClockOfTransport`).
-/

namespace L3.RenewalReferenceClock

open Classical
open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3.AcceptedReceipts
open L3.AcceptedReceipts.WordEntrance
open L3.AcceptedReceipts.WordEntrance.CleanWorker
open L3.WordCertificate

set_option autoImplicit false
set_option Elab.async false

/-! ## The clean-word class and the clean W target -/

/-- The persistent clean-word class at a fixed root.  Consumer:
`cleanWordRootPhiStep`, `BankWordCleanWordTarget`, and the clean
reader / digit origins of group 6. -/
def CleanWordAtRoot {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) : Prop :=
  WFixedRoot ring root p ∧
    CleanWorkerWordValues ring root p ∧
    QWord ring p

/-- The clean-word class at some root.  Consumer: the clean reader
origin of group 6. -/
def CleanWord {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (p : Fin n → ProjW c) : Prop :=
  ∃ root : Fin n, CleanWordAtRoot ring root p

/-- The W entrance target: the clean-word class plus every SI free.
Consumer: `BankWordCleanWordClock`. -/
def BankWordCleanWordTarget {n : Nat}
    (ring : DirectedRing n)
    (p : Fin n → ProjW (compileAdvice (ceilLogTwo n))) : Prop :=
  ∃ root : Fin n,
    CleanWordAtRoot ring root p ∧ ∀ i : Fin n, freeSI (p i).si = true

/-- The W first-hit clock to the clean-word entrance target, with the
(440t+275)n² budget of `BankWordProjectedClock`.  Consumer: the
group 7 clean finish composition. -/
def BankWordCleanWordClock {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  ∀ z : BankReferenceState ring hbank,
    BankPreparedAtSomeRoot ring hbank z →
    ∀ T : Nat,
      costNumerator (phiW ring)
        (BankWordCleanWordTarget ring) (piW z.val.1) T ≤
      n ^ T *
        ((440 * ceilLogTwo (ceilLogTwo n) + 275) * n ^ 2)

/-! ## Group 5: closure of the clean-word class -/

/-- Every phiW step keeps the clean-word class: the root by the
literal E owner, QWord by `qword_step`, and the five word equations
because QWord fixes every visible (u, beta).  Consumer: the W factor
of the clean target closure. -/
theorem cleanWordRootPhiStep {n : Nat} {c : Compiled}
    (hn : 3 ≤ n) (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (e : Fin n)
    (h : CleanWordAtRoot ring root p) :
    CleanWordAtRoot ring root (phiW ring p e) :=
  ⟨bankRepairDigitWFixedRootPhiW hn ring root p e h.1,
    cleanWorkerWordValues_congr ring root (phiW ring p e) p
      (qword_visible_fixed ring p h.2.2 e) h.2.1,
    (qword_step ring p h.2.2 e).2⟩

/-- `CleanWord` is closed under every phiW step.  Consumer: the clean
reader origin closure. -/
theorem cleanWordPhiStep {n : Nat} {c : Compiled}
    (hn : 3 ≤ n) (ring : DirectedRing n)
    (p : Fin n → ProjW c) (e : Fin n)
    (h : CleanWord ring p) :
    CleanWord ring (phiW ring p e) := by
  obtain ⟨root, hr⟩ := h
  exact ⟨root, cleanWordRootPhiStep hn ring root p e hr⟩

/-! ## Group 4 base: GeneratedControl at a completion -/

/-- All SI free at BANK width is a GeneratedControl state: empty
shape, and the acceptance scrub holds because every site is free.
Consumer: `bankWordCompletionGeneratedControl`. -/
theorem generatedControlOfAllFree {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (p : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hfree : ∀ i : Fin n, freeSI (p i).si = true) :
    GeneratedControl ring root p := by
  have hw := bankWordPassWidth hbank
  exact generatedControlOfEmpty ring root p
    ⟨hw.1, by omega⟩ hfree
    (fun _ _ i _ _ => hfree i)

/-- Group 4 base: at every reachable completed epoch state the
physical word is a GeneratedControl state.  Consumer:
`bankWordCompletionFutureInvariant`. -/
theorem bankWordCompletionGeneratedControl {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hcomp : BankWordRenewalCompleted z) :
    GeneratedControl ring root z.2.1 :=
  generatedControlOfAllFree ring root hbank z.2.1
    (bankWordEpochCompletedClean ring hn hbank root s hs z hz hcomp).2

/-! ## Group 4: the transport premise on the completion future -/

/-- The epoch states reached from a reachable completion by some
further scheduler word.  Consumer: `GeneratedControlTransport`. -/
def BankWordCompletionFuture {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (y : BankWordEpochState n) : Prop :=
  ∃ z : BankWordEpochState n,
    BankWordEpochReachable ring root s z ∧
      BankWordRenewalCompleted z ∧
      ∃ word : List (Fin n), bankWordEpochRun ring root z word = y

/-- The completion future is closed under one service.  Consumer:
`bankWordCompletionFutureInvariant`, `cleanWorkerCompletionQWord`. -/
theorem bankWordCompletionFutureNext {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (y : BankWordEpochState n)
    (hy : BankWordCompletionFuture ring root s y) (e : Fin n) :
    BankWordCompletionFuture ring root s
      (bankWordEpochNext ring root y e) := by
  obtain ⟨z, hz, hc, word, hw⟩ := hy
  refine ⟨z, hz, hc, word ++ [e], ?_⟩
  rw [bankWordEpochRunSnoc, hw]

/-- The GeneratedControl transport that QWord at a completion needs,
stated on the future of reachable completions (both fields of
`qwordOfGeneratedControl`: selected quietness and the forward step,
whose acceptClean clause is the successor's GeneratedControl field).
Consumer: `cleanWorkerCompletionQWord`; its proof is the open
WordGeneratedStep lane. -/
structure GeneratedControlTransport {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop where
  selected : ∀ root : Fin n,
    ∀ s : Fin n → ProjW (compileAdvice (ceilLogTwo n)),
      BankWordSerializerRootClass ring hbank root s →
      ∀ y : BankWordEpochState n,
        BankWordCompletionFuture ring root s y →
        GeneratedControl ring root y.2.1 →
        CleanWorkerWordValues ring root y.2.1 →
        ∀ e : Fin n,
          SelectedWordQuiet (y.2.1 e) (y.2.1 (ring.rightNeighbor e))
  step : ∀ root : Fin n,
    ∀ s : Fin n → ProjW (compileAdvice (ceilLogTwo n)),
      BankWordSerializerRootClass ring hbank root s →
      ∀ y : BankWordEpochState n,
        BankWordCompletionFuture ring root s y →
        GeneratedControl ring root y.2.1 →
        CleanWorkerWordValues ring root y.2.1 →
        ∀ e : Fin n,
          GeneratedControl ring root (phiW ring y.2.1 e)

/-- A Cartesian selected-row lemma (the `hselected` premise of
`qwordOfGeneratedControl`) together with the future step gives the
transport.  Consumer: the WordGeneratedStep lane's delivery. -/
theorem generatedControlTransportOfSelected {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hselected : ∀ root : Fin n,
      ∀ q : Fin n → ProjW (compileAdvice (ceilLogTwo n)),
        GeneratedControl ring root q →
        CleanWorkerWordValues ring root q →
        ∀ e : Fin n,
          SelectedWordQuiet (q e) (q (ring.rightNeighbor e)))
    (hstep : ∀ root : Fin n,
      ∀ s : Fin n → ProjW (compileAdvice (ceilLogTwo n)),
        BankWordSerializerRootClass ring hbank root s →
        ∀ y : BankWordEpochState n,
          BankWordCompletionFuture ring root s y →
          GeneratedControl ring root y.2.1 →
          CleanWorkerWordValues ring root y.2.1 →
          ∀ e : Fin n,
            GeneratedControl ring root (phiW ring y.2.1 e)) :
    GeneratedControlTransport ring hbank :=
  ⟨fun root _ _ y _ hg hc e => hselected root y.2.1 hg hc e, hstep⟩

/-- On the completion future every state is a GeneratedControl state
with the clean word values.  Consumer: `cleanWorkerCompletionQWord`. -/
theorem bankWordCompletionFutureInvariant {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (htrans : GeneratedControlTransport ring hbank)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
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
    (bankWordCompletionGeneratedControl ring hn hbank root s hs z hz hc)
    (bankWordEpochCompletedClean ring hn hbank root s hs z hz hc).1

/-- Group 4: QWord at every reachable completion, from the transport
premise and the clean completion.  Consumer:
`bankWordCompletionCleanWordTarget`. -/
theorem cleanWorkerCompletionQWord {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (htrans : GeneratedControlTransport ring hbank)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
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
    obtain ⟨hg, hcl⟩ := bankWordCompletionFutureInvariant
      ring hn hbank htrans root s hs y hy
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

/-- Every reachable completion is a clean-word entrance state.
Consumer: `bankWordCleanWordClockOfTransport`. -/
theorem bankWordCompletionCleanWordTarget {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (htrans : GeneratedControlTransport ring hbank)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hcomp : BankWordRenewalCompleted z) :
    BankWordCleanWordTarget ring z.2.1 := by
  have hclean :=
    bankWordEpochCompletedClean ring hn hbank root s hs z hz hcomp
  exact ⟨root,
    ⟨bankWordEpochFixedRoot ring hn hbank root s hs z hz,
      hclean.1,
      cleanWorkerCompletionQWord ring hn hbank htrans root s hs z hz hcomp⟩,
    hclean.2⟩

/-! ## The clean W clock -/

/-- The W clock to the clean-word entrance target, by the argument of
`bankWordProjectedClockOfCompletionBridge`, with no AcceptedWord
premise: only the transport premise.  Consumer: the
group 7 clean finish composition. -/
theorem bankWordCleanWordClockOfTransport {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (htrans : GeneratedControlTransport ring hbank) :
    BankWordCleanWordClock ring hbank := by
  intro z hz T
  obtain ⟨root, hs, _⟩ :=
    bankWordPreparedProjectedSerializerRoot ring hbank z hz
  have hcompletionCost := bankWordEpochCompletionFiveCostHolds
    ring hn hbank root (piW z.val.1) hs T
  have hmono := costNumerator_target_mono_on
    (bankWordEpochNext ring root)
    (BankWordEpochReachable ring root (piW z.val.1))
    BankWordRenewalCompleted
    (fun q : BankWordEpochState n =>
      BankWordCleanWordTarget ring q.2.1)
    (fun q hq e =>
      bankWordEpochReachableNext
        ring root (piW z.val.1) q hq e)
    (fun q hq hcomplete =>
      bankWordCompletionCleanWordTarget ring hn hbank htrans root
        (piW z.val.1) hs q hq hcomplete)
    T (bankWordEpochStart (piW z.val.1)) ⟨[], rfl⟩
  have hmap := costNumerator_map_eq
    (bankWordEpochNext ring root)
    (phiW ring)
    (fun q : BankWordEpochState n => q.2.1)
    (by intro q e; exact bankWordEpochPhysicalNext ring root q e)
    (BankWordCleanWordTarget ring)
    T (bankWordEpochStart (piW z.val.1))
  rw [hmap] at hmono
  exact Nat.le_trans hmono hcompletionCost

#print axioms cleanWordRootPhiStep
#print axioms cleanWordPhiStep
#print axioms generatedControlOfAllFree
#print axioms bankWordCompletionGeneratedControl
#print axioms bankWordCompletionFutureNext
#print axioms generatedControlTransportOfSelected
#print axioms bankWordCompletionFutureInvariant
#print axioms cleanWorkerCompletionQWord
#print axioms bankWordCompletionCleanWordTarget
#print axioms bankWordCleanWordClockOfTransport

end L3.RenewalReferenceClock
