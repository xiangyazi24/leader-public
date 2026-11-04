import Leader.L3.Bank.WordCleanWord

/-!
# R10 W: the GeneratedControl transport on the completion future

Part A (wave scrub).  On every state of the completion future, the root is
either not VALIDATING, or the state carries an EWord.WValidationHistory from
the last hard S1 with no hard acceptance since.  Hence at any enabled hard
acceptance every follower SI is free (EWord.validationReachableHardAcceptClean):
gcAcceptClean holds and the I0 responder is free at every future state.

Part B (reduction).  With Part A, GeneratedControlTransport follows from the
Cartesian row transport GeneratedControlRowTransport, whose premises supply
the fixed root, the OLD responder-free fact at a hard acceptance, and the
successor's acceptance scrub.
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

/-! ## Serializer facts at the root -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 12000 in
/-- Without a hard S1 the OLD initiator never becomes VALIDATING.
Consumer: `bankWordFutureWaveStep` (root as initiator). -/
theorem bankWordSerSourceNonvalidating {c : Compiled}
    (x y : ProjW c)
    (hx : x.ser.wphase ≠ .VALIDATING)
    (hno : (serW x y).hard.hardS1 = false) :
    (serW x y).x.wphase ≠ .VALIDATING := by
  cases hpx : (postW x y).eX.l <;>
    cases hpy : (postW x y).eY.l <;>
    cases hc : x.ser.cert <;>
    cases hp : x.ser.phase <;>
    cases ho : x.ser.out <;>
    cases hq : y.ser.phase <;>
    simp [serW, serializerStep, ProjW.lift, serTbStar,
      serChallengeWrite, serEnterB, serEnterF, serCanonicalC,
      hpx, hpy, hc, hp, ho, hq, hx] at hno ⊢ <;>
    (repeat' split) <;> simp_all

/-- A post-E leader responder is never made VALIDATING (only ROOT_IN
or S7 rows apply).  Consumer: `bankWordFutureWaveStep` (root as
responder). -/
theorem bankWordSerLeaderResponderNonvalidating {c : Compiled}
    (x y : ProjW c)
    (hy : y.ser.wphase ≠ .VALIDATING)
    (hpy : (postW x y).eY.l = true) :
    (serW x y).y.wphase ≠ .VALIDATING := by
  cases hpx : (postW x y).eX.l <;>
    cases hc : y.ser.cert <;>
    cases hp : x.ser.phase <;>
    simp [serW, serializerStep, ProjW.lift, hpx, hpy, hc, hp, hy] <;>
    (repeat' split) <;> simp_all

/-- A hard acceptance on a ROOT_OUT pair leaves the initiator not
VALIDATING (the S6 row writes CURRENT).  Consumer:
`bankWordFutureWaveStep`. -/
theorem bankWordSerHardAcceptSourceCurrent {c : Compiled}
    (x y : ProjW c)
    (ha : (serW x y).hard.hardAccept = true)
    (hpy : (postW x y).eY.l = false) :
    (serW x y).x.wphase ≠ .VALIDATING := by
  cases hpx : (postW x y).eX.l <;>
    cases hc : x.ser.cert <;>
    cases hp : x.ser.phase <;>
    cases ho : x.ser.out <;>
    cases hq : y.ser.phase <;>
    simp [serW, serializerStep, ProjW.lift, hpx, hpy, hc, hp, ho, hq]
      at ha ⊢

/-! ## Geometry helpers -/

theorem bankWordPhiSource {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (p : Fin n → ProjW c) (e : Fin n) :
    (phiW ring p e) e = (pairW (p e) (p (ring.rightNeighbor e))).1 := by
  simp only [phiW, projectedEdge, if_pos rfl]

theorem bankWordPhiTarget {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    (phiW ring p e) (ring.rightNeighbor e) =
      (pairW (p e) (p (ring.rightNeighbor e))).2 := by
  simp only [phiW, projectedEdge, if_neg hne]
  rfl

/-- A post-E leader initiator is the fixed root.  Consumer: Part A. -/
theorem bankWordPostLeaderSourceRoot {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (e : Fin n)
    (hfix : WFixedRoot ring root p)
    (hl : (postW (p e) (p (ring.rightNeighbor e))).eX.l = true) :
    e = root := by
  apply hfix.2.1 e
  have h := L3.Closure.literalESourceLeader (p e).native
    (p (ring.rightNeighbor e)).native
  change (certLiteralEPair (p e).native
    (p (ring.rightNeighbor e)).native).1.l = true at hl
  rw [h] at hl
  exact hl

/-- The post-E responder flag is the successor's native leader bit.
Consumer: Part A. -/
theorem bankWordPostResponderLeader {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (p : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    (postW (p e) (p (ring.rightNeighbor e))).eY.l =
      ((phiW ring p e) (ring.rightNeighbor e)).native.l := by
  rw [bankWordPhiTarget ring p e hne]
  rfl

/-- hardS1 and hardAccept both need a post-E leader initiator.
Consumer: Part A. -/
theorem bankWordHardSOnePostLeader {c : Compiled} (x y : ProjW c)
    (h : (serW x y).hard.hardS1 = true) :
    (postW x y).eX.l = true ∧ x.ser.cert = .REQUESTED ∧
      x.siLease.val = 0 := by
  simp [serW, serializerStep, ProjW.lift] at h
  exact ⟨h.1.1, h.1.2, by rw [h.2]; rfl⟩

theorem bankWordHardAcceptPostLeader {c : Compiled} (x y : ProjW c)
    (h : (serW x y).hard.hardAccept = true) :
    (postW x y).eX.l = true ∧ x.ser.wphase = .VALIDATING := by
  simp [serW, serializerStep, ProjW.lift] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.2⟩

/-! ## Part A: the wave scrub on the completion future -/

/-- Root not VALIDATING, or a validation history from the last hard S1.
Consumer: `bankWordFutureAcceptClean`. -/
def BankWordFutureWave {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) : Prop :=
  (p root).ser.wphase ≠ .VALIDATING ∨
    ∃ g : L3.EWord.ValidationGhost,
      L3.EWord.WValidationHistory ring root p g

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 12000 in
/-- One phiW step keeps the wave scrub.  Consumer:
`bankWordCompletionFutureWave`. -/
theorem bankWordFutureWaveStep {n : Nat} {c : Compiled}
    (hn : 3 ≤ n) (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (e : Fin n)
    (hfix : WFixedRoot ring root p)
    (hfix' : WFixedRoot ring root (phiW ring p e))
    (h : BankWordFutureWave ring root p) :
    BankWordFutureWave ring root (phiW ring p e) := by
  have hne : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) e
  -- the post-E responder of a root edge is not a leader
  have hrespRoot : e = root →
      (postW (p e) (p (ring.rightNeighbor e))).eY.l = false := by
    intro he
    rw [bankWordPostResponderLeader ring p e hne]
    cases hl : ((phiW ring p e) (ring.rightNeighbor e)).native.l with
    | false => rfl
    | true =>
        have := hfix'.2.1 _ hl
        exact absurd (this.trans he.symm) hne
  rcases h with hroot | ⟨g, hg⟩
  · by_cases hs1 : (serW (p e) (p (ring.rightNeighbor e))).hard.hardS1 = true
    · obtain ⟨hx, hc, hz⟩ := bankWordHardSOnePostLeader _ _ hs1
      have he : e = root := bankWordPostLeaderSourceRoot ring root p e hfix hx
      subst he
      exact Or.inr ⟨_, L3.EWord.WValidationHistory.start p hn hx
        (hrespRoot rfl) hc hz hfix'⟩
    · have hs1' : (serW (p e) (p (ring.rightNeighbor e))).hard.hardS1 = false := by
        cases hh : (serW (p e) (p (ring.rightNeighbor e))).hard.hardS1 with
        | false => rfl
        | true => exact absurd hh hs1
      left
      by_cases hre : root = e
      · subst hre
        rw [bankWordPhiSource]
        exact bankWordSerSourceNonvalidating _ _ hroot hs1'
      · by_cases hrj : root = ring.rightNeighbor e
        · subst hrj
          rw [bankWordPhiTarget ring p e hne]
          apply bankWordSerLeaderResponderNonvalidating _ _ hroot
          rw [bankWordPostResponderLeader ring p e hne]
          exact hfix'.1
        · rw [cwPhiWFrame ring p e root hre hrj]
          exact hroot
  · by_cases ha : (serW (p e) (p (ring.rightNeighbor e))).hard.hardAccept = true
    · have hx := (bankWordHardAcceptPostLeader _ _ ha).1
      have he : e = root := bankWordPostLeaderSourceRoot ring root p e hfix hx
      subst he
      left
      rw [bankWordPhiSource]
      exact bankWordSerHardAcceptSourceCurrent _ _ ha (hrespRoot rfl)
    · have ha' : (serW (p e) (p (ring.rightNeighbor e))).hard.hardAccept = false := by
        cases hh : (serW (p e) (p (ring.rightNeighbor e))).hard.hardAccept with
        | false => rfl
        | true => exact absurd hh ha
      exact Or.inr ⟨_, L3.EWord.WValidationHistory.next hg e ha' hfix'⟩

/-- Under the wave scrub, an enabled hard acceptance finds every SI
other than the root free: gcAcceptClean, and the I0 responder is free.
Consumer: `generatedControlTransportOfRows`. -/
theorem bankWordFutureAcceptClean {n : Nat} {c : Compiled}
    (hn : 3 ≤ n) (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c)
    (hfix : WFixedRoot ring root p)
    (h : BankWordFutureWave ring root p) :
    ∀ e : Fin n,
      (serW (p e) (p (ring.rightNeighbor e))).hard.hardAccept = true →
      ∀ i : Fin n, i ≠ root → freeSI (p i).si = true := by
  intro e ha i hi
  obtain ⟨hx, hval⟩ := bankWordHardAcceptPostLeader _ _ ha
  have he : e = root := bankWordPostLeaderSourceRoot ring root p e hfix hx
  subst he
  rcases h with hroot | ⟨g, hg⟩
  · exact absurd (by simpa [ProjW.lift] using hval) hroot
  · have hclean := L3.EWord.validationReachableHardAcceptClean ring e hg ha
    have hpos : 0 < PPL.cyclicOffset ring e i := by
      rcases Nat.eq_zero_or_pos (PPL.cyclicOffset ring e i) with h0 | h0
      · exfalso
        apply hi
        have := L3.EWord.validationOffsetRepresentative ring e i
        rw [h0, L3.EWord.siteZero] at this
        exact this.symm
      · exact h0
    have := hclean ⟨PPL.cyclicOffset ring e i,
      L3.EWord.validationOffsetBound ring e i⟩ hpos
    rw [L3.EWord.validationOffsetRepresentative] at this
    exact this

/-- gcAcceptClean and the responder-free fact from the wave scrub.
Consumer: `generatedControlTransportOfRows`. -/
theorem bankWordFutureAcceptPair {n : Nat} {c : Compiled}
    (hn : 3 ≤ n) (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c)
    (hfix : WFixedRoot ring root p)
    (h : BankWordFutureWave ring root p) :
    gcAcceptClean ring p ∧
      ∀ e : Fin n,
        (serW (p e) (p (ring.rightNeighbor e))).hard.hardAccept = true →
        freeSI (p (ring.rightNeighbor e)).si = true := by
  have hall := bankWordFutureAcceptClean hn ring root p hfix h
  refine ⟨fun e ha i _ _ => ?_, fun e ha => ?_⟩
  · by_cases hi : i = root
    · obtain ⟨hx, _⟩ := bankWordHardAcceptPostLeader _ _ ha
      have he : e = root := bankWordPostLeaderSourceRoot ring root p e hfix hx
      subst hi
      exact absurd he.symm ‹i ≠ e›
    · exact hall e ha i hi
  · obtain ⟨hx, _⟩ := bankWordHardAcceptPostLeader _ _ ha
    have he : e = root := bankWordPostLeaderSourceRoot ring root p e hfix hx
    apply hall e ha
    rw [he]
    exact clockNeighborDifferent ring (by omega : 2 ≤ n) root

/-! ## Part B: the completion future and the reduction to row transports -/

/-- The retired pass state at every reachable completion (same proof as
`bankWordEpochCompletedClean`, keeping the retirement record).
Consumer: `bankWordCompletionFutureWave` (root not VALIDATING). -/
theorem bankWordEpochCompletedRetired {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
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
        bankWordEpochLiveFromSeedReachable ring hn hbank root s hs y hy
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
      rcases bankWordPassValuesRun ring hn hbank root s hs
          (word0 ++ [e]) seed.1.1 seed.1.2.1
          (bankWordPassShapeAtFreshSeed ring hn hbank root s hs seed)
          (bankWordPassValuesBase ring hn hbank root s hs seed) hnh' with
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

/-- Every completion-future state is reachable.  Consumer: the fixed
root on the completion future. -/
theorem bankWordCompletionFutureReachable {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (y : BankWordEpochState n)
    (hy : BankWordCompletionFuture ring root s y) :
    BankWordEpochReachable ring root s y := by
  obtain ⟨z, ⟨w0, hw0⟩, _, word, hw⟩ := hy
  refine ⟨w0 ++ word, ?_⟩
  rw [bankWordEpochRunAppend, hw0, hw]

/-- The wave scrub holds on the whole completion future.  Consumer:
`generatedControlTransportOfRows`. -/
theorem bankWordCompletionFutureWave {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
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
          (bankWordEpochFixedRoot ring hn hbank root s hs y0 hr)
          (bankWordEpochFixedRootNext ring hn hbank root s hs y0 hr e) h
  apply key word z ⟨z, hz, hc, [], rfl⟩
  exact Or.inl ((bankWordEpochCompletedRetired ring hn hbank root s hs
    z hz hc).1 root)

/-- The Cartesian GeneratedControl row transport, with the premises the
completion future supplies: fixed root, the OLD responder free at a hard
acceptance, and the successor's acceptance scrub.  Selected quietness is
the OLD-state row fact.  Consumer: `generatedControlTransportOfRows`;
its proof is the per-row shape lemmas. -/
def GeneratedControlRowTransport {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ root : Fin n,
    ∀ q : Fin n → ProjW (compileAdvice (ceilLogTwo n)),
      WFixedRoot ring root q →
      GeneratedControl ring root q →
      CleanWorkerWordValues ring root q →
      ∀ e : Fin n,
        ((serW (q e) (q (ring.rightNeighbor e))).hard.hardAccept = true →
          freeSI (q (ring.rightNeighbor e)).si = true) →
        gcAcceptClean ring (phiW ring q e) →
        GeneratedControl ring root (phiW ring q e) ∧
          SelectedWordQuiet (q e) (q (ring.rightNeighbor e))

/-- GeneratedControlTransport from the row transport and the wave scrub.
Consumer: `bankWordCleanWordClockOfRows`. -/
theorem generatedControlTransportOfRows {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrows : GeneratedControlRowTransport ring) :
    GeneratedControlTransport ring hbank := by
  have core : ∀ root : Fin n,
      ∀ s : Fin n → ProjW (compileAdvice (ceilLogTwo n)),
        BankWordSerializerRootClass ring hbank root s →
        ∀ y : BankWordEpochState n,
          BankWordCompletionFuture ring root s y →
          GeneratedControl ring root y.2.1 →
          CleanWorkerWordValues ring root y.2.1 →
          ∀ e : Fin n,
            GeneratedControl ring root (phiW ring y.2.1 e) ∧
              SelectedWordQuiet (y.2.1 e) (y.2.1 (ring.rightNeighbor e)) := by
    intro root s hs y hy hg hcl e
    have hr := bankWordCompletionFutureReachable ring root s y hy
    have hfix := bankWordEpochFixedRoot ring hn hbank root s hs y hr
    have hwave := bankWordCompletionFutureWave ring hn hbank root s hs y hy
    have hy' := bankWordCompletionFutureNext ring root s y hy e
    have hfix' := bankWordEpochFixedRoot ring hn hbank root s hs _
      (bankWordCompletionFutureReachable ring root s _ hy')
    have hwave' := bankWordCompletionFutureWave ring hn hbank root s hs _ hy'
    exact hrows root y.2.1 hfix hg hcl e
      ((bankWordFutureAcceptPair (by omega) ring root y.2.1 hfix hwave).2 e)
      (bankWordFutureAcceptPair (by omega) ring root _ hfix' hwave').1
  exact ⟨fun root s hs y hy hg hcl e => (core root s hs y hy hg hcl e).2,
    fun root s hs y hy hg hcl e => (core root s hs y hy hg hcl e).1⟩

/-- The clean W clock with the Cartesian row transport as its only
premise.  Consumer: the group 7 clean finish. -/
theorem bankWordCleanWordClockOfRows {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrows : GeneratedControlRowTransport ring) :
    BankWordCleanWordClock ring hbank :=
  bankWordCleanWordClockOfTransport ring hn hbank
    (generatedControlTransportOfRows ring hn hbank hrows)

/-! ## Part C: the Cartesian row transport -/

/-- Visible-word congruence of the current bit.  Consumer: shape
congruences below. -/
theorem bankWordCwBitEq {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p' p : Fin n → ProjW c)
    (hv : ∀ i : Fin n, wordVisible p' i = wordVisible p i) (k : Nat) :
    cwBit ring root p' k = cwBit ring root p k := by
  simp only [cwBit]
  exact congrArg Prod.fst (hv _)

theorem bankWordCwSumOrEq {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p' p : Fin n → ProjW c)
    (hv : ∀ i : Fin n, wordVisible p' i = wordVisible p i) (m j : Nat) :
    cwSumOr ring root p' m j = cwSumOr ring root p m j := by
  have hb := bankWordCwBitEq ring root p' p hv
  simp only [cwSumOr, cwSourceBit, hb]

theorem bankWordCwSumParityEq {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p' p : Fin n → ProjW c)
    (hv : ∀ i : Fin n, wordVisible p' i = wordVisible p i) (m j : Nat) :
    cwSumParity ring root p' m j = cwSumParity ring root p m j := by
  have hb := bankWordCwBitEq ring root p' p hv
  simp only [cwSumParity, cwSourceBit, hb]

theorem bankWordCwSumTrailingEq {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p' p : Fin n → ProjW c)
    (hv : ∀ i : Fin n, wordVisible p' i = wordVisible p i) (m j : Nat) :
    cwSumTrailing ring root p' m j = cwSumTrailing ring root p m j := by
  have hb := bankWordCwBitEq ring root p' p hv
  simp only [cwSumTrailing, cwSourceBit, hb]

theorem bankWordCwPrefixOrEq {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p' p : Fin n → ProjW c)
    (hv : ∀ i : Fin n, wordVisible p' i = wordVisible p i) (j : Nat) :
    cwPrefixOr ring root p' j = cwPrefixOr ring root p j := by
  have hb := bankWordCwBitEq ring root p' p hv
  simp only [cwPrefixOr, hb]

theorem bankWordCwPrefixAndEq {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p' p : Fin n → ProjW c)
    (hv : ∀ i : Fin n, wordVisible p' i = wordVisible p i) (j : Nat) :
    cwPrefixAnd ring root p' j = cwPrefixAnd ring root p j := by
  have hb := bankWordCwBitEq ring root p' p hv
  simp only [cwPrefixAnd, hb]

/-- The SUM cursor predicate depends only on the cursor SI and the
visible word.  Consumer: shape transports. -/
theorem bankWordSumCursorCongr {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p' p : Fin n → ProjW c) (m cur : Fin n)
    (hv : ∀ i : Fin n, wordVisible p' i = wordVisible p i)
    (hs : (p' cur).si = (p cur).si)
    (h : gcSumCursorAt ring root p m cur) :
    gcSumCursorAt ring root p' m cur := by
  unfold gcSumCursorAt at h ⊢
  rw [hs, bankWordCwSumOrEq ring root p' p hv,
    bankWordCwSumParityEq ring root p' p hv,
    bankWordCwSumTrailingEq ring root p' p hv]
  exact h

theorem bankWordBackCursorCongr {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p' p : Fin n → ProjW c) (m cur : Fin n)
    (hs : (p' cur).si = (p cur).si)
    (h : gcBackCursorAt ring root p m cur) :
    gcBackCursorAt ring root p' m cur := by
  unfold gcBackCursorAt at h ⊢
  rw [hs]
  exact h

theorem bankWordBusyTargetCongr {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p' p : Fin n → ProjW c) (m : Fin n)
    (hs : (p' m).si = (p m).si)
    (h : gcBusyTarget ring root p m) :
    gcBusyTarget ring root p' m := by
  unfold gcBusyTarget at h ⊢
  rw [hs]
  exact h

/-- Erasing any set of SI records to offSI, with the visible word
fixed, keeps GeneratedControl (each partial erasure of a worker is
one of the eight shapes).  Consumer: the I1 row. -/
theorem bankWordGeneratedControlErase {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (q q' : Fin n → ProjW c)
    (hgen : GeneratedControl ring root q)
    (hv : ∀ i : Fin n, wordVisible q' i = wordVisible q i)
    (hsi : ∀ i : Fin n, (q' i).si = (q i).si ∨ (q' i).si = offSI c.t)
    (hclean : gcAcceptClean ring q') :
    GeneratedControl ring root q' := by
  have hfree : ∀ i : Fin n, freeSI (q i).si = true →
      freeSI (q' i).si = true := by
    intro i hi
    rcases hsi i with h | h
    · rw [h]; exact hi
    · rw [h]; rfl
  have hoff : ∀ i : Fin n, (q' i).si = offSI c.t →
      freeSI (q' i).si = true := by
    intro i h; rw [h]; rfl
  refine {
    width := hgen.width
    rootNotBusy := ?_
    uniquePrefix := ?_
    shape := ?_
    acceptClean := hclean }
  · intro hbad
    rcases hsi root with h | h
    · rw [h] at hbad; exact hgen.rootNotBusy hbad
    · rw [h] at hbad; cases hbad.1
  · intro i j hi hj
    have hi' : (q i).si.kind = .PREFIX := by
      rcases hsi i with h | h
      · rw [h] at hi; exact hi
      · rw [h] at hi; cases hi
    have hj' : (q j).si.kind = .PREFIX := by
      rcases hsi j with h | h
      · rw [h] at hj; exact hj
      · rw [h] at hj; cases hj
    exact hgen.uniquePrefix i j hi' hj'
  · rcases hgen.shape with h | h | h | h | h | h | h | h
    · exact Or.inl (fun i => hfree i (h i))
    · obtain ⟨st, hk, hb, hc, hj, hz, ha, hother⟩ := h
      rcases hsi st with hs | hs
      · refine Or.inr (Or.inl ⟨st, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
        · rw [hs]; exact hk
        · rw [hs]; exact hb
        · rw [hs]; exact hc
        · rw [hs]; exact hj
        · rw [hs, bankWordCwPrefixOrEq ring root q' q hv]; exact hz
        · rw [hs, bankWordCwPrefixAndEq ring root q' q hv]; exact ha
        · intro i hi; exact hfree i (hother i hi)
      · refine Or.inl (fun i => ?_)
        by_cases hi : i = st
        · subst hi; exact hoff _ hs
        · exact hfree i (hother i hi)
    · obtain ⟨m, cur, hbusy, hcursor, hne, hout⟩ := h
      by_cases hcm : cur = m
      · subst hcm
        rcases hsi cur with hs | hs
        · exact Or.inr (Or.inr (Or.inl ⟨cur, cur,
            bankWordBusyTargetCongr ring root q' q cur hs hbusy,
            bankWordBackCursorCongr ring root q' q cur cur hs hcursor,
            fun h => absurd rfl h,
            fun i h1 h2 => hfree i (hout i h1 h2)⟩))
        · refine Or.inl (fun i => ?_)
          by_cases hi : i = cur
          · subst hi; exact hoff _ hs
          · exact hfree i (hout i hi hi)
      · have hne' := hne hcm
        rcases hsi cur with hs | hs <;> rcases hsi m with ht | ht
        · refine Or.inr (Or.inr (Or.inl ⟨m, cur,
            bankWordBusyTargetCongr ring root q' q m ht hbusy,
            bankWordBackCursorCongr ring root q' q m cur hs hcursor,
            fun _ => ⟨by rw [hs]; exact hne'.1, by rw [ht]; exact hne'.2⟩,
            fun i h1 h2 => hfree i (hout i h1 h2)⟩))
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨m, cur, hcm, hoff _ ht, by rw [hs]; exact hne'.1,
              bankWordBackCursorCongr ring root q' q m cur hs hcursor,
              fun i h1 h2 => hfree i (hout i h1 h2)⟩))))))
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨m, bankWordBusyTargetCongr ring root q' q m ht hbusy,
              by rw [ht]; exact hne'.2, fun i hi => ?_⟩)))))
          by_cases hic : i = cur
          · subst hic; exact hoff _ hs
          · exact hfree i (hout i hic hi)
        · refine Or.inl (fun i => ?_)
          by_cases hic : i = cur
          · subst hic; exact hoff _ hs
          · by_cases him : i = m
            · subst him; exact hoff _ ht
            · exact hfree i (hout i hic him)
    · obtain ⟨m, cur, hbusy, htcur, hcursor, hout⟩ := h
      have hcm : cur ≠ m := by
        intro h
        have h1 := hcursor.2.2.1
        have h2 := hbusy.2.2.1
        rw [h] at h1
        rw [h1] at h2
        cases h2
      rcases hsi cur with hs | hs <;> rcases hsi m with ht | ht
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨m, cur,
          bankWordBusyTargetCongr ring root q' q m ht hbusy,
          by rw [ht]; exact htcur,
          bankWordSumCursorCongr ring root q' q m cur hv hs hcursor,
          fun i h1 h2 => hfree i (hout i h1 h2)⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨m, cur, hcm, hoff _ ht,
            bankWordSumCursorCongr ring root q' q m cur hv hs hcursor,
            fun i h1 h2 => hfree i (hout i h1 h2)⟩))))))
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨m, bankWordBusyTargetCongr ring root q' q m ht hbusy,
            by rw [ht]; exact htcur, fun i hi => ?_⟩)))))
        by_cases hic : i = cur
        · subst hic; exact hoff _ hs
        · exact hfree i (hout i hic hi)
      · refine Or.inl (fun i => ?_)
        by_cases hic : i = cur
        · subst hic; exact hoff _ hs
        · by_cases him : i = m
          · subst him; exact hoff _ ht
          · exact hfree i (hout i hic him)
    · obtain ⟨m, hm, hoffm, hk, hb, hc, hother⟩ := h
      rcases hsi m with ht | ht
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨m, hm, hoffm, ?_, ?_, ?_, fun i hi => hfree i (hother i hi)⟩))))
        · rw [ht]; exact hk
        · rw [ht]; exact hb
        · rw [ht]; exact hc
      · refine Or.inl (fun i => ?_)
        by_cases hi : i = m
        · subst hi; exact hoff _ ht
        · exact hfree i (hother i hi)
    · obtain ⟨m, hbusy, hc, hother⟩ := h
      rcases hsi m with ht | ht
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨m, bankWordBusyTargetCongr ring root q' q m ht hbusy,
            by rw [ht]; exact hc, fun i hi => hfree i (hother i hi)⟩)))))
      · refine Or.inl (fun i => ?_)
        by_cases hi : i = m
        · subst hi; exact hoff _ ht
        · exact hfree i (hother i hi)
    · obtain ⟨m, cur, hcm, hft, hk, hcursor, hout⟩ := h
      rcases hsi cur with hs | hs
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨m, cur, hcm, hfree m hft, by rw [hs]; exact hk,
            bankWordBackCursorCongr ring root q' q m cur hs hcursor,
            fun i h1 h2 => hfree i (hout i h1 h2)⟩))))))
      · refine Or.inl (fun i => ?_)
        by_cases hic : i = cur
        · subst hic; exact hoff _ hs
        · by_cases him : i = m
          · subst him; exact hfree _ hft
          · exact hfree i (hout i hic him)
    · obtain ⟨m, cur, hcm, hft, hcursor, hout⟩ := h
      rcases hsi cur with hs | hs
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨m, cur, hcm, hfree m hft,
            bankWordSumCursorCongr ring root q' q m cur hv hs hcursor,
            fun i h1 h2 => hfree i (hout i h1 h2)⟩))))))
      · refine Or.inl (fun i => ?_)
        by_cases hic : i = cur
        · subst hic; exact hoff _ hs
        · by_cases him : i = m
          · subst him; exact hfree _ hft
          · exact hfree i (hout i hic him)

/-! ### Literal SI rows with no hard flag -/

/-- With no hard flag, a source that is not PREFIX/SUM/ready-ROOT and a
responder that is not a BACK cursor next to a free source give the
identity frame, including the four visible assignments.  Consumer:
every non-nominated edge of the shape transports. -/
theorem bankWordSiFrameRow {c : Compiled} (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hP : x.si.kind ≠ .PREFIX) (hS : x.si.cur ≠ .SUM)
    (hA : x.si.kind = .ROOT → x.si.busy = true ∨ x.si.cur ≠ .NONE)
    (hB : y.si.cur = .BACK → freeSI x.si = false) :
    (workerW x y).x = x.si ∧ (workerW x y).y = y.si ∧
      SelectedWordQuiet x y := by
  cases hk : x.si.kind <;> cases hb : x.si.busy <;>
    cases hc : x.si.cur <;> cases hyc : y.si.cur <;>
    simp_all [workerW, siStep, ProjW.lift, freeSI, SelectedWordQuiet]

/-- The SUM cursor stuck at its last index with no busy ROOT responder
frames.  Consumer: the orphan SUM shape. -/
theorem bankWordSiStuckSumRow {c : Compiled} (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hk : x.si.kind = .OFF) (hc : x.si.cur = .SUM)
    (hj : x.si.j.val + 1 = c.t)
    (hy : ¬ (y.si.kind = .ROOT ∧ y.si.busy = true)) :
    (workerW x y).x = x.si ∧ (workerW x y).y = y.si ∧
      SelectedWordQuiet x y := by
  have hj' : ¬ x.si.j.val + 1 < c.t := by omega
  cases hyk : y.si.kind <;> cases hyb : y.si.busy <;>
    cases hyc : y.si.cur <;>
    simp_all [workerW, siStep, ProjW.lift, freeSI, SelectedWordQuiet]

/-- A frame transport: both endpoint SI unchanged and quiet.
Consumer: the shape transports. -/
theorem bankWordFrameTransport {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (q : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hgen : GeneratedControl ring root q)
    (h : (workerW (q e) (q (ring.rightNeighbor e))).x = (q e).si ∧
      (workerW (q e) (q (ring.rightNeighbor e))).y =
        (q (ring.rightNeighbor e)).si ∧
      SelectedWordQuiet (q e) (q (ring.rightNeighbor e)))
    (hnext : gcAcceptClean ring (phiW ring q e)) :
    GeneratedControl ring root (phiW ring q e) ∧
      SelectedWordQuiet (q e) (q (ring.rightNeighbor e)) :=
  ⟨generatedControlFrameFromOwnerFields ring root q e hne hgen
    h.1 h.2.1 h.2.2 hnext, h.2.2⟩

/-! ### Offsets -/

theorem bankWordSiteOffset {n : Nat} (ring : DirectedRing n)
    (root i : Fin n) :
    L3.EWord.site ring root (PPL.cyclicOffset ring root i) = i :=
  L3.EWord.validationOffsetRepresentative ring root i

theorem bankWordLeftOfSite {n : Nat} (ring : DirectedRing n)
    (root e : Fin n) (k : Nat) (hk : 1 ≤ k)
    (h : ring.rightNeighbor e = L3.EWord.site ring root k) :
    e = L3.EWord.site ring root (k - 1) := by
  apply bankWordPassRightNeighborInjective ring
  rw [h, L3.EWord.siteSuccessor]
  congr 1
  omega

theorem bankWordOffsetOfRightRoot {n : Nat} (ring : DirectedRing n)
    (root e : Fin n) (h : ring.rightNeighbor e = root) :
    PPL.cyclicOffset ring root e = n - 1 := by
  have hb := L3.EWord.validationOffsetBound ring root e
  have he := bankWordSiteOffset ring root e
  have hs : L3.EWord.site ring root (PPL.cyclicOffset ring root e + 1) =
      L3.EWord.site ring root 0 := by
    rw [← L3.EWord.siteSuccessor, he, h, L3.EWord.siteZero]
  by_cases hlt : PPL.cyclicOffset ring root e + 1 < n
  · have := L3.EWord.validationSiteInjective ring root _ 0 hlt
      (by have := ring.hn; omega) hs
    omega
  · omega

theorem bankWordOffsetRight {n : Nat} (ring : DirectedRing n)
    (root e : Fin n) (h : ring.rightNeighbor e ≠ root) :
    PPL.cyclicOffset ring root (ring.rightNeighbor e) =
      PPL.cyclicOffset ring root e + 1 := by
  have hb := L3.EWord.validationOffsetBound ring root e
  have he := bankWordSiteOffset ring root e
  have hr : ring.rightNeighbor e =
      L3.EWord.site ring root (PPL.cyclicOffset ring root e + 1) := by
    have := L3.EWord.siteSuccessor ring root (PPL.cyclicOffset ring root e)
    rw [he] at this
    exact this
  by_cases hlt : PPL.cyclicOffset ring root e + 1 < n
  · rw [hr]; exact L3.EWord.validationSiteOffset ring root _ hlt
  · exfalso
    apply h
    have heq : PPL.cyclicOffset ring root e + 1 = n := by omega
    rw [hr, heq]
    apply Fin.ext
    simp [L3.EWord.site, PPL.shiftRight, Nat.mod_eq_of_lt root.isLt]

theorem bankWordSiteNeRoot {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (k : Nat) (hk : k < n) (hpos : 0 < k) :
    L3.EWord.site ring root k ≠ root :=
  L3.EWord.validationPositiveSiteNotRoot ring root k hk hpos

/-! ### Hard rows -/

/-- I0: a hard acceptance at the root launches the clean PREFIX.
Consumer: `bankWordRowTransport`. -/
theorem bankWordRowIzero {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (q : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hfix : WFixedRoot ring root q)
    (hgen : GeneratedControl ring root q)
    (hword : CleanWorkerWordValues ring root q)
    (ha : (serW (q e) (q (ring.rightNeighbor e))).hard.hardAccept = true)
    (hresp : freeSI (q (ring.rightNeighbor e)).si = true)
    (hnext : gcAcceptClean ring (phiW ring q e)) :
    GeneratedControl ring root (phiW ring q e) ∧
      SelectedWordQuiet (q e) (q (ring.rightNeighbor e)) := by
  have he : e = root := bankWordPostLeaderSourceRoot ring root q e hfix
    (bankWordHardAcceptPostLeader _ _ ha).1
  have hvis := (generatedControlIzeroWordStep ring root q e hne hword ha).1
  refine ⟨?_, (selectedWordQuiet_iff_edge ring q e hne).mpr hvis⟩
  subst he
  have hzero : PPL.cyclicOffset ring e e = 0 := by
    simp [PPL.cyclicOffset]
  exact generatedControlIzeroPostState ring e q hne hzero hgen ha hresp hnext

/-- I1: hard erasure keeps GeneratedControl.  Consumer:
`bankWordRowTransport`. -/
theorem bankWordRowIone {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (q : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hgen : GeneratedControl ring root q)
    (hword : CleanWorkerWordValues ring root q)
    (ha : (serW (q e) (q (ring.rightNeighbor e))).hard.hardAccept = false)
    (herase : ((serW (q e) (q (ring.rightNeighbor e))).hard.hardLeft ||
      (serW (q e) (q (ring.rightNeighbor e))).hard.hardRight) = true)
    (hnext : gcAcceptClean ring (phiW ring q e)) :
    GeneratedControl ring root (phiW ring q e) ∧
      SelectedWordQuiet (q e) (q (ring.rightNeighbor e)) := by
  have hvis := (generatedControlIoneWordStep ring root q e hne hword ha herase).1
  have hown := generatedControlIoneOwnerFields (q e) (q (ring.rightNeighbor e))
    ha herase
  refine ⟨?_, (selectedWordQuiet_iff_edge ring q e hne).mpr hvis⟩
  apply bankWordGeneratedControlErase ring root q _ hgen hvis _ hnext
  intro i
  by_cases hie : i = e
  · subst hie
    rw [bankWordPhiSource]
    change (workerW (q i) (q (ring.rightNeighbor i))).x = _ ∨
      (workerW (q i) (q (ring.rightNeighbor i))).x = _
    rw [hown.1]
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  · by_cases hij : i = ring.rightNeighbor e
    · subst hij
      rw [bankWordPhiTarget ring q e hne]
      change (workerW (q e) (q (ring.rightNeighbor e))).y = _ ∨
        (workerW (q e) (q (ring.rightNeighbor e))).y = _
      rw [hown.2]
      split
      · exact Or.inr rfl
      · exact Or.inl rfl
    · exact Or.inl (generatedControlRemoteSiFrame ring q e i hie hij)

/-! ### Quiet active rows (no hard flag) -/

theorem bankWordRowQuietBackMove {c : Compiled} (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hf : freeSI x.si = true)
    (hcur : y.si.cur = .BACK) (hj : 1 < y.si.j.val)
    (hk : y.si.kind ≠ .PREFIX) :
    SelectedWordQuiet x y := by
  have hfx := bankWordPassFreeFields x.si hf
  simp [workerW, siStep, ProjW.lift, freeSI, SelectedWordQuiet,
    hfa, hfl, hfr, hfx.1, hfx.2, hcur, hj, hk]

theorem bankWordRowQuietBackInit {c : Compiled} (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hf : freeSI x.si = true)
    (hcur : y.si.cur = .BACK) (hj : y.si.j.val = 1)
    (hk : y.si.kind ≠ .PREFIX) :
    SelectedWordQuiet x y := by
  have hfx := bankWordPassFreeFields x.si hf
  simp [workerW, siStep, ProjW.lift, freeSI, SelectedWordQuiet,
    hfa, hfl, hfr, hfx.1, hfx.2, hcur, hj, hk]

theorem bankWordRowQuietSumMove {c : Compiled} (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hk : x.si.kind = .OFF) (hc : x.si.cur = .SUM)
    (hj : x.si.j.val + 1 < c.t) (hf : freeSI y.si = true) :
    SelectedWordQuiet x y := by
  have hfy := bankWordPassFreeFields y.si hf
  simp [workerW, siStep, ProjW.lift, freeSI, SelectedWordQuiet,
    hfa, hfl, hfr, hk, hc, hj, hfy.1, hfy.2]

theorem bankWordRowQuietAdvance {c : Compiled} (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hk : x.si.kind = .ROOT) (hb : x.si.busy = false)
    (hc : x.si.cur = .NONE)
    (hy : (postW x y).eY.l = false) (hf : freeSI y.si = true) :
    SelectedWordQuiet x y := by
  have hfy := bankWordPassFreeFields y.si hf
  simp [workerW, siStep, ProjW.lift, freeSI, SelectedWordQuiet,
    hfa, hfl, hfr, hk, hb, hc, hy, hfy.1, hfy.2]

/-! ### Shape helpers -/

theorem bankWordPhiSISource {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (q : Fin n → ProjW c) (e : Fin n) :
    ((phiW ring q e) e).si = (workerW (q e) (q (ring.rightNeighbor e))).x := by
  rw [bankWordPhiSource]; rfl

theorem bankWordPhiSITarget {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (q : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    ((phiW ring q e) (ring.rightNeighbor e)).si =
      (workerW (q e) (q (ring.rightNeighbor e))).y := by
  rw [bankWordPhiTarget ring q e hne]; rfl

/-- GeneratedControl from a shape carried by at most two non-root,
non-PREFIX sites.  Consumer: the BACK/SUM/READY transports. -/
theorem bankWordGCOfPair {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (q : Fin n → ProjW c)
    (hwidth : 2 ≤ c.t ∧ c.t < n)
    (a b : Fin n) (ha : a ≠ root) (hb : b ≠ root)
    (hka : (q a).si.kind ≠ .PREFIX) (hkb : (q b).si.kind ≠ .PREFIX)
    (hout : gcOutsidePair q a b)
    (hshape : gcEmptyShape q ∨ gcPrefixShape ring root q ∨
      gcBackShape ring root q ∨ gcSumShape ring root q ∨
      gcReadyShape ring root q ∨ gcLoneBusyShape ring root q ∨
      gcOrphanBackShape ring root q ∨ gcOrphanSumShape ring root q)
    (hclean : gcAcceptClean ring q) :
    GeneratedControl ring root q := by
  have hnp : ∀ i : Fin n, (q i).si.kind ≠ .PREFIX := by
    intro i
    by_cases hia : i = a
    · rw [hia]; exact hka
    · by_cases hib : i = b
      · rw [hib]; exact hkb
      · have := (bankWordPassFreeFields _ (hout i hia hib)).1
        rw [this]; intro h; cases h
  refine {
    width := hwidth
    rootNotBusy := ?_
    uniquePrefix := fun i _ hi _ => absurd hi (hnp i)
    shape := hshape
    acceptClean := hclean }
  intro hbad
  have := (bankWordPassFreeFields _ (hout root ha.symm hb.symm)).1
  rw [this] at hbad
  cases hbad.1

/-! ### BACK shape -/

/-- With no hard flag, the BACK shape moves by B0, turns into SUM by
B1, and frames elsewhere.  Consumer: `bankWordRowQuiet`. -/
theorem bankWordRowBack {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (q : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hgen : GeneratedControl ring root q)
    (hfa : (serW (q e) (q (ring.rightNeighbor e))).hard.hardAccept = false)
    (hfl : (serW (q e) (q (ring.rightNeighbor e))).hard.hardLeft = false)
    (hfr : (serW (q e) (q (ring.rightNeighbor e))).hard.hardRight = false)
    (hshape : gcBackShape ring root q)
    (hnext : gcAcceptClean ring (phiW ring q e)) :
    GeneratedControl ring root (phiW ring q e) ∧
      SelectedWordQuiet (q e) (q (ring.rightNeighbor e)) := by
  obtain ⟨m, cur, hbusy, hcursor, hcm, hout⟩ := hshape
  obtain ⟨hmroot, hmoff, hmk, hmb⟩ := hbusy
  obtain ⟨_, _, hcc, hjpos, hpos, _, _, _⟩ := hcursor
  have hmlt := L3.EWord.validationOffsetBound ring root m
  have hJle : (q cur).si.j.val ≤ c.t := Nat.le_of_lt_succ (q cur).si.j.isLt
  have hwid := hgen.width
  generalize hJ : (q cur).si.j.val = J at hjpos hpos hJle
  have hcurk : (q cur).si.kind ≠ .PREFIX := by
    by_cases h : cur = m
    · rw [h, hmk]; intro h'; cases h'
    · rw [(hcm h).1]; intro h'; cases h'
  by_cases hA : e = cur ∨ e = m
  · apply bankWordFrameTransport ring root q e hne hgen _ hnext
    apply bankWordSiFrameRow _ _ hfa hfl hfr
    · rcases hA with h | h
      · rw [h]; exact hcurk
      · rw [h, hmk]; intro h'; cases h'
    · rcases hA with h | h
      · rw [h, hcc]; intro h'; cases h'
      · by_cases hc : cur = m
        · rw [h, ← hc, hcc]; intro h'; cases h'
        · rw [h, (hcm hc).2]; intro h'; cases h'
    · intro hk
      rcases hA with h | h
      · by_cases hc : cur = m
        · rw [h, hc]; exact Or.inl hmb
        · rw [h, (hcm hc).1] at hk; cases hk
      · rw [h]; exact Or.inl hmb
    · intro _
      rcases hA with h | h
      · rw [h]; simp [freeSI, hcc]
      · rw [h]; simp [freeSI, hmk]
  · have he1 : e ≠ cur := fun h => hA (Or.inl h)
    have he2 : e ≠ m := fun h => hA (Or.inr h)
    have hf := hout e he1 he2
    have hfx := bankWordPassFreeFields _ hf
    by_cases hr : ring.rightNeighbor e = cur
    · -- the active B0 / B1 edge
      have hcurR : (q (ring.rightNeighbor e)).si.cur = .BACK := by
        rw [hr]; exact hcc
      have hkR : (q (ring.rightNeighbor e)).si.kind ≠ .PREFIX := by
        rw [hr]; exact hcurk
      have hJR : (q (ring.rightNeighbor e)).si.j.val = J := by rw [hr]; exact hJ
      have hcsite : cur = L3.EWord.site ring root
          (PPL.cyclicOffset ring root m - c.t + J) := hpos
      have hk1 : 1 ≤ PPL.cyclicOffset ring root m - c.t + J := by omega
      have hesite := bankWordLeftOfSite ring root e _ hk1 (hr.trans hcsite)
      have heroot : e ≠ root := by
        rw [hesite]
        exact bankWordSiteNeRoot ring root _ (by omega) (by omega)
      have hyc : (workerW (q e) (q (ring.rightNeighbor e))).y =
          clearCursor (q (ring.rightNeighbor e)).si := by
        by_cases hj1 : J = 1
        · exact (bankWordPassBackInitFields _ _ hfa hfl hfr hf hcurR
            (by rw [hJR, hj1]) hkR).2.2.1
        · exact (bankWordPassBackMoveFields _ _ hfa hfl hfr hf hcurR
            (by rw [hJR]; omega) hkR).2.2.1
      have hothers : ∀ i : Fin n, i ≠ e → i ≠ m →
          freeSI ((phiW ring q e) i).si = true := by
        intro i hie him
        by_cases hic : i = cur
        · have hcm' : cur ≠ m := by rw [← hic]; exact him
          rw [hic, ← hr, bankWordPhiSITarget ring q e hne, hyc]
          apply bankWordPassFreeClear
          rw [hr]; exact (hcm hcm').1
        · rw [generatedControlRemoteSiFrame ring q e i hie
            (by rw [hr]; exact hic)]
          exact hout i hic him
      have hmfacts : ((phiW ring q e) m).si.kind = .ROOT ∧
          ((phiW ring q e) m).si.busy = true ∧
          ((phiW ring q e) m).si.cur = .NONE := by
        by_cases hc : cur = m
        · have hm' : m = ring.rightNeighbor e := hc.symm.trans hr.symm
          rw [hm', bankWordPhiSITarget ring q e hne, hyc]
          refine ⟨?_, ?_, rfl⟩
          · show (q (ring.rightNeighbor e)).si.kind = _
            rw [← hm']; exact hmk
          · show (q (ring.rightNeighbor e)).si.busy = _
            rw [← hm']; exact hmb
        · rw [generatedControlRemoteSiFrame ring q e m (Ne.symm he2)
            (by rw [hr]; exact Ne.symm hc)]
          exact ⟨hmk, hmb, (hcm hc).2⟩
      by_cases hj1 : J = 1
      · -- B1: BACK becomes SUM at the source
        have hj1' : (q (ring.rightNeighbor e)).si.j.val = 1 := by rw [hJR, hj1]
        obtain ⟨_, hx, _, _⟩ :=
          bankWordPassBackInitFields _ _ hfa hfl hfr hf hcurR hj1' hkR
        have hq := bankWordRowQuietBackInit _ _ hfa hfl hfr hf hcurR hj1' hkR
        have hesi : ((phiW ring q e) e).si =
            setCursor (q e).si .SUM 0 false false true := by
          rw [bankWordPhiSISource, hx]
        refine ⟨?_, hq⟩
        apply bankWordGCOfPair ring root _ hwid m e hmroot heroot
          (by rw [hmfacts.1]; intro h; cases h)
          (by rw [hesi]; show (q e).si.kind ≠ _; rw [hfx.1]; intro h; cases h)
          (fun i h1 h2 => hothers i h2 h1) _ hnext
        refine Or.inr (Or.inr (Or.inr (Or.inl ⟨m, e,
          ⟨hmroot, hmoff, hmfacts.1, hmfacts.2.1⟩, hmfacts.2.2, ?_,
          fun i h1 h2 => hothers i h1 h2⟩)))
        refine ⟨hmroot, hmoff, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hesi]; exact hfx.1
        · rw [hesi]; rfl
        · rw [hesi]; simp [setCursor, siJ]; omega
        · rw [hesi]; simp only [setCursor, siJ]
          rw [dif_pos (by omega)]
          rw [hesite, hj1]
          simp [L3.EWord.site]
        · rw [hesi]; simp [setCursor, siJ, cwSumOr]
        · rw [hesi]; simp [setCursor, siJ, cwSumParity]
        · rw [hesi]; simp [setCursor, siJ, cwSumTrailing]
      · -- B0: the BACK cursor moves to the source
        have hj2 : 1 < (q (ring.rightNeighbor e)).si.j.val := by rw [hJR]; omega
        obtain ⟨_, hx, _, _⟩ :=
          bankWordPassBackMoveFields _ _ hfa hfl hfr hf hcurR hj2 hkR
        have hq := bankWordRowQuietBackMove _ _ hfa hfl hfr hf hcurR hj2 hkR
        have hesi : ((phiW ring q e) e).si =
            setCursor (q e).si .BACK (J - 1) false false true := by
          rw [bankWordPhiSISource, hx, hJR]
        refine ⟨?_, hq⟩
        apply bankWordGCOfPair ring root _ hwid m e hmroot heroot
          (by rw [hmfacts.1]; intro h; cases h)
          (by rw [hesi]; show (q e).si.kind ≠ _; rw [hfx.1]; intro h; cases h)
          (fun i h1 h2 => hothers i h2 h1) _ hnext
        refine Or.inr (Or.inr (Or.inl ⟨m, e,
          ⟨hmroot, hmoff, hmfacts.1, hmfacts.2.1⟩,
          ?_, fun _ => ⟨by rw [hesi]; exact hfx.1, hmfacts.2.2⟩,
          fun i h1 h2 => hothers i h1 h2⟩))
        refine ⟨hmroot, hmoff, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hesi]; rfl
        · rw [hesi]; simp only [setCursor, siJ]
          rw [dif_pos (by omega)]
          show 0 < J - 1
          omega
        · rw [hesi]; simp only [setCursor, siJ]
          rw [dif_pos (by omega)]
          refine hesite.trans ?_
          show L3.EWord.site ring root _ = L3.EWord.site ring root _
          congr 1
          show _ = _ + (J - 1)
          omega
        · rw [hesi]; rfl
        · rw [hesi]; rfl
        · rw [hesi]; rfl
    · apply bankWordFrameTransport ring root q e hne hgen _ hnext
      apply bankWordSiFrameRow _ _ hfa hfl hfr
      · rw [hfx.1]; intro h; cases h
      · rw [hfx.2]; intro h; cases h
      · intro h; rw [hfx.1] at h; cases h
      · intro hR
        exfalso
        by_cases hrm : ring.rightNeighbor e = m
        · have hc : cur ≠ m := by rw [← hrm]; exact Ne.symm hr
          rw [hrm, (hcm hc).2] at hR; cases hR
        · have := (bankWordPassFreeFields _ (hout _ hr hrm)).2
          rw [this] at hR; cases hR

/-! ### SUM rows -/

theorem bankWordRowSumMoveResult {c : Compiled} (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hk : x.si.kind = .OFF) (hc : x.si.cur = .SUM)
    (hj : x.si.j.val + 1 < c.t) (hf : freeSI y.si = true) :
    (workerW x y).x = clearCursor x.si ∧
    (workerW x y).y = setCursor y.si .SUM (x.si.j.val + 1)
      (x.si.z || x.u) (Bool.xor x.si.p (c.taps x.si.j.val && x.u))
      (if x.si.j.val == 0 then true else (x.si.a && x.u)) := by
  have hfy := bankWordPassFreeFields y.si hf
  simp [workerW, siStep, ProjW.lift, freeSI,
    hfa, hfl, hfr, hk, hc, hj, hfy.1, hfy.2]

theorem bankWordRowSumPublishResult {c : Compiled} (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hk : x.si.kind = .OFF) (hc : x.si.cur = .SUM)
    (hj : x.si.j.val + 1 = c.t)
    (hrk : y.si.kind = .ROOT) (hrb : y.si.busy = true)
    (z p a : Bool)
    (hz : (x.si.z || x.u) = z)
    (hp : Bool.xor x.si.p (c.taps x.si.j.val && x.u) = p)
    (ha : (if x.si.j.val == 0 then true else (x.si.a && x.u)) = a) :
    (workerW x y).uX = x.u ∧ (workerW x y).betaX = x.beta ∧
    (workerW x y).uY = (if z = false then true else p) ∧
    (workerW x y).betaY = (a && (if z = false then true else p)) := by
  subst hz hp ha
  simp [workerW, siStep, ProjW.lift, freeSI, hfa, hfl, hfr, hk, hc, hj, hrk, hrb]

/-- The source bit of a SUM cursor is its own U.  Consumer: SUM rows. -/
theorem bankWordSumSourceBit {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (q : Fin n → ProjW c) (m cur : Fin n) (J : Nat)
    (hpos : cur = PPL.shiftRight ring root
      (PPL.cyclicOffset ring root m - c.t + J)) :
    cwSourceBit ring root q (PPL.cyclicOffset ring root m) J = (q cur).u := by
  simp only [cwSourceBit, cwBit]
  rw [← hpos]

/-- With no hard flag, the SUM shape moves by S0, publishes by S1 into
READY, and frames elsewhere.  Consumer: `bankWordRowQuiet`. -/
theorem bankWordRowSum {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (q : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hgen : GeneratedControl ring root q)
    (hword : CleanWorkerWordValues ring root q)
    (hfa : (serW (q e) (q (ring.rightNeighbor e))).hard.hardAccept = false)
    (hfl : (serW (q e) (q (ring.rightNeighbor e))).hard.hardLeft = false)
    (hfr : (serW (q e) (q (ring.rightNeighbor e))).hard.hardRight = false)
    (hshape : gcSumShape ring root q)
    (hnext : gcAcceptClean ring (phiW ring q e)) :
    GeneratedControl ring root (phiW ring q e) ∧
      SelectedWordQuiet (q e) (q (ring.rightNeighbor e)) := by
  obtain ⟨m, cur, hbusy, htcur, hcursor, hout⟩ := hshape
  obtain ⟨hmroot, hmoff, hmk, hmb⟩ := hbusy
  obtain ⟨_, _, hck, hcc, hjlt, hpos, hz, hp, ha⟩ := hcursor
  have hmlt := L3.EWord.validationOffsetBound ring root m
  have hwid := hgen.width
  have hcm : cur ≠ m := by
    intro h; rw [h, hmk] at hck; cases hck
  generalize hJ : (q cur).si.j.val = J at hjlt hpos hz hp ha
  have hcsite : cur = L3.EWord.site ring root
      (PPL.cyclicOffset ring root m - c.t + J) := hpos
  have hcoff : PPL.cyclicOffset ring root cur =
      PPL.cyclicOffset ring root m - c.t + J := by
    have := congrArg (PPL.cyclicOffset ring root) hcsite
    rw [L3.EWord.validationSiteOffset ring root _ (by omega)] at this
    exact this
  by_cases hec : e = cur
  · subst hec
    have hrsite : ring.rightNeighbor e = L3.EWord.site ring root
        (PPL.cyclicOffset ring root m - c.t + J + 1) := by
      rw [hcsite]; exact L3.EWord.siteSuccessor ring root _
    have hsrc := bankWordSumSourceBit ring root q m e J hpos
    by_cases hJt : J + 1 < c.t
    · -- S0
      have hrm : ring.rightNeighbor e ≠ m := by
        intro h
        have h1 := congrArg (PPL.cyclicOffset ring root) hrsite
        rw [h, L3.EWord.validationSiteOffset ring root _ (by omega)] at h1
        omega
      have hf := hout _ hne hrm
      have hj' : (q e).si.j.val + 1 < c.t := by rw [hJ]; exact hJt
      obtain ⟨hx, hy⟩ := bankWordRowSumMoveResult _ _ hfa hfl hfr hck hcc hj' hf
      have hq := bankWordRowQuietSumMove _ _ hfa hfl hfr hck hcc hj' hf
      have hvis := (selectedWordQuiet_iff_edge ring q e hne).mp hq
      have hRsi : ((phiW ring q e) (ring.rightNeighbor e)).si =
          setCursor (q (ring.rightNeighbor e)).si .SUM (J + 1)
            ((q e).si.z || (q e).u)
            (Bool.xor (q e).si.p (c.taps J && (q e).u))
            (if J == 0 then true else ((q e).si.a && (q e).u)) := by
        rw [bankWordPhiSITarget ring q e hne, hy, hJ]
      have hmsi : ((phiW ring q e) m).si = (q m).si :=
        generatedControlRemoteSiFrame ring q e m (Ne.symm hcm) (Ne.symm hrm)
      have hothers : ∀ i : Fin n, i ≠ ring.rightNeighbor e → i ≠ m →
          freeSI ((phiW ring q e) i).si = true := by
        intro i h1 h2
        by_cases hie : i = e
        · rw [hie, bankWordPhiSISource, hx]
          exact bankWordPassFreeClear _ hck
        · rw [generatedControlRemoteSiFrame ring q e i hie h1]
          exact hout i hie h2
      have hfy := bankWordPassFreeFields _ hf
      refine ⟨?_, hq⟩
      apply bankWordGCOfPair ring root _ hwid m (ring.rightNeighbor e) hmroot
        (by rw [hrsite]; exact bankWordSiteNeRoot ring root _ (by omega) (by omega))
        (by rw [hmsi, hmk]; intro h; cases h)
        (by rw [hRsi]; show (q (ring.rightNeighbor e)).si.kind ≠ _
            rw [hfy.1]; intro h; cases h)
        (fun i h1 h2 => hothers i h2 h1) _ hnext
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨m, ring.rightNeighbor e,
        ⟨hmroot, hmoff, by rw [hmsi]; exact hmk, by rw [hmsi]; exact hmb⟩,
        by rw [hmsi]; exact htcur, ?_, fun i h1 h2 => hothers i h1 h2⟩)))
      have hsiJ : (siJ c.t (J + 1)).val = J + 1 := by
        simp only [siJ]; rw [dif_pos (by omega)]
      refine ⟨hmroot, hmoff, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hRsi]; exact hfy.1
      · rw [hRsi]; rfl
      · rw [hRsi]; show (siJ c.t (J + 1)).val < c.t; rw [hsiJ]; exact hJt
      · rw [hRsi]; show ring.rightNeighbor e = PPL.shiftRight ring root
          (PPL.cyclicOffset ring root m - c.t + (siJ c.t (J + 1)).val)
        rw [hsiJ, hrsite]; rfl
      · rw [hRsi]; show ((q e).si.z || (q e).u) = cwSumOr ring root _ _
          (siJ c.t (J + 1)).val
        rw [hsiJ, bankWordCwSumOrEq ring root _ q hvis,
          generatedControlSumOrSucc, ← hz, hsrc]
      · rw [hRsi]; show Bool.xor (q e).si.p (c.taps J && (q e).u) =
          cwSumParity ring root _ _ (siJ c.t (J + 1)).val
        rw [hsiJ, bankWordCwSumParityEq ring root _ q hvis,
          generatedControlSumParitySucc, ← hp, hsrc]
      · rw [hRsi]; show (if J == 0 then true else ((q e).si.a && (q e).u)) =
          cwSumTrailing ring root _ _ (siJ c.t (J + 1)).val
        rw [hsiJ, bankWordCwSumTrailingEq ring root _ q hvis,
          generatedControlSumTrailingSucc, ← ha, hsrc]
        by_cases h0 : J = 0 <;> simp [h0]
    · -- S1: publication at the target
      have hJt' : J + 1 = c.t := by omega
      have hrm : ring.rightNeighbor e = m := by
        rw [hrsite, show PPL.cyclicOffset ring root m - c.t + J + 1 =
            PPL.cyclicOffset ring root m by omega]
        exact bankWordSiteOffset ring root m
      have hj' : (q e).si.j.val + 1 = c.t := by rw [hJ]; exact hJt'
      have hrk : (q (ring.rightNeighbor e)).si.kind = .ROOT := by rw [hrm]; exact hmk
      have hrb : (q (ring.rightNeighbor e)).si.busy = true := by rw [hrm]; exact hmb
      obtain ⟨_, hx, hyk, hyb, hyc, _⟩ :=
        bankWordPassSumPublishFields _ _ hfa hfl hfr hck hcc hj' hrk hrb
      -- the published values are the clean ones
      have hmk' : (⟨PPL.cyclicOffset ring root m, hmlt⟩ : Fin n).val =
          PPL.cyclicOffset ring root m := rfl
      have hzt : ((q e).si.z || (q e).u) = true := by
        have hs := generatedControlSumOrSucc ring root q
          (PPL.cyclicOffset ring root m) J
        rw [hJt'] at hs
        rw [hz, ← hsrc, ← hs]
        exact hword.laterNonzero ⟨_, hmlt⟩ hmoff
      have hpt : Bool.xor (q e).si.p (c.taps J && (q e).u) = (q m).u := by
        have hs := generatedControlSumParitySucc ring root q
          (PPL.cyclicOffset ring root m) J
        rw [hJt'] at hs
        rw [hp, ← hsrc, ← hs]
        have := hword.recurrence ⟨_, hmlt⟩ hmoff
        rw [← this]
        show (q (L3.EWord.site ring root (PPL.cyclicOffset ring root m))).u = _
        rw [bankWordSiteOffset ring root m]
      have hat : ((if J == 0 then true else ((q e).si.a && (q e).u)) &&
          (q m).u) = (q m).beta := by
        have hm := hword.markers ⟨_, hmlt⟩ (by omega)
        have hsm : PPL.shiftRight ring root (PPL.cyclicOffset ring root m) = m :=
          bankWordSiteOffset ring root m
        simp only [cwMarker, cwBit, hsm] at hm
        have htr := generatedControlSumTrailingSucc ring root q
          (PPL.cyclicOffset ring root m) J
        rw [hJt'] at htr
        rw [hm, htr, ← ha, hsrc]
        by_cases h0 : J = 0 <;> simp [h0]
      obtain ⟨hux, hbx, huy, hby⟩ := bankWordRowSumPublishResult _ _ hfa hfl hfr
        hck hcc hj' hrk hrb true ((q m).u)
        (if J == 0 then true else ((q e).si.a && (q e).u)) hzt
        (by rw [hJ]; exact hpt) (by rw [hJ])
      have hq : SelectedWordQuiet (q e) (q (ring.rightNeighbor e)) := by
        refine ⟨hux, ?_, hbx, ?_⟩
        · rw [huy, hrm, if_neg (show ¬ (true = false) by decide)]
        · rw [hby, hrm, if_neg (show ¬ (true = false) by decide)]; exact hat
      refine ⟨?_, hq⟩
      have hRsi := bankWordPhiSITarget ring q e hne
      have hothers : ∀ i : Fin n, i ≠ m →
          freeSI ((phiW ring q e) i).si = true := by
        intro i h2
        by_cases hie : i = e
        · rw [hie, bankWordPhiSISource, hx]
          exact bankWordPassFreeClear _ hck
        · rw [generatedControlRemoteSiFrame ring q e i hie (by rw [hrm]; exact h2)]
          exact hout i hie h2
      apply bankWordGCOfPair ring root _ hwid m m hmroot hmroot
        (by rw [← hrm, hRsi, hyk]; intro h; cases h)
        (by rw [← hrm, hRsi, hyk]; intro h; cases h)
        (fun i h1 _ => hothers i h1) _ hnext
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, hmroot, hmoff,
        by rw [← hrm, hRsi, hyk], by rw [← hrm, hRsi, hyb],
        by rw [← hrm, hRsi, hyc], hothers⟩))))
  · by_cases hem : e = m
    · apply bankWordFrameTransport ring root q e hne hgen _ hnext
      apply bankWordSiFrameRow _ _ hfa hfl hfr
      · rw [hem, hmk]; intro h; cases h
      · rw [hem, htcur]; intro h; cases h
      · intro _; rw [hem]; exact Or.inl hmb
      · intro _; rw [hem]; simp [freeSI, hmk]
    · have hf := hout e hec hem
      have hfx := bankWordPassFreeFields _ hf
      apply bankWordFrameTransport ring root q e hne hgen _ hnext
      apply bankWordSiFrameRow _ _ hfa hfl hfr
      · rw [hfx.1]; intro h; cases h
      · rw [hfx.2]; intro h; cases h
      · intro h; rw [hfx.1] at h; cases h
      · intro hR
        exfalso
        by_cases hrc : ring.rightNeighbor e = cur
        · rw [hrc, hcc] at hR; cases hR
        · by_cases hrm : ring.rightNeighbor e = m
          · rw [hrm, htcur] at hR; cases hR
          · rw [(bankWordPassFreeFields _ (hout _ hrc hrm)).2] at hR; cases hR

/-! ### Orphan BACK and orphan SUM -/

/-- The orphan BACK cursor still moves by B0 and turns by B1; its
former target is free.  Consumer: `bankWordRowQuiet`. -/
theorem bankWordRowOrphanBack {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (q : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hgen : GeneratedControl ring root q)
    (hfa : (serW (q e) (q (ring.rightNeighbor e))).hard.hardAccept = false)
    (hfl : (serW (q e) (q (ring.rightNeighbor e))).hard.hardLeft = false)
    (hfr : (serW (q e) (q (ring.rightNeighbor e))).hard.hardRight = false)
    (hshape : gcOrphanBackShape ring root q)
    (hnext : gcAcceptClean ring (phiW ring q e)) :
    GeneratedControl ring root (phiW ring q e) ∧
      SelectedWordQuiet (q e) (q (ring.rightNeighbor e)) := by
  obtain ⟨m, cur, hcm, hft, hck, hcursor, hout⟩ := hshape
  obtain ⟨hmroot, hmoff, hcc, hjpos, hpos, _, _, _⟩ := hcursor
  have hmlt := L3.EWord.validationOffsetBound ring root m
  have hJle : (q cur).si.j.val ≤ c.t := Nat.le_of_lt_succ (q cur).si.j.isLt
  have hwid := hgen.width
  generalize hJ : (q cur).si.j.val = J at hjpos hpos hJle
  have hfreeOf : ∀ i : Fin n, i ≠ cur → freeSI (q i).si = true := by
    intro i hi
    by_cases him : i = m
    · rw [him]; exact hft
    · exact hout i hi him
  by_cases hec : e = cur
  · apply bankWordFrameTransport ring root q e hne hgen _ hnext
    apply bankWordSiFrameRow _ _ hfa hfl hfr
    · rw [hec, hck]; intro h; cases h
    · rw [hec, hcc]; intro h; cases h
    · intro h; rw [hec, hck] at h; cases h
    · intro _; rw [hec]; simp [freeSI, hcc]
  · have hf := hfreeOf e hec
    have hfx := bankWordPassFreeFields _ hf
    by_cases hr : ring.rightNeighbor e = cur
    · have hcurR : (q (ring.rightNeighbor e)).si.cur = .BACK := by
        rw [hr]; exact hcc
      have hkR : (q (ring.rightNeighbor e)).si.kind ≠ .PREFIX := by
        rw [hr, hck]; intro h; cases h
      have hJR : (q (ring.rightNeighbor e)).si.j.val = J := by rw [hr]; exact hJ
      have hcsite : cur = L3.EWord.site ring root
          (PPL.cyclicOffset ring root m - c.t + J) := hpos
      have hk1 : 1 ≤ PPL.cyclicOffset ring root m - c.t + J := by omega
      have hesite := bankWordLeftOfSite ring root e _ hk1 (hr.trans hcsite)
      have heroot : e ≠ root := by
        rw [hesite]
        exact bankWordSiteNeRoot ring root _ (by omega) (by omega)
      have hem : e ≠ m := by
        intro h
        have h1 := congrArg (PPL.cyclicOffset ring root) hesite
        rw [h, L3.EWord.validationSiteOffset ring root _ (by omega)] at h1
        omega
      have hyc : (workerW (q e) (q (ring.rightNeighbor e))).y =
          clearCursor (q (ring.rightNeighbor e)).si := by
        by_cases hj1 : J = 1
        · exact (bankWordPassBackInitFields _ _ hfa hfl hfr hf hcurR
            (by rw [hJR, hj1]) hkR).2.2.1
        · exact (bankWordPassBackMoveFields _ _ hfa hfl hfr hf hcurR
            (by rw [hJR]; omega) hkR).2.2.1
      have hothers : ∀ i : Fin n, i ≠ e →
          freeSI ((phiW ring q e) i).si = true := by
        intro i hie
        by_cases hic : i = cur
        · rw [hic, ← hr, bankWordPhiSITarget ring q e hne, hyc]
          apply bankWordPassFreeClear
          rw [hr]; exact hck
        · rw [generatedControlRemoteSiFrame ring q e i hie
            (by rw [hr]; exact hic)]
          exact hfreeOf i hic
      by_cases hj1 : J = 1
      · have hj1' : (q (ring.rightNeighbor e)).si.j.val = 1 := by rw [hJR, hj1]
        obtain ⟨_, hx, _, _⟩ :=
          bankWordPassBackInitFields _ _ hfa hfl hfr hf hcurR hj1' hkR
        have hq := bankWordRowQuietBackInit _ _ hfa hfl hfr hf hcurR hj1' hkR
        have hesi : ((phiW ring q e) e).si =
            setCursor (q e).si .SUM 0 false false true := by
          rw [bankWordPhiSISource, hx]
        refine ⟨?_, hq⟩
        apply bankWordGCOfPair ring root _ hwid m e hmroot heroot
          (by
            have := (bankWordPassFreeFields _ (hothers m (Ne.symm hem))).1
            rw [this]; intro h; cases h)
          (by rw [hesi]; show (q e).si.kind ≠ _; rw [hfx.1]; intro h; cases h)
          (fun i _ h2 => hothers i h2) _ hnext
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨m, e, hem, hothers m (Ne.symm hem), ?_,
            fun i h1 _ => hothers i h1⟩))))))
        refine ⟨hmroot, hmoff, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hesi]; exact hfx.1
        · rw [hesi]; rfl
        · rw [hesi]; simp [setCursor, siJ]; omega
        · rw [hesi]; simp only [setCursor, siJ]
          rw [dif_pos (by omega)]
          rw [hesite, hj1]
          simp [L3.EWord.site]
        · rw [hesi]; simp [setCursor, siJ, cwSumOr]
        · rw [hesi]; simp [setCursor, siJ, cwSumParity]
        · rw [hesi]; simp [setCursor, siJ, cwSumTrailing]
      · have hj2 : 1 < (q (ring.rightNeighbor e)).si.j.val := by rw [hJR]; omega
        obtain ⟨_, hx, _, _⟩ :=
          bankWordPassBackMoveFields _ _ hfa hfl hfr hf hcurR hj2 hkR
        have hq := bankWordRowQuietBackMove _ _ hfa hfl hfr hf hcurR hj2 hkR
        have hesi : ((phiW ring q e) e).si =
            setCursor (q e).si .BACK (J - 1) false false true := by
          rw [bankWordPhiSISource, hx, hJR]
        refine ⟨?_, hq⟩
        apply bankWordGCOfPair ring root _ hwid m e hmroot heroot
          (by
            have := (bankWordPassFreeFields _ (hothers m (Ne.symm hem))).1
            rw [this]; intro h; cases h)
          (by rw [hesi]; show (q e).si.kind ≠ _; rw [hfx.1]; intro h; cases h)
          (fun i _ h2 => hothers i h2) _ hnext
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨m, e, hem, hothers m (Ne.symm hem),
            by rw [hesi]; exact hfx.1, ?_,
            fun i h1 _ => hothers i h1⟩))))))
        refine ⟨hmroot, hmoff, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hesi]; rfl
        · rw [hesi]; simp only [setCursor, siJ]
          rw [dif_pos (by omega)]
          show 0 < J - 1
          omega
        · rw [hesi]; simp only [setCursor, siJ]
          rw [dif_pos (by omega)]
          refine hesite.trans ?_
          show L3.EWord.site ring root _ = L3.EWord.site ring root _
          congr 1
          show _ = _ + (J - 1)
          omega
        · rw [hesi]; rfl
        · rw [hesi]; rfl
        · rw [hesi]; rfl
    · apply bankWordFrameTransport ring root q e hne hgen _ hnext
      apply bankWordSiFrameRow _ _ hfa hfl hfr
      · rw [hfx.1]; intro h; cases h
      · rw [hfx.2]; intro h; cases h
      · intro h; rw [hfx.1] at h; cases h
      · intro hR
        exfalso
        rw [(bankWordPassFreeFields _ (hfreeOf _ hr)).2] at hR; cases hR

/-- The orphan SUM cursor moves by S0 and is stuck at its last index.
Consumer: `bankWordRowQuiet`. -/
theorem bankWordRowOrphanSum {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (q : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hgen : GeneratedControl ring root q)
    (hfa : (serW (q e) (q (ring.rightNeighbor e))).hard.hardAccept = false)
    (hfl : (serW (q e) (q (ring.rightNeighbor e))).hard.hardLeft = false)
    (hfr : (serW (q e) (q (ring.rightNeighbor e))).hard.hardRight = false)
    (hshape : gcOrphanSumShape ring root q)
    (hnext : gcAcceptClean ring (phiW ring q e)) :
    GeneratedControl ring root (phiW ring q e) ∧
      SelectedWordQuiet (q e) (q (ring.rightNeighbor e)) := by
  obtain ⟨m, cur, hcm, hft, hcursor, hout⟩ := hshape
  obtain ⟨hmroot, hmoff, hck, hcc, hjlt, hpos, hz, hp, ha⟩ := hcursor
  have hmlt := L3.EWord.validationOffsetBound ring root m
  have hwid := hgen.width
  generalize hJ : (q cur).si.j.val = J at hjlt hpos hz hp ha
  have hfreeOf : ∀ i : Fin n, i ≠ cur → freeSI (q i).si = true := by
    intro i hi
    by_cases him : i = m
    · rw [him]; exact hft
    · exact hout i hi him
  have hcsite : cur = L3.EWord.site ring root
      (PPL.cyclicOffset ring root m - c.t + J) := hpos
  by_cases hec : e = cur
  · subst hec
    have hrsite : ring.rightNeighbor e = L3.EWord.site ring root
        (PPL.cyclicOffset ring root m - c.t + J + 1) := by
      rw [hcsite]; exact L3.EWord.siteSuccessor ring root _
    have hsrc := bankWordSumSourceBit ring root q m e J hpos
    have hf := hfreeOf _ hne
    by_cases hJt : J + 1 < c.t
    · have hrm : ring.rightNeighbor e ≠ m := by
        intro h
        have h1 := congrArg (PPL.cyclicOffset ring root) hrsite
        rw [h, L3.EWord.validationSiteOffset ring root _ (by omega)] at h1
        omega
      have hj' : (q e).si.j.val + 1 < c.t := by rw [hJ]; exact hJt
      obtain ⟨hx, hy⟩ := bankWordRowSumMoveResult _ _ hfa hfl hfr hck hcc hj' hf
      have hq := bankWordRowQuietSumMove _ _ hfa hfl hfr hck hcc hj' hf
      have hvis := (selectedWordQuiet_iff_edge ring q e hne).mp hq
      have hRsi : ((phiW ring q e) (ring.rightNeighbor e)).si =
          setCursor (q (ring.rightNeighbor e)).si .SUM (J + 1)
            ((q e).si.z || (q e).u)
            (Bool.xor (q e).si.p (c.taps J && (q e).u))
            (if J == 0 then true else ((q e).si.a && (q e).u)) := by
        rw [bankWordPhiSITarget ring q e hne, hy, hJ]
      have hothers : ∀ i : Fin n, i ≠ ring.rightNeighbor e →
          freeSI ((phiW ring q e) i).si = true := by
        intro i h1
        by_cases hie : i = e
        · rw [hie, bankWordPhiSISource, hx]
          exact bankWordPassFreeClear _ hck
        · rw [generatedControlRemoteSiFrame ring q e i hie h1]
          exact hfreeOf i hie
      have hfy := bankWordPassFreeFields _ hf
      refine ⟨?_, hq⟩
      apply bankWordGCOfPair ring root _ hwid m (ring.rightNeighbor e) hmroot
        (by rw [hrsite]; exact bankWordSiteNeRoot ring root _ (by omega) (by omega))
        (by
          have := (bankWordPassFreeFields _ (hothers m (Ne.symm hrm))).1
          rw [this]; intro h; cases h)
        (by rw [hRsi]; show (q (ring.rightNeighbor e)).si.kind ≠ _
            rw [hfy.1]; intro h; cases h)
        (fun i _ h2 => hothers i h2) _ hnext
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨m, ring.rightNeighbor e, hrm, hothers m (Ne.symm hrm), ?_,
          fun i h1 _ => hothers i h1⟩))))))
      have hsiJ : (siJ c.t (J + 1)).val = J + 1 := by
        simp only [siJ]; rw [dif_pos (by omega)]
      refine ⟨hmroot, hmoff, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hRsi]; exact hfy.1
      · rw [hRsi]; rfl
      · rw [hRsi]; show (siJ c.t (J + 1)).val < c.t; rw [hsiJ]; exact hJt
      · rw [hRsi]; show ring.rightNeighbor e = PPL.shiftRight ring root
          (PPL.cyclicOffset ring root m - c.t + (siJ c.t (J + 1)).val)
        rw [hsiJ, hrsite]; rfl
      · rw [hRsi]; show ((q e).si.z || (q e).u) = cwSumOr ring root _ _
          (siJ c.t (J + 1)).val
        rw [hsiJ, bankWordCwSumOrEq ring root _ q hvis,
          generatedControlSumOrSucc, ← hz, hsrc]
      · rw [hRsi]; show Bool.xor (q e).si.p (c.taps J && (q e).u) =
          cwSumParity ring root _ _ (siJ c.t (J + 1)).val
        rw [hsiJ, bankWordCwSumParityEq ring root _ q hvis,
          generatedControlSumParitySucc, ← hp, hsrc]
      · rw [hRsi]; show (if J == 0 then true else ((q e).si.a && (q e).u)) =
          cwSumTrailing ring root _ _ (siJ c.t (J + 1)).val
        rw [hsiJ, bankWordCwSumTrailingEq ring root _ q hvis,
          generatedControlSumTrailingSucc, ← ha, hsrc]
        by_cases h0 : J = 0 <;> simp [h0]
    · have hj' : (q e).si.j.val + 1 = c.t := by rw [hJ]; omega
      apply bankWordFrameTransport ring root q e hne hgen _ hnext
      apply bankWordSiStuckSumRow _ _ hfa hfl hfr hck hcc hj'
      intro hbad
      rw [(bankWordPassFreeFields _ hf).1] at hbad
      cases hbad.1
  · have hf := hfreeOf e hec
    have hfx := bankWordPassFreeFields _ hf
    apply bankWordFrameTransport ring root q e hne hgen _ hnext
    apply bankWordSiFrameRow _ _ hfa hfl hfr
    · rw [hfx.1]; intro h; cases h
    · rw [hfx.2]; intro h; cases h
    · intro h; rw [hfx.1] at h; cases h
    · intro hR
      exfalso
      by_cases hrc : ring.rightNeighbor e = cur
      · rw [hrc, hcc] at hR; cases hR
      · rw [(bankWordPassFreeFields _ (hfreeOf _ hrc)).2] at hR; cases hR

/-! ### READY, lone busy, PREFIX -/

/-- The READY target finishes by A0 at the root predecessor and
launches a fresh BACK window by A1 elsewhere.  Consumer:
`bankWordRowQuiet`. -/
theorem bankWordRowReady {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (q : Fin n → ProjW c) (e : Fin n)
    (hn : 3 ≤ n)
    (hne : ring.rightNeighbor e ≠ e)
    (hfix : WFixedRoot ring root q)
    (hgen : GeneratedControl ring root q)
    (hword : CleanWorkerWordValues ring root q)
    (hfa : (serW (q e) (q (ring.rightNeighbor e))).hard.hardAccept = false)
    (hfl : (serW (q e) (q (ring.rightNeighbor e))).hard.hardLeft = false)
    (hfr : (serW (q e) (q (ring.rightNeighbor e))).hard.hardRight = false)
    (hshape : gcReadyShape ring root q)
    (hnext : gcAcceptClean ring (phiW ring q e)) :
    GeneratedControl ring root (phiW ring q e) ∧
      SelectedWordQuiet (q e) (q (ring.rightNeighbor e)) := by
  obtain ⟨m, hmroot, hmoff, hmk, hmb, hmc, hother⟩ := hshape
  have hwid := hgen.width
  by_cases hem : e = m
  · subst hem
    have hfR := hother _ hne
    have hfixN := bankRepairDigitWFixedRootPhiW hn ring root q e hfix
    rcases clockPostTrichotomy ring root q e (by omega) hfixN with
      ⟨he, _, _⟩ | ⟨_, _, hy⟩ | ⟨_, hr, _, hy⟩
    · exact absurd he hmroot
    · obtain ⟨_, _, _, hq⟩ := generatedControlReadyAZeroOwner _ _
        hfa hfl hfr hmk hmb hmc hy hfR
      exact ⟨(generatedControlReadyAZeroStep ring root q e hne hgen
        ⟨e, hmroot, hmoff, hmk, hmb, hmc, hother⟩ hmk hword
        hfa hfl hfr hy hnext).2.1, hq⟩
    · obtain ⟨_, hx, hyy, _⟩ :=
        bankWordPassAdvanceFields _ _ hfa hfl hfr hmk hmb hmc hy hfR
      have hq := bankWordRowQuietAdvance _ _ hfa hfl hfr hmk hmb hmc hy hfR
      have hoffR := bankWordOffsetRight ring root e hr
      have hRsi : ((phiW ring q e) (ring.rightNeighbor e)).si =
          launchRootBack c.t := by
        rw [bankWordPhiSITarget ring q e hne, hyy]
      have hothers : ∀ i : Fin n, i ≠ ring.rightNeighbor e →
          freeSI ((phiW ring q e) i).si = true := by
        intro i h1
        by_cases hie : i = e
        · rw [hie, bankWordPhiSISource, hx]; rfl
        · rw [generatedControlRemoteSiFrame ring q e i hie h1]
          exact hother i hie
      refine ⟨?_, hq⟩
      apply bankWordGCOfPair ring root _ hwid (ring.rightNeighbor e)
        (ring.rightNeighbor e) hr hr
        (by rw [hRsi]; intro h; cases h) (by rw [hRsi]; intro h; cases h)
        (fun i h1 _ => hothers i h1) _ hnext
      refine Or.inr (Or.inr (Or.inl ⟨ring.rightNeighbor e,
        ring.rightNeighbor e, ?_, ?_, fun h => absurd rfl h,
        fun i h1 _ => hothers i h1⟩))
      · exact ⟨hr, by omega, by rw [hRsi]; rfl, by rw [hRsi]; rfl⟩
      · refine ⟨hr, by omega, by rw [hRsi]; rfl, ?_, ?_,
          by rw [hRsi]; rfl, by rw [hRsi]; rfl, by rw [hRsi]; rfl⟩
        · rw [hRsi]; show 0 < c.t; omega
        · rw [hRsi]
          show ring.rightNeighbor e = PPL.shiftRight ring root
            (PPL.cyclicOffset ring root (ring.rightNeighbor e) - c.t + c.t)
          rw [Nat.sub_add_cancel (by omega)]
          exact (bankWordSiteOffset ring root _).symm
  · have hf := hother e hem
    have hfx := bankWordPassFreeFields _ hf
    apply bankWordFrameTransport ring root q e hne hgen _ hnext
    apply bankWordSiFrameRow _ _ hfa hfl hfr
    · rw [hfx.1]; intro h; cases h
    · rw [hfx.2]; intro h; cases h
    · intro h; rw [hfx.1] at h; cases h
    · intro hR
      exfalso
      by_cases hrm : ring.rightNeighbor e = m
      · rw [hrm, hmc] at hR; cases hR
      · rw [(bankWordPassFreeFields _ (hother _ hrm)).2] at hR; cases hR

/-- A lone busy target with no cursor frames on every edge.
Consumer: `bankWordRowQuiet`. -/
theorem bankWordRowLoneBusy {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (q : Fin n → ProjW c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hgen : GeneratedControl ring root q)
    (hfa : (serW (q e) (q (ring.rightNeighbor e))).hard.hardAccept = false)
    (hfl : (serW (q e) (q (ring.rightNeighbor e))).hard.hardLeft = false)
    (hfr : (serW (q e) (q (ring.rightNeighbor e))).hard.hardRight = false)
    (hshape : gcLoneBusyShape ring root q)
    (hnext : gcAcceptClean ring (phiW ring q e)) :
    GeneratedControl ring root (phiW ring q e) ∧
      SelectedWordQuiet (q e) (q (ring.rightNeighbor e)) := by
  obtain ⟨m, ⟨_, _, hmk, hmb⟩, hmc, hother⟩ := hshape
  have hRnb : (q (ring.rightNeighbor e)).si.cur ≠ .BACK := by
    by_cases hrm : ring.rightNeighbor e = m
    · rw [hrm, hmc]; intro h; cases h
    · rw [(bankWordPassFreeFields _ (hother _ hrm)).2]; intro h; cases h
  apply bankWordFrameTransport ring root q e hne hgen _ hnext
  by_cases hem : e = m
  · apply bankWordSiFrameRow _ _ hfa hfl hfr
    · rw [hem, hmk]; intro h; cases h
    · rw [hem, hmc]; intro h; cases h
    · intro _; rw [hem]; exact Or.inl hmb
    · intro hR; exact absurd hR hRnb
  · have hfx := bankWordPassFreeFields _ (hother e hem)
    apply bankWordSiFrameRow _ _ hfa hfl hfr
    · rw [hfx.1]; intro h; cases h
    · rw [hfx.2]; intro h; cases h
    · intro h; rw [hfx.1] at h; cases h
    · intro hR; exact absurd hR hRnb

/-- The PREFIX advances by P1 or hands off by P3; at the root
predecessor it cannot sit (its index would exceed t).  Consumer:
`bankWordRowQuiet`. -/
theorem bankWordRowPrefix {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (q : Fin n → ProjW c) (e : Fin n)
    (hn : 3 ≤ n) (hroom : c.t + 2 ≤ n)
    (hne : ring.rightNeighbor e ≠ e)
    (hfix : WFixedRoot ring root q)
    (hgen : GeneratedControl ring root q)
    (hword : CleanWorkerWordValues ring root q)
    (hfa : (serW (q e) (q (ring.rightNeighbor e))).hard.hardAccept = false)
    (hfl : (serW (q e) (q (ring.rightNeighbor e))).hard.hardLeft = false)
    (hfr : (serW (q e) (q (ring.rightNeighbor e))).hard.hardRight = false)
    (hshape : gcPrefixShape ring root q)
    (hnext : gcAcceptClean ring (phiW ring q e)) :
    GeneratedControl ring root (phiW ring q e) ∧
      SelectedWordQuiet (q e) (q (ring.rightNeighbor e)) := by
  obtain ⟨st, hk, hb, hc, hj, hz, ha, hother⟩ := hshape
  have hjle : (q st).si.j.val ≤ c.t := Nat.le_of_lt_succ (q st).si.j.isLt
  by_cases hes : e = st
  · subst hes
    have hfR := hother _ hne
    have hfixN := bankRepairDigitWFixedRootPhiW hn ring root q e hfix
    have hy : (postW (q e) (q (ring.rightNeighbor e))).eY.l = false := by
      rcases clockPostTrichotomy ring root q e (by omega) hfixN with
        ⟨_, _, hy⟩ | ⟨hr, _, _⟩ | ⟨_, _, _, hy⟩
      · exact hy
      · exfalso
        have := bankWordOffsetOfRightRoot ring root e hr
        omega
      · exact hy
    have hpre : gcPrefixShape ring root q :=
      ⟨e, hk, hb, hc, hj, hz, ha, hother⟩
    by_cases hjt : (q e).si.j.val < c.t
    · obtain ⟨hrow, _⟩ :=
        bankWordPassPrefixAdvanceFields _ _ hfa hfl hfr hk hb hc hjt hy hfR
      have h := generatedControlPoneRowTransport ring root q e hgen hpre
        hword hfix hroom hrow hnext
      exact ⟨h.2.1, (selectedWordQuiet_iff_edge ring q e hne).mpr h.1⟩
    · obtain ⟨hrow, _⟩ :=
        bankWordPassPrefixHandoffFields _ _ hfa hfl hfr hk hb hc
          (by omega) hy hfR
      have h := generatedControlPthreeRowTransport ring root q e hgen hpre
        hword hfix hroom hrow hnext
      exact ⟨h.2.1, (selectedWordQuiet_iff_edge ring q e hne).mpr h.1⟩
  · have hfx := bankWordPassFreeFields _ (hother e hes)
    apply bankWordFrameTransport ring root q e hne hgen _ hnext
    apply bankWordSiFrameRow _ _ hfa hfl hfr
    · rw [hfx.1]; intro h; cases h
    · rw [hfx.2]; intro h; cases h
    · intro h; rw [hfx.1] at h; cases h
    · intro hR
      exfalso
      by_cases hrs : ring.rightNeighbor e = st
      · rw [hrs, hc] at hR; cases hR
      · rw [(bankWordPassFreeFields _ (hother _ hrs)).2] at hR; cases hR

/-! ### Dispatchers -/

/-- With no hard flag, every one of the eight GeneratedControl shapes
transports and the selected row is quiet.  Consumer:
`bankWordRowTransport`. -/
theorem bankWordRowQuiet {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (q : Fin n → ProjW c) (e : Fin n)
    (hn : 3 ≤ n) (hroom : c.t + 2 ≤ n)
    (hne : ring.rightNeighbor e ≠ e)
    (hfix : WFixedRoot ring root q)
    (hgen : GeneratedControl ring root q)
    (hword : CleanWorkerWordValues ring root q)
    (hfa : (serW (q e) (q (ring.rightNeighbor e))).hard.hardAccept = false)
    (hfl : (serW (q e) (q (ring.rightNeighbor e))).hard.hardLeft = false)
    (hfr : (serW (q e) (q (ring.rightNeighbor e))).hard.hardRight = false)
    (hnext : gcAcceptClean ring (phiW ring q e)) :
    GeneratedControl ring root (phiW ring q e) ∧
      SelectedWordQuiet (q e) (q (ring.rightNeighbor e)) := by
  rcases hgen.shape with h | h | h | h | h | h | h | h
  · have hs := generatedControlEmptyFrameStep ring root q e hne hgen h hword
      hfa hfl hfr hnext
    exact ⟨hs.2.1, (selectedWordQuiet_iff_edge ring q e hne).mpr hs.1⟩
  · exact bankWordRowPrefix ring root q e hn hroom hne hfix hgen hword
      hfa hfl hfr h hnext
  · exact bankWordRowBack ring root q e hne hgen hfa hfl hfr h hnext
  · exact bankWordRowSum ring root q e hne hgen hword hfa hfl hfr h hnext
  · exact bankWordRowReady ring root q e hn hne hfix hgen hword
      hfa hfl hfr h hnext
  · exact bankWordRowLoneBusy ring root q e hne hgen hfa hfl hfr h hnext
  · exact bankWordRowOrphanBack ring root q e hne hgen hfa hfl hfr h hnext
  · exact bankWordRowOrphanSum ring root q e hne hgen hfa hfl hfr h hnext

/-- The Cartesian GeneratedControl row transport on BANK rings
(n ≥ 5).  Consumer: `bankWordCleanWordClockOfBank`. -/
theorem bankWordRowTransport {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    GeneratedControlRowTransport ring := by
  intro root q hfix hgen hword e hresp hnext
  have hne := clockNeighborDifferent ring (by omega) e
  have hroom := (bankWordPassWidth hbank).2
  cases ha : (serW (q e) (q (ring.rightNeighbor e))).hard.hardAccept
  · cases herase : ((serW (q e) (q (ring.rightNeighbor e))).hard.hardLeft ||
        (serW (q e) (q (ring.rightNeighbor e))).hard.hardRight)
    · have hlr := Bool.or_eq_false_iff.mp herase
      exact bankWordRowQuiet ring root q e (by omega) hroom hne hfix hgen
        hword ha hlr.1 hlr.2 hnext
    · exact bankWordRowIone ring root q e hne hgen hword ha herase hnext
  · exact bankWordRowIzero ring root q e hne hfix hgen hword ha
      (hresp ha) hnext

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 12000 in
/-- The clean W clock on BANK rings, with no remaining
premise.  Consumer: the group 7 clean finish. -/
theorem bankWordCleanWordClockOfBank {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    :
    BankWordCleanWordClock ring hbank :=
  bankWordCleanWordClockOfRows ring hn hbank
    (bankWordRowTransport ring hn hbank)

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankWordSerSourceNonvalidating
#print axioms L3.RenewalReferenceClock.bankWordSerLeaderResponderNonvalidating
#print axioms L3.RenewalReferenceClock.bankWordSerHardAcceptSourceCurrent
#print axioms L3.RenewalReferenceClock.bankWordPhiSource
#print axioms L3.RenewalReferenceClock.bankWordPhiTarget
#print axioms L3.RenewalReferenceClock.bankWordPostLeaderSourceRoot
#print axioms L3.RenewalReferenceClock.bankWordPostResponderLeader
#print axioms L3.RenewalReferenceClock.bankWordHardSOnePostLeader
#print axioms L3.RenewalReferenceClock.bankWordHardAcceptPostLeader
#print axioms L3.RenewalReferenceClock.bankWordFutureWaveStep
#print axioms L3.RenewalReferenceClock.bankWordFutureAcceptClean
#print axioms L3.RenewalReferenceClock.bankWordFutureAcceptPair
#print axioms L3.RenewalReferenceClock.bankWordEpochCompletedRetired
#print axioms L3.RenewalReferenceClock.bankWordCompletionFutureReachable
#print axioms L3.RenewalReferenceClock.bankWordCompletionFutureWave
#print axioms L3.RenewalReferenceClock.generatedControlTransportOfRows
#print axioms L3.RenewalReferenceClock.bankWordCleanWordClockOfRows
#print axioms L3.RenewalReferenceClock.bankWordCwBitEq
#print axioms L3.RenewalReferenceClock.bankWordCwSumOrEq
#print axioms L3.RenewalReferenceClock.bankWordCwSumParityEq
#print axioms L3.RenewalReferenceClock.bankWordCwSumTrailingEq
#print axioms L3.RenewalReferenceClock.bankWordCwPrefixOrEq
#print axioms L3.RenewalReferenceClock.bankWordCwPrefixAndEq
#print axioms L3.RenewalReferenceClock.bankWordSumCursorCongr
#print axioms L3.RenewalReferenceClock.bankWordBackCursorCongr
#print axioms L3.RenewalReferenceClock.bankWordBusyTargetCongr
#print axioms L3.RenewalReferenceClock.bankWordGeneratedControlErase
#print axioms L3.RenewalReferenceClock.bankWordSiFrameRow
#print axioms L3.RenewalReferenceClock.bankWordSiStuckSumRow
#print axioms L3.RenewalReferenceClock.bankWordFrameTransport
#print axioms L3.RenewalReferenceClock.bankWordSiteOffset
#print axioms L3.RenewalReferenceClock.bankWordLeftOfSite
#print axioms L3.RenewalReferenceClock.bankWordOffsetOfRightRoot
#print axioms L3.RenewalReferenceClock.bankWordOffsetRight
#print axioms L3.RenewalReferenceClock.bankWordSiteNeRoot
#print axioms L3.RenewalReferenceClock.bankWordRowIzero
#print axioms L3.RenewalReferenceClock.bankWordRowIone
#print axioms L3.RenewalReferenceClock.bankWordRowQuietBackMove
#print axioms L3.RenewalReferenceClock.bankWordRowQuietBackInit
#print axioms L3.RenewalReferenceClock.bankWordRowQuietSumMove
#print axioms L3.RenewalReferenceClock.bankWordRowQuietAdvance
#print axioms L3.RenewalReferenceClock.bankWordPhiSISource
#print axioms L3.RenewalReferenceClock.bankWordPhiSITarget
#print axioms L3.RenewalReferenceClock.bankWordGCOfPair
#print axioms L3.RenewalReferenceClock.bankWordRowBack
#print axioms L3.RenewalReferenceClock.bankWordRowSumMoveResult
#print axioms L3.RenewalReferenceClock.bankWordRowSumPublishResult
#print axioms L3.RenewalReferenceClock.bankWordSumSourceBit
#print axioms L3.RenewalReferenceClock.bankWordRowSum
#print axioms L3.RenewalReferenceClock.bankWordRowOrphanBack
#print axioms L3.RenewalReferenceClock.bankWordRowOrphanSum
#print axioms L3.RenewalReferenceClock.bankWordRowReady
#print axioms L3.RenewalReferenceClock.bankWordRowLoneBusy
#print axioms L3.RenewalReferenceClock.bankWordRowPrefix
#print axioms L3.RenewalReferenceClock.bankWordRowQuiet
#print axioms L3.RenewalReferenceClock.bankWordRowTransport
#print axioms L3.RenewalReferenceClock.bankWordCleanWordClockOfBank
