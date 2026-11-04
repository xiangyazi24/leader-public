import Leader.L3.Bank.WordRenewalFrontier

/-!
R10a S-frontier closure: the all-edges step of the rooted soft shape
with the position/nomination claim, and the unconditional word
induction.
-/
namespace L3.RenewalReferenceClock

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- At an actual ROOT_OUT service with a non-REQUESTED B/DONE
    source and B responder, S2R frames all physical serializer
    records even though eX.l=true. Consumer: active covered
    B/DONE+B forward/return prefix row of R10a hfail. -/
theorem bankWordRenewalSoftOutgoingCoveredDoneFrame {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankWordEpochState n) (hn : 5 ≤ n)
    (hsourceB : (z.2.1 e).ser.phase = .B)
    (hsourceDone : (z.2.1 e).ser.out = .DONE)
    (htargetB : (z.2.1 (ring.rightNeighbor e)).ser.phase = .B)
    (hnotRequested : (z.2.1 e).ser.cert ≠ .REQUESTED)
    (hx : (postW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).eX.l = true)
    (hy : (postW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).eY.l = false)
    (hshape : BankWordRenewalSoftShape ring root z) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z e) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z e) =
        bankWordRenewalSoftRootedPosition ring root z := by
  have hne : ring.rightNeighbor e ≠ e :=
    L3.EWord.rightNeighborDifferent ring (by omega) e
  have hpair :
      (serW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).x =
        (z.2.1 e).ser ∧
      (serW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).y =
        (z.2.1 (ring.rightNeighbor e)).ser := by
    simp [serW, serializerStep, ProjW.lift,
      hx, hy, hsourceB, hsourceDone, htargetB,
      hnotRequested]
  have hserial (i : Fin n) :
      ((bankWordEpochNext ring root z e).2.1 i).ser =
        (z.2.1 i).ser := by
    by_cases hi : i = e
    · rw [hi]
      change ((phiW ring z.2.1 e) e).ser = _
      rw [phiW_ser_source]
      exact hpair.1
    · by_cases hj : i = ring.rightNeighbor e
      · rw [hj]
        change ((phiW ring z.2.1 e)
          (ring.rightNeighbor e)).ser = _
        rw [phiW_ser_target ring z.2.1 e hne]
        exact hpair.2
      · change ((phiW ring z.2.1 e) i).ser = _
        exact phiW_ser_remote ring z.2.1 e i hi hj
  have hforward (p : Nat)
      (hf : BankWordRenewalSoftForwardShape ring root z p) :
      BankWordRenewalSoftForwardShape ring root
        (bankWordEpochNext ring root z e) p := by
    refine {
      pivotBound := hf.pivotBound
      completed := ?_
      parentPhase := ?_
      parentCurrent := ?_
      front := ?_ }
    · intro j hj
      simpa only [hserial (L3.EWord.site ring root j)] using
        hf.completed j hj
    · simpa only [hserial (L3.EWord.site ring root p)] using
        hf.parentPhase
    · simpa only [hserial (L3.EWord.site ring root p)] using
        hf.parentCurrent
    · simpa only [hserial (L3.EWord.site ring root p),
        hserial (L3.EWord.site ring root (p + 1))] using hf.front
  have hreturn (q : Nat)
      (hr : BankWordRenewalSoftReturnShape ring root z q) :
      BankWordRenewalSoftReturnShape ring root
        (bankWordEpochNext ring root z e) q := by
    refine {
      pivotBound := hr.pivotBound
      rootRunning := ?_
      rootPhase := ?_
      rootDone := ?_
      rootCurrent := ?_
      completed := ?_
      leftmostPhase := ?_
      leftmostWphase := ?_
      suffix := ?_ }
    · simpa only [hserial root] using hr.rootRunning
    · simpa only [hserial root] using hr.rootPhase
    · simpa only [hserial root] using hr.rootDone
    · simpa only [hserial root] using hr.rootCurrent
    · intro j hj
      simpa only [hserial (L3.EWord.site ring root j)] using
        hr.completed j hj
    · simpa only [hserial (L3.EWord.site ring root (q + 1))]
        using hr.leftmostPhase
    · simpa only [hserial (L3.EWord.site ring root (q + 1))]
        using hr.leftmostWphase
    · intro j hj hjn
      simpa only [hserial (L3.EWord.site ring root j)] using
        hr.suffix j hj hjn
  have hnewShape :
      BankWordRenewalSoftShape ring root
        (bankWordEpochNext ring root z e) := by
    intro hactiveNew
    have hactiveOld :
        (z.2.1 root).ser.cert = .RUNNING ∧
        (z.2.1 root).ser.phase = .B ∧
        (z.2.1 root).ser.wphase = .CURRENT := by
      simpa only [hserial root] using hactiveNew
    rcases hshape hactiveOld with ⟨p, hf⟩ | ⟨q, hr⟩
    · exact Or.inl ⟨p, hforward p hf⟩
    · exact Or.inr ⟨q, hreturn q hr⟩
  have hpos :
      bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z e) =
      bankWordRenewalSoftRootedPosition ring root z := by
    simp [bankWordRenewalSoftRootedPosition, hserial]
  exact ⟨hnewShape, hpos⟩

/-- On any INTERNAL edge strictly in the return suffix, S3/S4
    preserves the source's phase and wphase and either frames or
    canonicalizes the responder to C/OFF. The first returning F
    is never erased, and the paid position stays n-1.
    Consumer: returning F/C suffix case of R10a S-frontier. -/
theorem bankWordRenewalSoftReturnSuffixStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s)
    (q k : Nat) (hn : 5 ≤ n)
    (hr : BankWordRenewalSoftReturnShape ring root z.1 q)
    (hafter : q < k) (hinside : k + 1 < n)
    (hx : (postW
      (z.1.2.1 (L3.EWord.site ring root k))
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root k)))).eX.l = false)
    (hy : (postW
      (z.1.2.1 (L3.EWord.site ring root k))
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root k)))).eY.l = false) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root k)) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root k)) =
      bankWordRenewalSoftRootedPosition ring root z.1 ∧
    bankWordRenewalSoftRootedChosen ring root s z = root ∧
    L3.EWord.site ring root k ≠
      bankWordRenewalSoftRootedChosen ring root s z := by
  have hkn : k < n := by omega
  have hsourcePhase :
      (z.1.2.1 (L3.EWord.site ring root k)).ser.phase = .F ∨
      (z.1.2.1 (L3.EWord.site ring root k)).ser.phase = .C := by
    by_cases hfirst : k = q + 1
    · left
      rw [hfirst]
      exact hr.leftmostPhase
    · rcases hr.suffix k (by omega) hkn with hf | hc
      · exact Or.inl hf.1
      · exact Or.inr hc.1
  have hsourceWphase :
      ((z.1.2.1 (L3.EWord.site ring root k)).ser.phase = .F ∧
        (z.1.2.1 (L3.EWord.site ring root k)).ser.wphase =
          (if k + 1 = n then .OFF else .CURRENT)) ∨
      ((z.1.2.1 (L3.EWord.site ring root k)).ser.phase = .C ∧
        (z.1.2.1 (L3.EWord.site ring root k)).ser.wphase =
          .OFF) := by
    by_cases hfirst : k = q + 1
    · left
      constructor
      · rw [hfirst]
        exact hr.leftmostPhase
      · rw [hfirst]
        exact hr.leftmostWphase
    · exact hr.suffix k (by omega) hkn
  have hne :
      ring.rightNeighbor (L3.EWord.site ring root k) ≠
        L3.EWord.site ring root k :=
    L3.EWord.rightNeighborDifferent ring (by omega)
      (L3.EWord.site ring root k)
  have hsourcePhaseNew :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root k)).2.1
          (L3.EWord.site ring root k)).ser.phase =
      (z.1.2.1 (L3.EWord.site ring root k)).ser.phase := by
    change ((phiW ring z.1.2.1
      (L3.EWord.site ring root k))
      (L3.EWord.site ring root k)).ser.phase = _
    rw [phiW_ser_source]
    rcases hsourcePhase with hF | hC
    · cases htarget :
        (z.1.2.1 (ring.rightNeighbor
          (L3.EWord.site ring root k))).ser.phase <;>
        simp [serW, serializerStep, ProjW.lift,
          hx, hy, hF, htarget]
    · cases htarget :
        (z.1.2.1 (ring.rightNeighbor
          (L3.EWord.site ring root k))).ser.phase <;>
        simp [serW, serializerStep, ProjW.lift,
          hx, hy, hC, htarget] <;>
        split <;> simp [hC]
  have hsourceWphaseNew :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root k)).2.1
          (L3.EWord.site ring root k)).ser.wphase =
      (z.1.2.1 (L3.EWord.site ring root k)).ser.wphase := by
    change ((phiW ring z.1.2.1
      (L3.EWord.site ring root k))
      (L3.EWord.site ring root k)).ser.wphase = _
    rw [phiW_ser_source]
    rcases hsourcePhase with hF | hC
    · cases htarget :
        (z.1.2.1 (ring.rightNeighbor
          (L3.EWord.site ring root k))).ser.phase <;>
        simp [serW, serializerStep, ProjW.lift,
          hx, hy, hF, htarget]
    · cases htarget :
        (z.1.2.1 (ring.rightNeighbor
          (L3.EWord.site ring root k))).ser.phase <;>
        simp [serW, serializerStep, ProjW.lift,
          hx, hy, hC, htarget] <;>
        split <;> simp [hC]
  have htargetOld :
      ((z.1.2.1 (L3.EWord.site ring root (k + 1))).ser.phase =
          .F ∧
        (z.1.2.1 (L3.EWord.site ring root (k + 1))).ser.wphase =
          (if k + 2 = n then .OFF else .CURRENT)) ∨
      ((z.1.2.1 (L3.EWord.site ring root (k + 1))).ser.phase =
          .C ∧
        (z.1.2.1 (L3.EWord.site ring root (k + 1))).ser.wphase =
          .OFF) := by
    exact hr.suffix (k + 1) (by omega) hinside
  have htargetNew :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root k)).2.1
          (L3.EWord.site ring root (k + 1))).ser.phase = .C ∧
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root k)).2.1
          (L3.EWord.site ring root (k + 1))).ser.wphase =
          .OFF := by
    rw [← L3.EWord.siteSuccessor ring root k]
    change
      ((phiW ring z.1.2.1
        (L3.EWord.site ring root k))
        (ring.rightNeighbor (L3.EWord.site ring root k))).ser.phase =
          .C ∧
      ((phiW ring z.1.2.1
        (L3.EWord.site ring root k))
        (ring.rightNeighbor (L3.EWord.site ring root k))).ser.wphase =
          .OFF
    rw [phiW_ser_target ring z.1.2.1
      (L3.EWord.site ring root k) hne]
    have htargetFOrC :
        (z.1.2.1 (ring.rightNeighbor
          (L3.EWord.site ring root k))).ser.phase = .F ∨
        ((z.1.2.1 (ring.rightNeighbor
          (L3.EWord.site ring root k))).ser.phase = .C ∧
         (z.1.2.1 (ring.rightNeighbor
          (L3.EWord.site ring root k))).ser.wphase = .OFF) := by
      rw [L3.EWord.siteSuccessor]
      rcases htargetOld with hf | hc
      · exact Or.inl hf.1
      · exact Or.inr hc
    rcases hsourcePhase with hsF | hsC
    · rcases htargetFOrC with htF | htC
      · simp [serW, serializerStep, ProjW.lift,
          serCanonicalC, hx, hy, hsF, htF]
      · simp [serW, serializerStep, ProjW.lift,
          hx, hy, hsF, htC.1, htC.2]
    · rcases htargetFOrC with htF | htC
      · simp [serW, serializerStep, ProjW.lift,
          serCanonicalC, hx, hy, hsC, htF]
      · simp [serW, serializerStep, ProjW.lift,
          hx, hy, hsC, htC.1, htC.2]
  have hframe (j : Nat) (hj : j < n)
      (hjk : j ≠ k) (hjkNext : j ≠ k + 1) :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root k)).2.1
          (L3.EWord.site ring root j)).ser =
      (z.1.2.1 (L3.EWord.site ring root j)).ser := by
    have hsourceNe :
        L3.EWord.site ring root j ≠
          L3.EWord.site ring root k := by
      intro h
      have hi := L3.EWord.validationSiteInjective
        ring root j k hj hkn h
      exact hjk hi
    have htargetNe :
        L3.EWord.site ring root j ≠
          ring.rightNeighbor (L3.EWord.site ring root k) := by
      rw [L3.EWord.siteSuccessor]
      intro h
      have hi := L3.EWord.validationSiteInjective
        ring root j (k + 1) hj hinside h
      exact hjkNext hi
    change ((phiW ring z.1.2.1
      (L3.EWord.site ring root k))
      (L3.EWord.site ring root j)).ser = _
    exact phiW_ser_remote ring z.1.2.1
      (L3.EWord.site ring root k)
      (L3.EWord.site ring root j) hsourceNe htargetNe
  have hrootSer :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root k)).2.1 root).ser =
      (z.1.2.1 root).ser := by
    simpa only [L3.EWord.siteZero] using
      hframe 0 (by omega) (by omega) (by omega)
  have hnextActive :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root k)).2.1 root).ser.cert =
          .RUNNING ∧
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root k)).2.1 root).ser.phase =
          .B ∧
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root k)).2.1 root).ser.wphase =
          .CURRENT := by
    simpa only [hrootSer] using
      (And.intro hr.rootRunning
        (And.intro hr.rootPhase hr.rootCurrent))
  have hrnew : BankWordRenewalSoftReturnShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root k)) q := by
    refine {
      pivotBound := hr.pivotBound
      rootRunning := hnextActive.1
      rootPhase := hnextActive.2.1
      rootDone := ?_
      rootCurrent := hnextActive.2.2
      completed := ?_
      leftmostPhase := ?_
      leftmostWphase := ?_
      suffix := ?_ }
    · simpa only [hrootSer] using hr.rootDone
    · intro j hj
      rw [hframe j (by omega) (by omega) (by omega)]
      exact hr.completed j hj
    · by_cases hfirst : k = q + 1
      · have hsource :
            (z.1.2.1 (L3.EWord.site ring root k)).ser.phase =
              .F := by
          rw [hfirst]
          exact hr.leftmostPhase
        rw [← hfirst, hsourcePhaseNew]
        exact hsource
      · rw [hframe (q + 1) hr.pivotBound (by omega) (by omega)]
        exact hr.leftmostPhase
    · by_cases hfirst : k = q + 1
      · have hsource :
            (z.1.2.1 (L3.EWord.site ring root k)).ser.wphase =
              (if q + 2 = n then .OFF else .CURRENT) := by
          rw [hfirst]
          exact hr.leftmostWphase
        rw [← hfirst, hsourceWphaseNew]
        exact hsource
      · rw [hframe (q + 1) hr.pivotBound (by omega) (by omega)]
        exact hr.leftmostWphase
    · intro j hj hjn
      by_cases hsource : j = k
      · rw [hsource]
        have hold := hr.suffix k (by omega) hkn
        rcases hold with hf | hc
        · left
          exact ⟨(by simpa only [hsourcePhaseNew] using hf.1),
            (by simpa only [hsourceWphaseNew] using hf.2)⟩
        · right
          exact ⟨(by simpa only [hsourcePhaseNew] using hc.1),
            (by simpa only [hsourceWphaseNew] using hc.2)⟩
      · by_cases htarget : j = k + 1
        · rw [htarget]
          exact Or.inr htargetNew
        · rw [hframe j hjn hsource htarget]
          exact hr.suffix j hj hjn
  have hidxOld := bankWordRenewalSoftReturnIndex
    ring root z.1 q hr
  have hidxNew := bankWordRenewalSoftReturnIndex
    ring root (bankWordEpochNext ring root z.1
      (L3.EWord.site ring root k)) q hrnew
  have hactive :
      (z.1.2.1 root).ser.cert = .RUNNING ∧
      (z.1.2.1 root).ser.phase = .B ∧
      (z.1.2.1 root).ser.wphase = .CURRENT :=
    ⟨hr.rootRunning, hr.rootPhase, hr.rootCurrent⟩
  have hposOld :
      bankWordRenewalSoftRootedPosition ring root z.1 =
        n - 1 := by
    simp [bankWordRenewalSoftRootedPosition,
      hactive, hidxOld, hr.pivotBound, hr.leftmostPhase]
  have hposNew :
      bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z.1
          (L3.EWord.site ring root k)) = n - 1 := by
    simp [bankWordRenewalSoftRootedPosition,
      hnextActive, hidxNew, hrnew.pivotBound, hrnew.leftmostPhase]
  have hchosen := bankWordRenewalSoftReturnNomination
    ring root s z q hr
  have hsourceNotRoot :
      L3.EWord.site ring root k ≠ root :=
    L3.EWord.validationPositiveSiteNotRoot
      ring root k hkn (by omega)
  refine ⟨(by intro _; exact Or.inr ⟨q, hrnew⟩),
    hposNew.trans hposOld.symm, hchosen, ?_⟩
  rw [hchosen]
  exact hsourceNotRoot

/-- R10a S-frontier physical row; consumer: all-edges closure. -/
theorem bankWordRenewalSoftReturnIncomingStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordRenewalPostSOne ring root s)
    (q : Nat) (hr : BankWordRenewalSoftReturnShape ring root z.1 q) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))) =
      bankWordRenewalSoftRootedPosition ring root z.1 ∧
    (bankWordEpochSelectedReceipt ring z.1
      (L3.EWord.site ring root (n - 1))).serializer.row =
        "S5" := by
  have hpred :
      ring.rightNeighbor (L3.EWord.site ring root (n - 1)) =
        root :=
    L3.EWord.validationSeamNeighbor ring root
      (L3.EWord.site ring root (n - 1)) rfl
  have hsourceNonroot :=
    L3.EWord.validationSeamNotRoot ring root
      (L3.EWord.site ring root (n - 1)) (by omega : 3 ≤ n) rfl
  have hflags := bankWordRenewalSoftIncomingFlags
    ring root (L3.EWord.site ring root (n - 1))
    s hn hbank hs z hsourceNonroot hpred
  have hstep := bankWordRenewalSoftRootIncomingReturnStep
    ring root s z q hn hr hflags.1 hflags.2
  have hrows := bankWordRenewalSoftIncomingRowCensus
    ring root (L3.EWord.site ring root (n - 1))
    s hn hbank hs z hpred
  have hrow :
      (bankWordEpochSelectedReceipt ring z.1
        (L3.EWord.site ring root (n - 1))).serializer.row =
          "S5" := by
    rcases hrows with hzero | hfive
    · have hbad : SerCert.RUNNING = SerCert.IDLE :=
        hr.rootRunning.symm.trans hzero.1
      cases hbad
    · exact hfive.2
  exact ⟨hstep.1, hstep.2.1, hrow⟩

/-- A returning soft lap is closed under every selected physical
    edge, including nonpivot B/DONE+B frames, the leftmost
    returning-F retreat, S3/S4 suffix sanitation, incoming S5,
    and the final ROOT_OUT soft S6 reset. Consumer: return branch
    of bankWordRenewalSoftShapeStep, R10a hfail. -/
theorem bankWordRenewalSoftReturnAllEdgesStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordRenewalPostSOne ring root s)
    (e : Fin n) (q : Nat)
    (hr : BankWordRenewalSoftReturnShape ring root z.1 q) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1 e) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1 e) ≤
      bankWordRenewalSoftRootedPosition ring root z.1 + 1 ∧
    (bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z.1 e) ≠
      bankWordRenewalSoftRootedPosition ring root z.1 →
      e = bankWordRenewalSoftRootedChosen ring root s z) := by
  have hshape : BankWordRenewalSoftShape ring root z.1 := by
    intro _
    exact Or.inr ⟨q, hr⟩
  rcases bankWordRenewalSoftReturnEdgeCases
      ring root e z.1 q hn hr with hroot | hseam | hinter
  · subst e
    by_cases hzero : q = 0
    · have hrootReturn :
          BankWordRenewalSoftReturnShape ring root z.1 0 := by
        simpa only [hzero] using hr
      exact bankWordRenewalSoftRootFinishStep
        ring root s hn hbank hs z hrootReturn
    · have hqpos : 0 < q := by omega
      have hrootOld := hr.completed 0 (by omega)
      have hchildOld := hr.completed 1 (by omega)
      have hrootB : (z.1.2.1 root).ser.phase = .B :=
        hr.rootPhase
      have hrootDone : (z.1.2.1 root).ser.out = .DONE := by
        simpa only [L3.EWord.siteZero] using hrootOld.2.1
      have hchildB :
          (z.1.2.1 (ring.rightNeighbor root)).ser.phase =
            .B := by
        simpa only [L3.EWord.siteOne] using hchildOld.1
      have hnotReq : (z.1.2.1 root).ser.cert ≠ .REQUESTED := by
        intro h
        have hbad := hr.rootRunning.symm.trans h
        cases hbad
      have hflags := bankWordRenewalSoftOutgoingFlags
        ring root s hn hbank hs z
      have hframe := bankWordRenewalSoftOutgoingCoveredDoneFrame
        ring root root z.1 hn hrootB hrootDone hchildB
        hnotReq hflags.1 hflags.2 hshape
      refine ⟨hframe.1, ?_, ?_⟩
      · rw [hframe.2]
        omega
      · intro hneq
        exact False.elim (hneq hframe.2)
  · rcases hseam with ⟨he, _⟩
    subst e
    have hstep := bankWordRenewalSoftReturnIncomingStep
      ring root s hn hbank hs z q hr
    refine ⟨hstep.1, ?_, ?_⟩
    · rw [hstep.2.1]
      omega
    · intro hneq
      exact False.elim (hneq hstep.2.1)
  · rcases hinter with ⟨k, hkpos, hinside, he, hclass⟩
    subst e
    rcases hclass with hcovered | hpivot | hsuffix
    · have hstep := bankWordRenewalSoftReturnCoveredStep
        ring root s hn hbank hs z q k hr hshape hkpos
        hcovered.1
      refine ⟨hstep.1, ?_, ?_⟩
      · rw [hstep.2.1]
        omega
      · intro hneq
        exact False.elim (hneq hstep.2.1)
    · have hqpositive : 0 < q := by
        omega
      have hrow := bankWordRenewalSoftReturnParentStep
        ring root s hn hbank hs z q hqpositive hr
      have hk : k = q := hpivot.1
      subst k
      exact hrow
    · have hsourceNotRoot :
          L3.EWord.site ring root k ≠ root :=
        L3.EWord.validationPositiveSiteNotRoot
          ring root k (by omega) hkpos
      have htargetNotRoot :
          ring.rightNeighbor (L3.EWord.site ring root k) ≠
            root := by
        rw [L3.EWord.siteSuccessor]
        exact L3.EWord.validationPositiveSiteNotRoot
          ring root (k + 1) hinside (by omega)
      have hflags := bankWordRenewalSoftInternalFlags
        ring root (L3.EWord.site ring root k)
        s hn hbank hs z hsourceNotRoot htargetNotRoot
      have hstep := bankWordRenewalSoftReturnSuffixStep
        ring root s z q k hn hr hsuffix.1 hinside
        hflags.1 hflags.2
      refine ⟨hstep.1, ?_, ?_⟩
      · rw [hstep.2.1]
        omega
      · intro hneq
        exact False.elim (hneq hstep.2.1)

/-- R10a S-frontier physical row; consumer: all-edges closure. -/
theorem bankWordRenewalSoftForwardParentStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordRenewalPostSOne ring root s)
    (p : Nat) (hp : 0 < p)
    (hf : BankWordRenewalSoftForwardShape ring root z.1 p)
    (hrun : (z.1.2.1 root).ser.cert = .RUNNING) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root p)) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root p)) ≤
      bankWordRenewalSoftRootedPosition ring root z.1 + 1 ∧
    (bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z.1
          (L3.EWord.site ring root p)) ≠
      bankWordRenewalSoftRootedPosition ring root z.1 →
      L3.EWord.site ring root p =
        bankWordRenewalSoftRootedChosen ring root s z) := by
  have hpn : p < n := by
    have hb := hf.pivotBound
    omega
  have hsourceNonroot :=
    L3.EWord.validationPositiveSiteNotRoot ring root p hpn hp
  have htargetNonroot :
      ring.rightNeighbor (L3.EWord.site ring root p) ≠
        root := by
    rw [L3.EWord.siteSuccessor]
    exact L3.EWord.validationPositiveSiteNotRoot
      ring root (p + 1) hf.pivotBound (by omega)
  have hflags := bankWordRenewalSoftInternalFlags
    ring root (L3.EWord.site ring root p)
    s hn hbank hs z hsourceNonroot htargetNonroot
  have hrootOld := hf.completed 0 hp
  have hrootPhase : (z.1.2.1 root).ser.phase = .B := by
    simpa only [L3.EWord.siteZero] using hrootOld.1
  have hrootCurrent : (z.1.2.1 root).ser.wphase =
      .CURRENT := by
    simpa only [L3.EWord.siteZero] using hrootOld.2.2
  have hactive :
      (z.1.2.1 root).ser.cert = .RUNNING ∧
      (z.1.2.1 root).ser.phase = .B ∧
      (z.1.2.1 root).ser.wphase = .CURRENT :=
    ⟨hrun, hrootPhase, hrootCurrent⟩
  rcases hf.front with hzero | hpositive
  · have hbad : False := by
      omega
    exact False.elim hbad
  · rcases hpositive.2 with hnew | hwaiting
    · have hstep := bankWordRenewalSoftForwardChallengeStep
        ring root s z p hn hp hf hrun hnew hflags.1 hflags.2
      refine ⟨hstep.1, ?_, ?_⟩
      · rw [hstep.2.1, hstep.2.2.1]
        omega
      · intro _
        exact hstep.2.2.2.symm
    · rcases hwaiting.2 with hpending | hinternal | hleaf
      · have hstep := bankWordRenewalSoftInternalPendingStall
          ring root s z p hn hp hf hactive hwaiting.1
          hpending.1 hpending.2.1 hflags.1 hflags.2
        refine ⟨hstep.1, ?_, ?_⟩
        · rw [hstep.2.1]
          omega
        · intro hne
          exact False.elim (hne hstep.2.1)
      · have hstep := bankWordRenewalSoftInternalAdmissionStep
          ring root s z p hn hp hf hrun hinternal.1
          hwaiting.1 hinternal.2.1 hinternal.2.2.1
          hflags.1 hflags.2
        refine ⟨hstep.1, ?_, ?_⟩
        · rw [hstep.2.1, hstep.2.2.1]
          omega
        · intro hne
          have heq := hstep.2.1.trans hstep.2.2.1.symm
          exact False.elim (hne heq)
      · have hpLast : p = n - 2 := by
          have hfull := hleaf.1
          omega
        subst p
        have hsub : n - 2 + 1 = n - 1 := by omega
        have hchildC :
            (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.phase = .C := by
          simpa only [hsub] using hleaf.2.1
        have hchildLeaf :
            (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.probe =
              .LEAF_OK := by
          simpa only [hsub] using hleaf.2.2.1
        have hchildOff :
            (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.wphase =
              .OFF := by
          simpa only [hsub] using hleaf.2.2.2
        have hstep := bankWordRenewalSoftLeafAdmissionStep
          ring root s z hn hf hrun hwaiting.1
          hchildC hchildLeaf hchildOff hflags.1 hflags.2
        refine ⟨hstep.1, ?_, ?_⟩
        · rw [hstep.2.1, hstep.2.2.1]
          omega
        · intro hne
          have heq := hstep.2.1.trans hstep.2.2.1.symm
          exact False.elim (hne heq)

/-- INTERNAL forward suffix services do not write the rooted
    frontier. Such an edge is not the old nominated pivot.
    Consumer: unrestricted S2N/S3/S4 suffix branch in the
    R10a all-edge position/nomination induction. -/
theorem bankWordRenewalSoftForwardSuffixStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s)
    (p k : Nat)
    (hf : BankWordRenewalSoftForwardShape ring root z.1 p)
    (hactive :
      (z.1.2.1 root).ser.cert = .RUNNING ∧
      (z.1.2.1 root).ser.phase = .B ∧
      (z.1.2.1 root).ser.wphase = .CURRENT)
    (hfar : p + 1 < k)
    (hinside : k + 1 < n) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root k)) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root k)) =
      bankWordRenewalSoftRootedPosition ring root z.1 ∧
    L3.EWord.site ring root k ≠
      bankWordRenewalSoftRootedChosen ring root s z := by
  have hstep := bankWordRenewalSoftSuffixFrameStep
    ring root s z p k hf hactive hfar hinside
  have hk : k < n := by omega
  have hp : p < n := by
    have hh := hf.pivotBound
    omega
  have hne :
      L3.EWord.site ring root k ≠
        L3.EWord.site ring root p := by
    intro h
    have heq := L3.EWord.validationSiteInjective
      ring root k p hk hp h
    omega
  refine ⟨hstep.1, hstep.2.1, ?_⟩
  rw [hstep.2.2]
  exact hne

/-- An inactive ROOT_OUT B/S2R service cannot create RUNNING/B/CURRENT
    without a REQUESTED S1. A genuine S6 instead makes IDLE/C.
    Consumer: inactive ROOT_OUT B row of the all-edge R10a induction. -/
theorem bankWordRenewalSoftInactiveRootOutgoingBStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordRenewalPostSOne ring root s)
    (hsourceB : (z.1.2.1 root).ser.phase = .B)
    (hnotRequested : (z.1.2.1 root).ser.cert ≠ .REQUESTED)
    (hinactive :
      ¬ ((z.1.2.1 root).ser.cert = .RUNNING ∧
        (z.1.2.1 root).ser.phase = .B ∧
        (z.1.2.1 root).ser.wphase = .CURRENT)) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1 root) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1 root) =
      bankWordRenewalSoftRootedPosition ring root z.1 := by
  have hflags := bankWordRenewalSoftOutgoingFlags
    ring root s hn hbank hs z
  have hrootSer :
      ((bankWordEpochNext ring root z.1 root).2.1 root).ser =
        (serW (z.1.2.1 root)
          (z.1.2.1 (ring.rightNeighbor root))).x := by
    change ((phiW ring z.1.2.1 root) root).ser = _
    rw [phiW_ser_source]
  have hnextInactive :
      ¬ (((bankWordEpochNext ring root z.1 root).2.1 root).ser.cert =
          .RUNNING ∧
        ((bankWordEpochNext ring root z.1 root).2.1 root).ser.phase =
          .B ∧
        ((bankWordEpochNext ring root z.1 root).2.1 root).ser.wphase =
          .CURRENT) := by
    intro hnext
    rw [hrootSer] at hnext
    cases htarget :
      (z.1.2.1 (ring.rightNeighbor root)).ser.phase <;>
      cases hout : (z.1.2.1 root).ser.out <;>
      simp [serW, serializerStep, ProjW.lift,
        hflags.1, hflags.2, hsourceB, hnotRequested,
        htarget, hout] at hnext <;>
      first
        | exact hinactive hnext
        | exact hinactive ⟨hnext.1, hsourceB, hnext.2⟩
        | (apply hinactive
           repeat' (split at hnext)
           all_goals (try simp only [serChallengeWrite] at hnext)
           all_goals first
             | exact hnext
             | exact ⟨hnext.1, hsourceB, hnext.2⟩
             | exact ⟨hnext.1, hsourceB, hnext.2.2⟩)
  have hposOld :
      bankWordRenewalSoftRootedPosition ring root z.1 = 0 := by
    simp [bankWordRenewalSoftRootedPosition, hinactive]
  have hposNew :
      bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z.1 root) = 0 := by
    simp [bankWordRenewalSoftRootedPosition, hnextInactive]
  exact ⟨(by intro h; exact False.elim (hnextInactive h)),
    hposNew.trans hposOld.symm⟩

/-- The rooted forward geometry partitions every selected source
    into ROOT_OUT, ROOT_IN, covered B/DONE+B, the active parent,
    the observed child, or an unrestricted later suffix.
    The B facts are derived from N's forward certificate.
    Consumer: the forward branch of bankWordRenewalSoftShapeStep. -/
theorem bankWordRenewalSoftForwardEdgeCases {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankWordEpochState n)
    (p : Nat) (hn : 5 ≤ n)
    (hf : BankWordRenewalSoftForwardShape ring root z p) :
    e = root ∨
    (e = L3.EWord.site ring root (n - 1) ∧
      ring.rightNeighbor e = root) ∨
    (∃ k : Nat, 0 < k ∧ k + 1 < n ∧
      e = L3.EWord.site ring root k ∧
      ((k + 1 ≤ p ∧
         (z.2.1 (L3.EWord.site ring root k)).ser.phase = .B ∧
         (z.2.1 (L3.EWord.site ring root k)).ser.out = .DONE ∧
         (z.2.1 (ring.rightNeighbor
           (L3.EWord.site ring root k))).ser.phase = .B) ∨
       (k = p ∧
         (z.2.1 (L3.EWord.site ring root k)).ser.phase = .B) ∨
       k = p + 1 ∨ p + 1 < k)) := by
  rcases bankWordRenewalSoftEdgeGeometry ring root e hn with
    hroot | hseam | hinter
  · exact Or.inl hroot
  · exact Or.inr (Or.inl hseam)
  · rcases hinter with ⟨k, hkpositive, hknext, he, _, _⟩
    right
    right
    refine ⟨k, hkpositive, hknext, he, ?_⟩
    by_cases hcovered : k + 1 ≤ p
    · left
      obtain ⟨hb, hd, _, hc, _, _⟩ :=
        bankWordRenewalSoftForwardCoveredSource
          ring root z p k hf hkpositive hcovered
      exact ⟨hcovered, hb, hd, hc⟩
    · right
      by_cases hparent : k = p
      · left
        constructor
        · exact hparent
        · rw [hparent]
          exact hf.parentPhase
      · right
        by_cases hchild : k = p + 1
        · left
          exact hchild
        · right
          omega

/-- R10a S-frontier physical row; consumer: all-edges closure. -/
theorem bankWordRenewalSoftInternalRowCensus {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordRenewalPostSOne ring root s)
    (he : e ≠ root) (hj : ring.rightNeighbor e ≠ root) :
    ((z.1.2.1 e).ser.phase = .B ∧
      (bankWordEpochSelectedReceipt ring z.1 e).serializer.row =
        "S2N") ∨
    ((z.1.2.1 e).ser.phase = .C ∧
      (bankWordEpochSelectedReceipt ring z.1 e).serializer.row =
        "S3") ∨
    ((z.1.2.1 e).ser.phase = .F ∧
      (bankWordEpochSelectedReceipt ring z.1 e).serializer.row =
        "S4") := by
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z.1 z.2.1
  have hfixed : WFixedRoot ring root (phiW ring z.1.2.1 e) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.1.2.1 hclass e).2
  have hpost := clockPostInternal ring root z.1.2.1 e
    (by omega : 2 ≤ n) hfixed he hj
  cases hp : (z.1.2.1 e).ser.phase with
  | B =>
      left
      constructor
      · rfl
      · change (serW (z.1.2.1 e)
          (z.1.2.1 (ring.rightNeighbor e))).row = "S2N"
        simp [serW, serializerStep, ProjW.lift,
          hpost.1, hpost.2, hp]
  | C =>
      right
      left
      constructor
      · rfl
      · change (serW (z.1.2.1 e)
          (z.1.2.1 (ring.rightNeighbor e))).row = "S3"
        simp [serW, serializerStep, ProjW.lift,
          hpost.1, hpost.2, hp]
  | F =>
      right
      right
      constructor
      · rfl
      · change (serW (z.1.2.1 e)
          (z.1.2.1 (ring.rightNeighbor e))).row = "S4"
        simp [serW, serializerStep, ProjW.lift,
          hpost.1, hpost.2, hp]

/-- R10a S-frontier physical row; consumer: all-edges closure. -/
theorem bankWordRenewalSoftForwardParentRow {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordRenewalPostSOne ring root s)
    (p : Nat) (hp : 0 < p)
    (hf : BankWordRenewalSoftForwardShape ring root z.1 p)
    (hactive :
      (z.1.2.1 root).ser.cert = .RUNNING ∧
      (z.1.2.1 root).ser.phase = .B ∧
      (z.1.2.1 root).ser.wphase = .CURRENT) :
    (bankWordEpochSelectedReceipt ring z.1
      (L3.EWord.site ring root p)).serializer.row = "S2N" ∧
    bankWordRenewalSoftRootedChosen ring root s z =
      L3.EWord.site ring root p := by
  have hpn : p < n := by
    have hb := hf.pivotBound
    omega
  have hsourceNonroot :=
    L3.EWord.validationPositiveSiteNotRoot ring root p hpn hp
  have htargetNonroot :
      ring.rightNeighbor (L3.EWord.site ring root p) ≠
        root := by
    rw [L3.EWord.siteSuccessor]
    exact L3.EWord.validationPositiveSiteNotRoot
      ring root (p + 1) hf.pivotBound (by omega)
  have hclasses := bankWordRenewalSoftInternalRowCensus
    ring root (L3.EWord.site ring root p) s hn hbank hs z
    hsourceNonroot htargetNonroot
  have hrow :
      (bankWordEpochSelectedReceipt ring z.1
        (L3.EWord.site ring root p)).serializer.row =
          "S2N" := by
    rcases hclasses with hb | hc | hfcase
    · exact hb.2
    · have hbad := hf.parentPhase.symm.trans hc.1
      cases hbad
    · have hbad := hf.parentPhase.symm.trans hfcase.1
      cases hbad
  exact ⟨hrow,
    bankWordRenewalSoftForwardNomination
      ring root s z p hf hactive⟩

/-- A non-IDLE ROOT_IN S5 with a foreign F or nonpending C
    leaves the entire serializer map unchanged; a later F
    cannot erase any rooted frontier site. Consumer: generic
    nonpending ROOT_IN and last LEAF_OK frame. -/
theorem bankWordRenewalSoftIncomingQuietFrame {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankWordEpochState n) (hn : 5 ≤ n)
    (hpred : ring.rightNeighbor e = root)
    (hrootNotIdle : (z.2.1 root).ser.cert ≠ .IDLE)
    (hsource : (z.2.1 e).ser.phase = .F ∨
      ((z.2.1 e).ser.phase = .C ∧
       (z.2.1 e).ser.probe ≠ .PENDING))
    (hx : (postW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).eX.l = false)
    (hy : (postW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).eY.l = true)
    (hshape : BankWordRenewalSoftShape ring root z) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z e) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z e) =
        bankWordRenewalSoftRootedPosition ring root z := by
  have hne : ring.rightNeighbor e ≠ e :=
    L3.EWord.rightNeighborDifferent ring (by omega) e
  have htargetNotIdle :
      (z.2.1 (ring.rightNeighbor e)).ser.cert ≠ .IDLE := by
    simpa only [hpred] using hrootNotIdle
  have hpair :
      (serW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).x =
        (z.2.1 e).ser ∧
      (serW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).y =
        (z.2.1 (ring.rightNeighbor e)).ser := by
    rcases hsource with hf | hc
    · simp [serW, serializerStep, ProjW.lift,
        hx, hy, htargetNotIdle, hf]
    · simp [serW, serializerStep, ProjW.lift,
        hx, hy, htargetNotIdle, hc.1, hc.2]
  have hserial (i : Fin n) :
      ((bankWordEpochNext ring root z e).2.1 i).ser =
        (z.2.1 i).ser := by
    by_cases hi : i = e
    · rw [hi]
      change ((phiW ring z.2.1 e) e).ser = _
      rw [phiW_ser_source]
      exact hpair.1
    · by_cases hj : i = ring.rightNeighbor e
      · rw [hj]
        change ((phiW ring z.2.1 e)
          (ring.rightNeighbor e)).ser = _
        rw [phiW_ser_target ring z.2.1 e hne]
        exact hpair.2
      · change ((phiW ring z.2.1 e) i).ser = _
        exact phiW_ser_remote ring z.2.1 e i hi hj
  have hforward (p : Nat)
      (hf : BankWordRenewalSoftForwardShape ring root z p) :
      BankWordRenewalSoftForwardShape ring root
        (bankWordEpochNext ring root z e) p := by
    refine {
      pivotBound := hf.pivotBound
      completed := ?_
      parentPhase := ?_
      parentCurrent := ?_
      front := ?_ }
    · intro j hj
      simpa only [hserial (L3.EWord.site ring root j)] using
        hf.completed j hj
    · simpa only [hserial (L3.EWord.site ring root p)] using
        hf.parentPhase
    · simpa only [hserial (L3.EWord.site ring root p)] using
        hf.parentCurrent
    · simpa only [hserial (L3.EWord.site ring root p),
        hserial (L3.EWord.site ring root (p + 1))] using hf.front
  have hreturn (q : Nat)
      (hr : BankWordRenewalSoftReturnShape ring root z q) :
      BankWordRenewalSoftReturnShape ring root
        (bankWordEpochNext ring root z e) q := by
    refine {
      pivotBound := hr.pivotBound
      rootRunning := ?_
      rootPhase := ?_
      rootDone := ?_
      rootCurrent := ?_
      completed := ?_
      leftmostPhase := ?_
      leftmostWphase := ?_
      suffix := ?_ }
    · simpa only [hserial root] using hr.rootRunning
    · simpa only [hserial root] using hr.rootPhase
    · simpa only [hserial root] using hr.rootDone
    · simpa only [hserial root] using hr.rootCurrent
    · intro j hj
      simpa only [hserial (L3.EWord.site ring root j)] using
        hr.completed j hj
    · simpa only [hserial (L3.EWord.site ring root (q + 1))]
        using hr.leftmostPhase
    · simpa only [hserial (L3.EWord.site ring root (q + 1))]
        using hr.leftmostWphase
    · intro j hj hjn
      simpa only [hserial (L3.EWord.site ring root j)] using
        hr.suffix j hj hjn
  have hnewShape :
      BankWordRenewalSoftShape ring root
        (bankWordEpochNext ring root z e) := by
    intro hactiveNew
    have hactiveOld :
        (z.2.1 root).ser.cert = .RUNNING ∧
        (z.2.1 root).ser.phase = .B ∧
        (z.2.1 root).ser.wphase = .CURRENT := by
      simpa only [hserial root] using hactiveNew
    rcases hshape hactiveOld with ⟨p, hf⟩ | ⟨q, hr⟩
    · exact Or.inl ⟨p, hforward p hf⟩
    · exact Or.inr ⟨q, hreturn q hr⟩
  have hpos :
      bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z e) =
      bankWordRenewalSoftRootedPosition ring root z := by
    simp [bankWordRenewalSoftRootedPosition, hserial]
  exact ⟨hnewShape, hpos⟩

/-- A terminal C/LEAF_OK/OFF has already been observed. A later
    ROOT_IN S5 merely frames its serializer records; it cannot
    alter the already-paid last forward position.
    Consumer: terminal WAIT/LEAF_OK incoming-root all-edge row. -/
theorem bankWordRenewalSoftTerminalObservedIncomingStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordRenewalPostSOne ring root s)
    (hf : BankWordRenewalSoftForwardShape ring root z.1 (n - 2))
    (hactive :
      (z.1.2.1 root).ser.cert = .RUNNING ∧
      (z.1.2.1 root).ser.phase = .B ∧
      (z.1.2.1 root).ser.wphase = .CURRENT)
    (hchildC :
      (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.phase = .C)
    (hchildObserved :
      (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.probe =
        .LEAF_OK) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))) =
      bankWordRenewalSoftRootedPosition ring root z.1 := by
  have hpred :
      ring.rightNeighbor (L3.EWord.site ring root (n - 1)) =
        root :=
    L3.EWord.validationSeamNeighbor ring root
      (L3.EWord.site ring root (n - 1)) rfl
  have hnonIdle : (z.1.2.1 root).ser.cert ≠ .IDLE := by
    intro h
    have hbad := hactive.1.symm.trans h
    cases hbad
  have hnonPending :
      (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.probe ≠
        .PENDING := by
    intro h
    have hbad := hchildObserved.symm.trans h
    cases hbad
  have hflags := bankWordRenewalSoftIncomingFlags
    ring root (L3.EWord.site ring root (n - 1))
    s hn hbank hs z
    (L3.EWord.validationSeamNotRoot ring root
      (L3.EWord.site ring root (n - 1))
      (by omega : 3 ≤ n) rfl) hpred
  have hshapeOld : BankWordRenewalSoftShape ring root z.1 := by
    intro _
    exact Or.inl ⟨n - 2, hf⟩
  exact bankWordRenewalSoftIncomingQuietFrame
    ring root (L3.EWord.site ring root (n - 1))
    z.1 hn hpred hnonIdle
    (Or.inr ⟨hchildC, hnonPending⟩)
    hflags.1 hflags.2 hshapeOld

/-- R10a S-frontier physical row; consumer: all-edges closure. -/
theorem bankWordRenewalSoftReturnParentRow {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordRenewalPostSOne ring root s)
    (q : Nat) (hq : 0 < q)
    (hr : BankWordRenewalSoftReturnShape ring root z.1 q) :
    (bankWordEpochSelectedReceipt ring z.1
      (L3.EWord.site ring root q)).serializer.row = "S2N" ∧
    bankWordRenewalSoftRootedChosen ring root s z = root := by
  have hqn : q < n := by
    have hb := hr.pivotBound
    omega
  have hsourceNonroot :=
    L3.EWord.validationPositiveSiteNotRoot ring root q hqn hq
  have htargetNonroot :
      ring.rightNeighbor (L3.EWord.site ring root q) ≠
        root := by
    rw [L3.EWord.siteSuccessor]
    exact L3.EWord.validationPositiveSiteNotRoot
      ring root (q + 1) hr.pivotBound (by omega)
  have hclasses := bankWordRenewalSoftInternalRowCensus
    ring root (L3.EWord.site ring root q) s hn hbank hs z
    hsourceNonroot htargetNonroot
  have hphase := (hr.completed q (by omega)).1
  have hrow :
      (bankWordEpochSelectedReceipt ring z.1
        (L3.EWord.site ring root q)).serializer.row =
          "S2N" := by
    rcases hclasses with hb | hc | hfcase
    · exact hb.2
    · have hbad := hphase.symm.trans hc.1
      cases hbad
    · have hbad := hphase.symm.trans hfcase.1
      cases hbad
  exact ⟨hrow, bankWordRenewalSoftReturnNomination
    ring root s z q hr⟩

/-- When the rooted soft activity guard is false, an INTERNAL
    or ROOT_IN service cannot create it, and a ROOT_OUT service
    either performs S1/SR or stays inactive on B/S2R/S6.
    Hence the position remains zero on every physical edge.
    Consumer: inactive half of bankWordRenewalSoftShapeStep. -/
theorem bankWordRenewalSoftInactiveAllEdgesStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordRenewalPostSOne ring root s)
    (e : Fin n)
    (hinactive :
      ¬ ((z.1.2.1 root).ser.cert = .RUNNING ∧
        (z.1.2.1 root).ser.phase = .B ∧
        (z.1.2.1 root).ser.wphase = .CURRENT)) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1 e) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1 e) =
      bankWordRenewalSoftRootedPosition ring root z.1 := by
  rcases bankWordRenewalSoftEdgeGeometry ring root e hn with
    hroot | hseam | hinter
  · subst e
    by_cases hrequested :
        (z.1.2.1 root).ser.cert = .REQUESTED
    · have hcase :
          ((z.1.2.1 root).ser.cert = .REQUESTED ∧
            0 < (z.1.2.1 root).siLease.val) ∨
          ((z.1.2.1 root).ser.cert = .REQUESTED ∧
            (z.1.2.1 root).siLease.val = 0) ∨
          (((z.1.2.1 root).ser.cert = .IDLE ∨
            (z.1.2.1 root).ser.cert = .RUNNING) ∧
           ((z.1.2.1 root).ser.phase = .C ∨
            (z.1.2.1 root).ser.phase = .F)) := by
        by_cases hzero : (z.1.2.1 root).siLease.val = 0
        · exact Or.inr (Or.inl ⟨hrequested, hzero⟩)
        · exact Or.inl ⟨hrequested, (by omega)⟩
      exact bankWordRenewalSoftRootEntryStep
        ring root s hn hbank hs z hcase
    · cases hphase : (z.1.2.1 root).ser.phase with
      | B =>
          exact bankWordRenewalSoftInactiveRootOutgoingBStep
            ring root s hn hbank hs z hphase hrequested
            hinactive
      | C =>
          have hcert :
              (z.1.2.1 root).ser.cert = .IDLE ∨
              (z.1.2.1 root).ser.cert = .RUNNING := by
            cases hc : (z.1.2.1 root).ser.cert with
            | IDLE => exact Or.inl rfl
            | REQUESTED => exact False.elim (hrequested hc)
            | RUNNING => exact Or.inr rfl
          exact bankWordRenewalSoftRootEntryStep
            ring root s hn hbank hs z
            (Or.inr (Or.inr ⟨hcert, Or.inl hphase⟩))
      | F =>
          have hcert :
              (z.1.2.1 root).ser.cert = .IDLE ∨
              (z.1.2.1 root).ser.cert = .RUNNING := by
            cases hc : (z.1.2.1 root).ser.cert with
            | IDLE => exact Or.inl rfl
            | REQUESTED => exact False.elim (hrequested hc)
            | RUNNING => exact Or.inr rfl
          exact bankWordRenewalSoftRootEntryStep
            ring root s hn hbank hs z
            (Or.inr (Or.inr ⟨hcert, Or.inr hphase⟩))
  · rcases hseam with ⟨he, hpred⟩
    have hnotRoot :=
      L3.EWord.validationSeamNotRoot ring root e
        (by omega : 3 ≤ n) he
    by_cases hidle : (z.1.2.1 root).ser.cert = .IDLE
    · have hflags := bankWordRenewalSoftIncomingFlags
        ring root e s hn hbank hs z hnotRoot hpred
      have hstep := bankWordRenewalSoftRootIncomingStep
        ring root e z.1 (by omega : 3 ≤ n) hpred
        hflags.1 hflags.2 hidle
      exact ⟨hstep.1, hstep.2.1⟩
    · exact bankWordRenewalSoftInactiveIncomingStep
        ring root e s hn hbank hs z hnotRoot hpred
        hidle hinactive
  · rcases hinter with ⟨k, hk, hbound, he, hnotRoot,
      hnotNeighborRoot⟩
    exact bankWordRenewalSoftInactiveInternalStep
      ring root e z.1 hnotRoot hnotNeighborRoot hinactive

/-- R10a S-frontier physical row; consumer: all-edges closure. -/
theorem bankWordRenewalSoftForwardLeafSeamStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordRenewalPostSOne ring root s)
    (hf : BankWordRenewalSoftForwardShape ring root z.1 (n - 2))
    (hrun : (z.1.2.1 root).ser.cert = .RUNNING)
    (hwait :
      (z.1.2.1 (L3.EWord.site ring root (n - 2))).ser.out =
        .WAIT)
    (hchildC :
      (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.phase =
        .C)
    (hchildPending :
      (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.probe =
        .PENDING) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))) =
      bankWordRenewalSoftRootedPosition ring root z.1 ∧
    bankWordRenewalSoftRootedPosition ring root z.1 =
      n - 1 ∧
    bankWordRenewalSoftRootedChosen ring root s z =
      L3.EWord.site ring root (n - 2) := by
  have hpred :
      ring.rightNeighbor (L3.EWord.site ring root (n - 1)) =
        root :=
    L3.EWord.validationSeamNeighbor ring root
      (L3.EWord.site ring root (n - 1)) rfl
  have hsourceNonroot :=
    L3.EWord.validationSeamNotRoot ring root
      (L3.EWord.site ring root (n - 1)) (by omega : 3 ≤ n) rfl
  have hflags := bankWordRenewalSoftIncomingFlags
    ring root (L3.EWord.site ring root (n - 1))
    s hn hbank hs z hsourceNonroot hpred
  have hstep := bankWordRenewalSoftRootIncomingLeafStep
    ring root s z hn hf hrun hwait hchildC hchildPending
    hflags.1 hflags.2
  exact ⟨hstep.1, hstep.2.2.2.1,
    hstep.2.2.2.2.1, hstep.2.2.2.2.2⟩

/-- R10a S-frontier physical row; consumer: all-edges closure. -/
theorem bankWordRenewalSoftForwardForeignSeamStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordRenewalPostSOne ring root s)
    (p : Nat)
    (hf : BankWordRenewalSoftForwardShape ring root z.1 p)
    (hactive :
      (z.1.2.1 root).ser.cert = .RUNNING ∧
      (z.1.2.1 root).ser.phase = .B ∧
      (z.1.2.1 root).ser.wphase = .CURRENT)
    (hbeforeLeaf : p + 2 < n)
    (hforeignB :
      (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.phase =
        .B) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))) =
      bankWordRenewalSoftRootedPosition ring root z.1 ∧
    bankWordRenewalSoftRootedChosen ring root s z =
      L3.EWord.site ring root p := by
  have hpred :
      ring.rightNeighbor (L3.EWord.site ring root (n - 1)) =
        root :=
    L3.EWord.validationSeamNeighbor ring root
      (L3.EWord.site ring root (n - 1)) rfl
  have hsourceNonroot :=
    L3.EWord.validationSeamNotRoot ring root
      (L3.EWord.site ring root (n - 1)) (by omega : 3 ≤ n) rfl
  have hflags := bankWordRenewalSoftIncomingFlags
    ring root (L3.EWord.site ring root (n - 1))
    s hn hbank hs z hsourceNonroot hpred
  have hstep := bankWordRenewalSoftRootIncomingForeignBStep
    ring root s z p hn hf hactive hbeforeLeaf hforeignB
    hflags.1 hflags.2
  exact ⟨hstep.1, hstep.2.1, hstep.2.2.1⟩

/-- Exhaustive rooted-forward physical edge step. Positive position
    increments occur only on the OLD nominated root-attached
    challenge/admission edge. S3 observation and arbitrary
    inherited suffix cleanup cannot add another charge.
    Consumer: forward branch of R10a hfail all-edges closure. -/
theorem bankWordRenewalSoftForwardAllEdgesStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordRenewalPostSOne ring root s)
    (e : Fin n) (p : Nat)
    (hf : BankWordRenewalSoftForwardShape ring root z.1 p)
    (hactive :
      (z.1.2.1 root).ser.cert = .RUNNING ∧
      (z.1.2.1 root).ser.phase = .B ∧
      (z.1.2.1 root).ser.wphase = .CURRENT) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1 e) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1 e) ≤
      bankWordRenewalSoftRootedPosition ring root z.1 + 1 ∧
    (bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z.1 e) ≠
      bankWordRenewalSoftRootedPosition ring root z.1 →
      e = bankWordRenewalSoftRootedChosen ring root s z) := by
  have hshape : BankWordRenewalSoftShape ring root z.1 := by
    intro _
    exact Or.inl ⟨p, hf⟩
  rcases bankWordRenewalSoftForwardEdgeCases
      ring root e z.1 p hn hf with hroot | hseam | hinter
  · subst e
    by_cases hpzero : p = 0
    · have hfzero :
          BankWordRenewalSoftForwardShape ring root z.1 0 := by
        simpa only [hpzero] using hf
      exact bankWordRenewalSoftRootFirstStep
        ring root s hn hbank hs z hfzero hactive.1
    · have hpositive : 0 < p := by omega
      have hrootOld := hf.completed 0 hpositive
      have hrootB : (z.1.2.1 root).ser.phase = .B := by
        simpa only [L3.EWord.siteZero] using hrootOld.1
      have hrootDone : (z.1.2.1 root).ser.out = .DONE := by
        simpa only [L3.EWord.siteZero] using hrootOld.2.1
      have hfirstB :
          (z.1.2.1 (ring.rightNeighbor root)).ser.phase =
            .B := by
        by_cases hpone : p = 1
        · simpa only [hpone, L3.EWord.siteOne] using
            hf.parentPhase
        · have hfirst := hf.completed 1 (by omega)
          simpa only [L3.EWord.siteOne] using hfirst.1
      have hnotRequested :
          (z.1.2.1 root).ser.cert ≠ .REQUESTED := by
        intro h
        have hbad := hactive.1.symm.trans h
        cases hbad
      have hflags := bankWordRenewalSoftOutgoingFlags
        ring root s hn hbank hs z
      have hstep := bankWordRenewalSoftOutgoingCoveredDoneFrame
        ring root root z.1 hn hrootB hrootDone
        hfirstB hnotRequested hflags.1 hflags.2 hshape
      refine ⟨hstep.1, ?_, ?_⟩
      · rw [hstep.2]
        omega
      · intro hneq
        exact False.elim (hneq hstep.2)
  · rcases hseam with ⟨he, _⟩
    subst e
    have hpred :
        ring.rightNeighbor (L3.EWord.site ring root (n - 1)) =
          root :=
      L3.EWord.validationSeamNeighbor ring root
        (L3.EWord.site ring root (n - 1)) rfl
    have hnotRoot :=
      L3.EWord.validationSeamNotRoot ring root
        (L3.EWord.site ring root (n - 1))
        (by omega : 3 ≤ n) rfl
    have hflags := bankWordRenewalSoftIncomingFlags
      ring root (L3.EWord.site ring root (n - 1))
      s hn hbank hs z hnotRoot hpred
    have hpres :
        BankWordRenewalSoftShape ring root
          (bankWordEpochNext ring root z.1
            (L3.EWord.site ring root (n - 1))) ∧
        bankWordRenewalSoftRootedPosition ring root
          (bankWordEpochNext ring root z.1
            (L3.EWord.site ring root (n - 1))) =
        bankWordRenewalSoftRootedPosition ring root z.1 := by
      by_cases hbefore : p + 2 < n
      · have hstep := bankWordRenewalSoftForwardSeamOutsideFront
          ring root s z p hn hf hactive hbefore
          hflags.1 hflags.2
        exact ⟨hstep.1, hstep.2.1⟩
      · have hterminal : p + 2 = n := by
          have hb := hf.pivotBound
          omega
        rcases hf.front with hzero | hpositive
        · have hbad : False := by omega
          exact False.elim hbad
        · rcases hpositive.2 with hnew | hwaiting
          · have hstep := bankWordRenewalSoftTerminalNewIncomingStep
              ring root s z p hn hf hactive hterminal hnew
              hflags.1 hflags.2
            exact ⟨hstep.1, hstep.2.1⟩
          · rcases hwaiting.2 with hpending | hinternal | hleaf
            · have hpLast : p = n - 2 := by omega
              have hsub : p + 1 = n - 1 := by omega
              have hfLast :
                  BankWordRenewalSoftForwardShape ring root
                    z.1 (n - 2) := by
                simpa only [hpLast] using hf
              have hwaitLast :
                  (z.1.2.1 (L3.EWord.site ring root (n - 2))).ser.out =
                    .WAIT := by
                simpa only [hpLast] using hwaiting.1
              have hchildC :
                  (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.phase =
                    .C := by
                simpa only [hsub] using hpending.1
              have hchildPending :
                  (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.probe =
                    .PENDING := by
                simpa only [hsub] using hpending.2.1
              have hstep := bankWordRenewalSoftForwardLeafSeamStep
                ring root s hn hbank hs z hfLast hactive.1
                hwaitLast hchildC hchildPending
              exact ⟨hstep.1, hstep.2.1⟩
            · have hbad : False := by omega
              exact False.elim hbad
            · have hpLast : p = n - 2 := by omega
              have hsub : p + 1 = n - 1 := by omega
              have hfLast :
                  BankWordRenewalSoftForwardShape ring root
                    z.1 (n - 2) := by
                simpa only [hpLast] using hf
              have hchildC :
                  (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.phase =
                    .C := by
                simpa only [hsub] using hleaf.2.1
              have hchildObserved :
                  (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.probe =
                    .LEAF_OK := by
                simpa only [hsub] using hleaf.2.2.1
              exact bankWordRenewalSoftTerminalObservedIncomingStep
                ring root s hn hbank hs z hfLast hactive
                hchildC hchildObserved
    refine ⟨hpres.1, ?_, ?_⟩
    · rw [hpres.2]
      omega
    · intro hneq
      exact False.elim (hneq hpres.2)
  · rcases hinter with ⟨k, hkpositive, hinside, he, hcases⟩
    subst e
    rcases hcases with hcovered | hpivot | hchild | hfar
    · have hstep := bankWordRenewalSoftForwardCoveredStep
        ring root s hn hbank hs z p k hf hactive hshape
        hkpositive hcovered.1
      refine ⟨hstep.1, ?_, ?_⟩
      · rw [hstep.2.1]
        omega
      · intro hneq
        exact False.elim (hneq hstep.2.1)
    · have hp : 0 < p := by omega
      have hk : k = p := hpivot.1
      subst k
      exact bankWordRenewalSoftForwardParentStep
        ring root s hn hbank hs z p hp hf hactive.1
    · have hk : k = p + 1 := hchild
      by_cases hnew :
          (z.1.2.1 (L3.EWord.site ring root p)).ser.out = .NEW
      · have hfar : p < k := by omega
        have hstep := bankWordRenewalSoftForwardNewChildStep
          ring root s z p k hf hactive hfar hnew hinside
        refine ⟨hstep.1, ?_, ?_⟩
        · rw [hstep.2.1]
          omega
        · intro hneq
          exact False.elim (hneq hstep.2.1)
      · have hwait :
            (z.1.2.1 (L3.EWord.site ring root p)).ser.out =
              .WAIT := by
          rcases hf.front with hzero | hpositive
          · exact hzero.2.1
          · rcases hpositive.2 with hnewOld | hwaiting
            · exact False.elim (hnew hnewOld)
            · exact hwaiting.1
        have hchildCases :
            ((z.1.2.1 (L3.EWord.site ring root (p + 1))).ser.phase =
                .C ∧
              (z.1.2.1 (L3.EWord.site ring root (p + 1))).ser.probe =
                .PENDING ∧
              (z.1.2.1 (L3.EWord.site ring root (p + 1))).ser.wphase =
                .CURRENT) ∨
            ((z.1.2.1 (L3.EWord.site ring root (p + 1))).ser.phase =
                .C ∧
              (z.1.2.1 (L3.EWord.site ring root (p + 1))).ser.probe =
                .INTERNAL_OK ∧
              (z.1.2.1 (L3.EWord.site ring root (p + 1))).ser.wphase =
                .CURRENT) := by
          rcases hf.front with hzero | hpositive
          · rcases hzero.2.2.2.2 with hpending | hinternal
            · exact Or.inl ⟨hzero.2.2.1, hpending,
                hzero.2.2.2.1⟩
            · exact Or.inr ⟨hzero.2.2.1, hinternal,
                hzero.2.2.2.1⟩
          · rcases hpositive.2 with hnewOld | hwaiting
            · exact False.elim (hnew hnewOld)
            · rcases hwaiting.2 with hpending | hinternal | hleaf
              · exact Or.inl hpending
              · exact Or.inr ⟨hinternal.2.1, hinternal.2.2.1,
                  hinternal.2.2.2⟩
              · have hbad : False := by omega
                exact False.elim hbad
        have hsourceNotRoot :
            L3.EWord.site ring root (p + 1) ≠ root :=
          L3.EWord.validationPositiveSiteNotRoot
            ring root (p + 1) (by omega) (by omega)
        have htargetNotRoot :
            ring.rightNeighbor (L3.EWord.site ring root (p + 1)) ≠
              root := by
          rw [L3.EWord.siteSuccessor]
          exact L3.EWord.validationPositiveSiteNotRoot
            ring root (p + 2) (by omega) (by omega)
        have hflags := bankWordRenewalSoftInternalFlags
          ring root (L3.EWord.site ring root (p + 1))
          s hn hbank hs z hsourceNotRoot htargetNotRoot
        have hpres :
            BankWordRenewalSoftShape ring root
              (bankWordEpochNext ring root z.1
                (L3.EWord.site ring root k)) ∧
            bankWordRenewalSoftRootedPosition ring root
              (bankWordEpochNext ring root z.1
                (L3.EWord.site ring root k)) =
            bankWordRenewalSoftRootedPosition ring root z.1 := by
          rcases hchildCases with hpending | hinternal
          · have hstep := bankWordRenewalSoftPendingObservationStep
              ring root s z p hn hf hactive (by omega)
              hwait hpending.1 hpending.2.1 hpending.2.2
              hflags.1 hflags.2
            simpa only [hk] using
              ⟨hstep.1, hstep.2.1⟩
          · have hstep := bankWordRenewalSoftInternalAnsweredChildStep
              ring root s z p hn hf hactive (by omega)
              hwait hinternal.1 hinternal.2.1 hinternal.2.2
              hflags.1 hflags.2
            simpa only [hk] using
              ⟨hstep.1, hstep.2.1⟩
        refine ⟨hpres.1, ?_, ?_⟩
        · rw [hpres.2]
          omega
        · intro hneq
          exact False.elim (hneq hpres.2)
    · have hstep := bankWordRenewalSoftForwardSuffixStep
        ring root s z p k hf hactive hfar hinside
      refine ⟨hstep.1, ?_, ?_⟩
      · rw [hstep.2.1]
        omega
      · intro hneq
        exact False.elim (hneq hstep.2.1)

/-- Exact selected-letter S-frontier preservation on every
    physical edge: the rooted soft normal shape N persists;
    the charged position moves by at most one; any change
    is on the old-state nominated edge. Consumer: R10a
    serializer first-H lower cover in 5B hfail. -/
theorem bankWordRenewalSoftShapeStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordRenewalPostSOne ring root s)
    (e : Fin n)
    (hshape : BankWordRenewalSoftShape ring root z.1) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1 e) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1 e) ≤
      bankWordRenewalSoftRootedPosition ring root z.1 + 1 ∧
    (bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z.1 e) ≠
      bankWordRenewalSoftRootedPosition ring root z.1 →
      e = bankWordRenewalSoftRootedChosen ring root s z) := by
  by_cases hactive :
      (z.1.2.1 root).ser.cert = .RUNNING ∧
      (z.1.2.1 root).ser.phase = .B ∧
      (z.1.2.1 root).ser.wphase = .CURRENT
  · rcases hshape hactive with hforward | hreturn
    · obtain ⟨p, hf⟩ := hforward
      exact bankWordRenewalSoftForwardAllEdgesStep
        ring root s hn hbank hs z e p hf hactive
    · obtain ⟨q, hr⟩ := hreturn
      exact bankWordRenewalSoftReturnAllEdgesStep
        ring root s hn hbank hs z e q hr
  · have hstep := bankWordRenewalSoftInactiveAllEdgesStep
      ring root s hn hbank hs z e hactive
    refine ⟨hstep.1, ?_, ?_⟩
    · rw [hstep.2]
      omega
    · intro hneq
      exact False.elim (hneq hstep.2)

/-- The rooted S-frontier spatial invariant holds on every
    original BANK physical word following a genuinely ticketed
    hard-S6 fresh cut. No postulated step hypothesis remains;
    the induction invokes bankWordRenewalSoftShapeStep.
    Consumer: 5B hfail serializer-frontier word census. -/
theorem bankWordRenewalSoftShapeWord {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (seed : BankWordRenewalFreshSeed ring root s)
    (word : List (Fin n)) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochRun ring root seed.1.1 word) := by
  have hstep :
      ∀ (z : BankWordRenewalPostSOne ring root s)
        (e : Fin n), BankWordRenewalSoftShape ring root z.1 →
        BankWordRenewalSoftShape ring root
          (bankWordEpochNext ring root z.1 e) := by
    intro z e hshape
    exact (bankWordRenewalSoftShapeStep
      ring root s hn hbank hs z e hshape).1
  exact bankWordRenewalSoftShapeWordFromSeed
    ring root s hn hbank hs hstep seed word

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open Classical
open L3.GrantDrainEntrance
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- Consumer: R10 first-H retry upper-tail bound. For every
predictable state-based nomination, the exact number of length-T
scheduler words with at least Q nominated hits is the complement
of the already-proved binomial short count. No independence of
successive *states* is assumed. -/
theorem bankWordRenewalNominatedUpperTailLaw
    {S : Type} {n : Nat}
    (next : S → Fin n → S)
    (chosen : S → Fin n)
    (x : S) (T Q : Nat) (hn : 0 < n) :
    L3.Prob.scheduleSum n T
      (fun w => if Q ≤
        grantDrainLabelHits next chosen x w then 1 else 0) =
      n ^ T - grantDrainLabelBinomialShort n T Q := by
  have hshort := grantDrainLabelBinomialLaw
    next chosen x T Q hn
  have hpart :
      L3.Prob.scheduleSum n T
        (fun w => if grantDrainLabelHits next chosen x w < Q
          then 1 else 0) +
      L3.Prob.scheduleSum n T
        (fun w => if Q ≤ grantDrainLabelHits next chosen x w
          then 1 else 0) =
      L3.Prob.scheduleSum n T
        (fun _ : List (Fin n) => 1) := by
    change
      FixedSpanRenewalPayload.wordSum n T
        (fun w => if grantDrainLabelHits next chosen x w < Q
          then 1 else 0) +
      FixedSpanRenewalPayload.wordSum n T
        (fun w => if Q ≤ grantDrainLabelHits next chosen x w
          then 1 else 0) =
      FixedSpanRenewalPayload.wordSum n T
        (fun _ : List (Fin n) => 1)
    rw [← FixedSpanRenewalPayload.rawWord_sum n T
      (fun w => if grantDrainLabelHits next chosen x w < Q
        then 1 else 0)]
    rw [← FixedSpanRenewalPayload.rawWord_sum n T
      (fun w => if Q ≤ grantDrainLabelHits next chosen x w
        then 1 else 0)]
    rw [← FixedSpanRenewalPayload.rawWord_sum n T
      (fun _ : List (Fin n) => 1)]
    rw [← ofFn_sum_add]
    apply ofFn_sum_eq
    intro i
    by_cases hlt :
        grantDrainLabelHits next chosen x
          (FixedSpanRenewalPayload.rawWord n T i) < Q
    · have hnot : ¬ Q ≤
          grantDrainLabelHits next chosen x
            (FixedSpanRenewalPayload.rawWord n T i) := by
        omega
      simp only [if_pos hlt, if_neg hnot, Nat.add_zero]
    · have hge : Q ≤
          grantDrainLabelHits next chosen x
            (FixedSpanRenewalPayload.rawWord n T i) := by
        omega
      simp only [if_neg hlt, if_pos hge, Nat.zero_add]
  have htotal :
      L3.Prob.scheduleSum n T
        (fun _ : List (Fin n) => 1) = n ^ T := by
    change FixedSpanRenewalPayload.wordSum n T
      (fun _ : List (Fin n) => 1) = n ^ T
    rw [← FixedSpanRenewalPayload.rawWord_sum n T
      (fun _ : List (Fin n) => 1)]
    rw [ofFn_sum_const]
    simp
  rw [hshort, htotal] at hpart
  omega

/-- Consumer: R10 serializer nominated-hit charging. On a
genuine reachable post-S1 physical edge, rooted soft-position
growth is at most the indicator of the OLD state's nominated
edge. This is an upper bound, not a claim that a hit progresses. -/
theorem bankWordRenewalSoftRootedPositionHitStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordRenewalPostSOne ring root s)
    (e : Fin n)
    (hshape : BankWordRenewalSoftShape ring root z.1) :
    bankWordRenewalSoftRootedPosition ring root
        (bankWordRenewalNext ring root s z e).1 ≤
      bankWordRenewalSoftRootedPosition ring root z.1 +
        (if e = bankWordRenewalSoftRootedChosen ring root s z
          then 1 else 0) := by
  have hstep := bankWordRenewalSoftShapeStep
    ring root s hn hbank hs z e hshape
  by_cases he :
      e = bankWordRenewalSoftRootedChosen ring root s z
  · rw [if_pos he]
    exact hstep.2.1
  · rw [if_neg he]
    by_cases hsame :
        bankWordRenewalSoftRootedPosition ring root
            (bankWordRenewalNext ring root s z e).1 =
          bankWordRenewalSoftRootedPosition ring root z.1
    · rw [hsame]
      exact Nat.le_refl _
    · exact False.elim (he (hstep.2.2 hsame))

/-- Consumer: R10 pathwise nominated-hit charging on the
actual selected-letter renewal transition. This remains valid
when a soft S6 resets the rooted position to zero. -/
theorem bankWordRenewalSoftRootedWordHitBound {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (word : List (Fin n)) :
    ∀ z : BankWordRenewalPostSOne ring root s,
      BankWordRenewalSoftShape ring root z.1 →
      bankWordRenewalSoftRootedPosition ring root
          (grantDrainLabelRun (bankWordRenewalNext ring root s)
            z word).1 ≤
        bankWordRenewalSoftRootedPosition ring root z.1 +
          grantDrainLabelHits (bankWordRenewalNext ring root s)
            (bankWordRenewalSoftRootedChosen ring root s) z word := by
  induction word with
  | nil =>
      intro z _
      change
        bankWordRenewalSoftRootedPosition ring root z.1 ≤
          bankWordRenewalSoftRootedPosition ring root z.1 + 0
      omega
  | cons e es ih =>
      intro z hshape
      have hnextShape :=
        (bankWordRenewalSoftShapeStep
          ring root s hn hbank hs z e hshape).1
      have hfirst := bankWordRenewalSoftRootedPositionHitStep
        ring root s hn hbank hs z e hshape
      have htail :=
        ih (bankWordRenewalNext ring root s z e) hnextShape
      change
        bankWordRenewalSoftRootedPosition ring root
          (grantDrainLabelRun (bankWordRenewalNext ring root s)
            (bankWordRenewalNext ring root s z e) es).1 ≤
        bankWordRenewalSoftRootedPosition ring root z.1 +
          ((if e = bankWordRenewalSoftRootedChosen ring root s z
            then 1 else 0) +
            grantDrainLabelHits (bankWordRenewalNext ring root s)
              (bankWordRenewalSoftRootedChosen ring root s)
              (bankWordRenewalNext ring root s z e) es)
      omega

/-- Consumer: R10 genuine-hard-cut frontend. The actual
post-hard-S6 fresh seed has zero rooted position, and any
subsequent rooted position is charged to OLD-state nominated
scheduler letters. No invented clean restart is inserted. -/
theorem bankWordRenewalFreshNominatedHitBound {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (seed : BankWordRenewalFreshSeed ring root s)
    (word : List (Fin n)) :
    bankWordRenewalSoftRootedPosition ring root
        (grantDrainLabelRun (bankWordRenewalNext ring root s)
          seed.1 word).1 ≤
      grantDrainLabelHits (bankWordRenewalNext ring root s)
        (bankWordRenewalSoftRootedChosen ring root s)
        seed.1 word := by
  have hseed := bankWordRenewalSoftShapeSeed
    ring root s hn hbank hs seed
  have hcharge := bankWordRenewalSoftRootedWordHitBound
    ring root s hn hbank hs word seed.1 hseed.1
  rw [hseed.2] at hcharge
  simpa only [Nat.zero_add] using hcharge

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open Classical
open L3.GrantDrainEntrance

set_option autoImplicit false
set_option Elab.async false

/-- Consumer: the incoming-root branch of the fresh hard-epoch
clean-ledger induction. At ANY actual reachable post-S1 cut,
a source with a physically free SI record cannot produce an
unrecorded P0/P2/A0 done, and the incoming edge cannot debit
the responder root's lease. The still-missing word invariant
must establish the free-source premise on the appropriate
active prefixes; this theorem does not assume that premise
for an arbitrary reached state. -/
theorem bankWordRenewalFreshIncomingDoneOrCompletion {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordRenewalPostSOne ring root s)
    (e : Fin n)
    (hpred : ring.rightNeighbor e = root)
    (hfree : freeSI (z.1.2.1 e).si = true) :
    (bankWordEpochSelectedReceipt ring z.1 e).worker.done =
        false ∧
    ((bankWordRenewalNext ring root s z e).1.2.1 root).siLease =
      (z.1.2.1 root).siLease := by
  have hself : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) e
  have hne : e ≠ root := by
    intro he
    exact hself (hpred.trans he.symm)
  have hacc :
      (bankWordEpochSelectedReceipt ring z.1 e).serializer.hard.hardAccept =
        false :=
    bankWordRootNonrootHardAcceptFalse
      ring hn hbank root s hs z.1 z.2.1 e hne
  have hdone :
      (bankWordEpochSelectedReceipt ring z.1 e).worker.done =
        false := by
    change (workerW (z.1.2.1 e)
      (z.1.2.1 (ring.rightNeighbor e))).done = false
    exact bankWordRenewalFrontierFreeSourceNoDone
      (z.1.2.1 e) (z.1.2.1 (ring.rightNeighbor e))
      hfree
  refine ⟨hdone, ?_⟩
  change (phiW ring z.1.2.1 e root).siLease =
    (z.1.2.1 root).siLease
  change
    ((if root = e then
        (pairW (z.1.2.1 e)
          (z.1.2.1 (ring.rightNeighbor e))).1
      else if root = ring.rightNeighbor e then
        (pairW (z.1.2.1 e)
          (z.1.2.1 (ring.rightNeighbor e))).2
      else z.1.2.1 root)).siLease =
        (z.1.2.1 root).siLease
  rw [if_neg hne.symm, if_pos hpred.symm]
  rw [hpred]
  change
    (leasePair (compileAdvice (ceilLogTwo n))
      (z.1.2.1 e).siLease (z.1.2.1 root).siLease
      (serW (z.1.2.1 e) (z.1.2.1 root)).hard.hardAccept
      (serW (z.1.2.1 e) (z.1.2.1 root)).hard.softAccept
      (workerW (z.1.2.1 e) (z.1.2.1 root)).done).2 =
        (z.1.2.1 root).siLease
  change
    (serW (z.1.2.1 e)
      (z.1.2.1 (ring.rightNeighbor e))).hard.hardAccept = false at hacc
  change
    (workerW (z.1.2.1 e)
      (z.1.2.1 (ring.rightNeighbor e))).done = false at hdone
  rw [hpred] at hacc hdone
  cases hsoft :
      (serW (z.1.2.1 e)
        (z.1.2.1 root)).hard.softAccept with
  | false =>
      simp [leasePair, hacc, hdone, hsoft]
  | true =>
      simp [leasePair, hacc, hdone, hsoft]

/-- Consumer: the L disjoint soft-episode charges in the
fresh hard-S1 quota. The OLD root is REQUESTED with positive
physical lease, so its literal S1 makes a rooted position-0
soft episode. If a later word has reached the precise OLD
ReturnShape at pivot zero, that SAME episode has paid at
least n-1 nominated hits before the terminal soft S6.
No monotonicity and no assumed progress on every hit is used. -/
theorem bankWordRenewalFreshSoftLapHitCharge {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordRenewalPostSOne ring root s)
    (hrequested : (z.1.2.1 root).ser.cert = .REQUESTED)
    (hpositive : 0 < (z.1.2.1 root).siLease.val)
    (word : List (Fin n))
    (hfinish : BankWordRenewalSoftReturnShape ring root
      (grantDrainLabelRun (bankWordRenewalNext ring root s)
        (bankWordRenewalNext ring root s z root) word).1 0) :
    n - 1 ≤
      grantDrainLabelHits (bankWordRenewalNext ring root s)
        (bankWordRenewalSoftRootedChosen ring root s)
        (bankWordRenewalNext ring root s z root) word := by
  have hflags := bankWordRenewalSoftOutgoingFlags
    ring root s hn hbank hs z
  have hstart := bankWordRenewalSoftRootEntryAndRecovery
    ring root z.1 (by omega : 3 ≤ n)
    hflags.1 hflags.2 (Or.inl ⟨hrequested, hpositive⟩)
  have hfinishFlags := bankWordRenewalSoftOutgoingFlags
    ring root s hn hbank hs
    (grantDrainLabelRun (bankWordRenewalNext ring root s)
      (bankWordRenewalNext ring root s z root) word)
  have hterminal := bankWordRenewalSoftRootOutgoingFinishStep
    ring root s
    (grantDrainLabelRun (bankWordRenewalNext ring root s)
      (bankWordRenewalNext ring root s z root) word)
    hn hfinish hfinishFlags.1 hfinishFlags.2
  have hbound := bankWordRenewalSoftRootedWordHitBound
    ring root s hn hbank hs word
    (bankWordRenewalNext ring root s z root) hstart.1
  have hzero : bankWordRenewalSoftRootedPosition ring root
      (bankWordRenewalNext ring root s z root).val = 0 := by
    exact hstart.2.1
  rw [hterminal.2.2.1, hzero] at hbound
  simpa only [Nat.zero_add] using hbound

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open Classical
open L3.GrantDrainEntrance

set_option autoImplicit false
set_option Elab.async false

theorem bankWordRenewalFreshSoftEpisodePairing {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s)
    (hshape : BankWordRenewalSoftShape ring root z.1)
    (hrun : (z.1.2.1 root).ser.cert = .RUNNING)
    (hb : (z.1.2.1 root).ser.phase = .B)
    (hcurrent : (z.1.2.1 root).ser.wphase = .CURRENT)
    (hdone : (z.1.2.1 root).ser.out = .DONE)
    (hchild :
      (z.1.2.1 (ring.rightNeighbor root)).ser.phase = .F) :
    BankWordRenewalSoftReturnShape ring root z.1 0 := by
  rcases hshape ⟨hrun, hb, hcurrent⟩ with
    ⟨p, hf⟩ | ⟨q, hr⟩
  · cases p with
    | zero =>
        rcases hf.front with hzero | hpositive
        · have hwait :
            (z.1.2.1 root).ser.out = .WAIT := by
            simpa only [L3.EWord.siteZero] using hzero.2.1
          rw [hwait] at hdone
          cases hdone
        · exact False.elim (Nat.not_lt_zero 0 hpositive.1)
    | succ k =>
        cases k with
        | zero =>
            have hbefore :
                (z.1.2.1 (ring.rightNeighbor root)).ser.phase =
                  .B := by
              have h1 := hf.parentPhase
              simp only [Nat.zero_add] at h1
              exact h1
            rw [hbefore] at hchild
            cases hchild
        | succ k =>
            have hbefore :
                (z.1.2.1 (ring.rightNeighbor root)).ser.phase =
                  .B := by
              simpa only [L3.EWord.siteOne] using
                (hf.completed 1 (by omega)).1
            rw [hbefore] at hchild
            cases hchild
  · cases q with
    | zero =>
        exact hr
    | succ k =>
        have hbefore :
            (z.1.2.1 (ring.rightNeighbor root)).ser.phase =
              .B := by
          simpa only [L3.EWord.siteOne] using
            (hr.completed 1 (by omega)).1
        rw [hbefore] at hchild
        cases hchild

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open Classical
open L3.GrantDrainEntrance

set_option autoImplicit false
set_option Elab.async false

/-- Consumer: the fresh ROOT_OUT S1 and S6 branches of
R10a (A*) clean-epoch induction. This augments the literal
BankWordHardEpochCleanInvariant, without replacing its
five clauses. The RUNNING/VALIDATING case describes the
zero-lease hard S1 episode, before its genuine S6 retry. -/
def BankWordRenewalFreshRootLedger {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) : Prop :=
  (0 < (bankWordHardEpochLedger ring root z).hardEpochs ∧
    (bankWordHardEpochLedger ring root z).workerDone = false) →
    (((z.2.1 root).ser.cert = .IDLE ∨
      (z.2.1 root).ser.cert = .REQUESTED) →
      (bankWordHardEpochLedger ring root z).pendingSoft = false) ∧
    (((z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .CURRENT) →
      (bankWordHardEpochLedger ring root z).pendingSoft = true) ∧
    (((z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING) →
      (bankWordHardEpochLedger ring root z).pendingSoft = false ∧
      (z.2.1 root).siLease.val = 0 ∧
      (bankWordHardEpochLedger ring root z).softFinishes =
        bankWordRenewalLease n) ∧
    (z.2.1 root).siLease.val =
      bankWordRenewalLease n -
        (bankWordHardEpochLedger ring root z).softFinishes

/-- Consumer: first prefix of the (A*) stopped genealogy.
A genuine selected hard S6 has root certificate IDLE
(not RUNNING), physical lease L, zero soft counters and
pendingSoft=false. -/
theorem bankWordRenewalFreshRootLedgerBase {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (seed : BankWordRenewalFreshSeed ring root s) :
    BankWordRenewalFreshRootLedger ring root seed.1.1 := by
  have hfields :=
    bankWordRenewalFreshHardFields ring root s seed.1 seed.2
  have hidle :=
    bankWordRenewalFrontierFreshRootIdle
      ring root s hn hbank hs seed
  have hlease :=
    (bankWordRenewalFrontierFreshBankPrepared
      ring root s hbank seed).2
  unfold BankWordRenewalFreshRootLedger
  intro _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _
    exact hfields.2.2.1
  · intro h
    rw [hidle] at h
    cases h.1
  · intro h
    rw [hidle] at h
    cases h.1
  · rw [hlease, hfields.2.1]
    simp

/-- Consumer: remote source/target branch of both the
strengthened root/ledger step and J-C. The ROOT record and
all counted soft fields frame under the actual selected
bankWordEpochNext edge. -/
theorem bankWordRenewalFreshRootLedgerStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s)
    (e : Fin n)
    (he : e ≠ root) (hj : ring.rightNeighbor e ≠ root)
    (hclean : BankWordHardEpochCleanInvariant ring root z.1)
    (hroot : BankWordRenewalFreshRootLedger ring root z.1) :
    BankWordHardEpochCleanInvariant ring root
        (bankWordRenewalNext ring root s z e).1 ∧
      BankWordRenewalFreshRootLedger ring root
        (bankWordRenewalNext ring root s z e).1 := by
  have hcleanNext :=
    bankWordRenewalFrontierHardEpochRemoteStep
      ring root z.1 e he hj hclean
  have hframes :=
    bankWordRenewalFrontierNonrootLedgerStep
      ring root z.1 e he
  have hphysical :=
    bankWordHardEpochRootRemoteFrame
      ring root z.1 e he.symm hj.symm
  constructor
  · exact hcleanNext
  · change BankWordRenewalFreshRootLedger ring root
      (bankWordEpochNext ring root z.1 e)
    unfold BankWordRenewalFreshRootLedger at hroot ⊢
    intro hnew
    have hold :
        0 < (bankWordHardEpochLedger ring root z.1).hardEpochs ∧
          (bankWordHardEpochLedger ring root z.1).workerDone =
            false := by
      constructor
      · simpa only [hframes.1] using hnew.1
      · exact hframes.2.2.2.2 hnew.2
    obtain ⟨hquiet, hcurrent, hvalidating, hlease⟩ :=
      hroot hold
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      have hbefore :
          (z.1.2.1 root).ser.cert = .IDLE ∨
            (z.1.2.1 root).ser.cert = .REQUESTED := by
        simpa only [hphysical] using h
      simpa only [hframes.2.2.2.1] using hquiet hbefore
    · intro h
      have hbefore :
          (z.1.2.1 root).ser.cert = .RUNNING ∧
            (z.1.2.1 root).ser.wphase = .CURRENT := by
        simpa only [hphysical] using h
      simpa only [hframes.2.2.2.1] using hcurrent hbefore
    · intro h
      have hbefore :
          (z.1.2.1 root).ser.cert = .RUNNING ∧
            (z.1.2.1 root).ser.wphase = .VALIDATING := by
        simpa only [hphysical] using h
      obtain ⟨hp, hl, hf⟩ := hvalidating hbefore
      refine ⟨?_, ?_, ?_⟩
      · simpa only [hframes.2.2.2.1] using hp
      · simpa only [hphysical] using hl
      · simpa only [hframes.2.2.1] using hf
    · simpa only [hphysical, hframes.2.2.1] using hlease

theorem bankWordRenewalFreshCleanEpochWord {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (seed : BankWordRenewalFreshSeed ring root s)
    (word : List (Fin n))
    (hremote : ∀ e : Fin n, e ∈ word →
      e ≠ root ∧ ring.rightNeighbor e ≠ root) :
    BankWordHardEpochCleanInvariant ring root
        (grantDrainLabelRun (bankWordRenewalNext ring root s)
          seed.1 word).1 ∧
      BankWordRenewalFreshRootLedger ring root
        (grantDrainLabelRun (bankWordRenewalNext ring root s)
          seed.1 word).1 := by
  have hseedClean :=
    bankWordRenewalFrontierFreshBankCleanOfRootClass
      ring root s hn hbank hs seed
  have hseedRoot :=
    bankWordRenewalFreshRootLedgerBase
      ring root s hn hbank hs seed
  have hfold :
      ∀ (w : List (Fin n))
        (z : BankWordRenewalPostSOne ring root s),
        (∀ e : Fin n, e ∈ w →
          e ≠ root ∧ ring.rightNeighbor e ≠ root) →
        BankWordHardEpochCleanInvariant ring root z.1 →
        BankWordRenewalFreshRootLedger ring root z.1 →
        BankWordHardEpochCleanInvariant ring root
          (grantDrainLabelRun (bankWordRenewalNext ring root s)
            z w).1 ∧
        BankWordRenewalFreshRootLedger ring root
          (grantDrainLabelRun (bankWordRenewalNext ring root s)
            z w).1 := by
    intro w
    induction w with
    | nil =>
        intro z _ hc hr
        exact ⟨hc, hr⟩
    | cons e es ih =>
        intro z hw hc hr
        have hge : e ≠ root ∧ ring.rightNeighbor e ≠ root :=
          hw e (List.mem_cons_self ..)
        have htail :
            ∀ a : Fin n, a ∈ es →
              a ≠ root ∧ ring.rightNeighbor a ≠ root := by
          intro a ha
          exact hw a (List.mem_cons_of_mem e ha)
        have hstep :=
          bankWordRenewalFreshRootLedgerStep ring root s
            z e hge.1 hge.2 hc hr
        exact ih (bankWordRenewalNext ring root s z e)
          htail hstep.1 hstep.2
  exact hfold word seed.1 hremote hseedClean hseedRoot

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftOutgoingCoveredDoneFrame
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftReturnSuffixStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftReturnIncomingStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftReturnAllEdgesStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftForwardParentStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftForwardSuffixStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftInactiveRootOutgoingBStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftForwardEdgeCases
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftInternalRowCensus
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftForwardParentRow
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftIncomingQuietFrame
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftTerminalObservedIncomingStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftReturnParentRow
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftInactiveAllEdgesStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftForwardLeafSeamStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftForwardForeignSeamStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftForwardAllEdgesStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftShapeStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftShapeWord
#print axioms L3.RenewalReferenceClock.bankWordRenewalNominatedUpperTailLaw
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftRootedPositionHitStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftRootedWordHitBound
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshNominatedHitBound
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshIncomingDoneOrCompletion
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshSoftLapHitCharge
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshSoftEpisodePairing
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshRootLedgerBase
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshRootLedgerStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalFreshCleanEpochWord
