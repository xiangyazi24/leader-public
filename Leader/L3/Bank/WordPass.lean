import Leader.L3.Bank.WordRenewalClose

/-!
R10 W: the clean-worker pass (research/lean-l3/ledgers/R10W-pass-plan.md).

Layer G of the pass invariant: no VALIDATING serializer anywhere (J-N)
and the exact physical worker shape with the ghost trail
(`BankWordRenewalFrontierPhysicalShape`).  This file proves the
one-edge serializer step of J-N, the literal SI rows under all hard
flags false, and the all-edges step of Layer G with its rank laws.
Consumers: (C*) of the retry estimate, the QWord completion base, and
the monitor coupling (plan page).
-/

namespace L3.RenewalReferenceClock

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-! ## J-N: no VALIDATING serializer is created without a hard S1 -/

/-- No site carries a VALIDATING serializer wphase.
Consumer: all hard flags false on the pass. -/
def BankWordPassNonvalidating {n : Nat}
    (z : BankWordEpochState n) : Prop :=
  ∀ i : Fin n, (z.2.1 i).ser.wphase ≠ .VALIDATING

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 12000 in
/-- One selected pair: without a hard S1 neither endpoint becomes
VALIDATING (the only writers are the zero-lease S1 and the challenge /
enterB copies of a VALIDATING parent).  Consumer: J-N step. -/
theorem bankWordPassSerializerNonvalidating {c : Compiled}
    (x y : ProjW c)
    (hx : x.ser.wphase ≠ .VALIDATING)
    (hy : y.ser.wphase ≠ .VALIDATING)
    (hno : (serW x y).hard.hardS1 = false) :
    (serW x y).x.wphase ≠ .VALIDATING ∧
    (serW x y).y.wphase ≠ .VALIDATING := by
  cases hpx : (postW x y).eX.l <;>
    cases hpy : (postW x y).eY.l <;>
    cases hc : x.ser.cert <;>
    cases hp : x.ser.phase <;>
    cases ho : x.ser.out <;>
    cases hq : y.ser.phase <;>
    simp [serW, serializerStep, ProjW.lift, serTbStar,
      serChallengeWrite, serEnterB, serEnterF, serCanonicalC,
      hpx, hpy, hc, hp, ho, hq, hx, hy] at hno ⊢ <;>
    (repeat' split) <;> simp_all

/-- Hard flags are all false on a nonvalidating pair without a hard S1.
Consumer: the SI row lemmas below. -/
theorem bankWordPassFlagsQuiet {c : Compiled}
    (x y : ProjW c)
    (hx : x.ser.wphase ≠ .VALIDATING)
    (hy : y.ser.wphase ≠ .VALIDATING)
    (hno : (serW x y).hard.hardS1 = false) :
    (serW x y).hard.hardAccept = false ∧
    (serW x y).hard.hardLeft = false ∧
    (serW x y).hard.hardRight = false := by
  have hlr := bankWordRenewalFrontierNonvalidatingGuardsQuiet x y hx hy hno
  refine ⟨?_, hlr.1, hlr.2⟩
  simp [serW, serializerStep, ProjW.lift, hx]

/-! ## Literal SI rows under all hard flags false -/

theorem bankWordPassPrefixAdvanceFields {c : Compiled}
    (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hk : x.si.kind = .PREFIX) (hb : x.si.busy = false)
    (hc : x.si.cur = .NONE) (hj : x.si.j.val < c.t)
    (hy : (postW x y).eY.l = false) (hf : freeSI y.si = true) :
    (workerW x y).row = "P1" ∧
    (workerW x y).x = offSI c.t ∧
    (workerW x y).y.kind = .PREFIX ∧
    (workerW x y).y.busy = false ∧
    (workerW x y).y.cur = .NONE ∧
    (workerW x y).y.j.val = x.si.j.val + 1 ∧
    (workerW x y).done = false := by
  have hj' : x.si.j.val + 1 < c.t + 1 := by omega
  simp [workerW, siStep, ProjW.lift, siJ,
    hfa, hfl, hfr, hk, hb, hc, hj, hj', hy, hf]

theorem bankWordPassPrefixHandoffFields {c : Compiled}
    (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hk : x.si.kind = .PREFIX) (hb : x.si.busy = false)
    (hc : x.si.cur = .NONE) (hj : x.si.j.val = c.t)
    (hy : (postW x y).eY.l = false) (hf : freeSI y.si = true) :
    (workerW x y).row = "P3" ∧
    (workerW x y).x = offSI c.t ∧
    (workerW x y).y = launchRootBack c.t ∧
    (workerW x y).done = false := by
  simp [workerW, siStep, ProjW.lift,
    hfa, hfl, hfr, hk, hb, hc, hj, hy, hf]

theorem bankWordPassBackMoveFields {c : Compiled}
    (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hf : freeSI x.si = true)
    (hcur : y.si.cur = .BACK) (hj : 1 < y.si.j.val)
    (hk : y.si.kind ≠ .PREFIX) :
    (workerW x y).row = "B0" ∧
    (workerW x y).x = setCursor x.si .BACK (y.si.j.val - 1) false false true ∧
    (workerW x y).y = clearCursor y.si ∧
    (workerW x y).done = false := by
  have hfx : x.si.kind = .OFF ∧ x.si.cur = .NONE := by
    simpa [freeSI] using hf
  simp [workerW, siStep, ProjW.lift, freeSI,
    hfa, hfl, hfr, hfx.1, hfx.2, hcur, hj, hk]

theorem bankWordPassBackInitFields {c : Compiled}
    (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hf : freeSI x.si = true)
    (hcur : y.si.cur = .BACK) (hj : y.si.j.val = 1)
    (hk : y.si.kind ≠ .PREFIX) :
    (workerW x y).row = "B1" ∧
    (workerW x y).x = setCursor x.si .SUM 0 false false true ∧
    (workerW x y).y = clearCursor y.si ∧
    (workerW x y).done = false := by
  have hfx : x.si.kind = .OFF ∧ x.si.cur = .NONE := by
    simpa [freeSI] using hf
  simp [workerW, siStep, ProjW.lift, freeSI,
    hfa, hfl, hfr, hfx.1, hfx.2, hcur, hj, hk]

theorem bankWordPassSumMoveFields {c : Compiled}
    (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hk : x.si.kind = .OFF) (hc : x.si.cur = .SUM)
    (hj : x.si.j.val + 1 < c.t) (hf : freeSI y.si = true) :
    (workerW x y).row = "S0" ∧
    (workerW x y).x = clearCursor x.si ∧
    (workerW x y).y.kind = y.si.kind ∧
    (workerW x y).y.busy = y.si.busy ∧
    (workerW x y).y.cur = .SUM ∧
    (workerW x y).y.j.val = x.si.j.val + 1 ∧
    (workerW x y).done = false := by
  have hj' : x.si.j.val + 1 < c.t + 1 := by omega
  have hfy : y.si.kind = .OFF ∧ y.si.cur = .NONE := by
    simpa [freeSI] using hf
  simp [workerW, siStep, ProjW.lift, setCursor, siJ, freeSI,
    hfa, hfl, hfr, hk, hc, hj, hj', hfy.1, hfy.2]

theorem bankWordPassSumPublishFields {c : Compiled}
    (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hk : x.si.kind = .OFF) (hc : x.si.cur = .SUM)
    (hj : x.si.j.val + 1 = c.t)
    (hrk : y.si.kind = .ROOT) (hrb : y.si.busy = true) :
    (workerW x y).row = "S1" ∧
    (workerW x y).x = clearCursor x.si ∧
    (workerW x y).y.kind = .ROOT ∧
    (workerW x y).y.busy = false ∧
    (workerW x y).y.cur = .NONE ∧
    (workerW x y).done = false := by
  simp [workerW, siStep, ProjW.lift, freeSI,
    hfa, hfl, hfr, hk, hc, hj, hrk, hrb]

theorem bankWordPassAdvanceFields {c : Compiled}
    (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hk : x.si.kind = .ROOT) (hb : x.si.busy = false)
    (hc : x.si.cur = .NONE)
    (hy : (postW x y).eY.l = false) (hf : freeSI y.si = true) :
    (workerW x y).row = "A1" ∧
    (workerW x y).x = offSI c.t ∧
    (workerW x y).y = launchRootBack c.t ∧
    (workerW x y).done = false := by
  have hfy : y.si.kind = .OFF ∧ y.si.cur = .NONE := by
    simpa [freeSI] using hf
  simp [workerW, siStep, ProjW.lift, freeSI,
    hfa, hfl, hfr, hk, hb, hc, hy, hfy.1, hfy.2]

theorem bankWordPassTerminalFields {c : Compiled}
    (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hk : x.si.kind = .ROOT) (hb : x.si.busy = false)
    (hc : x.si.cur = .NONE)
    (hy : (postW x y).eY.l = true) (hf : freeSI y.si = true) :
    (workerW x y).row = "A0" ∧
    (workerW x y).x = offSI c.t ∧
    (workerW x y).y = y.si ∧
    (workerW x y).done = true := by
  have hfy : y.si.kind = .OFF ∧ y.si.cur = .NONE := by
    simpa [freeSI] using hf
  simp [workerW, siStep, ProjW.lift, freeSI,
    hfa, hfl, hfr, hk, hb, hc, hy, hfy.1, hfy.2]

/-- A free source whose responder is not a BACK cursor: frame. -/
theorem bankWordPassFrameFreeSource {c : Compiled}
    (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hk : x.si.kind = .OFF) (hc : x.si.cur = .NONE)
    (hyc : y.si.cur ≠ .BACK) :
    (workerW x y).row = "F" ∧
    (workerW x y).x = x.si ∧
    (workerW x y).y = y.si ∧
    (workerW x y).done = false := by
  simp [workerW, siStep, ProjW.lift, freeSI,
    hfa, hfl, hfr, hk, hc, hyc]

/-- A busy ROOT source whose responder is not a BACK cursor: frame. -/
theorem bankWordPassFrameBusySource {c : Compiled}
    (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hk : x.si.kind = .ROOT) (hb : x.si.busy = true) :
    (workerW x y).row = "F" ∧
    (workerW x y).x = x.si ∧
    (workerW x y).y = y.si ∧
    (workerW x y).done = false := by
  simp [workerW, siStep, ProjW.lift, freeSI,
    hfa, hfl, hfr, hk, hb]

/-- An OFF site holding a BACK cursor as source, responder not a
BACK cursor: frame. -/
theorem bankWordPassFrameBackSource {c : Compiled}
    (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hk : x.si.kind = .OFF) (hc : x.si.cur = .BACK) :
    (workerW x y).row = "F" ∧
    (workerW x y).x = x.si ∧
    (workerW x y).y = y.si ∧
    (workerW x y).done = false := by
  simp [workerW, siStep, ProjW.lift, freeSI,
    hfa, hfl, hfr, hk, hc]


/-! ## Geometry and record frames on the epoch chain -/

theorem bankWordPassSiteWrap {n : Nat} (ring : DirectedRing n)
    (root : Fin n) : L3.EWord.site ring root n = root := by
  apply Fin.ext
  simp [L3.EWord.site, PPL.shiftRight, Nat.mod_eq_of_lt root.isLt]

/-- Two sites with distinct offsets below n are distinct. -/
theorem bankWordPassSiteNe {n : Nat} (ring : DirectedRing n)
    (root : Fin n) (i j : Nat) (hi : i < n) (hj : j < n) (hne : i ≠ j) :
    L3.EWord.site ring root i ≠ L3.EWord.site ring root j :=
  fun h => hne (L3.EWord.validationSiteInjective ring root i j hi hj h)

/-- BANK width facts for the pass: `2 ≤ t` and `t + 2 ≤ n`. -/
theorem bankWordPassWidth {n : Nat}
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    2 ≤ (compileAdvice (ceilLogTwo n)).t ∧
    (compileAdvice (ceilLogTwo n)).t + 2 ≤ n := by
  refine ⟨?_, bankWordRenewalFrontierBankRoom hbank⟩
  rw [bankWordHardEpochBankSourceWidth hbank]
  have h80 := bankWordHardEpochBankAdviceLower hbank
  exact ceilLogTwo_ge_two _ (by omega)

theorem bankWordPassPairSILeft {c : Compiled} (x y : ProjW c) :
    (pairW x y).1.si = (workerW x y).x := rfl

theorem bankWordPassPairSIRight {c : Compiled} (x y : ProjW c) :
    (pairW x y).2.si = (workerW x y).y := rfl

theorem bankWordPassSourceRecord {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n) :
    (bankWordEpochNext ring root z e).2.1 e =
      (pairW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).1 := by
  rw [bankWordEpochPhysicalNext]
  simp [phiW, projectedEdge]

theorem bankWordPassTargetRecord {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    (bankWordEpochNext ring root z e).2.1 (ring.rightNeighbor e) =
      (pairW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).2 := by
  rw [bankWordEpochPhysicalNext]
  simp [phiW, projectedEdge, hne]

theorem bankWordPassRemoteRecord {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e i : Fin n)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    (bankWordEpochNext ring root z e).2.1 i = z.2.1 i := by
  rw [bankWordEpochPhysicalNext]
  simp [phiW, projectedEdge, hi, hj]

theorem bankWordPassGhostWorker {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n) :
    (bankWordEpochNext ring root z e).2.2.worker =
      (wWorkerReceiptStep root e (ring.rightNeighbor e)
        (z.2.2.clock + 1) (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        (wGenuineAcceptance root e (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (z.2.2.validation e) (z.2.2.validation (ring.rightNeighbor e)))
        z.2.2.worker).1 := rfl

theorem bankWordPassGhostCompletion {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n) :
    (bankWordEpochNext ring root z e).2.2.completion =
      (wWorkerReceiptStep root e (ring.rightNeighbor e)
        (z.2.2.clock + 1) (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        (wGenuineAcceptance root e (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (z.2.2.validation e) (z.2.2.validation (ring.rightNeighbor e)))
        z.2.2.worker).2 := rfl

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 12000 in
/-- J-N transfers along one edge without a hard S1. -/
theorem bankWordPassNonvalidatingStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (hN : BankWordPassNonvalidating z)
    (hno : (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 = false) :
    BankWordPassNonvalidating (bankWordEpochNext ring root z e) := by
  have hn2 : 2 ≤ n := by omega
  have hne := clockNeighborDifferent ring hn2 e
  have hser := bankWordPassSerializerNonvalidating (z.2.1 e)
    (z.2.1 (ring.rightNeighbor e)) (hN e) (hN _) hno
  intro i
  by_cases hi : i = e
  · subst hi
    rw [bankWordPassSourceRecord, pairW_ser_left]
    exact hser.1
  · by_cases hj : i = ring.rightNeighbor e
    · subst hj
      rw [bankWordPassTargetRecord ring root z e hne, pairW_ser_right]
      exact hser.2
    · rw [bankWordPassRemoteRecord ring root z e i hi hj]
      exact hN i

/-- The shape depends only on the SI fields and the ghost worker. -/
theorem bankWordPassShapeOfSIEq {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z z' : BankWordEpochState n)
    (hsi : ∀ i : Fin n, (z'.2.1 i).si = (z.2.1 i).si)
    (hw : z'.2.2.worker = z.2.2.worker)
    (h : BankWordRenewalFrontierPhysicalShape ring root z) :
    BankWordRenewalFrontierPhysicalShape ring root z' := by
  obtain ⟨w, hwz, hsh⟩ := h
  refine ⟨w, by rw [hw]; exact hwz, ?_⟩
  revert hsh
  cases w.phase <;> simp only [hsi] <;> exact id

/-- A frame row (both SI fields unchanged, no hard S1) keeps the ghost
trail and the whole SI field.  Consumer: the non-nominated edges. -/
theorem bankWordPassFrameStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n) (w : WWorkerTrail n)
    (hw : z.2.2.worker = some w)
    (hno : (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 = false)
    (hrow : (workerW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).row = "F")
    (hx : (workerW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).x = (z.2.1 e).si)
    (hy : (workerW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).y =
      (z.2.1 (ring.rightNeighbor e)).si) :
    (∀ i : Fin n, ((bankWordEpochNext ring root z e).2.1 i).si = (z.2.1 i).si) ∧
    (bankWordEpochNext ring root z e).2.2.worker = some w := by
  have hn2 : 2 ≤ n := by omega
  have hne := clockNeighborDifferent ring hn2 e
  refine ⟨?_, ?_⟩
  · intro i
    by_cases hi : i = e
    · subst hi
      rw [bankWordPassSourceRecord, bankWordPassPairSILeft, hx]
    · by_cases hj : i = ring.rightNeighbor e
      · subst hj
        rw [bankWordPassTargetRecord ring root z e hne, bankWordPassPairSIRight, hy]
      · rw [bankWordPassRemoteRecord ring root z e i hi hj]
  · exact (bankWordRenewalFrontierPhysicalFrame ring root z e w hw hrow hno).1

/-! ## Ghost trail moves on the literal rows -/

theorem bankWordPassGhostPrefixAdvance {n : Nat} {c : Compiled}
    (root edge next : Fin n) (clock : Nat) (x y : ProjW c)
    (accept : Option WValidationTicket) (w : WWorkerTrail n)
    (hrow : (workerW x y).row = "P1")
    (hno : (serW x y).hard.hardS1 = false)
    (hphase : w.phase = .prefixRun) (hhost : w.host = edge)
    (hidx : x.si.j.val = w.index) :
    ∃ w' : WWorkerTrail n,
      (wWorkerReceiptStep root edge next clock x y accept (some w)).1 = some w' ∧
      w'.phase = .prefixRun ∧ w'.host = next ∧ w'.target = w.target ∧
      w'.index = w.index + 1 := by
  simp [wWorkerReceiptStep, hrow, hno, hphase, hhost, hidx]

theorem bankWordPassGhostPrefixHandoff {n : Nat} {c : Compiled}
    (root edge next : Fin n) (clock : Nat) (x y : ProjW c)
    (accept : Option WValidationTicket) (w : WWorkerTrail n)
    (hrow : (workerW x y).row = "P3")
    (hno : (serW x y).hard.hardS1 = false)
    (hphase : w.phase = .prefixRun) (hhost : w.host = edge)
    (hidx : w.index = c.t) :
    ∃ w' : WWorkerTrail n,
      (wWorkerReceiptStep root edge next clock x y accept (some w)).1 = some w' ∧
      w'.phase = .backRun ∧ w'.host = next ∧ w'.target = next ∧
      w'.index = c.t := by
  simp [wWorkerReceiptStep, hrow, hno, hphase, hhost, hidx]

theorem bankWordPassGhostBackMove {n : Nat} {c : Compiled}
    (root edge next : Fin n) (clock : Nat) (x y : ProjW c)
    (accept : Option WValidationTicket) (w : WWorkerTrail n)
    (hrow : (workerW x y).row = "B0")
    (hno : (serW x y).hard.hardS1 = false)
    (hphase : w.phase = .backRun) (hhost : w.host = next)
    (hidx : y.si.j.val = w.index) :
    ∃ w' : WWorkerTrail n,
      (wWorkerReceiptStep root edge next clock x y accept (some w)).1 = some w' ∧
      w'.phase = .backRun ∧ w'.host = edge ∧ w'.target = w.target ∧
      w'.index = w.index - 1 := by
  simp [wWorkerReceiptStep, hrow, hno, hphase, hhost, hidx]

theorem bankWordPassGhostBackInit {n : Nat} {c : Compiled}
    (root edge next : Fin n) (clock : Nat) (x y : ProjW c)
    (accept : Option WValidationTicket) (w : WWorkerTrail n)
    (hrow : (workerW x y).row = "B1")
    (hno : (serW x y).hard.hardS1 = false)
    (hphase : w.phase = .backRun) (hhost : w.host = next)
    (hidx : w.index = 1) :
    ∃ w' : WWorkerTrail n,
      (wWorkerReceiptStep root edge next clock x y accept (some w)).1 = some w' ∧
      w'.phase = .sumRun ∧ w'.host = edge ∧ w'.target = w.target ∧
      w'.index = 0 := by
  simp [wWorkerReceiptStep, hrow, hno, hphase, hhost, hidx]

theorem bankWordPassGhostSumMove {n : Nat} {c : Compiled}
    (root edge next : Fin n) (clock : Nat) (x y : ProjW c)
    (accept : Option WValidationTicket) (w : WWorkerTrail n)
    (hrow : (workerW x y).row = "S0")
    (hno : (serW x y).hard.hardS1 = false)
    (hphase : w.phase = .sumRun) (hhost : w.host = edge)
    (hidx : x.si.j.val = w.index) :
    ∃ w' : WWorkerTrail n,
      (wWorkerReceiptStep root edge next clock x y accept (some w)).1 = some w' ∧
      w'.phase = .sumRun ∧ w'.host = next ∧ w'.target = w.target ∧
      w'.index = w.index + 1 := by
  simp [wWorkerReceiptStep, hrow, hno, hphase, hhost, hidx]

theorem bankWordPassGhostSumPublish {n : Nat} {c : Compiled}
    (root edge next : Fin n) (clock : Nat) (x y : ProjW c)
    (accept : Option WValidationTicket) (w : WWorkerTrail n)
    (hrow : (workerW x y).row = "S1")
    (hno : (serW x y).hard.hardS1 = false)
    (hphase : w.phase = .sumRun) (hhost : w.host = edge)
    (htarget : w.target = next)
    (hidx : x.si.j.val = w.index) :
    ∃ w' : WWorkerTrail n,
      (wWorkerReceiptStep root edge next clock x y accept (some w)).1 = some w' ∧
      w'.phase = .readyRun ∧ w'.host = next ∧ w'.target = w.target ∧
      w'.index = 0 := by
  simp [wWorkerReceiptStep, hrow, hno, hphase, hhost, htarget, hidx]

theorem bankWordPassGhostAdvance {n : Nat} {c : Compiled}
    (root edge next : Fin n) (clock : Nat) (x y : ProjW c)
    (accept : Option WValidationTicket) (w : WWorkerTrail n)
    (hrow : (workerW x y).row = "A1")
    (hno : (serW x y).hard.hardS1 = false)
    (hphase : w.phase = .readyRun) (hhost : w.host = edge) :
    ∃ w' : WWorkerTrail n,
      (wWorkerReceiptStep root edge next clock x y accept (some w)).1 = some w' ∧
      w'.phase = .backRun ∧ w'.host = next ∧ w'.target = next ∧
      w'.index = c.t := by
  simp [wWorkerReceiptStep, hrow, hno, hphase, hhost]

theorem bankWordPassGhostTerminal {n : Nat} {c : Compiled}
    (root edge next : Fin n) (clock : Nat) (x y : ProjW c)
    (accept : Option WValidationTicket) (w : WWorkerTrail n)
    (hrow : (workerW x y).row = "A0")
    (hno : (serW x y).hard.hardS1 = false)
    (hphase : w.phase = .readyRun) (hhost : w.host = edge)
    (hnext : next = root) :
    (wWorkerReceiptStep root edge next clock x y accept (some w)).1 = none ∧
    (wWorkerReceiptStep root edge next clock x y accept (some w)).2 =
      some { service := clock, worker := w } := by
  simp [wWorkerReceiptStep, hrow, hno, hphase, hhost, hnext]

/-! ## Layer G: the pass shape, its nomination and its rank -/

/-- A busy target whose cursor has left it (BACK with host away from
the target, or SUM) carries no cursor, so no edge into it fires a
backward row.  Consumer: the frame classification of Layer G. -/
def BankWordPassTargetQuiet {n : Nat}
    (z : BankWordEpochState n) : Prop :=
  ∀ w : WWorkerTrail n, z.2.2.worker = some w →
    ((w.phase = .backRun ∧ w.host ≠ w.target) ∨ w.phase = .sumRun) →
    (z.2.1 w.target).si.cur = .NONE

/-- Layer G of the pass invariant: J-N, the exact physical worker
shape with the ghost trail, and the quiet busy target.
Consumer: (C*) and the completion base. -/
def BankWordPassShape {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) : Prop :=
  BankWordPassNonvalidating z ∧
    BankWordRenewalFrontierPhysicalShape ring root z ∧
    BankWordPassTargetQuiet z

theorem bankWordPassTargetQuietOfSIEq {n : Nat}
    (z z' : BankWordEpochState n)
    (hsi : ∀ i : Fin n, (z'.2.1 i).si = (z.2.1 i).si)
    (hw : z'.2.2.worker = z.2.2.worker)
    (h : BankWordPassTargetQuiet z) : BankWordPassTargetQuiet z' := by
  intro w hw' hcase
  rw [hsi]
  exact h w (by rw [← hw]; exact hw') hcase

/-- A frame edge keeps Layer G.  Consumer: all non-nominated edges. -/
theorem bankWordPassFrameShape {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n) (w : WWorkerTrail n)
    (hw : z.2.2.worker = some w)
    (hsh : BankWordRenewalFrontierPhysicalShape ring root z)
    (hTQ : BankWordPassTargetQuiet z)
    (hN' : BankWordPassNonvalidating (bankWordEpochNext ring root z e))
    (hsi : ∀ i : Fin n, ((bankWordEpochNext ring root z e).2.1 i).si = (z.2.1 i).si)
    (hw' : (bankWordEpochNext ring root z e).2.2.worker = some w) :
    BankWordPassShape ring root (bankWordEpochNext ring root z e) ∧
    (bankWordEpochNext ring root z e).2.2.worker = some w :=
  ⟨⟨hN', bankWordPassShapeOfSIEq ring root z _ hsi (by rw [hw', hw]) hsh,
    bankWordPassTargetQuietOfSIEq z _ hsi (by rw [hw', hw]) hTQ⟩, hw'⟩

/-- The retired pass after its A0: no trail, a completion receipt,
every SI free, still nonvalidating.  Consumer: the QWord base. -/
def BankWordPassRetired {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) : Prop :=
  BankWordPassNonvalidating z ∧
    z.2.2.worker = none ∧
    BankWordRenewalCompleted z ∧
    ∀ i : Fin n, freeSI (z.2.1 i).si = true

/-- The predictable nominated edge of the pass, from the ghost trail:
PREFIX/SUM/READY nominate the host, BACK nominates the edge into the
host (its source is the host's predecessor offset).  Without a trail
the root is nominated. -/
noncomputable def bankWordPassNomination {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) : Fin n :=
  match z.2.2.worker with
  | none => root
  | some w =>
    match w.phase with
    | .backRun =>
        L3.EWord.site ring root
          (PPL.cyclicOffset ring root w.target -
            ((compileAdvice (ceilLogTwo n)).t - w.index) - 1)
    | _ => w.host

/-- Remaining nominated services of the trail (`C = 2t+1`). -/
noncomputable def bankWordPassRank {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) : Nat :=
  match z.2.2.worker with
  | none => 0
  | some w =>
    match w.phase with
    | .prefixRun =>
        ((compileAdvice (ceilLogTwo n)).t + 1 - w.index) +
          (n - (compileAdvice (ceilLogTwo n)).t - 1) *
            (2 * (compileAdvice (ceilLogTwo n)).t + 1)
    | .backRun =>
        (n - 1 - PPL.cyclicOffset ring root w.target) *
            (2 * (compileAdvice (ceilLogTwo n)).t + 1) +
          w.index + (compileAdvice (ceilLogTwo n)).t + 1
    | .sumRun =>
        (n - 1 - PPL.cyclicOffset ring root w.target) *
            (2 * (compileAdvice (ceilLogTwo n)).t + 1) +
          ((compileAdvice (ceilLogTwo n)).t - w.index) + 1
    | .readyRun =>
        (n - 1 - PPL.cyclicOffset ring root w.target) *
            (2 * (compileAdvice (ceilLogTwo n)).t + 1) + 1

theorem bankWordPassRankOfWorkerEq {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z z' : BankWordEpochState n)
    (hw : z'.2.2.worker = z.2.2.worker) :
    bankWordPassRank ring root z' = bankWordPassRank ring root z := by
  unfold bankWordPassRank
  rw [hw]

theorem bankWordPassNominationOfWorkerEq {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z z' : BankWordEpochState n)
    (hw : z'.2.2.worker = z.2.2.worker) :
    bankWordPassNomination ring root z' = bankWordPassNomination ring root z := by
  unfold bankWordPassNomination
  rw [hw]


/-! ## Small SI facts -/

theorem bankWordPassFreeFields {t : Nat} (s : SI t) (h : freeSI s = true) :
    s.kind = .OFF ∧ s.cur = .NONE := by
  simpa [freeSI] using h

theorem bankWordPassFreeOff (t : Nat) : freeSI (offSI t) = true := rfl

theorem bankWordPassFreeClear {t : Nat} (s : SI t) (hk : s.kind = .OFF) :
    freeSI (clearCursor s) = true := by
  simp [freeSI, clearCursor, hk]

/-- The nomination at a PREFIX/SUM/READY trail is the host. -/
theorem bankWordPassNominationHost {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (w : WWorkerTrail n)
    (hw : z.2.2.worker = some w)
    (hphase : w.phase = .prefixRun ∨ w.phase = .sumRun ∨ w.phase = .readyRun) :
    bankWordPassNomination ring root z = w.host := by
  unfold bankWordPassNomination
  rw [hw]
  rcases hphase with h | h | h <;> simp [h]

theorem bankWordPassNominationBack {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (w : WWorkerTrail n)
    (hw : z.2.2.worker = some w) (hphase : w.phase = .backRun) :
    bankWordPassNomination ring root z =
      L3.EWord.site ring root
        (PPL.cyclicOffset ring root w.target -
          ((compileAdvice (ceilLogTwo n)).t - w.index) - 1) := by
  unfold bankWordPassNomination
  rw [hw]
  simp [hphase]

/-- Post-E flag of the responder at a selected edge, from the fixed
root: the responder is the leader iff it is the root. -/
theorem bankWordPassResponderFlag {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z) (e : Fin n) :
    (postW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).eY.l =
      decide (ring.rightNeighbor e = root) := by
  have hn2 : 2 ≤ n := by omega
  have hfixed := bankWordEpochFixedRootNext ring hn hbank root s hs z hz e
  rcases clockPostTrichotomy ring root z.2.1 e hn2 hfixed with
    ⟨he, _, hpy⟩ | ⟨hj, _, hpy⟩ | ⟨_, hnj, _, hpy⟩
  · rw [hpy]
    have hj : ring.rightNeighbor e ≠ root := by
      rw [he]
      exact clockNeighborDifferent ring hn2 root
    simp [hj]
  · rw [hpy]
    simp [hj]
  · rw [hpy]
    simp [hnj]

/-! ## Layer G step, PREFIX phase -/

theorem bankWordPassPrefixStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z) (e : Fin n)
    (hN : BankWordPassNonvalidating z)
    (w : WWorkerTrail n) (hw : z.2.2.worker = some w)
    (hphase : w.phase = .prefixRun)
    (hsh : BankWordRenewalFrontierPhysicalShape ring root z)
    (hTQ : BankWordPassTargetQuiet z)
    (hno : (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 = false) :
    (e ≠ bankWordPassNomination ring root z →
      BankWordPassShape ring root (bankWordEpochNext ring root z e) ∧
      (bankWordEpochNext ring root z e).2.2.worker = some w) ∧
    (e = bankWordPassNomination ring root z →
      BankWordPassShape ring root (bankWordEpochNext ring root z e) ∧
      bankWordPassRank ring root (bankWordEpochNext ring root z e) + 1 =
        bankWordPassRank ring root z) := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨ht2, hroom⟩ := bankWordPassWidth hbank
  have hsh₀ := hsh
  have hnom := bankWordPassNominationHost ring root z w hw (Or.inl hphase)
  have hN' := bankWordPassNonvalidatingStep ring hn root z e hN hno
  have hflags := bankWordPassFlagsQuiet (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
    (hN e) (hN _) hno
  obtain ⟨hfa, hfl, hfr⟩ := hflags
  have hnoroot := bankWordRenewalFrontierShapePrefixNoRoot ring root z hbank hsh w hw hphase
  obtain ⟨w₀, hw₀, hfields⟩ := hsh
  rw [hw] at hw₀
  cases hw₀
  simp only [hphase] at hfields
  obtain ⟨htarget, hindex, hindexn, hhost, hk, hb, hc, hjv, hother⟩ := hfields
  rw [hnom]
  constructor
  · intro he
    have hxfree := hother e he
    obtain ⟨hxk, hxc⟩ := bankWordPassFreeFields _ hxfree
    have hyc : (z.2.1 (ring.rightNeighbor e)).si.cur ≠ .BACK := by
      by_cases hj : ring.rightNeighbor e = w.host
      · rw [hj, hc]
        exact fun h => by cases h
      · rw [(bankWordPassFreeFields _ (hother _ hj)).2]
        exact fun h => by cases h
    obtain ⟨hrow, hx, hy, _⟩ := bankWordPassFrameFreeSource _ _ hfa hfl hfr hxk hxc hyc
    obtain ⟨hsi, hw'⟩ := bankWordPassFrameStep ring hn root z e w hw hno hrow hx hy
    exact bankWordPassFrameShape ring root z e w hw hsh₀ hTQ hN' hsi hw'
  · intro he
    rw [← he] at hk hb hc hjv hhost hother hnoroot
    have hne := clockNeighborDifferent ring hn2 e
    have hyfree := hother _ hne
    have hpy : (postW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).eY.l = false := by
      rw [bankWordPassResponderFlag ring hn hbank root s hs z hz e]
      simp [hnoroot]
    have hsucc : ring.rightNeighbor e = L3.EWord.site ring root (w.index + 1) := by
      rw [hhost]
      exact L3.EWord.siteSuccessor ring root w.index
    by_cases hidx : w.index < (compileAdvice (ceilLogTwo n)).t
    · -- P1
      have hj : (z.2.1 e).si.j.val < (compileAdvice (ceilLogTwo n)).t := by
        rw [hjv]; exact hidx
      obtain ⟨hrow, hx, hyk, hyb, hyc, hyj, _⟩ :=
        bankWordPassPrefixAdvanceFields _ _ hfa hfl hfr hk hb hc hj hpy hyfree
      obtain ⟨w', hw', hp', hh', ht', hi'⟩ :=
        bankWordPassGhostPrefixAdvance root e (ring.rightNeighbor e)
          (z.2.2.clock + 1) (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (wGenuineAcceptance root e (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
            (z.2.2.validation e) (z.2.2.validation (ring.rightNeighbor e)))
          w hrow hno hphase he.symm hjv
      have hworker' : (bankWordEpochNext ring root z e).2.2.worker = some w' := by
        rw [bankWordPassGhostWorker, hw]; exact hw'
      have hsiTarget : ((bankWordEpochNext ring root z e).2.1 (ring.rightNeighbor e)).si =
          (workerW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).y := by
        rw [bankWordPassTargetRecord ring root z e hne, bankWordPassPairSIRight]
      have hsiSource : ((bankWordEpochNext ring root z e).2.1 e).si = offSI _ := by
        rw [bankWordPassSourceRecord, bankWordPassPairSILeft, hx]
      refine ⟨⟨hN', ⟨w', hworker', ?_⟩, ?_⟩, ?_⟩
      · simp only [hp']
        refine ⟨by rw [ht']; exact htarget, by omega, by omega,
          by rw [hh', hi', hsucc], ?_, ?_, ?_, ?_, ?_⟩
        · rw [hh', hsiTarget]; exact hyk
        · rw [hh', hsiTarget]; exact hyb
        · rw [hh', hsiTarget]; exact hyc
        · rw [hh', hsiTarget, hyj, hjv, hi']
        · intro i hi
          rw [hh'] at hi
          by_cases hie : i = e
          · subst hie
            rw [hsiSource]
            exact bankWordPassFreeOff _
          · rw [bankWordPassRemoteRecord ring root z e i hie hi]
            exact hother i hie
      · intro w'' hw'' hcase
        rw [hworker'] at hw''
        cases hw''
        rcases hcase with ⟨hb', _⟩ | hs'
        · rw [hp'] at hb'; cases hb'
        · rw [hp'] at hs'; cases hs'
      · unfold bankWordPassRank
        rw [hworker', hw]
        simp only [hp', hphase]
        generalize (n - (compileAdvice (ceilLogTwo n)).t - 1) *
          (2 * (compileAdvice (ceilLogTwo n)).t + 1) = K
        omega
    · -- P3
      have hidxt : w.index = (compileAdvice (ceilLogTwo n)).t := by omega
      have hj : (z.2.1 e).si.j.val = (compileAdvice (ceilLogTwo n)).t := by
        rw [hjv]; exact hidxt
      obtain ⟨hrow, hx, hy, _⟩ :=
        bankWordPassPrefixHandoffFields _ _ hfa hfl hfr hk hb hc hj hpy hyfree
      obtain ⟨w', hw', hp', hh', ht', hi'⟩ :=
        bankWordPassGhostPrefixHandoff root e (ring.rightNeighbor e)
          (z.2.2.clock + 1) (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (wGenuineAcceptance root e (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
            (z.2.2.validation e) (z.2.2.validation (ring.rightNeighbor e)))
          w hrow hno hphase he.symm hidxt
      have hworker' : (bankWordEpochNext ring root z e).2.2.worker = some w' := by
        rw [bankWordPassGhostWorker, hw]; exact hw'
      have hsiTarget : ((bankWordEpochNext ring root z e).2.1 (ring.rightNeighbor e)).si =
          launchRootBack _ := by
        rw [bankWordPassTargetRecord ring root z e hne, bankWordPassPairSIRight, hy]
      have hsiSource : ((bankWordEpochNext ring root z e).2.1 e).si = offSI _ := by
        rw [bankWordPassSourceRecord, bankWordPassPairSILeft, hx]
      have hsite : ring.rightNeighbor e =
          L3.EWord.site ring root ((compileAdvice (ceilLogTwo n)).t + 1) := by
        rw [hsucc, hidxt]
      have hoff : PPL.cyclicOffset ring root (ring.rightNeighbor e) =
          (compileAdvice (ceilLogTwo n)).t + 1 := by
        rw [hsite]
        exact L3.EWord.validationSiteOffset ring root _ (by omega)
      refine ⟨⟨hN', ⟨w', hworker', ?_⟩, ?_⟩, ?_⟩
      · simp only [hp']
        refine ⟨(compileAdvice (ceilLogTwo n)).t + 1, Nat.le_refl _, by omega,
          by rw [hi']; omega, by rw [hi']; exact Nat.le_refl _, by rw [ht']; exact hsite,
          by rw [hh', hi', Nat.sub_self, Nat.sub_zero]; exact hsite, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hh', hsiTarget]; rfl
        · rw [hh', hsiTarget, hi']; rfl
        · rw [ht', hsiTarget]; rfl
        · rw [ht', hsiTarget]; rfl
        · rw [hh', ht', if_pos rfl, hsiTarget]; rfl
        · intro i hi _
          rw [hh'] at hi
          by_cases hie : i = e
          · subst hie
            rw [hsiSource]
            exact bankWordPassFreeOff _
          · rw [bankWordPassRemoteRecord ring root z e i hie hi]
            exact hother i hie
      · intro w'' hw'' hcase
        rw [hworker'] at hw''
        cases hw''
        rcases hcase with ⟨_, hne'⟩ | hs'
        · exact absurd (hh'.trans ht'.symm) hne'
        · rw [hp'] at hs'; cases hs'
      · unfold bankWordPassRank
        rw [hworker', hw]
        simp only [hp', hphase]
        rw [ht', hoff, hi', hidxt]
        have h1 : n - 1 - ((compileAdvice (ceilLogTwo n)).t + 1) =
            n - (compileAdvice (ceilLogTwo n)).t - 2 := by omega
        have h2 : n - (compileAdvice (ceilLogTwo n)).t - 1 =
            (n - (compileAdvice (ceilLogTwo n)).t - 2) + 1 := by omega
        rw [h1, h2, Nat.add_mul, Nat.one_mul]
        generalize (n - (compileAdvice (ceilLogTwo n)).t - 2) *
          (2 * (compileAdvice (ceilLogTwo n)).t + 1) = K
        omega


theorem bankWordPassRightNeighborInjective {n : Nat}
    (ring : DirectedRing n) (a b : Fin n)
    (h : ring.rightNeighbor a = ring.rightNeighbor b) : a = b := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  change (a.val + 1) % n = (b.val + 1) % n at hv
  have ha := a.isLt
  have hb := b.isLt
  by_cases ha1 : a.val + 1 < n
  · rw [Nat.mod_eq_of_lt ha1] at hv
    by_cases hb1 : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb1] at hv
      omega
    · have hbn : b.val + 1 = n := by omega
      rw [hbn, Nat.mod_self] at hv
      omega
  · have han : a.val + 1 = n := by omega
    rw [han, Nat.mod_self] at hv
    by_cases hb1 : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb1] at hv
      omega
    · omega

/-! ## Layer G step, BACK phase -/

theorem bankWordPassBackStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z) (e : Fin n)
    (hN : BankWordPassNonvalidating z)
    (w : WWorkerTrail n) (hw : z.2.2.worker = some w)
    (hphase : w.phase = .backRun)
    (hsh : BankWordRenewalFrontierPhysicalShape ring root z)
    (hTQ : BankWordPassTargetQuiet z)
    (hno : (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 = false) :
    (e ≠ bankWordPassNomination ring root z →
      BankWordPassShape ring root (bankWordEpochNext ring root z e) ∧
      (bankWordEpochNext ring root z e).2.2.worker = some w) ∧
    (e = bankWordPassNomination ring root z →
      BankWordPassShape ring root (bankWordEpochNext ring root z e) ∧
      bankWordPassRank ring root (bankWordEpochNext ring root z e) + 1 =
        bankWordPassRank ring root z) := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨ht2, hroom⟩ := bankWordPassWidth hbank
  have hsh₀ := hsh
  have hN' := bankWordPassNonvalidatingStep ring hn root z e hN hno
  obtain ⟨hfa, hfl, hfr⟩ := bankWordPassFlagsQuiet (z.2.1 e)
    (z.2.1 (ring.rightNeighbor e)) (hN e) (hN _) hno
  have hne := clockNeighborDifferent ring hn2 e
  obtain ⟨w₀, hw₀, hfields⟩ := hsh
  rw [hw] at hw₀
  cases hw₀
  simp only [hphase] at hfields
  obtain ⟨k, hk1, hkn, hipos, hit, htarget, hhost, hcur, hjv, htk, htb, hhk, hother⟩ := hfields
  have hoff : PPL.cyclicOffset ring root w.target = k := by
    rw [htarget]
    exact L3.EWord.validationSiteOffset ring root k hkn
  have hnom : bankWordPassNomination ring root z =
      L3.EWord.site ring root
        (k - ((compileAdvice (ceilLogTwo n)).t - w.index) - 1) := by
    rw [bankWordPassNominationBack ring root z w hw hphase, hoff]
  have hsuccm : ring.rightNeighbor
      (L3.EWord.site ring root (k - ((compileAdvice (ceilLogTwo n)).t - w.index) - 1)) =
      w.host := by
    rw [hhost, L3.EWord.siteSuccessor]
    congr 1
    omega
  have hTQ' : w.host ≠ w.target → (z.2.1 w.target).si.cur = .NONE :=
    fun hne' => hTQ w hw (Or.inl ⟨hphase, hne'⟩)
  have hhostkind : w.host ≠ w.target → (z.2.1 w.host).si.kind = .OFF := by
    intro hne'
    have := hhk
    rw [if_neg hne'] at this
    exact this
  have hhostroot : w.host = w.target → (z.2.1 w.host).si.kind = .ROOT := by
    intro heq
    have := hhk
    rw [if_pos heq] at this
    exact this
  rw [hnom]
  constructor
  · intro he
    by_cases heh : e = w.host
    · by_cases hht : w.host = w.target
      · obtain ⟨hrow, hx, hy, _⟩ := bankWordPassFrameBusySource _ _ hfa hfl hfr
          (by rw [heh]; exact hhostroot hht) (by rw [heh, hht]; exact htb)
        obtain ⟨hsi, hw'⟩ := bankWordPassFrameStep ring hn root z e w hw hno hrow hx hy
        exact bankWordPassFrameShape ring root z e w hw hsh₀ hTQ hN' hsi hw'
      · obtain ⟨hrow, hx, hy, _⟩ := bankWordPassFrameBackSource _ _ hfa hfl hfr
          (by rw [heh]; exact hhostkind hht) (by rw [heh]; exact hcur)
        obtain ⟨hsi, hw'⟩ := bankWordPassFrameStep ring hn root z e w hw hno hrow hx hy
        exact bankWordPassFrameShape ring root z e w hw hsh₀ hTQ hN' hsi hw'
    · by_cases het : e = w.target
      · obtain ⟨hrow, hx, hy, _⟩ := bankWordPassFrameBusySource _ _ hfa hfl hfr
          (by rw [het]; exact htk) (by rw [het]; exact htb)
        obtain ⟨hsi, hw'⟩ := bankWordPassFrameStep ring hn root z e w hw hno hrow hx hy
        exact bankWordPassFrameShape ring root z e w hw hsh₀ hTQ hN' hsi hw'
      · have hxfree := hother e heh het
        obtain ⟨hxk, hxc⟩ := bankWordPassFreeFields _ hxfree
        have hyc : (z.2.1 (ring.rightNeighbor e)).si.cur ≠ .BACK := by
          by_cases hj : ring.rightNeighbor e = w.host
          · exfalso
            apply he
            apply bankWordPassRightNeighborInjective ring
            rw [hj, hsuccm]
          · by_cases hjt : ring.rightNeighbor e = w.target
            · rw [hjt, hTQ' (fun h => hj (hjt.trans h.symm))]
              exact fun h => by cases h
            · rw [(bankWordPassFreeFields _ (hother _ hj hjt)).2]
              exact fun h => by cases h
        obtain ⟨hrow, hx, hy, _⟩ := bankWordPassFrameFreeSource _ _ hfa hfl hfr hxk hxc hyc
        obtain ⟨hsi, hw'⟩ := bankWordPassFrameStep ring hn root z e w hw hno hrow hx hy
        exact bankWordPassFrameShape ring root z e w hw hsh₀ hTQ hN' hsi hw'
  · intro he
    have hrne : ring.rightNeighbor e = w.host := by rw [he]; exact hsuccm
    have hem : e ≠ w.host := by
      rw [he, hhost]
      exact bankWordPassSiteNe ring root _ _ (by omega) (by omega) (by omega)
    have het : e ≠ w.target := by
      rw [he, htarget]
      exact bankWordPassSiteNe ring root _ _ (by omega) hkn (by omega)
    have hxfree := hother e hem het
    obtain ⟨hxk, hxc⟩ := bankWordPassFreeFields _ hxfree
    have hykind : (z.2.1 (ring.rightNeighbor e)).si.kind ≠ .PREFIX := by
      rw [hrne]
      by_cases hht : w.host = w.target
      · rw [hhostroot hht]; exact fun h => by cases h
      · rw [hhostkind hht]; exact fun h => by cases h
    have hycur : (z.2.1 (ring.rightNeighbor e)).si.cur = .BACK := by rw [hrne]; exact hcur
    have hyj : (z.2.1 (ring.rightNeighbor e)).si.j.val = w.index := by rw [hrne]; exact hjv
    have hsiTargetRec : ∀ hht : w.host ≠ w.target,
        (bankWordEpochNext ring root z e).2.1 w.target = z.2.1 w.target := by
      intro hht
      exact bankWordPassRemoteRecord ring root z e _ (Ne.symm het)
        (by rw [hrne]; exact Ne.symm hht)
    by_cases hi1 : 1 < w.index
    · obtain ⟨hrow, hx, hy, _⟩ := bankWordPassBackMoveFields _ _ hfa hfl hfr hxfree hycur
        (by rw [hyj]; exact hi1) hykind
      obtain ⟨w', hw', hp', hh', ht', hi'⟩ :=
        bankWordPassGhostBackMove root e (ring.rightNeighbor e)
          (z.2.2.clock + 1) (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (wGenuineAcceptance root e (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
            (z.2.2.validation e) (z.2.2.validation (ring.rightNeighbor e)))
          w hrow hno hphase hrne.symm hyj
      have hworker' : (bankWordEpochNext ring root z e).2.2.worker = some w' := by
        rw [bankWordPassGhostWorker, hw]; exact hw'
      have hsiSource : ((bankWordEpochNext ring root z e).2.1 e).si =
          setCursor (z.2.1 e).si .BACK (w.index - 1) false false true := by
        rw [bankWordPassSourceRecord, bankWordPassPairSILeft, hx, hyj]
      have hsiHost : ((bankWordEpochNext ring root z e).2.1 w.host).si =
          clearCursor (z.2.1 w.host).si := by
        rw [← hrne, bankWordPassTargetRecord ring root z e hne, bankWordPassPairSIRight, hy]
      have hjval : (setCursor (z.2.1 e).si .BACK (w.index - 1) false false true).j.val =
          w.index - 1 := by
        have hlt : w.index - 1 < (compileAdvice (ceilLogTwo n)).t + 1 := by omega
        simp [setCursor, siJ, hlt]
      refine ⟨⟨hN', ⟨w', hworker', ?_⟩, ?_⟩, ?_⟩
      · simp only [hp']
        refine ⟨k, hk1, hkn, by omega, by omega, by rw [ht']; exact htarget, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hh', he, hi']
          congr 1
          omega
        · rw [hh', hsiSource]; rfl
        · rw [hh', hsiSource, hi']; exact hjval
        · rw [ht']
          by_cases hht : w.host = w.target
          · rw [← hht, hsiHost]; show (z.2.1 w.host).si.kind = _; rw [hht]; exact htk
          · rw [hsiTargetRec hht]; exact htk
        · rw [ht']
          by_cases hht : w.host = w.target
          · rw [← hht, hsiHost]; show (z.2.1 w.host).si.busy = _; rw [hht]; exact htb
          · rw [hsiTargetRec hht]; exact htb
        · rw [hh', ht', if_neg het, hsiSource]
          show (z.2.1 e).si.kind = _
          exact hxk
        · intro i hi hit'
          rw [hh'] at hi
          rw [ht'] at hit'
          by_cases hih : i = w.host
          · subst hih
            rw [hsiHost]
            exact bankWordPassFreeClear _ (hhostkind hit')
          · rw [bankWordPassRemoteRecord ring root z e i hi (by rw [hrne]; exact hih)]
            exact hother i hih hit'
      · intro w'' hw'' hcase
        rw [hworker'] at hw''
        cases hw''
        rcases hcase with ⟨_, hne'⟩ | hs'
        · rw [ht']
          by_cases hht : w.host = w.target
          · rw [← hht, hsiHost]; rfl
          · rw [hsiTargetRec hht]; exact hTQ' hht
        · rw [hp'] at hs'; cases hs'
      · unfold bankWordPassRank
        rw [hworker', hw]
        simp only [hp', hphase]
        rw [ht', hoff, hi']
        generalize (n - 1 - k) * (2 * (compileAdvice (ceilLogTwo n)).t + 1) = K
        omega
    · have hi : w.index = 1 := by omega
      obtain ⟨hrow, hx, hy, _⟩ := bankWordPassBackInitFields _ _ hfa hfl hfr hxfree hycur
        (by rw [hyj]; exact hi) hykind
      obtain ⟨w', hw', hp', hh', ht', hi'⟩ :=
        bankWordPassGhostBackInit root e (ring.rightNeighbor e)
          (z.2.2.clock + 1) (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (wGenuineAcceptance root e (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
            (z.2.2.validation e) (z.2.2.validation (ring.rightNeighbor e)))
          w hrow hno hphase hrne.symm hi
      have hworker' : (bankWordEpochNext ring root z e).2.2.worker = some w' := by
        rw [bankWordPassGhostWorker, hw]; exact hw'
      have hsiSource : ((bankWordEpochNext ring root z e).2.1 e).si =
          setCursor (z.2.1 e).si .SUM 0 false false true := by
        rw [bankWordPassSourceRecord, bankWordPassPairSILeft, hx]
      have hsiHost : ((bankWordEpochNext ring root z e).2.1 w.host).si =
          clearCursor (z.2.1 w.host).si := by
        rw [← hrne, bankWordPassTargetRecord ring root z e hne, bankWordPassPairSIRight, hy]
      refine ⟨⟨hN', ⟨w', hworker', ?_⟩, ?_⟩, ?_⟩
      · simp only [hp']
        refine ⟨k, hk1, hkn, by omega, by rw [ht']; exact htarget, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hh', he, hi', hi]
          congr 1
          omega
        · rw [hh', hsiSource]; show (z.2.1 e).si.kind = _; exact hxk
        · rw [hh', hsiSource]; rfl
        · rw [hh', hsiSource, hi']; simp [setCursor, siJ]
        · rw [ht']
          by_cases hht : w.host = w.target
          · rw [← hht, hsiHost]; show (z.2.1 w.host).si.kind = _; rw [hht]; exact htk
          · rw [hsiTargetRec hht]; exact htk
        · rw [ht']
          by_cases hht : w.host = w.target
          · rw [← hht, hsiHost]; show (z.2.1 w.host).si.busy = _; rw [hht]; exact htb
          · rw [hsiTargetRec hht]; exact htb
        · intro i hi hit'
          rw [hh'] at hi
          rw [ht'] at hit'
          by_cases hih : i = w.host
          · subst hih
            rw [hsiHost]
            exact bankWordPassFreeClear _ (hhostkind hit')
          · rw [bankWordPassRemoteRecord ring root z e i hi (by rw [hrne]; exact hih)]
            exact hother i hih hit'
      · intro w'' hw'' hcase
        rw [hworker'] at hw''
        cases hw''
        rcases hcase with ⟨hb', _⟩ | _
        · rw [hp'] at hb'; cases hb'
        · rw [ht']
          by_cases hht : w.host = w.target
          · rw [← hht, hsiHost]; rfl
          · rw [hsiTargetRec hht]; exact hTQ' hht
      · unfold bankWordPassRank
        rw [hworker', hw]
        simp only [hp', hphase]
        rw [ht', hoff, hi', hi]
        generalize (n - 1 - k) * (2 * (compileAdvice (ceilLogTwo n)).t + 1) = K
        omega


/-! ## Layer G step, SUM phase -/

theorem bankWordPassSumStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z) (e : Fin n)
    (hN : BankWordPassNonvalidating z)
    (w : WWorkerTrail n) (hw : z.2.2.worker = some w)
    (hphase : w.phase = .sumRun)
    (hsh : BankWordRenewalFrontierPhysicalShape ring root z)
    (hTQ : BankWordPassTargetQuiet z)
    (hno : (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 = false) :
    (e ≠ bankWordPassNomination ring root z →
      BankWordPassShape ring root (bankWordEpochNext ring root z e) ∧
      (bankWordEpochNext ring root z e).2.2.worker = some w) ∧
    (e = bankWordPassNomination ring root z →
      BankWordPassShape ring root (bankWordEpochNext ring root z e) ∧
      bankWordPassRank ring root (bankWordEpochNext ring root z e) + 1 =
        bankWordPassRank ring root z) := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨ht2, hroom⟩ := bankWordPassWidth hbank
  have hsh₀ := hsh
  have hN' := bankWordPassNonvalidatingStep ring hn root z e hN hno
  obtain ⟨hfa, hfl, hfr⟩ := bankWordPassFlagsQuiet (z.2.1 e)
    (z.2.1 (ring.rightNeighbor e)) (hN e) (hN _) hno
  have hne := clockNeighborDifferent ring hn2 e
  have hnom := bankWordPassNominationHost ring root z w hw (Or.inr (Or.inl hphase))
  obtain ⟨w₀, hw₀, hfields⟩ := hsh
  rw [hw] at hw₀
  cases hw₀
  simp only [hphase] at hfields
  obtain ⟨k, hk1, hkn, hit, htarget, hhost, hk, hc, hjv, htk, htb, hother⟩ := hfields
  have hoff : PPL.cyclicOffset ring root w.target = k := by
    rw [htarget]
    exact L3.EWord.validationSiteOffset ring root k hkn
  have hTQ' : (z.2.1 w.target).si.cur = .NONE := hTQ w hw (Or.inr hphase)
  have hht : w.host ≠ w.target := by
    rw [hhost, htarget]
    exact bankWordPassSiteNe ring root _ _ (by omega) hkn (by omega)
  rw [hnom]
  constructor
  · intro he
    by_cases het : e = w.target
    · obtain ⟨hrow, hx, hy, _⟩ := bankWordPassFrameBusySource _ _ hfa hfl hfr
        (by rw [het]; exact htk) (by rw [het]; exact htb)
      obtain ⟨hsi, hw'⟩ := bankWordPassFrameStep ring hn root z e w hw hno hrow hx hy
      exact bankWordPassFrameShape ring root z e w hw hsh₀ hTQ hN' hsi hw'
    · have hxfree := hother e he het
      obtain ⟨hxk, hxc⟩ := bankWordPassFreeFields _ hxfree
      have hyc : (z.2.1 (ring.rightNeighbor e)).si.cur ≠ .BACK := by
        by_cases hj : ring.rightNeighbor e = w.host
        · rw [hj, hc]; exact fun h => by cases h
        · by_cases hjt : ring.rightNeighbor e = w.target
          · rw [hjt, hTQ']; exact fun h => by cases h
          · rw [(bankWordPassFreeFields _ (hother _ hj hjt)).2]
            exact fun h => by cases h
      obtain ⟨hrow, hx, hy, _⟩ := bankWordPassFrameFreeSource _ _ hfa hfl hfr hxk hxc hyc
      obtain ⟨hsi, hw'⟩ := bankWordPassFrameStep ring hn root z e w hw hno hrow hx hy
      exact bankWordPassFrameShape ring root z e w hw hsh₀ hTQ hN' hsi hw'
  · intro he
    rw [← he] at hk hc hjv hhost hother hht
    have hsucc : ring.rightNeighbor e =
        L3.EWord.site ring root (k - (compileAdvice (ceilLogTwo n)).t + w.index + 1) := by
      rw [hhost]
      exact L3.EWord.siteSuccessor ring root _
    have hsiSource : ((bankWordEpochNext ring root z e).2.1 e).si =
        clearCursor (z.2.1 e).si := by
      rw [bankWordPassSourceRecord, bankWordPassPairSILeft]
      by_cases hidx : w.index + 1 < (compileAdvice (ceilLogTwo n)).t
      · have hyne : ring.rightNeighbor e ≠ w.target := by
          rw [hsucc, htarget]
          exact bankWordPassSiteNe ring root _ _ (by omega) hkn (by omega)
        exact (bankWordPassSumMoveFields _ _ hfa hfl hfr hk hc (by rw [hjv]; exact hidx)
          (hother _ hne hyne)).2.1
      · have hidxt : w.index + 1 = (compileAdvice (ceilLogTwo n)).t := by omega
        have hyt : ring.rightNeighbor e = w.target := by
          rw [hsucc, htarget]
          congr 1
          omega
        exact (bankWordPassSumPublishFields _ _ hfa hfl hfr hk hc (by rw [hjv]; exact hidxt)
          (by rw [hyt]; exact htk) (by rw [hyt]; exact htb)).2.1
    by_cases hidx : w.index + 1 < (compileAdvice (ceilLogTwo n)).t
    · have hyne : ring.rightNeighbor e ≠ w.target := by
        rw [hsucc, htarget]
        exact bankWordPassSiteNe ring root _ _ (by omega) hkn (by omega)
      have hyfree := hother _ hne hyne
      obtain ⟨hrow, hx, hyk, hyb, hyc, hyj, _⟩ :=
        bankWordPassSumMoveFields _ _ hfa hfl hfr hk hc (by rw [hjv]; exact hidx) hyfree
      obtain ⟨w', hw', hp', hh', ht', hi'⟩ :=
        bankWordPassGhostSumMove root e (ring.rightNeighbor e)
          (z.2.2.clock + 1) (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (wGenuineAcceptance root e (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
            (z.2.2.validation e) (z.2.2.validation (ring.rightNeighbor e)))
          w hrow hno hphase he.symm hjv
      have hworker' : (bankWordEpochNext ring root z e).2.2.worker = some w' := by
        rw [bankWordPassGhostWorker, hw]; exact hw'
      have hsiTarget : ((bankWordEpochNext ring root z e).2.1 (ring.rightNeighbor e)).si =
          (workerW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).y := by
        rw [bankWordPassTargetRecord ring root z e hne, bankWordPassPairSIRight]
      have hT : (bankWordEpochNext ring root z e).2.1 w.target = z.2.1 w.target :=
        bankWordPassRemoteRecord ring root z e _ (Ne.symm (hht)) (Ne.symm hyne)
      refine ⟨⟨hN', ⟨w', hworker', ?_⟩, ?_⟩, ?_⟩
      · simp only [hp']
        refine ⟨k, hk1, hkn, by omega, by rw [ht']; exact htarget,
          by rw [hh', hi', hsucc]; congr 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hh', hsiTarget, hyk]; exact (bankWordPassFreeFields _ hyfree).1
        · rw [hh', hsiTarget]; exact hyc
        · rw [hh', hsiTarget, hyj, hjv, hi']
        · rw [ht', hT]; exact htk
        · rw [ht', hT]; exact htb
        · intro i hi hit'
          rw [hh'] at hi
          rw [ht'] at hit'
          by_cases hie : i = e
          · subst hie
            rw [hsiSource]
            exact bankWordPassFreeClear _ hk
          · rw [bankWordPassRemoteRecord ring root z e i hie hi]
            exact hother i hie hit'
      · intro w'' hw'' hcase
        rw [hworker'] at hw''
        cases hw''
        rw [ht', hT]
        exact hTQ'
      · unfold bankWordPassRank
        rw [hworker', hw]
        simp only [hp', hphase]
        rw [ht', hoff, hi']
        generalize (n - 1 - k) * (2 * (compileAdvice (ceilLogTwo n)).t + 1) = K
        omega
    · have hidxt : w.index + 1 = (compileAdvice (ceilLogTwo n)).t := by omega
      have hyt : ring.rightNeighbor e = w.target := by
        rw [hsucc, htarget]
        congr 1
        omega
      obtain ⟨hrow, hx, hyk, hyb, hyc, _⟩ :=
        bankWordPassSumPublishFields _ _ hfa hfl hfr hk hc (by rw [hjv]; exact hidxt)
          (by rw [hyt]; exact htk) (by rw [hyt]; exact htb)
      obtain ⟨w', hw', hp', hh', ht', hi'⟩ :=
        bankWordPassGhostSumPublish root e (ring.rightNeighbor e)
          (z.2.2.clock + 1) (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (wGenuineAcceptance root e (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
            (z.2.2.validation e) (z.2.2.validation (ring.rightNeighbor e)))
          w hrow hno hphase he.symm hyt.symm hjv
      have hworker' : (bankWordEpochNext ring root z e).2.2.worker = some w' := by
        rw [bankWordPassGhostWorker, hw]; exact hw'
      have hsiTarget : ((bankWordEpochNext ring root z e).2.1 (ring.rightNeighbor e)).si =
          (workerW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).y := by
        rw [bankWordPassTargetRecord ring root z e hne, bankWordPassPairSIRight]
      refine ⟨⟨hN', ⟨w', hworker', ?_⟩, ?_⟩, ?_⟩
      · simp only [hp']
        refine ⟨k, hk1, hkn, by rw [hh', hsucc]; congr 1; omega,
          by rw [ht', hh', hyt], ?_, ?_, ?_, ?_⟩
        · rw [hh', hsiTarget]; exact hyk
        · rw [hh', hsiTarget]; exact hyb
        · rw [hh', hsiTarget]; exact hyc
        · intro i hi
          rw [hh'] at hi
          by_cases hie : i = e
          · subst hie
            rw [hsiSource]
            exact bankWordPassFreeClear _ hk
          · rw [bankWordPassRemoteRecord ring root z e i hie hi]
            exact hother i hie (by rw [← hyt]; exact hi)
      · intro w'' hw'' hcase
        rw [hworker'] at hw''
        cases hw''
        rcases hcase with ⟨hb', _⟩ | hs'
        · rw [hp'] at hb'; cases hb'
        · rw [hp'] at hs'; cases hs'
      · unfold bankWordPassRank
        rw [hworker', hw]
        simp only [hp', hphase]
        rw [ht', hoff]
        generalize (n - 1 - k) * (2 * (compileAdvice (ceilLogTwo n)).t + 1) = K
        omega

/-! ## Layer G step, READY phase: advance or complete -/

theorem bankWordPassReadyStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z) (e : Fin n)
    (hN : BankWordPassNonvalidating z)
    (w : WWorkerTrail n) (hw : z.2.2.worker = some w)
    (hphase : w.phase = .readyRun)
    (hsh : BankWordRenewalFrontierPhysicalShape ring root z)
    (hTQ : BankWordPassTargetQuiet z)
    (hno : (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 = false) :
    (e ≠ bankWordPassNomination ring root z →
      BankWordPassShape ring root (bankWordEpochNext ring root z e) ∧
      (bankWordEpochNext ring root z e).2.2.worker = some w) ∧
    (e = bankWordPassNomination ring root z →
      (BankWordPassShape ring root (bankWordEpochNext ring root z e) ∧
        bankWordPassRank ring root (bankWordEpochNext ring root z e) + 1 =
          bankWordPassRank ring root z) ∨
      BankWordPassRetired ring root (bankWordEpochNext ring root z e)) := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨ht2, hroom⟩ := bankWordPassWidth hbank
  have hsh₀ := hsh
  have hN' := bankWordPassNonvalidatingStep ring hn root z e hN hno
  obtain ⟨hfa, hfl, hfr⟩ := bankWordPassFlagsQuiet (z.2.1 e)
    (z.2.1 (ring.rightNeighbor e)) (hN e) (hN _) hno
  have hne := clockNeighborDifferent ring hn2 e
  have hnom := bankWordPassNominationHost ring root z w hw (Or.inr (Or.inr hphase))
  obtain ⟨w₀, hw₀, hfields⟩ := hsh
  rw [hw] at hw₀
  cases hw₀
  simp only [hphase] at hfields
  obtain ⟨k, hk1, hkn, hhost, htarget, hk, hb, hc, hother⟩ := hfields
  have hoff : PPL.cyclicOffset ring root w.target = k := by
    rw [htarget, hhost]
    exact L3.EWord.validationSiteOffset ring root k hkn
  rw [hnom]
  constructor
  · intro he
    have hxfree := hother e he
    obtain ⟨hxk, hxc⟩ := bankWordPassFreeFields _ hxfree
    have hyc : (z.2.1 (ring.rightNeighbor e)).si.cur ≠ .BACK := by
      by_cases hj : ring.rightNeighbor e = w.host
      · rw [hj, hc]; exact fun h => by cases h
      · rw [(bankWordPassFreeFields _ (hother _ hj)).2]
        exact fun h => by cases h
    obtain ⟨hrow, hx, hy, _⟩ := bankWordPassFrameFreeSource _ _ hfa hfl hfr hxk hxc hyc
    obtain ⟨hsi, hw'⟩ := bankWordPassFrameStep ring hn root z e w hw hno hrow hx hy
    exact bankWordPassFrameShape ring root z e w hw hsh₀ hTQ hN' hsi hw'
  · intro he
    rw [← he] at hk hb hc hhost hother
    have hyfree := hother _ hne
    have hsucc : ring.rightNeighbor e = L3.EWord.site ring root (k + 1) := by
      rw [hhost]
      exact L3.EWord.siteSuccessor ring root k
    have hsiSource : ((bankWordEpochNext ring root z e).2.1 e).si = offSI _ := by
      rw [bankWordPassSourceRecord, bankWordPassPairSILeft]
      by_cases hkn1 : k + 1 < n
      · have hnotroot : ring.rightNeighbor e ≠ root := by
          rw [hsucc]
          have := bankWordPassSiteNe ring root (k + 1) 0 hkn1 (by omega) (by omega)
          rw [L3.EWord.siteZero] at this
          exact this
        have hpy : (postW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).eY.l = false := by
          rw [bankWordPassResponderFlag ring hn hbank root s hs z hz e]
          simp [hnotroot]
        exact (bankWordPassAdvanceFields _ _ hfa hfl hfr hk hb hc hpy hyfree).2.1
      · have hkn' : k + 1 = n := by omega
        have hroot : ring.rightNeighbor e = root := by
          rw [hsucc, hkn']
          exact bankWordPassSiteWrap ring root
        have hpy : (postW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).eY.l = true := by
          rw [bankWordPassResponderFlag ring hn hbank root s hs z hz e]
          simp [hroot]
        exact (bankWordPassTerminalFields _ _ hfa hfl hfr hk hb hc hpy hyfree).2.1
    by_cases hkn1 : k + 1 < n
    · left
      have hnotroot : ring.rightNeighbor e ≠ root := by
        rw [hsucc]
        have := bankWordPassSiteNe ring root (k + 1) 0 hkn1 (by omega) (by omega)
        rw [L3.EWord.siteZero] at this
        exact this
      have hpy : (postW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).eY.l = false := by
        rw [bankWordPassResponderFlag ring hn hbank root s hs z hz e]
        simp [hnotroot]
      obtain ⟨hrow, hx, hy, _⟩ := bankWordPassAdvanceFields _ _ hfa hfl hfr hk hb hc hpy hyfree
      obtain ⟨w', hw', hp', hh', ht', hi'⟩ :=
        bankWordPassGhostAdvance root e (ring.rightNeighbor e)
          (z.2.2.clock + 1) (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (wGenuineAcceptance root e (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
            (z.2.2.validation e) (z.2.2.validation (ring.rightNeighbor e)))
          w hrow hno hphase he.symm
      have hworker' : (bankWordEpochNext ring root z e).2.2.worker = some w' := by
        rw [bankWordPassGhostWorker, hw]; exact hw'
      have hsiTarget : ((bankWordEpochNext ring root z e).2.1 (ring.rightNeighbor e)).si =
          launchRootBack _ := by
        rw [bankWordPassTargetRecord ring root z e hne, bankWordPassPairSIRight, hy]
      have hoff' : PPL.cyclicOffset ring root (ring.rightNeighbor e) = k + 1 := by
        rw [hsucc]
        exact L3.EWord.validationSiteOffset ring root _ hkn1
      refine ⟨⟨hN', ⟨w', hworker', ?_⟩, ?_⟩, ?_⟩
      · simp only [hp']
        refine ⟨k + 1, by omega, hkn1, by rw [hi']; omega, by rw [hi']; exact Nat.le_refl _,
          by rw [ht']; exact hsucc,
          by rw [hh', hi', Nat.sub_self, Nat.sub_zero]; exact hsucc, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hh', hsiTarget]; rfl
        · rw [hh', hsiTarget, hi']; rfl
        · rw [ht', hsiTarget]; rfl
        · rw [ht', hsiTarget]; rfl
        · rw [hh', ht', if_pos rfl, hsiTarget]; rfl
        · intro i hi _
          rw [hh'] at hi
          by_cases hie : i = e
          · subst hie
            rw [hsiSource]
            exact bankWordPassFreeOff _
          · rw [bankWordPassRemoteRecord ring root z e i hie hi]
            exact hother i hie
      · intro w'' hw'' hcase
        rw [hworker'] at hw''
        cases hw''
        rcases hcase with ⟨_, hne'⟩ | hs'
        · exact absurd (hh'.trans ht'.symm) hne'
        · rw [hp'] at hs'; cases hs'
      · unfold bankWordPassRank
        rw [hworker', hw]
        simp only [hp', hphase]
        rw [ht', hoff', hi', hoff]
        have h1 : n - 1 - (k + 1) = n - k - 2 := by omega
        have h2 : n - 1 - k = (n - k - 2) + 1 := by omega
        rw [h1, h2, Nat.add_mul, Nat.one_mul]
        generalize (n - k - 2) * (2 * (compileAdvice (ceilLogTwo n)).t + 1) = K
        omega
    · right
      have hkn' : k + 1 = n := by omega
      have hroot : ring.rightNeighbor e = root := by
        rw [hsucc, hkn']
        exact bankWordPassSiteWrap ring root
      have hpy : (postW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).eY.l = true := by
        rw [bankWordPassResponderFlag ring hn hbank root s hs z hz e]
        simp [hroot]
      obtain ⟨hrow, hx, hy, _⟩ := bankWordPassTerminalFields _ _ hfa hfl hfr hk hb hc hpy hyfree
      obtain ⟨hwnone, hcomp⟩ :=
        bankWordPassGhostTerminal root e (ring.rightNeighbor e)
          (z.2.2.clock + 1) (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (wGenuineAcceptance root e (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
            (z.2.2.validation e) (z.2.2.validation (ring.rightNeighbor e)))
          w hrow hno hphase he.symm hroot
      refine ⟨hN', ?_, ⟨{ service := z.2.2.clock + 1, worker := w }, ?_⟩, ?_⟩
      · rw [bankWordPassGhostWorker, hw]; exact hwnone
      · rw [bankWordPassGhostCompletion, hw]; exact hcomp
      · intro i
        by_cases hie : i = e
        · subst hie
          rw [hsiSource]
          exact bankWordPassFreeOff _
        · by_cases hij : i = ring.rightNeighbor e
          · subst hij
            rw [bankWordPassTargetRecord ring root z e hne, bankWordPassPairSIRight, hy]
            exact hyfree
          · rw [bankWordPassRemoteRecord ring root z e i hie hij]
            exact hother i hie


/-! ## Layer G all-edges step and the rank word -/

/-- The Layer G all-edges step: on every edge without a hard S1 the
pass shape is kept; a non-nominated edge keeps the trail (hence the
rank and the nomination), the nominated edge lowers the rank by one or
retires the pass with a completion receipt and every SI free.
Consumer: `bankWordPassRankWord`. -/
theorem bankWordPassStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z) (e : Fin n)
    (hpass : BankWordPassShape ring root z)
    (hno : (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 = false) :
    (e ≠ bankWordPassNomination ring root z →
      BankWordPassShape ring root (bankWordEpochNext ring root z e) ∧
      (bankWordEpochNext ring root z e).2.2.worker = z.2.2.worker) ∧
    (e = bankWordPassNomination ring root z →
      (BankWordPassShape ring root (bankWordEpochNext ring root z e) ∧
        bankWordPassRank ring root (bankWordEpochNext ring root z e) + 1 =
          bankWordPassRank ring root z) ∨
      BankWordPassRetired ring root (bankWordEpochNext ring root z e)) := by
  obtain ⟨hN, hsh, hTQ⟩ := hpass
  have hsh₀ := hsh
  obtain ⟨w, hw, _⟩ := hsh₀
  cases hphase : w.phase with
  | prefixRun =>
      obtain ⟨h1, h2⟩ := bankWordPassPrefixStep ring hn hbank root s hs z hz e hN w hw
        hphase hsh hTQ hno
      exact ⟨fun he => ⟨(h1 he).1, by rw [(h1 he).2, hw]⟩, fun he => Or.inl (h2 he)⟩
  | backRun =>
      obtain ⟨h1, h2⟩ := bankWordPassBackStep ring hn hbank root s hs z hz e hN w hw
        hphase hsh hTQ hno
      exact ⟨fun he => ⟨(h1 he).1, by rw [(h1 he).2, hw]⟩, fun he => Or.inl (h2 he)⟩
  | sumRun =>
      obtain ⟨h1, h2⟩ := bankWordPassSumStep ring hn hbank root s hs z hz e hN w hw
        hphase hsh hTQ hno
      exact ⟨fun he => ⟨(h1 he).1, by rw [(h1 he).2, hw]⟩, fun he => Or.inl (h2 he)⟩
  | readyRun =>
      obtain ⟨h1, h2⟩ := bankWordPassReadyStep ring hn hbank root s hs z hz e hN w hw
        hphase hsh hTQ hno
      exact ⟨fun he => ⟨(h1 he).1, by rw [(h1 he).2, hw]⟩, h2⟩

/-- No hard S1 is selected along the word. -/
def BankWordPassNoHardStart {n : Nat} (ring : DirectedRing n) (root : Fin n) :
    BankWordEpochState n → List (Fin n) → Prop
  | _, [] => True
  | z, e :: es =>
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 = false ∧
        BankWordPassNoHardStart ring root (bankWordEpochNext ring root z e) es

/-- The pass retires (completes) at some letter of the word. -/
def BankWordPassCompletes {n : Nat} (ring : DirectedRing n) (root : Fin n) :
    BankWordEpochState n → List (Fin n) → Prop
  | _, [] => False
  | z, e :: es =>
      BankWordPassRetired ring root (bankWordEpochNext ring root z e) ∨
        BankWordPassCompletes ring root (bankWordEpochNext ring root z e) es

/-- The rank word: along any no-hard-S1 word from a pass state, either
the pass is still on and the nominated hits are paid by the rank drop,
or the pass has completed.  Consumer: (C*) of the retry estimate
(`bankWordRenewalWorkerNominationHalf` with this nomination). -/
theorem bankWordPassRankWord {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s) :
    ∀ (word : List (Fin n)) (z : BankWordEpochState n),
      BankWordEpochReachable ring root s z →
      BankWordPassShape ring root z →
      BankWordPassNoHardStart ring root z word →
      (BankWordPassShape ring root
          (L3.GrantDrainEntrance.grantDrainLabelRun (bankWordEpochNext ring root) z word) ∧
        L3.GrantDrainEntrance.grantDrainLabelHits (bankWordEpochNext ring root)
            (bankWordPassNomination ring root) z word +
          bankWordPassRank ring root
            (L3.GrantDrainEntrance.grantDrainLabelRun (bankWordEpochNext ring root) z word) ≤
          bankWordPassRank ring root z) ∨
      BankWordPassCompletes ring root z word := by
  intro word
  induction word with
  | nil =>
      intro z _ hpass _
      exact Or.inl ⟨hpass, by
        simp only [L3.GrantDrainEntrance.grantDrainLabelHits,
          L3.GrantDrainEntrance.grantDrainLabelRun, Nat.zero_add]
        exact Nat.le_refl _⟩
  | cons e es ih =>
      intro z hz hpass hnh
      obtain ⟨hno, hnh'⟩ := hnh
      obtain ⟨hframe, hnom⟩ := bankWordPassStep ring hn hbank root s hs z hz e hpass hno
      have hz' := bankWordEpochReachableNext ring root s z hz e
      by_cases he : e = bankWordPassNomination ring root z
      · rcases hnom he with ⟨hpass', hrank⟩ | hret
        · rcases ih _ hz' hpass' hnh' with ⟨hpassEnd, hcount⟩ | hcomp
          · left
            refine ⟨hpassEnd, ?_⟩
            show (if e = bankWordPassNomination ring root z then 1 else 0) +
              L3.GrantDrainEntrance.grantDrainLabelHits (bankWordEpochNext ring root)
                (bankWordPassNomination ring root) (bankWordEpochNext ring root z e) es +
              bankWordPassRank ring root
                (L3.GrantDrainEntrance.grantDrainLabelRun (bankWordEpochNext ring root)
                  (bankWordEpochNext ring root z e) es) ≤ _
            rw [if_pos he]
            omega
          · exact Or.inr (Or.inr hcomp)
        · exact Or.inr (Or.inl hret)
      · obtain ⟨hpass', hw'⟩ := hframe he
        have hrank := bankWordPassRankOfWorkerEq ring root z _ hw'
        rcases ih _ hz' hpass' hnh' with ⟨hpassEnd, hcount⟩ | hcomp
        · left
          refine ⟨hpassEnd, ?_⟩
          show (if e = bankWordPassNomination ring root z then 1 else 0) +
            L3.GrantDrainEntrance.grantDrainLabelHits (bankWordEpochNext ring root)
              (bankWordPassNomination ring root) (bankWordEpochNext ring root z e) es +
            bankWordPassRank ring root
              (L3.GrantDrainEntrance.grantDrainLabelRun (bankWordEpochNext ring root)
                (bankWordEpochNext ring root z e) es) ≤ _
          rw [if_neg he]
          omega
        · exact Or.inr (Or.inr hcomp)

/-- The launch rank `(t+1) + (n-t-1)(2t+1)` is below `(2t+1) n`.
Consumer: (C*) with the worker quota `C n`. -/
theorem bankWordPassLaunchRankBound {n : Nat}
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ((compileAdvice (ceilLogTwo n)).t + 1) +
        (n - (compileAdvice (ceilLogTwo n)).t - 1) *
          (2 * (compileAdvice (ceilLogTwo n)).t + 1) <
      (2 * (compileAdvice (ceilLogTwo n)).t + 1) * n := by
  obtain ⟨ht2, hroom⟩ := bankWordPassWidth hbank
  generalize hT : (compileAdvice (ceilLogTwo n)).t = t at ht2 hroom
  have hsplit : (2 * t + 1) * n =
      (2 * t + 1) * (t + 1) + (2 * t + 1) * (n - t - 1) := by
    rw [← Nat.mul_add]
    congr 1
    omega
  have hfirst : t + 1 < (2 * t + 1) * (t + 1) := by
    have hpos : 0 < t + 1 := by omega
    have := Nat.mul_lt_mul_of_pos_right (by omega : 1 < 2 * t + 1) hpos
    rw [Nat.one_mul] at this
    exact this
  rw [hsplit, Nat.mul_comm (n - t - 1) (2 * t + 1)]
  omega

/-- At a launch state (PREFIX at the root, index 0) the rank is the
launch rank.  Consumer: (C*). -/
theorem bankWordPassRankAtLaunch {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (w : WWorkerTrail n)
    (hw : z.2.2.worker = some w) (hphase : w.phase = .prefixRun)
    (hindex : w.index = 0) :
    bankWordPassRank ring root z =
      ((compileAdvice (ceilLogTwo n)).t + 1) +
        (n - (compileAdvice (ceilLogTwo n)).t - 1) *
          (2 * (compileAdvice (ceilLogTwo n)).t + 1) := by
  unfold bankWordPassRank
  rw [hw]
  simp [hphase, hindex]

/-- (C*) at the pass level: from a launch state, a no-hard-S1 word that
does not complete the pass has fewer than `(2t+1) n` nominated hits.
Consumer: the worker half of the first-H retry cover. -/
theorem bankWordPassWorkerHitsBelowQuota {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hpass : BankWordPassShape ring root z)
    (w : WWorkerTrail n) (hw : z.2.2.worker = some w)
    (hphase : w.phase = .prefixRun) (hindex : w.index = 0)
    (word : List (Fin n))
    (hnh : BankWordPassNoHardStart ring root z word)
    (hnc : ¬ BankWordPassCompletes ring root z word) :
    L3.GrantDrainEntrance.grantDrainLabelHits (bankWordEpochNext ring root)
        (bankWordPassNomination ring root) z word <
      (2 * (compileAdvice (ceilLogTwo n)).t + 1) * n := by
  rcases bankWordPassRankWord ring hn hbank root s hs word z hz hpass hnh with
    ⟨_, hcount⟩ | hcomp
  · rw [bankWordPassRankAtLaunch ring root z w hw hphase hindex] at hcount
    have := bankWordPassLaunchRankBound hbank
    omega
  · exact absurd hcomp hnc


/-! ## No stray physical completion on the pass (consumer: hnoStrayDone) -/

/-- Under quiet flags a physical `done` is a P0/P2 at a PREFIX source
or an A0 at an idle ROOT source, in both cases into the leader. -/
theorem bankWordPassDoneClassify {c : Compiled} (x y : ProjW c)
    (hfa : (serW x y).hard.hardAccept = false)
    (hfl : (serW x y).hard.hardLeft = false)
    (hfr : (serW x y).hard.hardRight = false)
    (hd : (workerW x y).done = true) :
    (x.si.kind = .PREFIX ∧ (postW x y).eY.l = true) ∨
    (x.si.kind = .ROOT ∧ x.si.busy = false ∧ x.si.cur = .NONE ∧
      (postW x y).eY.l = true ∧ freeSI y.si = true) := by
  cases hk : x.si.kind <;> cases hb : x.si.busy <;> cases hc : x.si.cur <;>
    cases hpy : (postW x y).eY.l <;>
    simp [workerW, siStep, ProjW.lift, hfa, hfl, hfr, hk, hb, hc, hpy] at hd ⊢ <;>
    (repeat' split at hd) <;> simp_all

/-- On the pass, a ROOT_IN service with a physical `done` is the
tracked A0 and produces the completion receipt: there is no stray
P0/P2/done before completion.  Consumer: the hnoStrayDone premise of
the (A*) half. -/
theorem bankWordPassIncomingDoneCompletes {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hpass : BankWordPassShape ring root z) (e : Fin n)
    (hpred : ring.rightNeighbor e = root)
    (hno : (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 = false)
    (hd : (bankWordEpochSelectedReceipt ring z e).worker.done = true) :
    BankWordRenewalCompleted (bankWordEpochNext ring root z e) := by
  have hn2 : 2 ≤ n := by omega
  have hne := clockNeighborDifferent ring hn2 e
  obtain ⟨hN, hsh, _⟩ := hpass
  have hsh₀ := hsh
  obtain ⟨hfa, hfl, hfr⟩ := bankWordPassFlagsQuiet (z.2.1 e)
    (z.2.1 (ring.rightNeighbor e)) (hN e) (hN _) hno
  have hd' : (workerW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).done = true := hd
  have hclass := bankWordPassDoneClassify _ _ hfa hfl hfr hd'
  obtain ⟨w, hw, hfields⟩ := hsh
  cases hphase : w.phase with
  | prefixRun =>
      exfalso
      simp only [hphase] at hfields
      obtain ⟨_, _, _, _, hk, _, _, _, hother⟩ := hfields
      have hnoroot := bankWordRenewalFrontierShapePrefixNoRoot ring root z hbank hsh₀ w hw hphase
      by_cases he : e = w.host
      · subst he
        exact hnoroot hpred
      · have hfree := bankWordPassFreeFields _ (hother e he)
        rcases hclass with ⟨hkp, _⟩ | ⟨hkr, _⟩
        · rw [hfree.1] at hkp; cases hkp
        · rw [hfree.1] at hkr; cases hkr
  | backRun =>
      exfalso
      simp only [hphase] at hfields
      obtain ⟨k, _, _, _, _, _, _, _, _, htk, htb, hhk, hother⟩ := hfields
      by_cases he : e = w.host
      · by_cases hht : w.host = w.target
        · have hkr : (z.2.1 e).si.kind = .ROOT := by
            rw [he]; have := hhk; rw [if_pos hht] at this; exact this
          have hbusy : (z.2.1 e).si.busy = true := by rw [he, hht]; exact htb
          rcases hclass with ⟨hkp, _⟩ | ⟨_, hb, _⟩
          · rw [hkr] at hkp; cases hkp
          · rw [hbusy] at hb; cases hb
        · have hko : (z.2.1 e).si.kind = .OFF := by
            rw [he]; have := hhk; rw [if_neg hht] at this; exact this
          rcases hclass with ⟨hkp, _⟩ | ⟨hkr, _⟩
          · rw [hko] at hkp; cases hkp
          · rw [hko] at hkr; cases hkr
      · by_cases het : e = w.target
        · have hbusy : (z.2.1 e).si.busy = true := by rw [het]; exact htb
          have hkr : (z.2.1 e).si.kind = .ROOT := by rw [het]; exact htk
          rcases hclass with ⟨hkp, _⟩ | ⟨_, hb, _⟩
          · rw [hkr] at hkp; cases hkp
          · rw [hbusy] at hb; cases hb
        · have hfree := bankWordPassFreeFields _ (hother e he het)
          rcases hclass with ⟨hkp, _⟩ | ⟨hkr, _⟩
          · rw [hfree.1] at hkp; cases hkp
          · rw [hfree.1] at hkr; cases hkr
  | sumRun =>
      exfalso
      simp only [hphase] at hfields
      obtain ⟨k, _, _, _, _, _, hk, _, _, htk, htb, hother⟩ := hfields
      by_cases he : e = w.host
      · have hko : (z.2.1 e).si.kind = .OFF := by rw [he]; exact hk
        rcases hclass with ⟨hkp, _⟩ | ⟨hkr, _⟩
        · rw [hko] at hkp; cases hkp
        · rw [hko] at hkr; cases hkr
      · by_cases het : e = w.target
        · have hbusy : (z.2.1 e).si.busy = true := by rw [het]; exact htb
          have hkr : (z.2.1 e).si.kind = .ROOT := by rw [het]; exact htk
          rcases hclass with ⟨hkp, _⟩ | ⟨_, hb, _⟩
          · rw [hkr] at hkp; cases hkp
          · rw [hbusy] at hb; cases hb
        · have hfree := bankWordPassFreeFields _ (hother e he het)
          rcases hclass with ⟨hkp, _⟩ | ⟨hkr, _⟩
          · rw [hfree.1] at hkp; cases hkp
          · rw [hfree.1] at hkr; cases hkr
  | readyRun =>
      simp only [hphase] at hfields
      obtain ⟨k, _, _, _, _, hk, hb, hc, hother⟩ := hfields
      by_cases he : e = w.host
      · rw [← he] at hk hb hc hother
        have hyfree := hother _ hne
        have hpy : (postW (z.2.1 e) (z.2.1 (ring.rightNeighbor e))).eY.l = true := by
          rw [bankWordPassResponderFlag ring hn hbank root s hs z hz e]
          simp [hpred]
        obtain ⟨hrow, _, _, _⟩ := bankWordPassTerminalFields _ _ hfa hfl hfr hk hb hc hpy hyfree
        obtain ⟨_, hcomp⟩ :=
          bankWordPassGhostTerminal root e (ring.rightNeighbor e)
            (z.2.2.clock + 1) (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
            (wGenuineAcceptance root e (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
              (z.2.2.validation e) (z.2.2.validation (ring.rightNeighbor e)))
            w hrow hno hphase he.symm hpred
        refine ⟨{ service := z.2.2.clock + 1, worker := w }, ?_⟩
        rw [bankWordPassGhostCompletion, hw]
        exact hcomp
      · exfalso
        have hfree := bankWordPassFreeFields _ (hother e he)
        rcases hclass with ⟨hkp, _⟩ | ⟨hkr, _⟩
        · rw [hfree.1] at hkp; cases hkp
        · rw [hfree.1] at hkr; cases hkr

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
Post-genuine S6 base of the no-hard-S1 worker pass.
All facts below refer to the unchanged actual BankWordEpochNext
and the canonical BankWordRenewalFreshSeed, not a restart surrogate.
Consumer: BankWordPassShape and the worker (C*) quota.
-/

/-- A genuine physical S6 leaves the selected first follower's
serializer wphase untouched, while retiring the root to CURRENT.
This is the local serializer case of repair.tex's clean-launch
pass base; the right-hand F is the OLD accepting responder. -/
theorem bankWordPassHardAcceptCurrentRootAndChild
    {c : Compiled} (x y : ProjW c)
    (hx : (postW x y).eX.l = true)
    (hy : (postW x y).eY.l = false)
    (ha : (serW x y).hard.hardAccept = true) :
    (serW x y).x.wphase = .CURRENT ∧
      (serW x y).y.wphase = y.ser.wphase ∧
      y.ser.phase = .F := by
  have hlocal :=
    bankWordHardEpochHardAcceptLocalIdle x y hx hy ha
  have hflags :
      (((((postW x y).eX.l &&
          (x.ser.cert == .RUNNING)) &&
          (x.ser.wphase == .VALIDATING)) &&
          (x.ser.phase == .B)) &&
          (x.ser.out == .DONE) &&
          (y.ser.phase == .F)) = true := ha
  simp only [Bool.and_eq_true] at hflags
  obtain ⟨⟨⟨⟨⟨_, hcertFlag⟩, _⟩,
    hphaseFlag⟩, houtFlag⟩, htailFlag⟩ := hflags
  have hcert : x.ser.cert = .RUNNING := by
    cases hc : x.ser.cert <;> simp [hc] at hcertFlag ⊢
  have hphase : x.ser.phase = .B := by
    cases hp : x.ser.phase <;> simp [hp] at hphaseFlag ⊢
  have hout : x.ser.out = .DONE := by
    cases ho : x.ser.out <;> simp [ho] at houtFlag ⊢
  have hchild : y.ser.phase = .F := by
    cases hf : y.ser.phase <;> simp [hf] at htailFlag ⊢
  refine ⟨hlocal.2, ?_, hchild⟩
  simp [serW, serializerStep, ProjW.lift, hx, hy,
    hcert, hphase, hout, hchild]

/-- The geometric RETURN certificate is exactly what the J-N
base needs: F at the first follower forces pivot=1, and all
old nonroot serializer phases are already nonvalidating.
The genuine S6 changes only the root's wphase to CURRENT.
Consumer: bankWordPassNonvalidatingAfterGenuine. -/
theorem bankWordPassNonvalidatingOfReturnAccept
    {n : Nat}
    (ring : DirectedRing n) (hn2 : 2 ≤ n) (root : Fin n)
    (z : BankWordEpochState n)
    (g : L3.EWord.ValidationGhost)
    (hreturn : L3.EWord.ReturnShape ring root z.2.1 g)
    (hx : (postW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).eX.l = true)
    (hy : (postW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).eY.l = false)
    (ha : (serW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).hard.hardAccept = true) :
    BankWordPassNonvalidating
      (bankWordEpochNext ring root z root) := by
  have hpair :=
    bankWordPassHardAcceptCurrentRootAndChild
      (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
      hx hy ha
  have hpivot :
      g.pivot = 1 :=
    bankWordRenewalFrontierReturnChildForcesPivot
      ring root z.2.1 g hreturn hpair.2.2
  have hnonroot : ∀ i : Fin n, i ≠ root →
      (z.2.1 i).ser.wphase ≠ .VALIDATING :=
    bankWordRenewalFrontierReturnedNonrootNonvalidating
      ring root z.2.1 g hreturn hpivot
  have hne : ring.rightNeighbor root ≠ root :=
    clockNeighborDifferent ring hn2 root
  intro i
  by_cases hi : i = root
  · subst i
    rw [bankWordPassSourceRecord ring root z root,
      pairW_ser_left, hpair.1]
    decide
  · by_cases hj : i = ring.rightNeighbor root
    · subst i
      rw [bankWordPassTargetRecord ring root z root hne,
        pairW_ser_right, hpair.2.1]
      exact hnonroot (ring.rightNeighbor root) hne
    · rw [bankWordPassRemoteRecord ring root z root i hi hj]
      exact hnonroot i hi

/-- J-N immediately after ANY represented, genuinely ticketed
hard S6 (including the first one). The joined DONE ticket has an
actual earlier hard-S1 origin; its intervening nonaccepting word
carries EWord.WValidationHistory, hence a RETURN shape at the
accepting prestate. No premise of previous S6s or prior J-N is used.
Consumer: fresh-seed BankWordPassShape, then the worker (C*) bound. -/
theorem bankWordPassNonvalidatingAfterGenuine
    {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (e : Fin n)
    (hg : bankWordHardEpochGenuine ring root
      (bankWordEpochSelectedReceipt ring z e)
      (bankWordHardEpochLedger ring root z) = true) :
    BankWordPassNonvalidating
      (bankWordEpochNext ring root z e) := by
  obtain ⟨he, _, ha⟩ :=
    bankWordHardEpochSelectedGenuineOwnerFlags
      ring root z e hg
  subst e
  obtain ⟨ticket, child, hdone, _, _, _⟩ :=
    bankWordHardEpochGenuineJoinedStamps
      ring root (bankWordEpochSelectedReceipt ring z root)
      (bankWordHardEpochLedger ring root z) hg
  have hrootTicket :
      wTicketAt .done
        ((bankWordHardEpochLedger ring root z).validation root) =
          some ticket := by
    exact hdone
  have horigin :=
    (bankWordRootDoneOriginReachable
      ring hn hbank root s hs z hz) ticket hrootTicket
  obtain ⟨pre, mid, request, hstate, hreq, hzero,
    hrequested, hrequestStamp, hstartStamp, hhard, hmid⟩ :=
      horigin
  have hpre : BankWordEpochReachable ring root s
      (bankWordEpochRun ring root (bankWordEpochStart s) pre) :=
    ⟨pre, rfl⟩
  obtain ⟨g, hhistory⟩ :=
    bankWordTicketHardStartThroughWord
      ring hn hbank root s hs
      (bankWordEpochRun ring root (bankWordEpochStart s) pre)
      hpre hreq hzero mid hmid
  have hdecomp :
      bankWordEpochRun ring root (bankWordEpochStart s)
          (pre ++ [root] ++ mid) =
        bankWordEpochRun ring root
          (bankWordEpochNext ring root
            (bankWordEpochRun ring root
              (bankWordEpochStart s) pre) root) mid := by
    rw [bankWordRootRunAppend, bankWordEpochRunSnoc]
  have heq :
      z = bankWordEpochRun ring root
        (bankWordEpochNext ring root
          (bankWordEpochRun ring root
            (bankWordEpochStart s) pre) root) mid :=
    hstate.trans hdecomp
  have hhistoryZ :
      L3.EWord.WValidationHistory ring root z.2.1 g := by
    rw [heq]
    exact hhistory
  have hshape :
      L3.EWord.ValidationShape ring root z.2.1 g :=
    L3.EWord.validationReachableShape
      ring root hhistoryZ
  have haccept :
      (serW (z.2.1 root)
        (z.2.1 (ring.rightNeighbor root))).hard.hardAccept =
          true := ha
  have hreturn :
      L3.EWord.ReturnShape ring root z.2.1 g := by
    rcases hshape.stageShape with hf | hr
    · have hno :=
        L3.EWord.forwardNoAccept ring root z.2.1 g hf
      rw [haccept] at hno
      cases hno
    · exact hr
  have hclass :=
    bankWordEpochReachablePhysicalRootClass
      ring hn hbank root s hs z hz
  have hfixed :
      WFixedRoot ring root (phiW ring z.2.1 root) :=
    ((bankWordSerializerRootClassClosed
      ring hn hbank root).2 z.2.1 hclass root).2
  have hpost :=
    clockPostOutgoing ring root z.2.1 root
      (by omega : 2 ≤ n) hfixed rfl
  exact bankWordPassNonvalidatingOfReturnAccept
    ring (by omega) root z g hreturn hpost.1 hpost.2 haccept

/-- A fresh genuine hard S6 has only the initial prefixRun
ghost. TargetQuiet therefore holds vacuously, without additional
claims about the word or future worker publication.
Consumer: bankWordPassShapeAtFreshSeed. -/
theorem bankWordPassFreshTargetQuiet
    {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (seed : BankWordRenewalFreshSeed ring root s) :
    BankWordPassTargetQuiet seed.1.1 := by
  obtain ⟨v, hv, hp, hh, ht, hi⟩ :=
    bankWordRenewalFrontierFreshWorkerWitness
      ring root s seed
  intro w hw hcase
  have hwEq : w = v :=
    Option.some.inj (hw.symm.trans hv)
  have hprefix : w.phase = .prefixRun := by
    rw [hwEq]
    exact hp
  rcases hcase with hback | hsum
  · rw [hprefix] at hback
    cases hback.1
  · rw [hprefix] at hsum
    cases hsum

/-- Complete Layer-G base at every actual fresh seed.
J-N comes from the causal RETURN history; physical PREFIX shape
comes from FreshShapeOnBank; TargetQuiet is vacuous for prefixRun.
Consumer: bankWordPassFreshWorkerHitsBelowQuota. -/
theorem bankWordPassShapeAtFreshSeed
    {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (seed : BankWordRenewalFreshSeed ring root s) :
    BankWordPassShape ring root seed.1.1 := by
  obtain ⟨pre, e, hgen, heq⟩ := seed.2
  have hNold :=
    bankWordPassNonvalidatingAfterGenuine
      ring hn hbank root s hs
      pre.1 pre.2.1 e hgen
  have hN : BankWordPassNonvalidating seed.1.1 := by
    have hstate := congrArg
      (fun v : BankWordRenewalPostSOne ring root s => v.1)
      heq
    change BankWordPassNonvalidating
      (bankWordRenewalNext ring root s pre e).1 at hNold
    rw [hstate] at hNold
    exact hNold
  have hphysical :
      BankWordRenewalFrontierPhysicalShape ring root
        seed.1.1 :=
    bankWordRenewalFrontierFreshShapeOnBank
      ring root s hbank hs seed
  exact ⟨hN, hphysical,
    bankWordPassFreshTargetQuiet ring root s seed⟩

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 12000 in
/-- Fresh-seed worker nomination quota (C*): on every physical
scheduler word without a hard S1, failure to complete the pass
forces fewer than (2t+1)n nominated worker services. The actual
seed has a prefixRun trail with index zero.
Consumer: the worker half of the R10 W first-H retry cover. -/
theorem bankWordPassFreshWorkerHitsBelowQuota
    {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hs : BankWordSerializerRootClass ring hbank root s)
    (seed : BankWordRenewalFreshSeed ring root s)
    (word : List (Fin n))
    (hnh : BankWordPassNoHardStart ring root seed.1.1 word)
    (hnc : ¬ BankWordPassCompletes ring root seed.1.1 word) :
    L3.GrantDrainEntrance.grantDrainLabelHits
        (bankWordEpochNext ring root)
        (bankWordPassNomination ring root)
        seed.1.1 word <
      (2 * (compileAdvice (ceilLogTwo n)).t + 1) * n := by
  obtain ⟨w, hw, hp, hh, ht, hi⟩ :=
    bankWordRenewalFrontierFreshWorkerWitness
      ring root s seed
  exact bankWordPassWorkerHitsBelowQuota
    ring hn hbank root s hs seed.1.1 seed.1.2.1
    (bankWordPassShapeAtFreshSeed ring hn hbank root s hs seed)
    w hw hp hi word hnh hnc

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankWordPassDoneClassify
#print axioms L3.RenewalReferenceClock.bankWordPassIncomingDoneCompletes
#print axioms L3.RenewalReferenceClock.bankWordPassStep
#print axioms L3.RenewalReferenceClock.bankWordPassRankWord
#print axioms L3.RenewalReferenceClock.bankWordPassWorkerHitsBelowQuota
#print axioms L3.RenewalReferenceClock.bankWordPassSumStep
#print axioms L3.RenewalReferenceClock.bankWordPassReadyStep
#print axioms L3.RenewalReferenceClock.bankWordPassBackStep
#print axioms L3.RenewalReferenceClock.bankWordPassPrefixStep
#print axioms L3.RenewalReferenceClock.bankWordPassNonvalidatingStep
#print axioms L3.RenewalReferenceClock.bankWordPassFrameStep
#print axioms L3.RenewalReferenceClock.bankWordPassGhostTerminal
#print axioms L3.RenewalReferenceClock.bankWordPassSerializerNonvalidating
#print axioms L3.RenewalReferenceClock.bankWordPassFlagsQuiet
#print axioms L3.RenewalReferenceClock.bankWordPassBackMoveFields
#print axioms L3.RenewalReferenceClock.bankWordPassSumPublishFields
#print axioms L3.RenewalReferenceClock.bankWordPassFrameFreeSource
#print axioms L3.RenewalReferenceClock.bankWordPassHardAcceptCurrentRootAndChild
#print axioms L3.RenewalReferenceClock.bankWordPassNonvalidatingOfReturnAccept
#print axioms L3.RenewalReferenceClock.bankWordPassNonvalidatingAfterGenuine
#print axioms L3.RenewalReferenceClock.bankWordPassFreshTargetQuiet
#print axioms L3.RenewalReferenceClock.bankWordPassShapeAtFreshSeed
#print axioms L3.RenewalReferenceClock.bankWordPassFreshWorkerHitsBelowQuota
