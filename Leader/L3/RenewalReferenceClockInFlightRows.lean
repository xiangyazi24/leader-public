import Leader.L3.RenewalReferenceClockInFlight
import Leader.L3.Bank.MemoryRoot

/-!
R7 / sigma_B: the remaining in-flight BANK rows (root matched,
root changed, non-root changed, top spacer, top zero) and the closed
BankInFlightAligned step and word theorems. Kept in its own module
importing RenewalReferenceClockInFlight, whose compile is long.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option maxErrors 2000
set_option Elab.async false

/-- The physical projection also gives the responder MODE.
Suppression changes only req/grant, not this coordinate. -/
private theorem inFlightResponderBankMode {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ((rbRun ring r [e]).1 (ring.rightNeighbor e)).mode =
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.mode := by
  have hf := rbReferenceSelectedPairFrame ring hn r e
  have hforget := renewalMaskedPairFrames
    (compileAdvice (ceilLogTwo n))
    (renewalBankCut ring r.1 r.2 e)
    (r.1 e) (r.1 (ring.rightNeighbor e))
  have htrip := Counter.resetTransitionBankTrip
    (compileAdvice (ceilLogTwo n))
    (r.1 e) (r.1 (ring.rightNeighbor e)) hbank
  have hmask := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.mode)
    hforget.2
  change (renewalMaskedPair (compileAdvice (ceilLogTwo n))
      (renewalBankCut ring r.1 r.2 e)
      (r.1 e) (r.1 (ring.rightNeighbor e))).2.mode =
    (transition (compileAdvice (ceilLogTwo n))
      (r.1 e) (r.1 (ring.rightNeighbor e))).2.mode at hmask
  have hbase := congrArg
    (fun t : Mode × Bool × BTok => t.1) htrip.2
  change (transition (compileAdvice (ceilLogTwo n))
      (r.1 e) (r.1 (ring.rightNeighbor e))).2.mode =
    (Counter.resetBankOld
      (r.1 e) (r.1 (ring.rightNeighbor e))).2.mode at hbase
  rw [hf.2.1]
  exact hmask.trans hbase

/-- A selected-pair reconstruction including the possible
role-zero responder; the earlier earlier bridge has a stronger
nonzero-postrole hypothesis which is inapplicable here. -/
private theorem inFlightOfAllLocalBankShapes {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (hAligned : BankInFlightAligned ring r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hsc : bankInFlightControllerShape (r.1 e).pack.val
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.mode
      (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
        r.2 e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.controller)
    (hsw : bankInFlightWorkerShape
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.tok
      (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
        r.2 e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.worker)
    (htc : bankInFlightControllerShape
      (packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b)
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.mode
      (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
        r.2 e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.controller)
    (htw : bankInFlightWorkerShape
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.tok
      (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
        r.2 e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.worker) :
    BankInFlightAligned ring (rbRun ring r [e]) := by
  have hf := rbReferenceSelectedPairFrame ring hn r e
  have hp := rbBankReferencePairPack ring hn r e
  obtain ⟨hsm, hst, hdt⟩ :=
    inFlightPhysicalBankFields ring hn r e hbank
  have hdm := inFlightResponderBankMode ring hn r e hbank
  have hs :
      bankInFlightControllerShape
        ((rbRun ring r [e]).1 e).pack.val
        ((rbRun ring r [e]).1 e).mode
        ((rbRun ring r [e]).2.sites e).controller ∧
      bankInFlightWorkerShape
        ((rbRun ring r [e]).1 e).tok
        ((rbRun ring r [e]).2.sites e).worker := by
    constructor
    · rw [hp.1, hsm, hf.2.2.1]
      exact hsc
    · rw [hst, hf.2.2.1]
      exact hsw
  have ht :
      bankInFlightControllerShape
        ((rbRun ring r [e]).1 (ring.rightNeighbor e)).pack.val
        ((rbRun ring r [e]).1 (ring.rightNeighbor e)).mode
        ((rbRun ring r [e]).2.sites
          (ring.rightNeighbor e)).controller ∧
      bankInFlightWorkerShape
        ((rbRun ring r [e]).1 (ring.rightNeighbor e)).tok
        ((rbRun ring r [e]).2.sites
          (ring.rightNeighbor e)).worker := by
    constructor
    · rw [hp.2, hdm, hf.2.2.2]
      exact htc
    · rw [hdt, hf.2.2.2]
      exact htw
  intro i
  by_cases he : i = e
  · rw [he]
    exact hs
  · by_cases hd : i = ring.rightNeighbor e
    · rw [hd]
      exact ht
    · exact bankInFlightAlignedOutsidePair
        ring r e i hAligned he hd

/-- Exhaustive unchanged-PACK geometry: matched first digit,
consecutive interior, top-to-zero, top-to-spacer, spacer-to-zero. -/
private theorem inFlightUnchangedPackGeometry
    (c : Compiled) (x y : Agent c)
    (hb : 0 < c.b)
    (hsame : packNext x.pack.val y.pack.val c.b = y.pack.val) :
    (x.pack.val = 0 ∧ y.pack.val = 1) ∨
    (∃ j : Nat, 1 ≤ j ∧ j < c.b ∧
      x.pack.val = j ∧ y.pack.val = j + 1) ∨
    (x.pack.val = c.b ∧ y.pack.val = 0) ∨
    (x.pack.val = c.b ∧ y.pack.val = c.b + 1) ∨
    (c.b < x.pack.val ∧ y.pack.val = 0) := by
  by_cases hxzero : x.pack.val = 0
  · have hp : packNext x.pack.val y.pack.val c.b = 1 := by
      rw [hxzero]
      simp [packNext, hb]
    exact Or.inl ⟨hxzero, by omega⟩
  · by_cases hinside : x.pack.val < c.b
    · have hj : 1 ≤ x.pack.val := by omega
      have hp : packNext x.pack.val y.pack.val c.b =
          x.pack.val + 1 := by
        simp [packNext, hinside]
      exact Or.inr (Or.inl
        ⟨x.pack.val, hj, hinside, rfl, by omega⟩)
    · by_cases htop : x.pack.val = c.b
      · by_cases hyzero : y.pack.val = 0
        · exact Or.inr (Or.inr (Or.inl ⟨htop, hyzero⟩))
        · have hp : packNext x.pack.val y.pack.val c.b =
            c.b + 1 := by
            rw [htop]
            simp [packNext, hyzero]
          exact Or.inr (Or.inr (Or.inr (Or.inl
            ⟨htop, by omega⟩)))
      · have hgt : c.b < x.pack.val := by omega
        have hp : packNext x.pack.val y.pack.val c.b = 0 := by
          simp [packNext, hinside, htop]
        exact Or.inr (Or.inr (Or.inr (Or.inr
          ⟨hgt, by omega⟩)))

/-- Literal old root/first-digit case for *all* mode/token/worker
branches; includes the passive ERASURE and FRAME outcomes. -/
private theorem inFlightRootMatchedLocal {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b) (hwide : c.b ≠ 1)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hsc : bankInFlightControllerShape x.pack.val
      x.mode (m.sites e).controller)
    (htw : bankInFlightWorkerShape
      y.tok (m.sites dest).worker) :
    bankInFlightControllerShape x.pack.val
      (Counter.resetBankOld x y).1.mode
      (renewalBankPairMemory c m e dest x y).1.controller ∧
    bankInFlightWorkerShape (Counter.resetBankOld x y).1.tok
      (renewalBankPairMemory c m e dest x y).1.worker ∧
    bankInFlightControllerShape
      (packNext x.pack.val y.pack.val c.b)
      (Counter.resetBankOld x y).2.mode
      (renewalBankPairMemory c m e dest x y).2.controller ∧
    bankInFlightWorkerShape (Counter.resetBankOld x y).2.tok
      (renewalBankPairMemory c m e dest x y).2.worker := by
  -- Root source, responder of PACK 1 kept: rewrite both steps with their root normal forms
  -- (BankPairRoot.lean), then split the grant, the mode and the token before the bit, lease and
  -- threshold.
  have hb2 : 2 ≤ c.b := by omega
  have hp : packNext x.pack.val y.pack.val c.b = 1 := by
    rw [hx, hy]; simp [packNext]; omega
  have hP : Counter.resetBankOld x y = bankPairRootKeep (bankCell x 0) (bankCell y 1) c.b c.theta := by
    unfold Counter.resetBankOld
    rw [hp, hx, hy]
    exact bankPair_rootKeep _ _ _ _ rfl rfl hb2
  rw [hP, renewalBankPairMemory_rootKeep c m e dest x y hx hy hb2, hp]
  rw [hx] at hsc ⊢
  cases hg : x.grant
  case true => simp [bankPairRootKeep, bankMemoryRootKeep, bankCell, bankInFlightControllerShape, bankInFlightWorkerShape, isRetTok, isWaitMode, renewalBankWaitSlot, hg]
  cases hm : x.mode <;> simp [bankPairRootKeep, bankMemoryRootKeep, bankCell, bankInFlightControllerShape, bankInFlightWorkerShape, isRetTok, isWaitMode, renewalBankWaitSlot, hg, hm] at hsc ⊢
  all_goals (try (cases ht : y.tok <;> simp [bankPairRootKeep, bankMemoryRootKeep, bankCell, bankInFlightControllerShape, bankInFlightWorkerShape, isRetTok, isWaitMode, renewalBankWaitSlot, hg, hm, ht] at htw ⊢))
  all_goals (try (cases hbit : y.bit <;> simp [bankPairRootKeep, bankMemoryRootKeep, bankCell, bankInFlightControllerShape, bankInFlightWorkerShape, isRetTok, isWaitMode, renewalBankWaitSlot, hg, hm, ht, hbit] at hsc htw ⊢))
  all_goals (try (by_cases hlease : 1 < x.lease.val <;> simp [bankPairRootKeep, bankMemoryRootKeep, bankCell, bankInFlightControllerShape, bankInFlightWorkerShape, isRetTok, isWaitMode, renewalBankWaitSlot, hg, hm, ht, hlease] at hsc htw ⊢))
  all_goals (try (cases hth : c.theta 0 <;> simp [bankPairRootKeep, bankMemoryRootKeep, bankCell, bankInFlightControllerShape, bankInFlightWorkerShape, isRetTok, isWaitMode, renewalBankWaitSlot, hg, hm, ht, hth] at hsc htw ⊢))
  all_goals try
    first
    | assumption
    | rfl
    | exact ⟨hsc, htw⟩
    | exact ⟨_, rfl⟩
    | exact Or.inl ⟨_, rfl⟩
    | exact Or.inr ⟨_, rfl⟩

/-- Changed-role root sanitation with a literal source PACK successor. -/
private theorem inFlightRootChangedLocal {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val ≠ 1)
    (hsc : bankInFlightControllerShape x.pack.val
      x.mode (m.sites e).controller) :
    bankInFlightControllerShape x.pack.val
      (Counter.resetBankOld x y).1.mode
      (renewalBankPairMemory c m e dest x y).1.controller ∧
    bankInFlightWorkerShape (Counter.resetBankOld x y).1.tok
      (renewalBankPairMemory c m e dest x y).1.worker ∧
    bankInFlightControllerShape
      (packNext x.pack.val y.pack.val c.b)
      (Counter.resetBankOld x y).2.mode
      (renewalBankPairMemory c m e dest x y).2.controller ∧
    bankInFlightWorkerShape (Counter.resetBankOld x y).2.tok
      (renewalBankPairMemory c m e dest x y).2.worker := by
  have hp : packNext x.pack.val y.pack.val c.b = 1 := by
    rw [hx]
    simp [packNext, hb]
  have hneq : 1 ≠ y.pack.val := Ne.symm hy
  have hinside : 1 ≤ c.b := by omega
  have hbz : c.b ≠ 0 := by omega
  have hp0 : packNext 0 y.pack.val c.b = 1 := by
    simp [packNext, hb]
  have hchanged0 : packNext 0 y.pack.val c.b ≠
      y.pack.val := by
    rw [hp0]
    exact hneq
  cases hg : x.grant <;> cases hm : x.mode <;>
    by_cases hlease : 1 < x.lease.val <;>
    simp [Counter.resetBankOld, bankPair,
      renewalBankPairMemory, bankCell,
      bankInFlightControllerShape, bankInFlightWorkerShape,
      renewalBankWaitSlot, isWaitMode, isRetTok,
      hx, hp, hp0, hbz, hchanged0, hneq, hinside, hg, hm, hlease, hsc]
      at hsc ⊢ <;>
    first | assumption | rfl | exact ⟨_, rfl⟩

/-- Changed-role nonroot sanitation by the three source-PACK ranges. -/
private theorem inFlightNonrootChangedLocal {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hx : x.pack.val ≠ 0)
    (hchanged :
      packNext x.pack.val y.pack.val c.b ≠ y.pack.val)
    (hsw : bankInFlightWorkerShape
      x.tok (m.sites e).worker) :
    bankInFlightControllerShape x.pack.val
      (Counter.resetBankOld x y).1.mode
      (renewalBankPairMemory c m e dest x y).1.controller ∧
    bankInFlightWorkerShape (Counter.resetBankOld x y).1.tok
      (renewalBankPairMemory c m e dest x y).1.worker ∧
    bankInFlightControllerShape
      (packNext x.pack.val y.pack.val c.b)
      (Counter.resetBankOld x y).2.mode
      (renewalBankPairMemory c m e dest x y).2.controller ∧
    bankInFlightWorkerShape (Counter.resetBankOld x y).2.tok
      (renewalBankPairMemory c m e dest x y).2.worker := by
  have hpositive : 1 ≤ x.pack.val := by omega
  unfold Counter.resetBankOld
  rw [bankPair_nonroot (bankCell x x.pack.val) (bankCell y y.pack.val) _ _ _ hx,
    renewalBankPairMemory_nonroot c m e dest x y hx]
  by_cases hinside : x.pack.val < c.b
  · have hpost : packNext x.pack.val y.pack.val c.b =
        x.pack.val + 1 := by
      simp [packNext, hinside]
    have hnextPos : 1 ≤ x.pack.val + 1 := by omega
    have hnextLe : x.pack.val + 1 ≤ c.b := by omega
    have hnotBeyond : ¬ c.b < x.pack.val := by omega
    have hneq : x.pack.val + 1 ≠ y.pack.val := by
      intro h
      exact hchanged (hpost.trans h)
    cases ht : x.tok <;>
      simp [Counter.resetBankOld, bankPairNR, bankPairModeY,
        bankMemoryNRW, bankMemoryCtlY, bankCell,
        bankInFlightControllerShape, bankInFlightWorkerShape,
        hx, hchanged, hpositive, hinside, hnotBeyond, hpost,
        hnextPos, hnextLe, hneq, ht, hsw] at hsw ⊢ <;>
      first | exact hsw | assumption | rfl | ((repeat' split) <;> (first | exact hsw | assumption | rfl | simp [bankInFlightWorkerShape, ht] at hsw ⊢))
  · by_cases htop : x.pack.val = c.b
    · have hbz : c.b ≠ 0 := by omega
      have hyzero : y.pack.val ≠ 0 := by
        intro hy0
        have hh : packNext x.pack.val y.pack.val c.b =
            y.pack.val := by
          rw [htop, hy0]
          simp [packNext]
        exact hchanged hh
      have hpost : packNext x.pack.val y.pack.val c.b =
          c.b + 1 := by
        rw [htop]
        simp [packNext, hyzero]
      have hneq : c.b + 1 ≠ y.pack.val := by
        intro h
        exact hchanged (hpost.trans h)
      have houtside : ¬ c.b + 1 ≤ c.b := by omega
      have hnotBeyond : ¬ c.b < x.pack.val := by omega
      have hpostTop : packNext c.b y.pack.val c.b = c.b + 1 := by
        simp [packNext, hyzero]
      have hyzeroRev : ¬ (0 = y.pack.val) := fun h => hyzero h.symm
      cases ht : x.tok <;>
        simp [Counter.resetBankOld, bankPairNR, bankPairModeY,
          bankMemoryNRW, bankMemoryCtlY, bankCell,
          bankInFlightControllerShape, bankInFlightWorkerShape,
          hx, hchanged, hpositive, hinside, htop, hbz,
          hyzero, hpost, hpostTop, hnotBeyond,
          hneq, houtside, ht, hsw, hyzeroRev] at hsw ⊢ <;>
        first | exact hsw | assumption | rfl | ((repeat' split) <;> (first | exact hsw | assumption | rfl | simp [bankInFlightWorkerShape, ht] at hsw ⊢))
    · have hgt : c.b < x.pack.val := by omega
      have hnotUpper : ¬ x.pack.val ≤ c.b := by omega
      have hpost : packNext x.pack.val y.pack.val c.b = 0 := by
        simp [packNext, hinside, htop]
      have hyzero : y.pack.val ≠ 0 := by
        intro hy0
        exact hchanged (hpost.trans hy0.symm)
      have hyzeroRev : ¬ (0 = y.pack.val) := fun h => hyzero h.symm
      simp [bankPairNR, bankPairModeY,
        bankMemoryNRW, bankMemoryCtlY, bankCell,
        bankInFlightControllerShape, bankInFlightWorkerShape,
        hx, hchanged, hpositive, hinside, htop, hgt,
        hnotUpper, hpost, hyzero, hyzeroRev]

/-- Top-to-spacer row with an explicitly nonzero responder PACK. -/
private theorem inFlightTopSpacerLocal {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = c.b)
    (hy : y.pack.val = c.b + 1)
    (hsw : bankInFlightWorkerShape
      x.tok (m.sites e).worker) :
    bankInFlightControllerShape x.pack.val
      (Counter.resetBankOld x y).1.mode
      (renewalBankPairMemory c m e dest x y).1.controller ∧
    bankInFlightWorkerShape (Counter.resetBankOld x y).1.tok
      (renewalBankPairMemory c m e dest x y).1.worker ∧
    bankInFlightControllerShape
      (packNext x.pack.val y.pack.val c.b)
      (Counter.resetBankOld x y).2.mode
      (renewalBankPairMemory c m e dest x y).2.controller ∧
    bankInFlightWorkerShape (Counter.resetBankOld x y).2.tok
      (renewalBankPairMemory c m e dest x y).2.worker := by
  have hyNotZero : y.pack ≠ 0 := by
    intro hh
    have hv := congrArg Fin.val hh
    change y.pack.val = 0 at hv
    omega
  have hp : packNext x.pack.val y.pack.val c.b =
      c.b + 1 := by
    rw [hx]
    simp [packNext, hyNotZero]
  have hpositive : 1 ≤ c.b := by omega
  have hbz : c.b ≠ 0 := by omega
  have hpTop : packNext c.b (c.b + 1) c.b =
      c.b + 1 := by
    simp [packNext]
  have houtside : ¬ c.b + 1 ≤ c.b := by omega
  have hxn : x.pack.val ≠ 0 := by omega
  unfold Counter.resetBankOld
  rw [bankPair_nonroot (bankCell x x.pack.val) (bankCell y y.pack.val) _ _ _ hxn,
    renewalBankPairMemory_nonroot c m e dest x y hxn]
  cases ht : x.tok <;>
    simp [Counter.resetBankOld, bankPairNR, bankPairModeY,
      bankMemoryNRW, bankMemoryCtlY, bankCell,
      bankInFlightControllerShape, bankInFlightWorkerShape,
      hx, hy, hp, hpTop, hb, hbz, hpositive,
      houtside, hyNotZero, ht, hsw]
      at hsw ⊢ <;> first | exact hsw | assumption | rfl | ((repeat' split) <;> (first | exact hsw | assumption | rfl | simp_all))

/-- Local boundary helper for the top-to-zero preservation row. -/
private theorem inFlightTopZeroPack
    (c : Compiled) (x y : Agent c)
    (hx : c.b ≤ x.pack.val)
    (hy : y.pack.val = 0) :
    packNext x.pack.val y.pack.val c.b = 0 := by
  rw [hy]
  by_cases htop : x.pack.val = c.b
  · rw [htop]
    simp [packNext]
  · have hgt : c.b < x.pack.val := by omega
    have hnotInside : ¬ x.pack.val < c.b := by omega
    have hnotTop : x.pack.val ≠ c.b := by omega
    simp [packNext, hnotInside, hnotTop]

/-- The source is nonroot; the public memory row clears its controller.
No token split or responder state assumption is necessary here. -/
private theorem inFlightTopZeroSourceController {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : c.b ≤ x.pack.val)
    (hy : y.pack.val = 0) :
    bankInFlightControllerShape x.pack.val
      (Counter.resetBankOld x y).1.mode
      (renewalBankPairMemory c m e dest x y).1.controller := by
  have hnonzero : x.pack.val ≠ 0 := by omega
  unfold bankInFlightControllerShape
  rw [if_neg hnonzero]
  exact (rbBankNonrootControllerPair c m e dest x y hnonzero).1

/-- Helper for inFlightTopZeroSourceWorker.
Output BANK tokens and ghost workers, with all other fields opaque.
The top IR case is split before simplifying the pair programs. -/
private theorem inFlightTopZeroWorkerProjection {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : c.b ≤ x.pack.val)
    (hy : y.pack.val = 0) :
    (Counter.resetBankOld x y).1.tok =
      (if x.pack.val = c.b then
        if x.tok = .IR then .E else x.tok else .E) ∧
    (renewalBankPairMemory c m e dest x y).1.worker =
      (if x.pack.val = c.b then
        if x.tok = .IR then .empty else (m.sites e).worker
       else .empty) ∧
    (Counter.resetBankOld x y).2.tok = .E ∧
    (renewalBankPairMemory c m e dest x y).2.worker = .empty := by
  have hbz : c.b ≠ 0 := by omega
  have hpositive : 1 ≤ x.pack.val := by omega
  have hnonzero : x.pack.val ≠ 0 := by omega
  have hnotInside : ¬ x.pack.val < c.b := by omega
  have hp := inFlightTopZeroPack c x y hx hy
  unfold Counter.resetBankOld
  rw [bankPair_nonroot (bankCell x x.pack.val) (bankCell y y.pack.val) _ _ _ hnonzero,
    renewalBankPairMemory_nonroot c m e dest x y hnonzero]
  by_cases htop : x.pack.val = c.b
  · have hpTop : packNext c.b 0 c.b = 0 := by
      simp [packNext]
    by_cases hir : x.tok = .IR
    · simp [bankPairNR, bankPairModeY,
          bankMemoryNRW, bankMemoryCtlY, bankCell,
          hb, hbz, hpositive, hnonzero, hnotInside,
          hx, hy, hp, htop, hpTop, hir]
    · simp [bankPairNR, bankPairModeY,
          bankMemoryNRW, bankMemoryCtlY, bankCell,
          hb, hbz, hpositive, hnonzero, hnotInside,
          hx, hy, hp, htop, hpTop, hir]
  · have hxSpacer : x.pack.val = c.b + 1 := by
      have hbound := x.pack.isLt
      omega
    have hnotUpper : ¬ x.pack.val ≤ c.b := by omega
    have hpSpacer : packNext (c.b + 1) 0 c.b = 0 := by
      simp [packNext]
    simp [bankPairNR, bankPairModeY,
        bankMemoryNRW, bankMemoryCtlY, bankCell,
        hb, hbz, hpositive, hnonzero, hnotInside,
        hx, hy, hp, htop, hxSpacer, hnotUpper,
        hpSpacer]

/-- Local boundary helper for the top-to-zero preservation row. -/
private theorem inFlightTopZeroSourceWorker {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : c.b ≤ x.pack.val)
    (hy : y.pack.val = 0)
    (hsw : bankInFlightWorkerShape
      x.tok (m.sites e).worker) :
    bankInFlightWorkerShape (Counter.resetBankOld x y).1.tok
      (renewalBankPairMemory c m e dest x y).1.worker := by
  have hfields :=
    inFlightTopZeroWorkerProjection c m e dest x y hb hx hy
  rw [hfields.1, hfields.2.1]
  by_cases htop : x.pack.val = c.b
  · simp only [if_pos htop]
    by_cases hir : x.tok = .IR
    · simp [hir, bankInFlightWorkerShape]
    · simp only [if_neg hir]
      exact hsw
  · simp [htop, bankInFlightWorkerShape]

/-- Local boundary helper for the top-to-zero preservation row. -/
private theorem inFlightTopZeroResponderWorker {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : c.b ≤ x.pack.val)
    (hy : y.pack.val = 0) :
    bankInFlightWorkerShape (Counter.resetBankOld x y).2.tok
      (renewalBankPairMemory c m e dest x y).2.worker := by
  have hfields :=
    inFlightTopZeroWorkerProjection c m e dest x y hb hx hy
  rw [hfields.2.2.1, hfields.2.2.2]
  rfl

/-- Helper for inFlightTopZeroResponderControllerAtTop.
The role-zero controller shape is preserved by the exact waiting
lease ticker. No pair or symbolic word is unfolded here. -/
private theorem inFlightTopZeroTickerShape {n : Nat}
    (grant : Bool) (mode : Mode) (lease : Nat)
    (controller : RenewalBankController n)
    (htc : bankInFlightControllerShape 0 mode controller) :
    bankInFlightControllerShape 0
      (if grant || mode == .ARMED then .RESET
       else if isWaitMode mode then
         if 1 < lease then mode else .RESET else mode)
      (if grant || mode == .ARMED then .empty
       else renewalBankWaitSlot mode lease controller) := by
  cases hg : grant <;> cases hm : mode <;>
    by_cases hl : 1 < lease <;>
    simp [bankInFlightControllerShape, renewalBankWaitSlot,
      isWaitMode, hg, hm, hl] at htc ⊢ <;>
    first | exact htc | assumption | rfl

/-- Helper for inFlightTopZeroResponderControllerAtTop,
after inFlightTopZeroTickerShape. The top-to-zero pair has
a literal physical waiting tick and a matching ghost wait-slot.
Split IR, grant, mode, and lease before simplifying. -/
private theorem inFlightTopZeroControllerProjection {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = c.b)
    (hy : y.pack.val = 0) :
    (Counter.resetBankOld x y).2.mode =
      (if y.grant || y.mode == .ARMED then .RESET
       else if isWaitMode y.mode then
         if 1 < y.lease.val then y.mode else .RESET
       else y.mode) ∧
    (renewalBankPairMemory c m e dest x y).2.controller =
      (if y.grant || y.mode == .ARMED then .empty
       else renewalBankWaitSlot y.mode y.lease.val
         (m.sites dest).controller) := by
  have hbz : c.b ≠ 0 := by omega
  have hpositive : 1 ≤ c.b := by omega
  have hp : packNext x.pack.val y.pack.val c.b = 0 := by
    rw [hx, hy]
    simp [packNext]
  have hpTop : packNext c.b 0 c.b = 0 := by simp [packNext]
  have hxn : x.pack.val ≠ 0 := by omega
  unfold Counter.resetBankOld
  rw [(bankPair_snd_mode (bankCell x x.pack.val) (bankCell y y.pack.val) _ c.b c.theta).1,
    (renewalBankPairMemory_nonroot_controllers c m e dest x y hxn).2]
  cases hg : y.grant <;> cases hm : y.mode <;>
    by_cases hl : 1 < y.lease.val <;>
    simp [bankPairModeY, bankMemoryCtlY, bankCell, renewalBankWaitSlot, isWaitMode,
      hb, hbz, hpositive, hx, hy, hp, hpTop, hg, hm, hl]

/-- Isolated incoming-root controller mode and ghost wait-slot row. -/
private theorem inFlightTopZeroResponderControllerAtTop {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = c.b)
    (hy : y.pack.val = 0)
    (htc : bankInFlightControllerShape y.pack.val
      y.mode (m.sites dest).controller) :
    bankInFlightControllerShape
      (packNext x.pack.val y.pack.val c.b)
      (Counter.resetBankOld x y).2.mode
      (renewalBankPairMemory c m e dest x y).2.controller := by
  have hp : packNext x.pack.val y.pack.val c.b = 0 := by
    rw [hx, hy]
    simp [packNext]
  have hprojection :=
    inFlightTopZeroControllerProjection c m e dest x y
      hb hx hy
  have htcZero :
      bankInFlightControllerShape 0 y.mode
        (m.sites dest).controller := by
    rw [hy] at htc
    exact htc
  rw [hp, hprojection.1, hprojection.2]
  exact inFlightTopZeroTickerShape
    y.grant y.mode y.lease.val (m.sites dest).controller
    htcZero

/-- Isolated incoming-root controller mode and ghost wait-slot row. -/
private theorem inFlightTopZeroResponderControllerBeyondTop {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hgt : c.b < x.pack.val)
    (hy : y.pack.val = 0)
    (htc : bankInFlightControllerShape y.pack.val
      y.mode (m.sites dest).controller) :
    bankInFlightControllerShape
      (packNext x.pack.val y.pack.val c.b)
      (Counter.resetBankOld x y).2.mode
      (renewalBankPairMemory c m e dest x y).2.controller := by
  have hpositive : 1 ≤ x.pack.val := by omega
  have hnonzero : x.pack.val ≠ 0 := by omega
  have hnotInside : ¬ x.pack.val < c.b := by omega
  have hnotUpper : ¬ x.pack.val ≤ c.b := by omega
  have hnotTop : x.pack.val ≠ c.b := by omega
  have hp : packNext x.pack.val y.pack.val c.b = 0 := by
    exact inFlightTopZeroPack c x y (Nat.le_of_lt hgt) hy
  have hxSpacer : x.pack.val = c.b + 1 := by
    have hbound := x.pack.isLt
    omega
  have hpSpacer : packNext (c.b + 1) 0 c.b = 0 := by
    simp [packNext]
  have hp0 : packNext x.pack.val 0 c.b = 0 := by
    have h := hp
    rw [hy] at h
    exact h
  unfold Counter.resetBankOld
  rw [(bankPair_snd_mode (bankCell x x.pack.val) (bankCell y y.pack.val) _ c.b c.theta).1,
    (renewalBankPairMemory_nonroot_controllers c m e dest x y hnonzero).2]
  cases hg : y.grant <;> cases hm : y.mode <;>
    by_cases hlease : 1 < y.lease.val <;>
    simp [bankPairModeY, bankMemoryCtlY, bankCell,
      bankInFlightControllerShape, renewalBankWaitSlot,
      isWaitMode, hy, hp, hp0, hg, hm, hlease] at htc ⊢ <;>
    first | exact htc | assumption | rfl

/-- Top-or-spacer to root, assembled from isolated sitewise facts. -/
private theorem inFlightTopZeroLocal {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : c.b ≤ x.pack.val)
    (hy : y.pack.val = 0)
    (hsw : bankInFlightWorkerShape
      x.tok (m.sites e).worker)
    (htc : bankInFlightControllerShape y.pack.val
      y.mode (m.sites dest).controller) :
    bankInFlightControllerShape x.pack.val
      (Counter.resetBankOld x y).1.mode
      (renewalBankPairMemory c m e dest x y).1.controller ∧
    bankInFlightWorkerShape (Counter.resetBankOld x y).1.tok
      (renewalBankPairMemory c m e dest x y).1.worker ∧
    bankInFlightControllerShape
      (packNext x.pack.val y.pack.val c.b)
      (Counter.resetBankOld x y).2.mode
      (renewalBankPairMemory c m e dest x y).2.controller ∧
    bankInFlightWorkerShape (Counter.resetBankOld x y).2.tok
      (renewalBankPairMemory c m e dest x y).2.worker := by
  refine ⟨
    inFlightTopZeroSourceController c m e dest x y hb hx hy,
    inFlightTopZeroSourceWorker c m e dest x y hb hx hy hsw,
    ?_,
    inFlightTopZeroResponderWorker c m e dest x y hb hx hy⟩
  by_cases htop : x.pack.val = c.b
  · exact inFlightTopZeroResponderControllerAtTop
      c m e dest x y hb htop hy htc
  · have hgt : c.b < x.pack.val := by omega
    exact inFlightTopZeroResponderControllerBeyondTop
      c m e dest x y hgt hy htc

/-- The simultaneous local C/W coupling on every selected BANK
pair, not only on rows which move a worker. -/
private theorem inFlightEveryLocalPair {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hsc : bankInFlightControllerShape x.pack.val
      x.mode (m.sites e).controller)
    (hsw : bankInFlightWorkerShape
      x.tok (m.sites e).worker)
    (htc : bankInFlightControllerShape y.pack.val
      y.mode (m.sites dest).controller)
    (htw : bankInFlightWorkerShape
      y.tok (m.sites dest).worker) :
    bankInFlightControllerShape x.pack.val
      (Counter.resetBankOld x y).1.mode
      (renewalBankPairMemory c m e dest x y).1.controller ∧
    bankInFlightWorkerShape (Counter.resetBankOld x y).1.tok
      (renewalBankPairMemory c m e dest x y).1.worker ∧
    bankInFlightControllerShape
      (packNext x.pack.val y.pack.val c.b)
      (Counter.resetBankOld x y).2.mode
      (renewalBankPairMemory c m e dest x y).2.controller ∧
    bankInFlightWorkerShape (Counter.resetBankOld x y).2.tok
      (renewalBankPairMemory c m e dest x y).2.worker := by
  have hb : 0 < c.b := by
    unfold Compiled.b
    omega
  have hwide : c.b ≠ 1 := by
    unfold Compiled.b
    omega
  by_cases hsame :
      packNext x.pack.val y.pack.val c.b = y.pack.val
  · have hgeo := inFlightUnchangedPackGeometry
      c x y hb hsame
    rcases hgeo with ⟨hx, hy⟩ |
      ⟨j, hj, hjtop, hx, hy⟩ |
      ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact inFlightRootMatchedLocal c m e dest x y
        hb hwide hx hy hsc htw
    · obtain ⟨hsourceC, hsourceW, htargetC, htargetW⟩ :=
        inFlightConsecutiveLocal c m e dest x y
          j hj hjtop hx hy hsw htw
      exact ⟨hsourceC, hsourceW, htargetC _, htargetW⟩
    · exact inFlightTopZeroLocal c m e dest x y
        hb (by omega) hy hsw htc
    · exact inFlightTopSpacerLocal c m e dest x y
        hb hx hy hsw
    · exact inFlightTopZeroLocal c m e dest x y
        hb (by omega) hy hsw htc
  · by_cases hx : x.pack.val = 0
    · have hy : y.pack.val ≠ 1 := by
        intro hy
        have hp : packNext x.pack.val y.pack.val c.b = 1 := by
          rw [hx]
          simp [packNext, hb]
        exact hsame (hp.trans hy.symm)
      exact inFlightRootChangedLocal c m e dest x y
        hb hx hy hsc
    · exact inFlightNonrootChangedLocal c m e dest x y
        hx hsame hsw

/-- Every BANK reference edge preserves in-flight C/W shape:
physical BANK and ghost memory read the same OLD selected pair. -/
private theorem inFlightAlignedAnyBankStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (hAligned : BankInFlightAligned ring r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankInFlightAligned ring (rbRun ring r [e]) := by
  have htwo : 2 ≤ n := by omega
  obtain ⟨hsc, hsw, htc, htw⟩ :=
    inFlightEveryLocalPair
      (compileAdvice (ceilLogTwo n)) r.2
      e (ring.rightNeighbor e)
      (r.1 e) (r.1 (ring.rightNeighbor e))
      (hAligned e).1 (hAligned e).2
      (hAligned (ring.rightNeighbor e)).1
      (hAligned (ring.rightNeighbor e)).2
  exact inFlightOfAllLocalBankShapes
    ring htwo r e hAligned hbank hsc hsw htc htw

/-- The observational sanitation/collision row, including
role-change, grant and mismatched return erasures. -/
theorem bankInFlightAlignedEraseOrSanitizeStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hAligned : BankInFlightAligned ring r)
    (_hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (_hrow : rbRow ring r e = .eraseOrSanitize) :
    BankInFlightAligned ring (rbRun ring r [e]) := by
  exact inFlightAlignedAnyBankStep ring hn r e hAligned hbank

/-- General observational frame, NOT RBPureFrame. In particular
top IR erasure and destination wait-slot cleanup are included. -/
theorem bankInFlightAlignedFrameStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hAligned : BankInFlightAligned ring r)
    (_hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (_hrow : rbRow ring r e = .frame) :
    BankInFlightAligned ring (rbRun ring r [e]) := by
  exact inFlightAlignedAnyBankStep ring hn r e hAligned hbank

/-- Eliminate the earlier three-row residual from the new sanitation
and frame rows and the merged timeout row. -/
theorem bankInFlightResidualPreservationClosed {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (seed : RootedSeed ring)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankInFlightResidualPreservation ring seed := by
  intro pre r e hi hAligned hrow
  rcases hrow with ht | he | hf
  · exact bankInFlightAlignedTimeoutStep
      ring hn seed pre r e hAligned hi hbank ht
  · exact bankInFlightAlignedEraseOrSanitizeStep
      ring hn seed pre r e hAligned hi hbank he
  · exact bankInFlightAlignedFrameStep
      ring hn seed pre r e hAligned hi hbank hf

/-- Twelve-row step via the earlier conditional assembly, now with
the residual discharged. -/
theorem bankInFlightAlignedStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hAligned : BankInFlightAligned ring r)
    (hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankInFlightAligned ring (rbRun ring r [e]) := by
  exact bankInFlightAlignedStepOfResidualRows
    ring hn seed hbank
    (bankInFlightResidualPreservationClosed ring hn seed hbank)
    pre r e hAligned hi

/-- Full-word R7 preservation through unconditional receipt
step induction already performed earlier. -/
theorem bankInFlightAlignedWord {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (seed : RootedSeed ring)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (word : List (Fin n)) :
    BankInFlightAligned ring
      (rbRun ring (renewalBankStart ring seed) word) := by
  exact bankInFlightAlignedWordOfResidualRows
    ring hn seed hbank
    (bankInFlightResidualPreservationClosed ring hn seed hbank)
    word

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankInFlightAlignedEraseOrSanitizeStep
#print axioms L3.RenewalReferenceClock.bankInFlightAlignedFrameStep
#print axioms L3.RenewalReferenceClock.bankInFlightResidualPreservationClosed
#print axioms L3.RenewalReferenceClock.bankInFlightAlignedStep
#print axioms L3.RenewalReferenceClock.bankInFlightAlignedWord
