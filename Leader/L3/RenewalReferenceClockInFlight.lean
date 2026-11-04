import Leader.L3.RenewalReferenceClock

/-!
R7 / sigma_B: resetMove, carryMove, compareMove.

This is a new module, not an
edit to RenewalReferenceClock.lean. In particular the private
physical-trip and root-pair helpers in that file are reproved here
using the public selected-pair and BANK projection theorems.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- Selected BANK mode and token coordinates are independent of
suppression: the mask only changes req and grant. -/
theorem inFlightPhysicalBankFields {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ((rbRun ring r [e]).1 e).mode =
        (Counter.resetBankOld (r.1 e)
          (r.1 (ring.rightNeighbor e))).1.mode ∧
      ((rbRun ring r [e]).1 e).tok =
        (Counter.resetBankOld (r.1 e)
          (r.1 (ring.rightNeighbor e))).1.tok ∧
      ((rbRun ring r [e]).1
        (ring.rightNeighbor e)).tok =
        (Counter.resetBankOld (r.1 e)
          (r.1 (ring.rightNeighbor e))).2.tok := by
  have hf := rbReferenceSelectedPairFrame ring hn r e
  have hforget := renewalMaskedPairFrames
    (compileAdvice (ceilLogTwo n))
    (renewalBankCut ring r.1 r.2 e)
    (r.1 e) (r.1 (ring.rightNeighbor e))
  have htrip := Counter.resetTransitionBankTrip
    (compileAdvice (ceilLogTwo n))
    (r.1 e) (r.1 (ring.rightNeighbor e)) hbank
  have hsmask := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.mode)
    hforget.1
  change (renewalMaskedPair (compileAdvice (ceilLogTwo n))
      (renewalBankCut ring r.1 r.2 e)
      (r.1 e) (r.1 (ring.rightNeighbor e))).1.mode =
    (transition (compileAdvice (ceilLogTwo n))
      (r.1 e) (r.1 (ring.rightNeighbor e))).1.mode at hsmask
  have hsbank := congrArg
    (fun t : Mode × Bool × BTok => t.1) htrip.1
  change (transition (compileAdvice (ceilLogTwo n))
      (r.1 e) (r.1 (ring.rightNeighbor e))).1.mode =
    (Counter.resetBankOld (r.1 e)
      (r.1 (ring.rightNeighbor e))).1.mode at hsbank
  have hstmask := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
    hforget.1
  change (renewalMaskedPair (compileAdvice (ceilLogTwo n))
      (renewalBankCut ring r.1 r.2 e)
      (r.1 e) (r.1 (ring.rightNeighbor e))).1.tok =
    (transition (compileAdvice (ceilLogTwo n))
      (r.1 e) (r.1 (ring.rightNeighbor e))).1.tok at hstmask
  have hstbank := congrArg
    (fun t : Mode × Bool × BTok => t.2.2) htrip.1
  change (transition (compileAdvice (ceilLogTwo n))
      (r.1 e) (r.1 (ring.rightNeighbor e))).1.tok =
    (Counter.resetBankOld (r.1 e)
      (r.1 (ring.rightNeighbor e))).1.tok at hstbank
  have hdtmask := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
    hforget.2
  change (renewalMaskedPair (compileAdvice (ceilLogTwo n))
      (renewalBankCut ring r.1 r.2 e)
      (r.1 e) (r.1 (ring.rightNeighbor e))).2.tok =
    (transition (compileAdvice (ceilLogTwo n))
      (r.1 e) (r.1 (ring.rightNeighbor e))).2.tok at hdtmask
  have hdtbank := congrArg
    (fun t : Mode × Bool × BTok => t.2.2) htrip.2
  change (transition (compileAdvice (ceilLogTwo n))
      (r.1 e) (r.1 (ring.rightNeighbor e))).2.tok =
    (Counter.resetBankOld (r.1 e)
      (r.1 (ring.rightNeighbor e))).2.tok at hdtbank
  constructor
  · rw [hf.1]
    exact hsmask.trans hsbank
  constructor
  · rw [hf.1]
    exact hstmask.trans hstbank
  · rw [hf.2.1]
    exact hdtmask.trans hdtbank

/-- Reconstruct the sitewise invariant from the literal OLD BANK
pair and its two local controller/worker shapes. The target
controller clause is quantified over modes since every row
handled here leaves the target at a nonzero PACK role. -/
private theorem inFlightOfLocalBankShapes {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (hAligned : BankInFlightAligned ring r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hsourceC :
      bankInFlightControllerShape (r.1 e).pack.val
        (Counter.resetBankOld
          (r.1 e) (r.1 (ring.rightNeighbor e))).1.mode
        (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
          r.2 e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).1.controller)
    (hsourceW :
      bankInFlightWorkerShape
        (Counter.resetBankOld
          (r.1 e) (r.1 (ring.rightNeighbor e))).1.tok
        (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
          r.2 e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).1.worker)
    (htargetC :
      ∀ mode : Mode,
        bankInFlightControllerShape
          (packNext (r.1 e).pack.val
            (r.1 (ring.rightNeighbor e)).pack.val
            (compileAdvice (ceilLogTwo n)).b)
          mode
          (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
            r.2 e (ring.rightNeighbor e)
            (r.1 e) (r.1 (ring.rightNeighbor e))).2.controller)
    (htargetW :
      bankInFlightWorkerShape
        (Counter.resetBankOld
          (r.1 e) (r.1 (ring.rightNeighbor e))).2.tok
        (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
          r.2 e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).2.worker) :
    BankInFlightAligned ring (rbRun ring r [e]) := by
  have hf := rbReferenceSelectedPairFrame ring hn r e
  have hp := rbBankReferencePairPack ring hn r e
  obtain ⟨hm, hs, ht⟩ :=
    inFlightPhysicalBankFields ring hn r e hbank
  have hsource :
      bankInFlightControllerShape
          ((rbRun ring r [e]).1 e).pack.val
          ((rbRun ring r [e]).1 e).mode
          ((rbRun ring r [e]).2.sites e).controller ∧
        bankInFlightWorkerShape
          ((rbRun ring r [e]).1 e).tok
          ((rbRun ring r [e]).2.sites e).worker := by
    constructor
    · rw [hp.1, hm, hf.2.2.1]
      exact hsourceC
    · rw [hs, hf.2.2.1]
      exact hsourceW
  have htarget :
      bankInFlightControllerShape
          ((rbRun ring r [e]).1
            (ring.rightNeighbor e)).pack.val
          ((rbRun ring r [e]).1
            (ring.rightNeighbor e)).mode
          ((rbRun ring r [e]).2.sites
            (ring.rightNeighbor e)).controller ∧
        bankInFlightWorkerShape
          ((rbRun ring r [e]).1
            (ring.rightNeighbor e)).tok
          ((rbRun ring r [e]).2.sites
            (ring.rightNeighbor e)).worker := by
    constructor
    · rw [hp.2, hf.2.2.2]
      exact htargetC _
    · rw [ht, hf.2.2.2]
      exact htargetW
  intro i
  by_cases he : i = e
  · rw [he]
    exact hsource
  · by_cases hd : i = ring.rightNeighbor e
    · rw [hd]
      exact htarget
    · exact bankInFlightAlignedOutsidePair
        ring r e i hAligned he hd

/-- The three requested tags can occur only at a matched root
first-digit pair or a consecutive nonroot interior pair.
This uses the actual ordered guards, not the unguarded row names. -/
private theorem inFlightTransferGeometry {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n)
    (hrow : rbRow ring r e = .resetMove ∨
      rbRow ring r e = .carryMove ∨
      rbRow ring r e = .compareMove) :
    ((r.1 e).pack.val = 0 ∧
      (r.1 (ring.rightNeighbor e)).pack.val = 1) ∨
    ∃ j : Nat,
      1 ≤ j ∧ j < (compileAdvice (ceilLogTwo n)).b ∧
      (r.1 e).pack.val = j ∧
      (r.1 (ring.rightNeighbor e)).pack.val = j + 1 := by
  have hb := rbBankWidthPositive (ceilLogTwo n)
  have hnotErase :
      rbRow ring r e ≠ .eraseOrSanitize := by
    rcases hrow with h | h | h <;> simp [h]
  have hnotFrame :
      rbRow ring r e ≠ .frame := by
    rcases hrow with h | h | h <;> simp [h]
  by_cases hchanged :
      (packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b !=
          (r.1 (ring.rightNeighbor e)).pack.val) = true
  · have hbad : rbRow ring r e = .eraseOrSanitize := by
      unfold rbRow
      dsimp only [bankCell]
      simp only [if_pos hchanged]
    exact False.elim (hnotErase hbad)
  · have hsame :
        packNext (r.1 e).pack.val
          (r.1 (ring.rightNeighbor e)).pack.val
          (compileAdvice (ceilLogTwo n)).b =
        (r.1 (ring.rightNeighbor e)).pack.val := by
      by_cases hs :
          packNext (r.1 e).pack.val
            (r.1 (ring.rightNeighbor e)).pack.val
            (compileAdvice (ceilLogTwo n)).b =
              (r.1 (ring.rightNeighbor e)).pack.val
      · exact hs
      · have hc :
            (packNext (r.1 e).pack.val
              (r.1 (ring.rightNeighbor e)).pack.val
              (compileAdvice (ceilLogTwo n)).b !=
                (r.1 (ring.rightNeighbor e)).pack.val) = true := by
          simp [hs]
        exact False.elim (hchanged hc)
    by_cases hroot : ((r.1 e).pack.val == 0) = true
    · have hx : (r.1 e).pack.val = 0 := by
        simpa using hroot
      have hp :
          packNext (r.1 e).pack.val
            (r.1 (ring.rightNeighbor e)).pack.val
            (compileAdvice (ceilLogTwo n)).b = 1 := by
        rw [hx]
        simp [packNext, hb]
      exact Or.inl ⟨hx, hsame.symm.trans hp⟩
    · by_cases hgeo :
        (1 ≤ (r.1 e).pack.val &&
          (r.1 e).pack.val < (compileAdvice (ceilLogTwo n)).b &&
          packNext (r.1 e).pack.val
            (r.1 (ring.rightNeighbor e)).pack.val
            (compileAdvice (ceilLogTwo n)).b ==
              (r.1 e).pack.val + 1) = true
      · have hg :
            (1 ≤ (r.1 e).pack.val ∧
              (r.1 e).pack.val < (compileAdvice (ceilLogTwo n)).b) ∧
            packNext (r.1 e).pack.val
              (r.1 (ring.rightNeighbor e)).pack.val
              (compileAdvice (ceilLogTwo n)).b =
                (r.1 e).pack.val + 1 := by
          simpa using hgeo
        exact Or.inr ⟨(r.1 e).pack.val,
          hg.1.1, hg.1.2, rfl, hsame.symm.trans hg.2⟩
      · have hframe : rbRow ring r e = .frame := by
          unfold rbRow
          dsimp only [bankCell]
          simp only [if_neg hchanged, if_neg hroot, if_neg hgeo]
        exact False.elim (hnotFrame hframe)

/-- All consecutive nonroot BANK services keep C/W aligned. For
the three selected labels this is the common interior transport
piece: RR/RL, IR/AL, CR/CL all use the SAME six ghost wirings as
the corresponding physical tokens. The top-digit IR erasure is
split separately before enumerating the finite token alphabet. -/
theorem inFlightConsecutiveLocal {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (j : Nat) (hj : 1 ≤ j) (hjtop : j < c.b)
    (hx : x.pack.val = j) (hy : y.pack.val = j + 1)
    (hs : bankInFlightWorkerShape x.tok (m.sites e).worker)
    (ht : bankInFlightWorkerShape y.tok (m.sites dest).worker) :
    bankInFlightControllerShape x.pack.val
        (Counter.resetBankOld x y).1.mode
        (renewalBankPairMemory c m e dest x y).1.controller ∧
      bankInFlightWorkerShape
        (Counter.resetBankOld x y).1.tok
        (renewalBankPairMemory c m e dest x y).1.worker ∧
      (∀ mode : Mode,
        bankInFlightControllerShape
          (packNext x.pack.val y.pack.val c.b) mode
          (renewalBankPairMemory c m e dest x y).2.controller) ∧
      bankInFlightWorkerShape
        (Counter.resetBankOld x y).2.tok
        (renewalBankPairMemory c m e dest x y).2.worker := by
  have hle : j ≤ c.b := by omega
  have hnz : j ≠ 0 := by omega
  have hne : j ≠ c.b := by omega
  have hnextLe : j + 1 ≤ c.b := by omega
  have hnextPos : 1 ≤ j + 1 := by omega
  have hnextNz : j + 1 ≠ 0 := by omega
  have hbz : c.b ≠ 0 := by omega
  have hp : packNext j (j + 1) c.b = j + 1 := by
    simp [packNext, hjtop]
  -- The source is nonroot: rewrite both steps with their nonroot normal forms
  -- (BankPairNonroot.lean, BankMemoryNonroot.lean) before the token splits.
  have hxn : x.pack.val ≠ 0 := by omega
  unfold Counter.resetBankOld
  rw [bankPair_nonroot (bankCell x x.pack.val) (bankCell y y.pack.val) _ _ _ hxn,
    renewalBankPairMemory_nonroot c m e dest x y hxn]
  by_cases htop : j + 1 = c.b
  · have hpTop : packNext j c.b c.b = c.b := by
      simpa only [htop] using hp
    cases hxt : x.tok <;> cases hyt : y.tok <;>
      simp [bankPairNR, bankPairModeY, bankMemoryNRW, bankMemoryCtlY,
        bankCell, bankInFlightControllerShape, bankInFlightWorkerShape,
        hx, hy, hj, hjtop, hle, hnz, hne,
        hnextLe, hnextPos, hnextNz, hbz,
        hp, hpTop, htop, hxt, hyt, hs, ht] <;>
      first
      | assumption
      | (simp only [hyt, bankInFlightWorkerShape] at ht; exact ht)
      | (simp only [hxt, bankInFlightWorkerShape] at hs; exact hs)
      | (simp only [hxt, hyt, bankInFlightWorkerShape] at hs ht; simp_all; done)
      | (simp only [hxt, hyt, bankInFlightWorkerShape] at hs ht; simp_all;
          cases hyb : y.bit <;> simp [hyb] <;> simp_all; done)
      | (cases hyb : y.bit <;> simp_all; done)
      | (rw [hxt] at hs; simp only [bankInFlightWorkerShape] at hs;
          by_cases hc : y.bit = c.theta (c.b - 1) <;> simp [hc] <;> exact hs)
      | (split <;> simp [bankInFlightWorkerShape, hs, ht])
  · cases hxt : x.tok <;> cases hyt : y.tok <;>
      simp [bankPairNR, bankPairModeY, bankMemoryNRW, bankMemoryCtlY,
        bankCell, bankInFlightControllerShape, bankInFlightWorkerShape,
        hx, hy, hj, hjtop, hle, hnz, hne,
        hnextLe, hnextPos, hnextNz, hbz,
        hp, htop, hxt, hyt, hs, ht] <;>
      first
      | assumption
      | (simp only [hyt, bankInFlightWorkerShape] at ht; exact ht)
      | (simp only [hxt, bankInFlightWorkerShape] at hs; exact hs)
      | (simp only [hxt, hyt, bankInFlightWorkerShape] at hs ht; simp_all; done)
      | (simp only [hxt, hyt, bankInFlightWorkerShape] at hs ht; simp_all;
          cases hyb : y.bit <;> simp [hyb] <;> simp_all; done)
      | (cases hyb : y.bit <;> simp_all; done)
      | (rw [hxt] at hs; simp only [bankInFlightWorkerShape] at hs;
          by_cases hc : y.bit = c.theta j <;> simp [hc] <;> exact hs)
      | (split <;> simp [bankInFlightWorkerShape, hs, ht])

/-- The resetMove constructor is an interior label, never a root
action. All root first-match outcomes are disjoint from it. -/
private theorem inFlightResetMoveNotRoot {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n)
    (hx : (r.1 e).pack.val = 0)
    (hrow : rbRow ring r e = .resetMove) : False := by
  have hb := rbBankWidthPositive (ceilLogTwo n)
  have hp :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b = 1 := by
    rw [hx]
    simp [packNext, hb]
  unfold rbRow at hrow
  dsimp only [bankCell] at hrow
  -- Split the selectors in the order the row reads them (grant, mode, token); the worker is
  -- read only on the RL/RWAIT row.
  cases hg : (r.1 e).grant <;> try simp [hx, hp, hg, isRetTok, isWaitMode, rbIteEqIff] at hrow
  all_goals (cases hm : (r.1 e).mode <;> try simp [hx, hp, hm, isRetTok, isWaitMode, rbIteEqIff] at hrow)
  all_goals (cases ht : (r.1 (ring.rightNeighbor e)).tok <;> try simp [hx, hp, ht, isRetTok, isWaitMode, rbIteEqIff] at hrow)
  all_goals (cases hw : (r.2.sites (ring.rightNeighbor e)).worker <;> try simp [hx, hp, hw, isRetTok, isWaitMode, rbIteEqIff] at hrow)

/-- A root carryMove has exactly an old IWAIT / AL return. -/
private theorem inFlightCarryRootFields {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n)
    (hx : (r.1 e).pack.val = 0)
    (hrow : rbRow ring r e = .carryMove) :
    (r.1 (ring.rightNeighbor e)).pack.val = 1 ∧
      (r.1 e).grant = false ∧
      (r.1 e).mode = .IWAIT ∧
      (r.1 (ring.rightNeighbor e)).tok = .AL := by
  have hb := rbBankWidthPositive (ceilLogTwo n)
  have hp :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b = 1 := by
    rw [hx]
    simp [packNext, hb]
  unfold rbRow at hrow
  dsimp only [bankCell] at hrow
  -- Split the selectors in the order the row reads them (grant, mode, token); the worker is
  -- read only on the RL/RWAIT row.
  cases hg : (r.1 e).grant <;> try simp [hx, hp, hg, isRetTok, isWaitMode, rbIteEqIff] at hrow ⊢
  all_goals (cases hm : (r.1 e).mode <;> try simp [hx, hp, hm, isRetTok, isWaitMode, rbIteEqIff] at hrow ⊢)
  all_goals (cases ht : (r.1 (ring.rightNeighbor e)).tok <;> try simp [hx, hp, ht, isRetTok, isWaitMode, rbIteEqIff] at hrow ⊢)
  all_goals (cases hw : (r.2.sites (ring.rightNeighbor e)).worker <;> try simp [hx, hp, hw, isRetTok, isWaitMode, rbIteEqIff] at hrow ⊢)
  all_goals omega

/-- A root compareMove is exactly an old CSTART / E issue. -/
private theorem inFlightCompareRootFields {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n)
    (hx : (r.1 e).pack.val = 0)
    (hrow : rbRow ring r e = .compareMove) :
    (r.1 (ring.rightNeighbor e)).pack.val = 1 ∧
      (r.1 e).grant = false ∧
      (r.1 e).mode = .CSTART ∧
      (r.1 (ring.rightNeighbor e)).tok = .E := by
  have hb := rbBankWidthPositive (ceilLogTwo n)
  have hp :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b = 1 := by
    rw [hx]
    simp [packNext, hb]
  unfold rbRow at hrow
  dsimp only [bankCell] at hrow
  -- Split the selectors in the order the row reads them (grant, mode, token); the worker is
  -- read only on the RL/RWAIT row.
  cases hg : (r.1 e).grant <;> try simp [hx, hp, hg, isRetTok, isWaitMode, rbIteEqIff] at hrow ⊢
  all_goals (cases hm : (r.1 e).mode <;> try simp [hx, hp, hm, isRetTok, isWaitMode, rbIteEqIff] at hrow ⊢)
  all_goals (cases ht : (r.1 (ring.rightNeighbor e)).tok <;> try simp [hx, hp, ht, isRetTok, isWaitMode, rbIteEqIff] at hrow ⊢)
  all_goals (cases hw : (r.2.sites (ring.rightNeighbor e)).worker <;> try simp [hx, hp, hw, isRetTok, isWaitMode, rbIteEqIff] at hrow ⊢)
  all_goals omega

/-- The C/W output shapes for the AL / IWAIT root return. -/
private theorem inFlightCarryRootLocal {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hm : x.mode = .IWAIT) (ht : y.tok = .AL) :
    bankInFlightControllerShape x.pack.val
        (Counter.resetBankOld x y).1.mode
        (renewalBankPairMemory c m e dest x y).1.controller ∧
      bankInFlightWorkerShape
        (Counter.resetBankOld x y).1.tok
        (renewalBankPairMemory c m e dest x y).1.worker ∧
      (∀ mode : Mode,
        bankInFlightControllerShape
          (packNext x.pack.val y.pack.val c.b) mode
          (renewalBankPairMemory c m e dest x y).2.controller) ∧
      bankInFlightWorkerShape
        (Counter.resetBankOld x y).2.tok
        (renewalBankPairMemory c m e dest x y).2.worker := by
  have hbz : c.b ≠ 0 := by omega
  have hp : packNext x.pack.val y.pack.val c.b = 1 := by
    rw [hx]
    simp [packNext, hb]
  have hmem :
      renewalBankPairMemory c m e dest x y =
        rbRootReturnedPair m e dest := by
    simpa only [rbRootReturnedPair] using
      (rbMatchedReturnMemoryExact c m e dest x y
        hb hx hy hg (Or.inl ⟨hm, ht⟩))
  have hmode :
      (Counter.resetBankOld x y).1.mode = .CSTART := by
    simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hg, hm, ht, packNext, hb, hbz, isRetTok]
  have hsourceTok :
      (Counter.resetBankOld x y).1.tok = .E := by
    simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hg, hm, ht, packNext, hb, hbz, isRetTok]
  have hdestTok :
      (Counter.resetBankOld x y).2.tok = .E := by
    simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hg, hm, ht, packNext, hb, hbz, isRetTok]
  constructor
  · rw [hx, hmode, hmem]
    change ∃ p : RenewalBankPayload n,
      RenewalBankController.active
        (renewalBankReturned (m.sites e).controller
          (m.sites dest).worker dest) = .active p
    exact ⟨renewalBankReturned (m.sites e).controller
      (m.sites dest).worker dest, rfl⟩
  constructor
  · rw [hsourceTok, hmem]
    rfl
  constructor
  · intro mode
    rw [hp, hmem]
    rfl
  · rw [hdestTok, hmem]
    rfl

/-- The root CSTART issue sends a payload on CR0 or CR1,
independently of the responder bit and the advice theta value. -/
private theorem inFlightCompareRootLocal {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hm : x.mode = .CSTART) (ht : y.tok = .E) :
    bankInFlightControllerShape x.pack.val
        (Counter.resetBankOld x y).1.mode
        (renewalBankPairMemory c m e dest x y).1.controller ∧
      bankInFlightWorkerShape
        (Counter.resetBankOld x y).1.tok
        (renewalBankPairMemory c m e dest x y).1.worker ∧
      (∀ mode : Mode,
        bankInFlightControllerShape
          (packNext x.pack.val y.pack.val c.b) mode
          (renewalBankPairMemory c m e dest x y).2.controller) ∧
      bankInFlightWorkerShape
        (Counter.resetBankOld x y).2.tok
        (renewalBankPairMemory c m e dest x y).2.worker := by
  have hbz : c.b ≠ 0 := by omega
  have hp : packNext x.pack.val y.pack.val c.b = 1 := by
    rw [hx]
    simp [packNext, hb]
  have hmem :
      renewalBankPairMemory c m e dest x y =
        rbRootCstartPair m e := by
    exact rbRootCstartMemoryExact c m e dest x y
      hb hx hy hg hm ht
  have hmode :
      (Counter.resetBankOld x y).1.mode = .CWAIT := by
    simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hg, hm, ht, packNext, hb, hbz, isRetTok]
  have hsourceTok :
      (Counter.resetBankOld x y).1.tok = .E := by
    simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hg, hm, ht, packNext, hb, hbz, isRetTok]
  have htoken :
      (Counter.resetBankOld x y).2.tok = .CR0 ∨
        (Counter.resetBankOld x y).2.tok = .CR1 := by
    simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hg, hm, ht, packNext, hb, hbz, isRetTok] <;>
      first
      | exact (Classical.em _).symm
      | (split <;> simp)
  have hshape := bankInFlightCompareIssuePairShape m e
    (Counter.resetBankOld x y).2.tok htoken
  constructor
  · rw [hx, hmode, hmem]
    exact hshape.1
  constructor
  · rw [hsourceTok, hmem]
    rfl
  constructor
  · intro mode
    rw [hp, hmem]
    rfl
  · rw [hmem]
    exact hshape.2

/-- resetMove: the three RR/RL motion arms, all at consecutive
nonroot digits; source, target and every off-pair site agree. -/
theorem bankInFlightAlignedResetMoveStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hAligned : BankInFlightAligned ring r)
    (_hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrow : rbRow ring r e = .resetMove) :
    BankInFlightAligned ring (rbRun ring r [e]) := by
  have htwo : 2 ≤ n := by omega
  have hgeo := inFlightTransferGeometry ring r e
    (Or.inl hrow)
  rcases hgeo with ⟨hx, _⟩ | ⟨j, hj, hjtop, hx, hy⟩
  · exact False.elim (inFlightResetMoveNotRoot ring r e hx hrow)
  · obtain ⟨hsc, hsw, htc, htw⟩ :=
      inFlightConsecutiveLocal
        (compileAdvice (ceilLogTwo n)) r.2
        e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))
        j hj hjtop hx hy
        (hAligned e).2 (hAligned (ring.rightNeighbor e)).2
    exact inFlightOfLocalBankShapes
      ring htwo r e hAligned hbank hsc hsw htc htw

/-- carryMove: either the matching AL/IWAIT root return, or an
interior AL-backward / IR-forward worker transfer. -/
theorem bankInFlightAlignedCarryMoveStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hAligned : BankInFlightAligned ring r)
    (_hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrow : rbRow ring r e = .carryMove) :
    BankInFlightAligned ring (rbRun ring r [e]) := by
  have htwo : 2 ≤ n := by omega
  have hgeo := inFlightTransferGeometry ring r e
    (Or.inr (Or.inl hrow))
  rcases hgeo with ⟨hx, _⟩ | ⟨j, hj, hjtop, hx, hy⟩
  · obtain ⟨hy, hg, hm, ht⟩ :=
      inFlightCarryRootFields ring r e hx hrow
    have hb := rbBankWidthPositive (ceilLogTwo n)
    obtain ⟨hsc, hsw, htc, htw⟩ :=
      inFlightCarryRootLocal
        (compileAdvice (ceilLogTwo n)) r.2
        e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))
        hb hx hy hg hm ht
    exact inFlightOfLocalBankShapes
      ring htwo r e hAligned hbank hsc hsw htc htw
  · obtain ⟨hsc, hsw, htc, htw⟩ :=
      inFlightConsecutiveLocal
        (compileAdvice (ceilLogTwo n)) r.2
        e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))
        j hj hjtop hx hy
        (hAligned e).2 (hAligned (ring.rightNeighbor e)).2
    exact inFlightOfLocalBankShapes
      ring htwo r e hAligned hbank hsc hsw htc htw

/-- compareMove: CSTART emission at root or an interior CR/CL
comparison movement; the output physical token determines the
unique ghost worker constructor on each selected endpoint. -/
theorem bankInFlightAlignedCompareMoveStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hAligned : BankInFlightAligned ring r)
    (_hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrow : rbRow ring r e = .compareMove) :
    BankInFlightAligned ring (rbRun ring r [e]) := by
  have htwo : 2 ≤ n := by omega
  have hgeo := inFlightTransferGeometry ring r e
    (Or.inr (Or.inr hrow))
  rcases hgeo with ⟨hx, _⟩ | ⟨j, hj, hjtop, hx, hy⟩
  · obtain ⟨hy, hg, hm, ht⟩ :=
      inFlightCompareRootFields ring r e hx hrow
    have hb := rbBankWidthPositive (ceilLogTwo n)
    obtain ⟨hsc, hsw, htc, htw⟩ :=
      inFlightCompareRootLocal
        (compileAdvice (ceilLogTwo n)) r.2
        e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))
        hb hx hy hg hm ht
    exact inFlightOfLocalBankShapes
      ring htwo r e hAligned hbank hsc hsw htc htw
  · obtain ⟨hsc, hsw, htc, htw⟩ :=
      inFlightConsecutiveLocal
        (compileAdvice (ceilLogTwo n)) r.2
        e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))
        j hj hjtop hx hy
        (hAligned e).2 (hAligned (ring.rightNeighbor e)).2
    exact inFlightOfLocalBankShapes
      ring htwo r e hAligned hbank hsc hsw htc htw

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The successful OLD CL1 return is the CWAIT first-digit row.
Its source and responder are still the OLD physical records. -/
private theorem inFlightSuccessOldFields {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n)
    (hrow : rbRow ring r e = .success) :
    (r.1 e).pack.val = 0 ∧
      (r.1 (ring.rightNeighbor e)).pack.val = 1 ∧
      (r.1 e).grant = false ∧
      (r.1 e).mode = .CWAIT ∧
      (r.1 (ring.rightNeighbor e)).tok = .CL1 := by
  unfold rbRow at hrow
  dsimp only [bankCell] at hrow
  -- Split the selectors in the order the row reads them (grant, mode, token); the worker is
  -- read only on the RL/RWAIT row.
  cases hg : (r.1 e).grant <;> try simp [hg, isRetTok, isWaitMode, rbIteEqIff] at hrow ⊢
  all_goals (cases hm : (r.1 e).mode <;> try simp [hm, isRetTok, isWaitMode, rbIteEqIff] at hrow ⊢)
  all_goals (cases ht : (r.1 (ring.rightNeighbor e)).tok <;> try simp [ht, isRetTok, isWaitMode, rbIteEqIff] at hrow ⊢)
  all_goals (cases hw : (r.2.sites (ring.rightNeighbor e)).worker <;> try simp [hw, isRetTok, isWaitMode, rbIteEqIff] at hrow ⊢)
  all_goals omega

/-- The CL1 success row consumes the responder's worker and erases
the source controller. This concerns the actual BANK reference
step, not the cut decision (which is evaluated on the OLD pair). -/
theorem bankInFlightAlignedSuccessStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n)
    (hAligned : BankInFlightAligned ring r)
    (_hi : ReceiptInv ring seed pre r)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrow : rbRow ring r e = .success) :
    BankInFlightAligned ring (rbRun ring r [e]) := by
  have htwo : 2 ≤ n := by omega
  obtain ⟨hx, hy, hg, hm, ht⟩ :=
    inFlightSuccessOldFields ring r e hrow
  have hb := rbBankWidthPositive (ceilLogTwo n)
  have hbz : (compileAdvice (ceilLogTwo n)).b ≠ 0 := by omega
  have hp :
      packNext (r.1 e).pack.val
          (r.1 (ring.rightNeighbor e)).pack.val
          (compileAdvice (ceilLogTwo n)).b = 1 := by
    rw [hx]
    simp [packNext, hb]
  have hmode :
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.mode =
          .RESET := by
    simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hg, hm, ht, packNext, hb, hbz, isRetTok]
  have hsourceTok :
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.tok =
          .E := by
    simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hg, hm, ht, packNext, hb, hbz, isRetTok]
  have htargetTok :
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).2.tok =
          .E := by
    simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hg, hm, ht, packNext, hb, hbz, isRetTok]
  have hpair :
      renewalBankPairMemory
          (compileAdvice (ceilLogTwo n)) r.2
          e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e)) =
        ({ worker := .empty, controller := .empty },
         { worker := .empty, controller := .empty }) := by
    simp [renewalBankPairMemory, bankCell,
      hx, hy, hg, hm, ht, packNext, hb, hbz, isRetTok]
  have hsourceC :
      bankInFlightControllerShape (r.1 e).pack.val
        (Counter.resetBankOld
          (r.1 e) (r.1 (ring.rightNeighbor e))).1.mode
        (renewalBankPairMemory
          (compileAdvice (ceilLogTwo n)) r.2
          e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).1.controller := by
    rw [hx, hmode, hpair]
    rfl
  have hsourceW :
      bankInFlightWorkerShape
        (Counter.resetBankOld
          (r.1 e) (r.1 (ring.rightNeighbor e))).1.tok
        (renewalBankPairMemory
          (compileAdvice (ceilLogTwo n)) r.2
          e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).1.worker := by
    rw [hsourceTok, hpair]
    rfl
  have htargetC :
      ∀ mode : Mode,
        bankInFlightControllerShape
          (packNext (r.1 e).pack.val
            (r.1 (ring.rightNeighbor e)).pack.val
            (compileAdvice (ceilLogTwo n)).b)
          mode
          (renewalBankPairMemory
            (compileAdvice (ceilLogTwo n)) r.2
            e (ring.rightNeighbor e)
            (r.1 e) (r.1 (ring.rightNeighbor e))).2.controller := by
    intro mode
    rw [hp, hpair]
    rfl
  have htargetW :
      bankInFlightWorkerShape
        (Counter.resetBankOld
          (r.1 e) (r.1 (ring.rightNeighbor e))).2.tok
        (renewalBankPairMemory
          (compileAdvice (ceilLogTwo n)) r.2
          e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).2.worker := by
    rw [htargetTok, hpair]
    rfl
  exact inFlightOfLocalBankShapes
    ring htwo r e hAligned hbank
    hsourceC hsourceW htargetC htargetW

/-- The stronger PURE-frame condition is sufficient for the full
in-flight invariant. The observational tag .frame alone is NOT
sufficient to invoke this theorem. -/
theorem bankInFlightAlignedPureFrameStep {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n)
    (hAligned : BankInFlightAligned ring r)
    (hframe : RBPureFrame ring r e) :
    BankInFlightAligned ring (rbRun ring r [e]) := by
  change BankInFlightAligned ring (renewalBankNext ring r e)
  unfold BankInFlightAligned
  intro i
  simpa only [hframe.physical, hframe.ghostSites] using
    hAligned i

/-- The exact outstanding obligations for the CASE ASSEMBLY:
timeout (if it is not yet merged), erase/sanitize, and the
non-PURE portion of the observational frame row.
This is a hypothesis, not a claimed invariant theorem. -/
def BankInFlightResidualPreservation {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring) : Prop :=
  ∀ (pre : List (Fin n))
    (r : RenewalBankReference n) (e : Fin n),
    ReceiptInv ring seed pre r →
    BankInFlightAligned ring r →
    (rbRow ring r e = .timeout ∨
      rbRow ring r e = .eraseOrSanitize ∨
      rbRow ring r e = .frame) →
    BankInFlightAligned ring (rbRun ring r [e])

/-- Conditional twelve-row assembly. Nine rows use the actual
available row theorems (including the CL1 success theorem above).
The remaining three must be separately discharged; there is
no hidden proof leaf or assumption of PURE frame. -/
theorem bankInFlightAlignedStepOfResidualRows {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (seed : RootedSeed ring)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hresidual : BankInFlightResidualPreservation ring seed)
    (pre : List (Fin n)) (r : RenewalBankReference n)
    (e : Fin n)
    (hAligned : BankInFlightAligned ring r)
    (hi : ReceiptInv ring seed pre r) :
    BankInFlightAligned ring (rbRun ring r [e]) := by
  cases hrow : rbRow ring r e with
  | resetLaunch =>
      exact bankInFlightAlignedResetLaunchStep
        ring hn seed pre r e hAligned hi hbank hrow
  | resetMove =>
      exact bankInFlightAlignedResetMoveStep
        ring hn seed pre r e hAligned hi hbank hrow
  | zeroAccept =>
      exact bankInFlightAlignedZeroAcceptStep
        ring hn seed pre r e hAligned hi hbank hrow
  | resetInheritedReturn =>
      exact bankInFlightAlignedResetInheritedReturnStep
        ring hn seed pre r e hAligned hi hbank hrow
  | armedHead =>
      exact bankInFlightAlignedArmedHeadStep
        ring hn seed pre r e hAligned hi hbank hrow
  | carryMove =>
      exact bankInFlightAlignedCarryMoveStep
        ring hn seed pre r e hAligned hi hbank hrow
  | compareMove =>
      exact bankInFlightAlignedCompareMoveStep
        ring hn seed pre r e hAligned hi hbank hrow
  | negativeReturn =>
      exact bankInFlightAlignedNegativeReturnStep
        ring hn seed pre r e hAligned hi hbank hrow
  | timeout =>
      exact hresidual pre r e hi hAligned (Or.inl hrow)
  | eraseOrSanitize =>
      exact hresidual pre r e hi hAligned
        (Or.inr (Or.inl hrow))
  | success =>
      exact bankInFlightAlignedSuccessStep
        ring hn seed pre r e hAligned hi hbank hrow
  | frame =>
      exact hresidual pre r e hi hAligned
        (Or.inr (Or.inr hrow))

/-- Word-level assembly under precisely the same explicitly
undischarged three-row condition. The ReceiptInv step is the
existing unconditional BANK-band theorem. -/
theorem bankInFlightAlignedWordOfResidualRows {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (seed : RootedSeed ring)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hresidual : BankInFlightResidualPreservation ring seed)
    (word : List (Fin n)) :
    BankInFlightAligned ring
      (rbRun ring (renewalBankStart ring seed) word) := by
  have hclosure :
      ∀ (tail : List (Fin n))
        (pre : List (Fin n))
        (r : RenewalBankReference n),
        ReceiptInv ring seed pre r →
        BankInFlightAligned ring r →
        BankInFlightAligned ring (rbRun ring r tail) := by
    intro tail
    induction tail with
    | nil =>
        intro pre r hi hAligned
        exact hAligned
    | cons e rest ih =>
        intro pre r hi hAligned
        have htwo : 2 ≤ n := by omega
        have hstep := bankInFlightAlignedStepOfResidualRows
          ring hn seed hbank hresidual pre r e hAligned hi
        have hiNext := rbReceiptInvStepBankOfInv
          ring htwo seed pre r e hi hbank
        change BankInFlightAligned ring
          (rbRun ring (rbRun ring r [e]) rest)
        exact ih (pre ++ [e]) (rbRun ring r [e])
          hiNext hstep
  exact hclosure word [] (renewalBankStart ring seed)
    (rbReceiptInvEmpty ring seed)
    (bankInFlightAlignedStart ring seed)

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankInFlightAlignedResetMoveStep
#print axioms L3.RenewalReferenceClock.bankInFlightAlignedCarryMoveStep
#print axioms L3.RenewalReferenceClock.bankInFlightAlignedCompareMoveStep
#print axioms L3.RenewalReferenceClock.bankInFlightAlignedSuccessStep
#print axioms L3.RenewalReferenceClock.bankInFlightAlignedPureFrameStep
#print axioms L3.RenewalReferenceClock.bankInFlightAlignedStepOfResidualRows
#print axioms L3.RenewalReferenceClock.bankInFlightAlignedWordOfResidualRows
