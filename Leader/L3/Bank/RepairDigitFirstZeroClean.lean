import Leader.L3.Bank.RepairDigitBoundaryClean

/-!
# R10c: the first-zero stage from the clean boundary cut

`BankRepairDigitFirstZeroCut` and its clock `bankRepairDigitFirstZeroGoneStage` name an audit
start with `BankRepairRFoldEstablished`; the clean boundary stage (`bankCleanBoundaryStage`)
lands on the clean boundary cut, whose audit restarts at a clean entrance
(`BankPostInheritedGrantDrain ∧ BankCleanRFold`). The old first-zero proof reads from its start
only the layout values at a singleton root (delimiters, the first block, the base-extinction
invariant) and passes the start clause unchanged into the cut witness. The clean entrance gives
the same state data (`bankCleanBoundaryRoot`), so the proof transfers with the start replaced:

* `BankCleanFirstZeroCut`: the old first-zero cut with the clean audit start;
* `bankCleanFirstZeroGoneStage`: from every state reachable from the clean gone cut, the first
  hit of the clean first-zero cut costs at most `bankRepairDigitFirstZeroMicroCharge n`;
* `bankCleanFirstZeroReceiptStable`, `bankCleanFirstZeroReceiptOfRetired`: the leader receipt,
  once produced at the clean boundary cut, is kept on every continuation;
* `bankCleanFirstZeroKeepStage`, `bankCleanFirstZeroClock`: the stage from the clean boundary
  cut (grant drain carried) into the clean first-zero cut with the receipt;
* `bankCleanFirstZeroEntranceClock`: the composition with `bankCleanBoundaryStage`, from the
  clean entrance at the boundary plus first-zero micro-charges.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open L3.AcceptedReceipts.WordEntrance.CleanWorker

set_option autoImplicit false

section CleanFirstZero

variable {n : Nat} (ring : DirectedRing n)
  (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)

/-- The clean first-zero cut: `BankRepairDigitFirstZeroCut` with the audit restarted at a clean
entrance instead of an `R`-fold-established one: two witnessed root-origin base passes after
retirement, at the W fixed root. Consumer: `bankCleanFirstZeroGoneStage`,
`bankCleanFirstZeroClock` (the clean first-block-zero cut of the clean digit core). -/
def BankCleanFirstZeroCut (z : BankReferenceState ring hbank) : Prop :=
  ∃ (start : BankReferenceState ring hbank) (word : List (Fin n)) (root : Fin n)
    (audit : DigitAudit (compileAdvice (ceilLogTwo n)) n) (retired : Nat),
    BankPostInheritedGrantDrain ring hbank start ∧ BankCleanRFold ring hbank start ∧
    word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (start, digitAuditInitial (piD start.val.1)) = (z, audit) ∧
    WFixedRoot ring root (piW z.val.1) ∧
    DigitAt ring audit audit.clock (piD z.val.1) audit.current ∧
    DigitTwoBaseCovers ring root audit 0 retired audit.clock

/-- **The first-zero clock from the clean gone cut**: from every state reachable from the clean
gone cut, the first hit of the clean first-zero cut costs at most the first-zero micro-charge.
The proof of `bankRepairDigitFirstZeroGoneStage` with the clean start. Consumer:
`bankCleanFirstZeroKeepStage`. -/
theorem bankCleanFirstZeroGoneStage (hn : 5 ≤ n) :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (BankCleanBoundaryGoneReachable ring hbank) (BankCleanFirstZeroCut ring hbank)
      (bankRepairDigitFirstZeroMicroCharge n) := by
  intro z hz T
  obtain ⟨_, w', ⟨start, word, hD, hC, hg, rfl⟩, rfl⟩ := hz
  obtain ⟨root, hss, hV⟩ := bankCleanBoundaryRoot ring hbank start hD hC
  obtain ⟨first, hd, hf2, hw, hft⟩ := bankRepairDigitZeroDelims ring hn hbank root start hV
  have hblock := (bankRepairDigitZeroGeomOf ring hn hbank root first start hd hf2
    hw).toBankRepairDigitZeroBlock
  have hi0 := bankRepairDigitZeroInvWord ring hn hbank root first hf2 hw _ word _
    (bankRepairDigitZeroInvInitial ring hbank root first start hd)
  have hext0 := bankRepairDigitBoundaryBaseExtinctOfSingleton ring hn hbank root start hss word hg
  have hpc := bankRepairDigitZeroPairCost ring hn hbank root first
    (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (start, digitAuditInitial (piD start.val.1))).2.clock
    (w'.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (start, digitAuditInitial (piD start.val.1))))
    (fun w => by
      have hiq := bankRepairDigitZeroInvWord ring hn hbank root first hf2 hw _ w _
        (bankRepairDigitZeroInvWord ring hn hbank root first hf2 hw _ w' _ hi0)
      refine ⟨bankRepairDigitZeroFrameOf ring hn hbank root first hf2 hw _ hblock _ hiq
        (bankRepairDigitZeroGoneWord hn ring hbank w _
          (bankRepairDigitZeroGoneWord hn ring hbank w' _ hg)) _
        (bankRepairDigitZeroExtinctMono ring root _ _ (by rw [hiq.2.2.2, hi0.2.2.2])
          (fun f hf => bankRepairDigitZeroFramesWord ring hbank w _ f
            (bankRepairDigitZeroFramesWord ring hbank w' _ f hf)) 0 _ hext0) ?_, hiq.2.1⟩
      rw [bankRepairDigitZeroClockWord ring hbank w, bankRepairDigitZeroClockWord ring hbank w']
      omega) T
  have htr := bankRepairDigitCostTransfer (bankRepairNext ring hbank)
    (bankRepairDigitBoundaryAuditNext ring hbank) (BankCleanFirstZeroCut ring hbank)
    (fun q => DigitTwoBaseCovers ring root q.2 0
      (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (start, digitAuditInitial (piD start.val.1))).2.clock q.2.clock) T
    (w'.foldl (bankRepairNext ring hbank) (word.foldl (bankRepairNext ring hbank) start))
    (w'.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
      (word.foldl (bankRepairDigitBoundaryAuditNext ring hbank)
        (start, digitAuditInitial (piD start.val.1))))
    (fun w hcov => by
      have hiq := bankRepairDigitZeroInvWord ring hn hbank root first hf2 hw _ w _
        (bankRepairDigitZeroInvWord ring hn hbank root first hf2 hw _ w' _ hi0)
      refine ⟨start, word ++ (w' ++ w), root, _, _, hD, hC, ?_, ?_, ?_, hcov⟩
      · rw [List.foldl_append, List.foldl_append]
        refine Prod.ext ?_ rfl
        rw [bankRepairDigitZeroFirstEq, bankRepairDigitZeroFirstEq, bankRepairDigitZeroFirstEq]
      · have hfix := bankRepairDigitBoundaryWFixedRootOfSingleton ring hn hbank root start hss
          (word ++ (w' ++ w))
        rw [List.foldl_append, List.foldl_append] at hfix
        exact hfix
      · have hat := hiq.1.2.1
        rw [bankRepairDigitZeroFirstEq, bankRepairDigitZeroFirstEq,
          bankRepairDigitZeroFirstEq] at hat
        exact hat)
  exact Nat.le_trans (Nat.mul_le_mul_left 2 (Nat.le_trans htr hpc))
    (bankRepairDigitZeroBudget hbank first hft T)

/-- Every state reachable from the clean gone cut is layout-fixed at some root. Consumer:
`bankCleanFirstZeroReceiptStable`. -/
theorem bankCleanFirstZeroGoneLayout (hn : 5 ≤ n) (z : BankReferenceState ring hbank)
    (hz : BankCleanBoundaryGoneReachable ring hbank z) :
    ∃ root, BankRepairDigitLayoutFixed ring hbank root z := by
  obtain ⟨_, w', ⟨start, word, hD, hC, _, rfl⟩, rfl⟩ := hz
  obtain ⟨root, _, hV⟩ := bankCleanBoundaryRoot ring hbank start hD hC
  exact ⟨root, (bankRepairDigitLayoutValuesWord ring hn hbank root w' _
    (bankRepairDigitLayoutValuesWord ring hn hbank root word start hV)).1⟩

/-- The clean boundary cut carries the leader receipt. Consumer:
`bankCleanFirstZeroKeepStage`. -/
theorem bankCleanFirstZeroReceiptOfRetired (z : BankReferenceState ring hbank)
    (hz : BankCleanBoundaryRetiredCut ring hbank z) :
    BankRepairDigitLeaderReceipt ring hbank z := by
  obtain ⟨_, _, root, _, _, _, _, hW, _, hrec, _⟩ := hz
  exact ⟨root, hW, hrec⟩

/-- Once produced, the leader receipt is kept on every run from a state reachable from the
clean gone cut. Consumer: `bankCleanFirstZeroKeepStage`. -/
theorem bankCleanFirstZeroReceiptStable (hn : 5 ≤ n) (z : BankReferenceState ring hbank)
    (hz : BankCleanBoundaryGoneReachable ring hbank z)
    (hrec : BankRepairDigitLeaderReceipt ring hbank z) (word : List (Fin n)) :
    BankRepairDigitLeaderReceipt ring hbank (word.foldl (bankRepairNext ring hbank) z) := by
  obtain ⟨root, hL⟩ := bankCleanFirstZeroGoneLayout ring hbank hn z hz
  obtain ⟨r, hW, hr⟩ := hrec
  have hrr : r = root := hL.1.2.2.1 r hW.1
  subst hrr
  exact ⟨r, bankRepairDigitBoundaryWFixedRootOfSingleton ring hn hbank r z hL.1 word,
    bankRepairDigitReceiptBankWord ring hn hbank r word z hL hr⟩

/-- The first-zero clock from the clean boundary cut, keeping the leader receipt. Consumer:
`bankCleanFirstZeroClock`. -/
theorem bankCleanFirstZeroKeepStage (hn : 5 ≤ n) :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (fun z => BankCleanBoundaryRetiredCut ring hbank z ∧
        BankCleanBoundaryGoneReachable ring hbank z)
      (fun z => BankCleanFirstZeroCut ring hbank z ∧ BankRepairDigitLeaderReceipt ring hbank z)
      (bankRepairDigitFirstZeroMicroCharge n) := by
  rintro z ⟨hr, hg⟩ T
  exact Nat.le_trans (Nat.mul_le_mul_left 2 (bankRepairDigitCostTransfer
    (bankRepairNext ring hbank) (bankRepairNext ring hbank)
    (fun y => BankCleanFirstZeroCut ring hbank y ∧ BankRepairDigitLeaderReceipt ring hbank y)
    (BankCleanFirstZeroCut ring hbank) T z z
    (fun w hw => ⟨hw, bankCleanFirstZeroReceiptStable ring hbank hn z hg
      (bankCleanFirstZeroReceiptOfRetired ring hbank z hr) w⟩)))
    (bankCleanFirstZeroGoneStage ring hbank hn z hg T)

/-- **The first-zero stage of the clean digit core**: from the clean boundary cut (grant drain,
clean retired cut, reachable from the clean gone cut; the target of `bankCleanBoundaryStage`),
the first hit of the clean first-zero cut with the leader receipt and the grant drain costs at
most `bankRepairDigitFirstZeroMicroCharge n`. Consumer: the clean digit core, as the
first-zero clock after its cuts are re-targeted to the clean audit start (the analogue of
`bankCleanDigitCoreFirstZeroClock`). -/
theorem bankCleanFirstZeroClock (hn : 5 ≤ n) :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (fun z => BankPostInheritedGrantDrain ring hbank z ∧
        (BankCleanBoundaryRetiredCut ring hbank z ∧ BankCleanBoundaryGoneReachable ring hbank z))
      (fun z => BankPostInheritedGrantDrain ring hbank z ∧
        (BankCleanFirstZeroCut ring hbank z ∧ BankRepairDigitLeaderReceipt ring hbank z))
      (bankRepairDigitFirstZeroMicroCharge n) := by
  have h := bankRepairDigitChargedWeaken (bankRepairNext ring hbank) _
    (fun z => BankPostInheritedGrantDrain ring hbank z ∧
      (BankCleanBoundaryRetiredCut ring hbank z ∧ BankCleanBoundaryGoneReachable ring hbank z))
    _ _ _ (fun _ hx => hx.2) (fun _ hx => hx) (bankCleanFirstZeroKeepStage ring hbank hn)
  exact bankCleanDigitChargedCarryDrain ring hn hbank _ _ _ (fun z hz => hz.1) h

/-- The boundary and first-zero stages composed from the clean entrance. Consumer: the clean
digit core (boundary plus first-zero part of the 201 pre-drain ledger). -/
theorem bankCleanFirstZeroEntranceClock (hn : 5 ≤ n)
    :
    BankRepairDigitChargedStage (bankRepairNext ring hbank)
      (fun z => BankPostInheritedGrantDrain ring hbank z ∧ BankCleanRFold ring hbank z)
      (fun z => BankPostInheritedGrantDrain ring hbank z ∧
        (BankCleanFirstZeroCut ring hbank z ∧ BankRepairDigitLeaderReceipt ring hbank z))
      (bankRepairDigitBoundaryMicroCharge n + bankRepairDigitFirstZeroMicroCharge n) :=
  bankRepairDigitZeroCompose (bankRepairNext ring hbank) _ _ _ _ _
    (bankCleanBoundaryStage ring hbank hn) (bankCleanFirstZeroClock ring hbank hn)

end CleanFirstZero

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankCleanFirstZeroGoneStage
#print axioms L3.RenewalReferenceClock.bankCleanFirstZeroGoneLayout
#print axioms L3.RenewalReferenceClock.bankCleanFirstZeroReceiptOfRetired
#print axioms L3.RenewalReferenceClock.bankCleanFirstZeroReceiptStable
#print axioms L3.RenewalReferenceClock.bankCleanFirstZeroKeepStage
#print axioms L3.RenewalReferenceClock.bankCleanFirstZeroClock
#print axioms L3.RenewalReferenceClock.bankCleanFirstZeroEntranceClock
