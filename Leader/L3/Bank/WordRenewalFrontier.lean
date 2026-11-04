import Leader.L3.Bank.WordRenewalFresh

/-!
R10a frontier rows on the original W epoch chain.

Two rows of the no-hard-S1 census: the P2 prefix terminal retires the
worker without a WCompletionReceipt, and a physical done service
clears the responder root's SI lease.  Outside the BANK band
(useSmall = true, or n < t + 2) a P2 return can come before any soft
lap, so the R10a frontier statements need the BANK-band premises
(PROGRESS 2026-11-01).
-/
namespace L3.RenewalReferenceClock

set_option autoImplicit false
set_option Elab.async false

/-- Target.wWorkerReceiptStep, P2 row: an authentic prefix whose
host is the selected initiator is retired on this non-hard-S1
terminal, without producing a WCompletionReceipt. Consumer:
the P2 row of the no-hard-S1 worker census for the R10a frontier
(repair.tex 1054--1074). -/
theorem bankWordRenewalFrontierPrefixTerminalRetires {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (w : WWorkerTrail n)
    (hworker : z.2.2.worker = some w)
    (hhost : e = w.host)
    (hrow :
      (bankWordEpochSelectedReceipt ring z e).worker.row = "P2")
    (hno :
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 =
        false) :
    (bankWordEpochNext ring root z e).2.2.worker = none ∧
      (bankWordEpochNext ring root z e).2.2.completion = none := by
  have hp :
      (workerW (z.2.1 e)
        (z.2.1 (ring.rightNeighbor e))).row = "P2" := hrow
  have hh :
      (serW (z.2.1 e)
        (z.2.1 (ring.rightNeighbor e))).hard.hardS1 = false := hno
  have hstep :
      wWorkerReceiptStep root e (ring.rightNeighbor e)
        (z.2.2.clock + 1)
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        (wGenuineAcceptance root e
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (z.2.2.validation e)
          (z.2.2.validation (ring.rightNeighbor e)))
        (some w) = (none, none) := by
    simp [wWorkerReceiptStep, hp, hh, wWorkerAuthorityAt, hhost.symm]
  constructor
  · change
        (wWorkerReceiptStep root e (ring.rightNeighbor e)
          (z.2.2.clock + 1)
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (wGenuineAcceptance root e
            (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
            (z.2.2.validation e)
            (z.2.2.validation (ring.rightNeighbor e)))
          z.2.2.worker).1 = none
    rw [hworker, hstep]
  · change
        (wWorkerReceiptStep root e (ring.rightNeighbor e)
          (z.2.2.clock + 1)
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (wGenuineAcceptance root e
            (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
            (z.2.2.validation e)
            (z.2.2.validation (ring.rightNeighbor e)))
          z.2.2.worker).2 = none
    rw [hworker, hstep]

/-- The physical incoming-root P2 done service, unlike the
WCompletionReceipt predicate, clears the responder's actual
SI lease to zero. Consumer: hard-S1 versus exhausted-soft-lap
discrimination in the serializer frontier argument. -/
theorem bankWordRenewalFrontierDoneClearsIncomingLease {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (hroot : ring.rightNeighbor e = root)
    (hdistinct : root ≠ e)
    (haccept :
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardAccept =
        false)
    (hdone :
      (bankWordEpochSelectedReceipt ring z e).worker.done = true) :
    ((bankWordEpochNext ring root z e).2.1 root).siLease.val = 0 := by
  have ha :
      (serW (z.2.1 e)
        (z.2.1 (ring.rightNeighbor e))).hard.hardAccept = false :=
    haccept
  have hd :
      (workerW (z.2.1 e)
        (z.2.1 (ring.rightNeighbor e))).done = true := hdone
  change (phiW ring z.2.1 e root).siLease.val = 0
  change
    ((if root = e then
      (pairW (z.2.1 e)
        (z.2.1 (ring.rightNeighbor e))).1
    else if root = ring.rightNeighbor e then
      (pairW (z.2.1 e)
        (z.2.1 (ring.rightNeighbor e))).2
    else z.2.1 root)).siLease.val = 0
  rw [if_neg hdistinct, if_pos hroot.symm]
  change
    (leasePair (compileAdvice (ceilLogTwo n))
      (z.2.1 e).siLease
      (z.2.1 (ring.rightNeighbor e)).siLease
      (serW (z.2.1 e)
        (z.2.1 (ring.rightNeighbor e))).hard.hardAccept
      (serW (z.2.1 e)
        (z.2.1 (ring.rightNeighbor e))).hard.softAccept
      (workerW (z.2.1 e)
        (z.2.1 (ring.rightNeighbor e))).done).2.val = 0
  rw [ha, hd]
  rfl

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- A genuine hard acceptance on the compiled BANK branch
physically installs the canonical prefix at the selected root
and reloads precisely the lease L used by the renewal argument.
Consumer: the first prefix/lease cut in repair.tex R10a W. -/
theorem bankWordRenewalFrontierFreshBankPrepared {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : BankWordRenewalFreshSeed ring root s) :
    (seed.1.1.2.1 root).si =
      launchPrefix (compileAdvice (ceilLogTwo n)).t ∧
    (seed.1.1.2.1 root).siLease.val =
      bankWordRenewalLease n := by
  obtain ⟨pre, e, hgen, heq⟩ := seed.2
  obtain ⟨he, _, ha⟩ :=
    bankWordHardEpochSelectedGenuineOwnerFlags
      ring root pre.1 e hgen
  obtain ⟨_, _, _, _, _, hlease⟩ :=
    bankWordHardEpochSelectedGenuineResetAndLease
      ring root pre.1 e hgen
  subst e
  have haccept :
      (serW (pre.1.2.1 root)
        (pre.1.2.1 (ring.rightNeighbor root))).hard.hardAccept =
        true := ha
  have hprefix := bankWordHardEpochHardAcceptRootLaunch
    ring root pre.1.2.1 haccept
  have hstate := congrArg
    (fun v : BankWordRenewalPostSOne ring root s => v.1) heq
  change
    ((bankWordRenewalNext ring root s pre root).1.2.1 root).si =
      launchPrefix (compileAdvice (ceilLogTwo n)).t at hprefix
  change
    ((bankWordRenewalNext ring root s pre root).1.2.1 root).siLease.val =
      (compileAdvice (ceilLogTwo n)).siLeaseMax at hlease
  rw [hstate] at hprefix hlease
  exact ⟨hprefix, hlease.trans
    (bankWordHardEpochBankLeaseMaximum hbank)⟩

/-- The existing rooted BANK invariant really holds at the
first fresh, ticketed S6 cut, when its *represented-root*
hypothesis is available. This does not claim preservation
through subsequent physical rows.
Consumer: the per-hard-epoch soft-finish/lease genealogy. -/
theorem bankWordRenewalFrontierFreshBankCleanOfRootClass {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (seed : BankWordRenewalFreshSeed ring root s) :
    BankWordHardEpochCleanInvariant ring root seed.1.1 := by
  obtain ⟨pre, e, hgen, heq⟩ := seed.2
  have hclean := bankWordHardEpochGenuineEstablishesClean
    ring hn hbank root s hs pre.1 pre.2.1 e hgen
  have hstate := congrArg
    (fun v : BankWordRenewalPostSOne ring root s => v.1) heq
  change
    BankWordHardEpochCleanInvariant ring root
      (bankWordRenewalNext ring root s pre e).1 at hclean
  rw [hstate] at hclean
  exact hclean

/-- A genuinely accepted root in the represented fixed-root
BANK class has no surviving physical foreign SI cursor.
This imports the verified ticket-origin to EWord hard-scrub
bridge; it does not assume empty initial private scratch.
Consumer: the starting case of the no-hard-S1 worker census. -/
theorem bankWordRenewalFrontierFreshBankForeignFree {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (seed : BankWordRenewalFreshSeed ring root s) :
    ∀ i : Fin n, i ≠ root →
      freeSI (seed.1.1.2.1 i).si = true := by
  obtain ⟨pre, e, hgen, heq⟩ := seed.2
  have horigin := bankWordRootDoneOriginReachable
    ring hn hbank root s hs pre.1 pre.2.1
  have hfree := bankWordRootDoneOriginGenuineClean
    ring hn hbank root s hs pre.1 horigin e hgen
  have hstate := congrArg
    (fun v : BankWordRenewalPostSOne ring root s => v.1) heq
  change
    ∀ i : Fin n, i ≠ root →
      freeSI
        (((bankWordRenewalNext ring root s pre e).1.2.1 i).si) =
          true at hfree
  rw [hstate] at hfree
  exact hfree

/-- Literal serializer guard: a hard S1 reads a zero OLD
physical source lease. Consumer: the serializer-interruption
side of repair.tex R10a, before using a historical ledger. -/
theorem bankWordRenewalFrontierHardStartReadsZero {c : Compiled}
    (x y : ProjW c)
    (hhard : (serW x y).hard.hardS1 = true) :
    x.siLease.val = 0 := by
  change
    ((postW x y).eX.l &&
      (x.ser.cert == .REQUESTED) &&
      (x.siLease.val == 0)) = true at hhard
  by_cases hz : x.siLease.val = 0
  · exact hz
  · simp [hz] at hhard

/-- Under the *physical* clean-epoch invariant, the actual
hard-S1 zero lease forces all L soft finishes since the most
recent genuine hard S6. This is the ledger-to-interruption
implication, not yet its preservation/genealogy proof.
Consumer: serializer upper-tail quota in repair.tex R10a W. -/
theorem bankWordRenewalFrontierHardStartNeedsSoftFinishes {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n)
    (hclean : BankWordHardEpochCleanInvariant ring root z)
    (hactive :
      0 < (bankWordHardEpochLedger ring root z).hardEpochs)
    (hnotdone :
      (bankWordHardEpochLedger ring root z).workerDone = false)
    (hhard :
      (bankWordEpochSelectedReceipt ring z root).serializer.hard.hardS1 =
        true) :
    (bankWordHardEpochLedger ring root z).softFinishes =
      bankWordRenewalLease n := by
  have hzero := bankWordRenewalFrontierHardStartReadsZero
    (z.2.1 root) (z.2.1 (ring.rightNeighbor root)) hhard
  have hc := hclean ⟨hactive, hnotdone⟩
  have horder := hc.1
  have hcap := hc.2.1
  have hlease := hc.2.2.2.1
  unfold bankWordRenewalLease
  omega

/-- Full I1 provenance census at one physical pair, without
assuming its authority-disjointness. A non-hard-S1 I1 either
frames the witness or erases it precisely on the two hard
authority guards.
Consumer: proving that the erasing alternative is unreachable
on the uninterrupted BANK worker trajectory. -/
theorem bankWordRenewalFrontierIoneAuthorityCensus
    {n : Nat} {c : Compiled}
    (root edge next : Fin n) (clock : Nat)
    (x y : ProjW c) (w : WWorkerTrail n)
    (accept : Option WValidationTicket)
    (hrow : (workerW x y).row = "I1")
    (hnot : (serW x y).hard.hardS1 = false) :
    wWorkerReceiptStep root edge next clock x y
      accept (some w) =
      (if ((serW x y).hard.hardLeft = true ∧
            wWorkerAuthorityAt w edge) ∨
          ((serW x y).hard.hardRight = true ∧
            wWorkerAuthorityAt w next)
       then (none, none) else (some w, none)) := by
  simp [wWorkerReceiptStep, hrow, hnot]

/-- The P0 physical done row, like the previously established
P2 row, is NOT WCompletionReceipt. If it meets the tracked
prefix host, the actual ghost worker is retired.
Consumer: the P0 exclusion case of the BANK frontier census. -/
theorem bankWordRenewalFrontierPrefixShortDoneRetires
    {n : Nat} {c : Compiled}
    (root edge next : Fin n) (clock : Nat)
    (x y : ProjW c) (w : WWorkerTrail n)
    (accept : Option WValidationTicket)
    (hrow : (workerW x y).row = "P0")
    (hnot : (serW x y).hard.hardS1 = false)
    (hhost : edge = w.host) :
    wWorkerReceiptStep root edge next clock x y
      accept (some w) = (none, none) := by
  simp [wWorkerReceiptStep, hrow, hnot,
    wWorkerAuthorityAt, hhost.symm]

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- R10a W serializer census, nonroot source row (including the
incoming-root service): no genuine root S6, soft S1 or soft S6
can be counted at a different source. The worker-done bit may
turn true, but cannot turn from true back to false.
Consumer: the nonroot part of the epoch-clean step. -/
theorem bankWordRenewalFrontierNonrootLedgerStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (he : e ≠ root) :
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).hardEpochs =
        (bankWordHardEpochLedger ring root z).hardEpochs ∧
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).softStarts =
        (bankWordHardEpochLedger ring root z).softStarts ∧
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).softFinishes =
        (bankWordHardEpochLedger ring root z).softFinishes ∧
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).pendingSoft =
        (bankWordHardEpochLedger ring root z).pendingSoft ∧
    ((bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).workerDone = false →
      (bankWordHardEpochLedger ring root z).workerDone = false) := by
  have hgen :
      bankWordHardEpochGenuine ring root
        (bankWordEpochSelectedReceipt ring z e)
        (bankWordHardEpochLedger ring root z) = false := by
    simp [bankWordHardEpochGenuine, wGenuineAcceptance,
      bankWordEpochSelectedReceipt, he]
  have hstart :
      bankWordHardEpochSoftStart root
        (bankWordEpochSelectedReceipt ring z e) = false := by
    simp [bankWordHardEpochSoftStart,
      bankWordEpochSelectedReceipt, he]
  have hfinish :
      bankWordHardEpochSoftFinish root
        (bankWordEpochSelectedReceipt ring z e) = false := by
    simp [bankWordHardEpochSoftFinish,
      bankWordEpochSelectedReceipt, he]
  unfold bankWordHardEpochGenuine at hgen
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [bankWordHardEpochLedgerNext,
      bankWordHardEpochStep, hgen]
  · simp [bankWordHardEpochLedgerNext,
      bankWordHardEpochStep, hgen, hstart]
  · simp [bankWordHardEpochLedgerNext,
      bankWordHardEpochStep, hgen, hfinish]
  · simp [bankWordHardEpochLedgerNext,
      bankWordHardEpochStep, hgen, hstart, hfinish]
  · intro hnew
    cases hold : (bankWordHardEpochLedger ring root z).workerDone with
    | false =>
        rfl
    | true =>
        have hpost :
            (bankWordHardEpochLedger ring root
              (bankWordEpochNext ring root z e)).workerDone =
                true := by
          simp [bankWordHardEpochLedgerNext,
            bankWordHardEpochStep, hgen, hold]
        rw [hpost] at hnew
        cases hnew

/-- R10a W serializer census, remote physical edge: the actual
phiW root record is framed, every counted soft field is framed,
and a newly completed worker only makes CleanInvariant vacuous.
No class or reachability premise is necessary for this subcase.
Consumer: nonincident branch of the requested epoch closure. -/
theorem bankWordRenewalFrontierHardEpochRemoteStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (he : e ≠ root)
    (hj : ring.rightNeighbor e ≠ root)
    (hclean : BankWordHardEpochCleanInvariant ring root z) :
    BankWordHardEpochCleanInvariant ring root
      (bankWordEpochNext ring root z e) := by
  have hledger :=
    bankWordRenewalFrontierNonrootLedgerStep
      ring root z e he
  have hroot :=
    bankWordHardEpochRootRemoteFrame
      ring root z e he.symm hj.symm
  unfold BankWordHardEpochCleanInvariant at hclean ⊢
  dsimp only at hclean ⊢
  intro hactive
  have hold :
      0 < (bankWordHardEpochLedger ring root z).hardEpochs ∧
      (bankWordHardEpochLedger ring root z).workerDone = false := by
    constructor
    · simpa only [hledger.1] using hactive.1
    · exact hledger.2.2.2.2 hactive.2
  obtain ⟨horder, hcap, hbalance, hlease, hrunning⟩ :=
    hclean hold
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hledger.2.2.1, hledger.2.1] using horder
  · simpa only [hledger.2.1] using hcap
  · simpa only [hledger.2.1, hledger.2.2.1,
      hledger.2.2.2.1] using hbalance
  · simpa only [hroot, hledger.2.2.1] using hlease
  · intro hr
    have holdRoot :
        (z.2.1 root).ser.cert = .RUNNING ∧
        (z.2.1 root).ser.wphase = .CURRENT := by
      simpa only [hroot] using hr
    simpa only [hledger.2.2.2.1] using
      (hrunning holdRoot)

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- One selected W service advances the hard-epoch ledger and the
WOriginGhost with identical ticket and worker coordinates.
Consumer: fresh I0 provenance in repair.tex, R10a W. -/
private theorem bankWordRenewalFrontierLedgerGhostStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (hvalidation :
      (bankWordHardEpochLedger ring root z).validation =
        z.2.2.validation)
    (hworker :
      (bankWordHardEpochLedger ring root z).worker =
        z.2.2.worker) :
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).validation =
        (bankWordEpochNext ring root z e).2.2.validation ∧
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).worker =
        (bankWordEpochNext ring root z e).2.2.worker := by
  rw [bankWordHardEpochLedgerNext]
  constructor
  · funext i
    change
      (if i = e then
        (wValidationPair (z.2.2.clock + 1)
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          ((bankWordHardEpochLedger ring root z).validation e)
          ((bankWordHardEpochLedger ring root z).validation
            (ring.rightNeighbor e))).1
       else if i = ring.rightNeighbor e then
        (wValidationPair (z.2.2.clock + 1)
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          ((bankWordHardEpochLedger ring root z).validation e)
          ((bankWordHardEpochLedger ring root z).validation
            (ring.rightNeighbor e))).2
       else (bankWordHardEpochLedger ring root z).validation i) =
      (if i = e then
        (wValidationPair (z.2.2.clock + 1)
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (z.2.2.validation e)
          (z.2.2.validation (ring.rightNeighbor e))).1
       else if i = ring.rightNeighbor e then
        (wValidationPair (z.2.2.clock + 1)
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (z.2.2.validation e)
          (z.2.2.validation (ring.rightNeighbor e))).2
       else z.2.2.validation i)
    rw [hvalidation]
  · change
      (wWorkerReceiptStep root e (ring.rightNeighbor e)
        (z.2.2.clock + 1)
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        (wGenuineAcceptance root e
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          ((bankWordHardEpochLedger ring root z).validation e)
          ((bankWordHardEpochLedger ring root z).validation
            (ring.rightNeighbor e)))
        (bankWordHardEpochLedger ring root z).worker).1 =
      (wWorkerReceiptStep root e (ring.rightNeighbor e)
        (z.2.2.clock + 1)
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        (wGenuineAcceptance root e
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (z.2.2.validation e)
          (z.2.2.validation (ring.rightNeighbor e)))
        z.2.2.worker).1
    rw [hvalidation, hworker]

/-- The hard-epoch ledger and WOriginGhost coincide on the
actual chronological physical service history. In particular
a genuine hard receipt in the former is not a fabricated
receipt in the latter. Consumer: fresh-worker base case. -/
theorem bankWordRenewalFrontierLedgerGhostCoherence {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z) :
    (bankWordHardEpochLedger ring root z).validation =
      z.2.2.validation ∧
    (bankWordHardEpochLedger ring root z).worker =
      z.2.2.worker := by
  have hrun :
      ∀ (word : List (Fin n)) (a : BankWordEpochState n),
        (bankWordHardEpochLedger ring root a).validation =
          a.2.2.validation →
        (bankWordHardEpochLedger ring root a).worker =
          a.2.2.worker →
        (bankWordHardEpochLedger ring root
          (bankWordEpochRun ring root a word)).validation =
            (bankWordEpochRun ring root a word).2.2.validation ∧
        (bankWordHardEpochLedger ring root
          (bankWordEpochRun ring root a word)).worker =
            (bankWordEpochRun ring root a word).2.2.worker := by
    intro word
    induction word with
    | nil =>
        intro a hv hw
        exact ⟨hv, hw⟩
    | cons e tail ih =>
        intro a hv hw
        have hnext :=
          bankWordRenewalFrontierLedgerGhostStep
            ring root a e hv hw
        exact ih (bankWordEpochNext ring root a e)
          hnext.1 hnext.2
  obtain ⟨word, hword⟩ := hz
  rw [← hword]
  exact hrun word (bankWordEpochStart s) rfl rfl

/-- A fresh genuine hard-S6 seed contains the actual tracked
canonical prefixRun worker in WOriginGhost, not merely a
canonical physical SI byte at the root. The historical hard
ledger and original ghost have the same joined ticket.
Consumer: R10a worker-half fresh-entry induction base. -/
theorem bankWordRenewalFrontierFreshWorkerWitness {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (seed : BankWordRenewalFreshSeed ring root s) :
    ∃ w : WWorkerTrail n,
      seed.1.1.2.2.worker = some w ∧
      w.phase = .prefixRun ∧
      w.host = root ∧
      w.target = root ∧
      w.index = 0 := by
  obtain ⟨pre, e, hgen, heq⟩ := seed.2
  have hcoherent :=
    bankWordRenewalFrontierLedgerGhostCoherence
      ring root s pre.1 pre.2.1
  have haccept :
      (wGenuineAcceptance root e
        (pre.1.2.1 e)
        (pre.1.2.1 (ring.rightNeighbor e))
        (pre.1.2.2.validation e)
        (pre.1.2.2.validation (ring.rightNeighbor e))).isSome =
        true := by
    have hcopy := hgen
    change
      (wGenuineAcceptance root e
        (pre.1.2.1 e)
        (pre.1.2.1 (ring.rightNeighbor e))
        ((bankWordHardEpochLedger ring root pre.1).validation e)
        ((bankWordHardEpochLedger ring root pre.1).validation
          (ring.rightNeighbor e))).isSome = true at hcopy
    rw [hcoherent.1] at hcopy
    exact hcopy
  have hflags :=
    bankWordHardEpochSelectedGenuineOwnerFlags
      ring root pre.1 e hgen
  have hrow :
      (workerW (pre.1.2.1 e)
        (pre.1.2.1 (ring.rightNeighbor e))).row = "I0" :=
    bankWordHardEpochHardAcceptIzeroRow
      (pre.1.2.1 e)
      (pre.1.2.1 (ring.rightNeighbor e)) hflags.2.2
  cases ht :
    wGenuineAcceptance root e
      (pre.1.2.1 e) (pre.1.2.1 (ring.rightNeighbor e))
      (pre.1.2.2.validation e)
      (pre.1.2.2.validation (ring.rightNeighbor e)) with
  | none =>
      simp [ht] at haccept
  | some ticket =>
      have hlaunch :
          (bankWordEpochNext ring root pre.1 e).2.2.worker =
            some (WWorkerTrail.mk ticket (pre.1.2.2.clock + 1) .prefixRun
              root root 0 [] []) := by
        change
          (wWorkerReceiptStep root e (ring.rightNeighbor e)
            (pre.1.2.2.clock + 1)
            (pre.1.2.1 e)
            (pre.1.2.1 (ring.rightNeighbor e))
            (wGenuineAcceptance root e
              (pre.1.2.1 e)
              (pre.1.2.1 (ring.rightNeighbor e))
              (pre.1.2.2.validation e)
              (pre.1.2.2.validation (ring.rightNeighbor e)))
            pre.1.2.2.worker).1 =
            some (WWorkerTrail.mk ticket (pre.1.2.2.clock + 1) .prefixRun
              root root 0 [] [])
        rw [ht]
        simp [wWorkerReceiptStep, hrow]
      have hstate : bankWordEpochNext ring root pre.1 e = seed.1.1 :=
        congrArg
          (fun v : BankWordRenewalPostSOne ring root s => v.1) heq
      rw [hstate] at hlaunch
      refine ⟨_, hlaunch, rfl, rfl, rfl, rfl⟩

/-- A physical F service, if it is not a hard S1, preserves the
actual tracked worker and generates no completion receipt.
Consumer: the F frame row of the no-hard-S1 census. -/
theorem bankWordRenewalFrontierPhysicalFrame {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (w : WWorkerTrail n)
    (hworker : z.2.2.worker = some w)
    (hrow :
      (bankWordEpochSelectedReceipt ring z e).worker.row = "F")
    (hnot :
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 =
        false) :
    (bankWordEpochNext ring root z e).2.2.worker = some w ∧
    (bankWordEpochNext ring root z e).2.2.completion = none := by
  have hstep :
      wWorkerReceiptStep root e (ring.rightNeighbor e)
        (z.2.2.clock + 1)
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        (wGenuineAcceptance root e
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (z.2.2.validation e)
          (z.2.2.validation (ring.rightNeighbor e)))
        (some w) = (some w, none) := by
    have hp : (workerW (z.2.1 e)
        (z.2.1 (ring.rightNeighbor e))).row = "F" := hrow
    have hh : (serW (z.2.1 e)
        (z.2.1 (ring.rightNeighbor e))).hard.hardS1 = false := hnot
    simp [wWorkerReceiptStep, hp, hh]
  constructor
  · change
      (wWorkerReceiptStep root e (ring.rightNeighbor e)
        (z.2.2.clock + 1)
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        (wGenuineAcceptance root e
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (z.2.2.validation e)
          (z.2.2.validation (ring.rightNeighbor e)))
        z.2.2.worker).1 = some w
    rw [hworker, hstep]
  · change
      (wWorkerReceiptStep root e (ring.rightNeighbor e)
        (z.2.2.clock + 1)
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        (wGenuineAcceptance root e
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (z.2.2.validation e)
          (z.2.2.validation (ring.rightNeighbor e)))
        z.2.2.worker).2 = none
    rw [hworker, hstep]

/-- Actual non-hard-S1 I1 leaves a tracked worker intact if the
specific serializer hardLeft/hardRight incident guards avoid
both sites carrying its authority. This is the precise
epoch-chain frame alternative; the physical shape induction
must establish disjointness on a no-hard-S1 BANK word.
Consumer: the I1 branch of R10a W. -/
theorem bankWordRenewalFrontierIoneEpochDisjointFrame {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (w : WWorkerTrail n)
    (hworker : z.2.2.worker = some w)
    (hrow :
      (bankWordEpochSelectedReceipt ring z e).worker.row = "I1")
    (hnot :
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 =
        false)
    (hdisjoint :
      ¬ (((bankWordEpochSelectedReceipt ring z e).serializer.hard.hardLeft =
            true ∧ wWorkerAuthorityAt w e) ∨
          ((bankWordEpochSelectedReceipt ring z e).serializer.hard.hardRight =
            true ∧ wWorkerAuthorityAt w (ring.rightNeighbor e)))) :
    (bankWordEpochNext ring root z e).2.2.worker = some w ∧
    (bankWordEpochNext ring root z e).2.2.completion = none := by
  have hstep :
      wWorkerReceiptStep root e (ring.rightNeighbor e)
        (z.2.2.clock + 1)
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        (wGenuineAcceptance root e
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (z.2.2.validation e)
          (z.2.2.validation (ring.rightNeighbor e)))
        (some w) = (some w, none) := by
    have hc := bankWordRenewalFrontierIoneAuthorityCensus
      root e (ring.rightNeighbor e) (z.2.2.clock + 1)
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e)) w
      (wGenuineAcceptance root e
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        (z.2.2.validation e)
        (z.2.2.validation (ring.rightNeighbor e)))
      hrow hnot
    rw [hc]
    exact if_neg hdisjoint
  constructor
  · change
      (wWorkerReceiptStep root e (ring.rightNeighbor e)
        (z.2.2.clock + 1)
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        (wGenuineAcceptance root e
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (z.2.2.validation e)
          (z.2.2.validation (ring.rightNeighbor e)))
        z.2.2.worker).1 = some w
    rw [hworker, hstep]
  · change
      (wWorkerReceiptStep root e (ring.rightNeighbor e)
        (z.2.2.clock + 1)
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        (wGenuineAcceptance root e
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          (z.2.2.validation e)
          (z.2.2.validation (ring.rightNeighbor e)))
        z.2.2.worker).2 = none
    rw [hworker, hstep]

/-- A matched A0 at the physical worker's readyRun host on
the predecessor edge of root writes an actual WCompletionReceipt
in the original WOriginGhost.
Consumer: BankWordRenewalCompleted (fresh-kernel success). -/
theorem bankWordRenewalFrontierTrackedAZeroCompletes {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e : Fin n)
    (w : WWorkerTrail n)
    (hworker : z.2.2.worker = some w)
    (hrow :
      (bankWordEpochSelectedReceipt ring z e).worker.row = "A0")
    (hnot :
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 =
        false)
    (hphase : w.phase = .readyRun)
    (hhost : w.host = e)
    (hnext : ring.rightNeighbor e = root) :
    BankWordRenewalCompleted
      (bankWordEpochNext ring root z e) := by
  refine ⟨{ service := z.2.2.clock + 1, worker := w }, ?_⟩
  change
    (wWorkerReceiptStep root e (ring.rightNeighbor e)
      (z.2.2.clock + 1)
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      (wGenuineAcceptance root e
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        (z.2.2.validation e)
        (z.2.2.validation (ring.rightNeighbor e)))
      z.2.2.worker).2 =
        some { service := z.2.2.clock + 1, worker := w }
  rw [hworker]
  have hp : (workerW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).row = "A0" := hrow
  have hh : (serW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).hard.hardS1 = false := hnot
  subst hnext
  simp [wWorkerReceiptStep, hp, hh, hphase, hhost]

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- R10a W R1, local SI census: no physical P0/P2/A0 done
can originate at a free source. Consumer: the incoming-root
first-service check after a genuine hard S6. -/
theorem bankWordRenewalFrontierFreeSourceNoDone
    {c : Compiled} (x y : ProjW c)
    (hfree : freeSI x.si = true) :
    (workerW x y).done = false := by
  have hk : x.si.kind = .OFF := by
    cases h : x.si.kind with
    | OFF => rfl
    | PREFIX => simp [freeSI, h] at hfree
    | ROOT => simp [freeSI, h] at hfree
  have hc : x.si.cur = .NONE := by
    cases h : x.si.cur with
    | NONE => rfl
    | BACK => simp [freeSI, h] at hfree
    | SUM => simp [freeSI, h] at hfree
  simp [workerW, siStep, ProjW.lift, hk, hc]
  repeat' (first | rfl | split)

/-- R10a W R1 base: at the fresh genuine cut every nonroot
SI is free; therefore its very next incoming-root service
cannot debit the root lease through worker.done.
This asserts the actual selected receipt, not an arbitrary
counterfactual worker state. -/
theorem bankWordRenewalFrontierFreshIncomingNoDone
    {n : Nat} (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (seed : BankWordRenewalFreshSeed ring root s)
    (hpred : ring.rightNeighbor e = root) :
    (bankWordEpochSelectedReceipt ring seed.1.1 e).worker.done =
      false := by
  have hd : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) e
  have he : e ≠ root := by
    intro h
    exact hd (hpred.trans h.symm)
  have hfree :=
    bankWordRenewalFrontierFreshBankForeignFree
      ring root s hn hbank hs seed e he
  change (workerW (seed.1.1.2.1 e)
    (seed.1.1.2.1 (ring.rightNeighbor e))).done = false
  exact bankWordRenewalFrontierFreeSourceNoDone
    (seed.1.1.2.1 e)
    (seed.1.1.2.1 (ring.rightNeighbor e)) hfree

/-- R10a W R1, exact bankWordHardEpochStep owner equation
on every nonroot source, including the incoming-root seam.
The observer credits workerDone only on a witnessed completion,
not merely on the physical workerW.done bit.
Consumer: matched A0 receipt and the remaining R1 census. -/
theorem bankWordRenewalFrontierNonrootWorkerDoneEquation
    {n : Nat} (ring : DirectedRing n) (root e : Fin n)
    (z : BankWordEpochState n) (he : e ≠ root) :
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).workerDone =
      ((bankWordHardEpochLedger ring root z).workerDone ||
        (bankWordHardEpochActive
            (bankWordHardEpochLedger ring root z) &&
          (wWorkerReceiptStep root e (ring.rightNeighbor e)
            (z.2.2.clock + 1)
            (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
            (wGenuineAcceptance root e
              (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
              ((bankWordHardEpochLedger ring root z).validation e)
              ((bankWordHardEpochLedger ring root z).validation
                (ring.rightNeighbor e)))
            (bankWordHardEpochLedger ring root z).worker).2.isSome)) := by
  simp [bankWordHardEpochLedgerNext,
    bankWordHardEpochStep, bankWordEpochSelectedReceipt,
    wGenuineAcceptance, he]

/-- R10a W R1, tracked A0 row: when the selected physical
incoming-root A0 really belongs to the current READY worker
trail, the same selected edge emits WCompletionReceipt, and
the actual epoch ledger makes workerDone true. This excludes
a false zero-lease objection on that row.
The unwitnessed P0/P2 alternatives are NOT covered here. -/
theorem bankWordRenewalFrontierIncomingReadyReceiptDone
    {n : Nat} (ring : DirectedRing n) (root e : Fin n)
    (z : BankWordEpochState n)
    (he : e ≠ root)
    (hpred : ring.rightNeighbor e = root)
    (hactive : 0 <
      (bankWordHardEpochLedger ring root z).hardEpochs)
    (hnotdone :
      (bankWordHardEpochLedger ring root z).workerDone = false)
    (w : WWorkerTrail n)
    (hworker :
      (bankWordHardEpochLedger ring root z).worker = some w)
    (hphase : w.phase = .readyRun)
    (hhost : w.host = e)
    (hrow :
      (bankWordEpochSelectedReceipt ring z e).worker.row = "A0")
    (hnohard :
      (bankWordEpochSelectedReceipt ring z e).serializer.hard.hardS1 =
        false) :
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).workerDone = true := by
  have hrow' :
      (workerW (z.2.1 e)
        (z.2.1 (ring.rightNeighbor e))).row = "A0" := hrow
  have hnohard' :
      (serW (z.2.1 e)
        (z.2.1 (ring.rightNeighbor e))).hard.hardS1 =
        false := hnohard
  have hreceipt :
      (wWorkerReceiptStep root e (ring.rightNeighbor e)
        (z.2.2.clock + 1)
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        (wGenuineAcceptance root e
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          ((bankWordHardEpochLedger ring root z).validation e)
          ((bankWordHardEpochLedger ring root z).validation
            (ring.rightNeighbor e)))
        (some w)).2.isSome = true := by
    subst hpred
    simp [wWorkerReceiptStep, hrow', hnohard',
      hphase, hhost]
  have hp :
      (bankWordHardEpochLedger ring root z).hardEpochs ≠ 0 :=
    Nat.ne_of_gt hactive
  have hactiveBool :
      bankWordHardEpochActive
        (bankWordHardEpochLedger ring root z) = true := by
    simp [bankWordHardEpochActive, hp, hnotdone]
  rw [bankWordRenewalFrontierNonrootWorkerDoneEquation
    ring root e z he]
  rw [hworker, hreceipt, hactiveBool, hnotdone]
  rfl

/-- R10a W R2 base: the physically selected genuine hard S6
returns the root serializer certificate to IDLE, not RUNNING.
Consumer: impossibility of another hard S6 on the first service
after the fresh cut. -/
theorem bankWordRenewalFrontierFreshRootIdle
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (seed : BankWordRenewalFreshSeed ring root s) :
    (seed.1.1.2.1 root).ser.cert = .IDLE := by
  obtain ⟨pre, e, hgen, heq⟩ := seed.2
  have hidle := bankWordHardEpochSelectedGenuineRootIdle
    ring hn hbank root s hs pre.1 pre.2.1 e hgen
  have hstate := congrArg
    (fun v : BankWordRenewalPostSOne ring root s => v.1) heq
  change
    ((bankWordRenewalNext ring root s pre e).1.2.1 root).ser.cert =
      .IDLE at hidle
  rw [hstate] at hidle
  exact hidle

/-- R10a W R2 base, original scheduler alphabet: no selected
old-state hard S6 can fire immediately after a fresh genuine
hard S6, on either a nonroot or root-outgoing service.
The later hard-S1-to-S6 ticket-completeness implication remains open. -/
theorem bankWordRenewalFrontierFreshNoImmediateHardAccept
    {n : Nat} (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (seed : BankWordRenewalFreshSeed ring root s) :
    (bankWordEpochSelectedReceipt ring seed.1.1 e).serializer.hard.hardAccept =
      false := by
  by_cases he : e = root
  · subst e
    have hidle :=
      bankWordRenewalFrontierFreshRootIdle
        ring root s hn hbank hs seed
    change (serW (seed.1.1.2.1 root)
      (seed.1.1.2.1 (ring.rightNeighbor root))).hard.hardAccept =
        false
    simp [serW, serializerStep, ProjW.lift, hidle]
  · exact bankWordRootNonrootHardAcceptFalse
      ring hn hbank root s hs seed.1.1 seed.1.2.1 e he

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Physical worker shape for the original W epoch. The BACK/SUM
phases have TWO possible nonfree sites: the cursor host and the
busy ROOT target. Thus "all non-host SI free" applies only to
PREFIX and READY. Consumer: repair.tex R10a W worker census. -/
def BankWordRenewalFrontierPhysicalShape {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) : Prop :=
  ∃ w : WWorkerTrail n, z.2.2.worker = some w ∧
    match w.phase with
    | .prefixRun =>
        w.target = root ∧
        w.index ≤ (compileAdvice (ceilLogTwo n)).t ∧
        w.index + 1 < n ∧
        w.host = L3.EWord.site ring root w.index ∧
        (z.2.1 w.host).si.kind = .PREFIX ∧
        (z.2.1 w.host).si.busy = false ∧
        (z.2.1 w.host).si.cur = .NONE ∧
        (z.2.1 w.host).si.j.val = w.index ∧
        ∀ i : Fin n, i ≠ w.host →
          freeSI (z.2.1 i).si = true
    | .backRun =>
        ∃ k : Nat,
          (compileAdvice (ceilLogTwo n)).t + 1 ≤ k ∧
          k < n ∧
          0 < w.index ∧
          w.index ≤ (compileAdvice (ceilLogTwo n)).t ∧
          w.target = L3.EWord.site ring root k ∧
          w.host = L3.EWord.site ring root
            (k - ((compileAdvice (ceilLogTwo n)).t - w.index)) ∧
          (z.2.1 w.host).si.cur = .BACK ∧
          (z.2.1 w.host).si.j.val = w.index ∧
          (z.2.1 w.target).si.kind = .ROOT ∧
          (z.2.1 w.target).si.busy = true ∧
          (if w.host = w.target
           then (z.2.1 w.host).si.kind = .ROOT
           else (z.2.1 w.host).si.kind = .OFF) ∧
          ∀ i : Fin n, i ≠ w.host → i ≠ w.target →
            freeSI (z.2.1 i).si = true
    | .sumRun =>
        ∃ k : Nat,
          (compileAdvice (ceilLogTwo n)).t + 1 ≤ k ∧
          k < n ∧
          w.index < (compileAdvice (ceilLogTwo n)).t ∧
          w.target = L3.EWord.site ring root k ∧
          w.host = L3.EWord.site ring root
            (k - (compileAdvice (ceilLogTwo n)).t + w.index) ∧
          (z.2.1 w.host).si.kind = .OFF ∧
          (z.2.1 w.host).si.cur = .SUM ∧
          (z.2.1 w.host).si.j.val = w.index ∧
          (z.2.1 w.target).si.kind = .ROOT ∧
          (z.2.1 w.target).si.busy = true ∧
          ∀ i : Fin n, i ≠ w.host → i ≠ w.target →
            freeSI (z.2.1 i).si = true
    | .readyRun =>
        ∃ k : Nat,
          (compileAdvice (ceilLogTwo n)).t + 1 ≤ k ∧
          k < n ∧
          w.host = L3.EWord.site ring root k ∧
          w.target = w.host ∧
          (z.2.1 w.host).si.kind = .ROOT ∧
          (z.2.1 w.host).si.busy = false ∧
          (z.2.1 w.host).si.cur = .NONE ∧
          ∀ i : Fin n, i ≠ w.host →
            freeSI (z.2.1 i).si = true

/-- The actual accepted BANK cut has the shape above. The
geometric inequality is explicit; it has not been derived here
from the BANK compiler guard. Consumer: prefix half of the
uninterrupted-worker induction in repair.tex R10a W. -/
theorem bankWordRenewalFrontierFreshPhysicalShape {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (hn : 5 ≤ n)
    (hgeom : (compileAdvice (ceilLogTwo n)).t + 2 ≤ n)
    (seed : BankWordRenewalFreshSeed ring root s) :
    BankWordRenewalFrontierPhysicalShape ring root seed.1.1 := by
  obtain ⟨w, hw, hp, hh, ht, hi⟩ :=
    bankWordRenewalFrontierFreshWorkerWitness ring root s seed
  have hphysical :=
    (bankWordRenewalFrontierFreshBankPrepared
      ring root s hbank seed).1
  have hfree :=
    bankWordRenewalFrontierFreshBankForeignFree
      ring root s hn hbank hs seed
  refine ⟨w, hw, ?_⟩
  rw [hp]
  change
    w.target = root ∧
    w.index ≤ (compileAdvice (ceilLogTwo n)).t ∧
    w.index + 1 < n ∧
    w.host = L3.EWord.site ring root w.index ∧
    (seed.1.1.2.1 w.host).si.kind = .PREFIX ∧
    (seed.1.1.2.1 w.host).si.busy = false ∧
    (seed.1.1.2.1 w.host).si.cur = .NONE ∧
    (seed.1.1.2.1 w.host).si.j.val = w.index ∧
    ∀ i : Fin n, i ≠ w.host →
      freeSI (seed.1.1.2.1 i).si = true
  refine ⟨ht, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hi]
    omega
  · rw [hi]
    omega
  · rw [hh, hi, L3.EWord.siteZero]
  · rw [hh, hphysical]
    rfl
  · rw [hh, hphysical]
    rfl
  · rw [hh, hphysical]
    rfl
  · rw [hh, hphysical, hi]
    rfl
  · intro i hne
    apply hfree i
    rw [hh] at hne
    exact hne

/-- The prefix's next clockwise service cannot encounter the
protected root before P3 when its physical offset is at most
the source width and there is room for the first target.
Consumer: exclusion of genuine-worker P0/P2 terminals. -/
theorem bankWordRenewalFrontierPrefixNoEarlyRoot {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (w : WWorkerTrail n)
    (hw : z.2.2.worker = some w)
    (hgeom : (compileAdvice (ceilLogTwo n)).t + 2 ≤ n)
    (hindex : w.index ≤ (compileAdvice (ceilLogTwo n)).t)
    (hhost : w.host = L3.EWord.site ring root w.index) :
    ring.rightNeighbor w.host ≠ root := by
  intro hroot
  have hnext :
      ring.rightNeighbor w.host =
        L3.EWord.site ring root (w.index + 1) := by
    rw [hhost]
    exact L3.EWord.siteSuccessor ring root w.index
  have hsame :
      L3.EWord.site ring root (w.index + 1) =
        L3.EWord.site ring root 0 := by
    rw [L3.EWord.siteZero]
    exact hnext.symm.trans hroot
  have hzero :=
    L3.EWord.validationSiteInjective ring root
      (w.index + 1) 0 (by omega) (by omega) hsame
  omega

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- R10a W R2: physical-to-ticket lineage at the nominated root.
The three independent guards respectively cover S0/REQUESTED,
the validating S1/S2R pending child, and the final B/DONE/F S6.
The root's probe is unrestricted; the first child's actual probe
is checked when the parent awaits an answer. This is deliberately
stronger than BankWordRootDoneOrigin, which proves only the
converse origin of tickets that already exist.
Consumer: root-edge hardAccept versus genuine S6. -/
def BankWordRenewalFrontierTicketLineage {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) : Prop :=
  ((z.2.1 root).ser.cert = .REQUESTED →
    ∃ request : WValidationTicket,
      wTicketAt .requested
        ((bankWordHardEpochLedger ring root z).validation root) =
          some request) ∧
  (((z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING ∧
      (z.2.1 root).ser.phase = .B ∧
      (z.2.1 root).ser.out = .WAIT ∧
      (z.2.1 (ring.rightNeighbor root)).ser.phase = .C ∧
      (z.2.1 (ring.rightNeighbor root)).ser.probe = .PENDING) →
    ∃ parent child : WValidationTicket,
      wTicketAt .waiting
        ((bankWordHardEpochLedger ring root z).validation root) =
          some parent ∧
      wTicketAt .pending
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor root)) = some child ∧
      parent.requestedAt = child.requestedAt ∧
      parent.startedAt = child.startedAt) ∧
  (((z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING ∧
      (z.2.1 root).ser.phase = .B ∧
      (z.2.1 root).ser.out = .DONE ∧
      (z.2.1 (ring.rightNeighbor root)).ser.phase = .F) →
    ∃ parent child : WValidationTicket,
      wTicketAt .done
        ((bankWordHardEpochLedger ring root z).validation root) =
          some parent ∧
      wTicketAt .returned
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor root)) = some child ∧
      parent.requestedAt = child.requestedAt ∧
      parent.startedAt = child.startedAt)

/-- At a genuinely accepted fresh BANK cut the physical root
is IDLE. Consequently none of the three lineage antecedents
has fired. This is the real post-S6 seed, not a manufactured
serializer configuration. Consumer: R2 lineage induction base. -/
theorem bankWordRenewalFrontierFreshTicketLineage {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (seed : BankWordRenewalFreshSeed ring root s) :
    BankWordRenewalFrontierTicketLineage ring root seed.1.1 := by
  have hidle := bankWordRenewalFrontierFreshRootIdle
    ring root s hn hbank hs seed
  unfold BankWordRenewalFrontierTicketLineage
  refine ⟨?_, ?_, ?_⟩
  · intro hrequested
    rw [hidle] at hrequested
    cases hrequested
  · intro hwaiting
    rw [hidle] at hwaiting
    cases hwaiting.1
  · intro hdone
    rw [hidle] at hdone
    cases hdone.1

/-- Actual S0 incoming-root service creates the REQUESTED root
and a matching .requested chronological ticket, including on
arbitrary inherited private serializer scratch.
Consumer: first obligation of R2 ticket-lineage propagation. -/
theorem bankWordRenewalFrontierIncomingRequestTicket {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hpred : ring.rightNeighbor e = root)
    (hidle : (z.2.1 root).ser.cert = .IDLE) :
    ((bankWordEpochNext ring root z e).2.1 root).ser.cert =
      .REQUESTED ∧
    wTicketAt .requested
      ((bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z e)).validation root) =
        some { requestedAt := z.2.2.clock + 1, startedAt := z.2.2.clock + 1, stage := .requested } := by
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 e) :=
    ((bankWordSerializerRootClassClosed
      ring hn hbank root).2 z.2.1 hclass e).2
  have hpost := clockPostIncoming ring root z.2.1 e
    (by omega : 2 ≤ n) hfixed hpred
  have hrow := serRootIncomingIdle
    (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
    hpost.1 hpost.2 (by simpa only [hpred] using hidle)
  have hphysical :
      ((bankWordEpochNext ring root z e).2.1 root).ser.cert =
        .REQUESTED := by
    change ((phiW ring z.2.1 e) root).ser.cert = .REQUESTED
    rw [← hpred]
    rw [phiW_ser_target ring z.2.1 e
      (clockNeighborDifferent ring (by omega : 2 ≤ n) e)]
    exact hrow.2
  have hticket := bankWordRootIncomingTicketExact
    ring root z e (by omega : 2 ≤ n) hfixed hpred
  have hrequested :
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z e)).validation root =
          some { requestedAt := z.2.2.clock + 1, startedAt := z.2.2.clock + 1, stage := .requested } := by
    simpa [hidle] using hticket
  refine ⟨hphysical, ?_⟩
  rw [hrequested]
  rfl

/-- The actual hard S1 is ticketed whenever the REQUESTED
portion of the proposed lineage holds. Its source creates
a waiting parent and a pending first-child ticket with the
same request/start stamps. Consumer: the R2 validating
S1-to-S2R lineage establishment, not an assumed S6 success. -/
theorem bankWordRenewalFrontierHardStartTicketPair {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hlineage : BankWordRenewalFrontierTicketLineage ring root z)
    (hrequested : (z.2.1 root).ser.cert = .REQUESTED)
    (hzero : (z.2.1 root).siLease.val = 0) :
    ∃ request : WValidationTicket,
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z root)).validation root =
          some { requestedAt := request.requestedAt, startedAt := z.2.2.clock + 1, stage := .waiting } ∧
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z root)).validation
          (ring.rightNeighbor root) =
          some { requestedAt := request.requestedAt, startedAt := z.2.2.clock + 1, stage := .pending } ∧
      (bankWordEpochSelectedReceipt ring z root).serializer.hard.hardS1 =
        true := by
  obtain ⟨request, ht⟩ := hlineage.1 hrequested
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 root) :=
    ((bankWordSerializerRootClassClosed
      ring hn hbank root).2 z.2.1 hclass root).2
  have hpost := clockPostOutgoing ring root z.2.1 root
    (by omega : 2 ≤ n) hfixed rfl
  have hwrite := bankWordTicketedHardStartWrites
    (z.2.2.clock + 1)
    (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
    ((bankWordHardEpochLedger ring root z).validation root)
    ((bankWordHardEpochLedger ring root z).validation
      (ring.rightNeighbor root))
    request hpost.1 hpost.2 hrequested hzero ht
  have hsource :
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z root)).validation root =
          some { requestedAt := request.requestedAt, startedAt := z.2.2.clock + 1, stage := .waiting } := by
    rw [bankWordRootOutgoingTicketExact ring root z]
    rw [hwrite]
  have hneq : ring.rightNeighbor root ≠ root :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) root
  have htargetEq :
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z root)).validation
          (ring.rightNeighbor root) =
      (wValidationPair (z.2.2.clock + 1)
        (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
        ((bankWordHardEpochLedger ring root z).validation root)
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor root))).2 := by
    rw [bankWordHardEpochLedgerNext]
    simp [bankWordHardEpochStep, bankWordEpochSelectedReceipt, hneq]
  have htarget :
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z root)).validation
          (ring.rightNeighbor root) =
          some { requestedAt := request.requestedAt, startedAt := z.2.2.clock + 1, stage := .pending } := by
    rw [htargetEq, hwrite]
  have hhard := (bankWordHardEpochZeroLeaseHardStart
    (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
    hpost.1 hpost.2 hrequested hzero).2.1
  exact ⟨request, hsource, htarget, hhard⟩

/-- A letter touching neither the root nor its first successor
frames the two serializer records and both chronological tickets.
Thus all three physical/ticket lineage clauses survive, with
no need to assume a clean epoch for this remote subcase.
Consumer: S2N/S3/S4 remote branches of the R2 row census. -/
theorem bankWordRenewalFrontierTicketLineageRemoteStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankWordEpochState n)
    (he : e ≠ root)
    (hj : ring.rightNeighbor e ≠ root)
    (hechild : e ≠ ring.rightNeighbor root)
    (hjchild : ring.rightNeighbor e ≠ ring.rightNeighbor root)
    (hlineage : BankWordRenewalFrontierTicketLineage ring root z) :
    BankWordRenewalFrontierTicketLineage ring root
      (bankWordEpochNext ring root z e) := by
  have hroot := bankWordHardEpochRootRemoteFrame
    ring root z e he.symm hj.symm
  have hchild :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor root)).ser =
      (z.2.1 (ring.rightNeighbor root)).ser := by
    change ((phiW ring z.2.1 e)
      (ring.rightNeighbor root)).ser =
        (z.2.1 (ring.rightNeighbor root)).ser
    exact phiW_ser_remote ring z.2.1 e
      (ring.rightNeighbor root) hechild.symm hjchild.symm
  have hrootTicket := bankWordRootTicketRemoteFrame
    ring root z e he.symm hj.symm
  have hchildNE : ring.rightNeighbor root ≠ e := hechild.symm
  have hchildOther :
      ring.rightNeighbor root ≠ ring.rightNeighbor e := hjchild.symm
  have hchildTicket :
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z e)).validation
          (ring.rightNeighbor root) =
      (bankWordHardEpochLedger ring root z).validation
        (ring.rightNeighbor root) := by
    rw [bankWordHardEpochLedgerNext]
    simp [bankWordHardEpochStep, bankWordEpochSelectedReceipt,
      hchildNE, hchildOther]
  obtain ⟨hrequested, hpending, hdone⟩ := hlineage
  unfold BankWordRenewalFrontierTicketLineage
  refine ⟨?_, ?_, ?_⟩
  · intro hnew
    have hold : (z.2.1 root).ser.cert = .REQUESTED := by
      simpa only [hroot] using hnew
    obtain ⟨request, ht⟩ := hrequested hold
    refine ⟨request, ?_⟩
    simpa only [hrootTicket] using ht
  · intro hnew
    have hold :
        (z.2.1 root).ser.cert = .RUNNING ∧
        (z.2.1 root).ser.wphase = .VALIDATING ∧
        (z.2.1 root).ser.phase = .B ∧
        (z.2.1 root).ser.out = .WAIT ∧
        (z.2.1 (ring.rightNeighbor root)).ser.phase = .C ∧
        (z.2.1 (ring.rightNeighbor root)).ser.probe = .PENDING := by
      simpa only [hroot, hchild] using hnew
    obtain ⟨parent, child, hp, hq, hr, hs⟩ := hpending hold
    refine ⟨parent, child, ?_, ?_, hr, hs⟩
    · simpa only [hrootTicket] using hp
    · simpa only [hchildTicket] using hq
  · intro hnew
    have hold :
        (z.2.1 root).ser.cert = .RUNNING ∧
        (z.2.1 root).ser.wphase = .VALIDATING ∧
        (z.2.1 root).ser.phase = .B ∧
        (z.2.1 root).ser.out = .DONE ∧
        (z.2.1 (ring.rightNeighbor root)).ser.phase = .F := by
      simpa only [hroot, hchild] using hnew
    obtain ⟨parent, child, hp, hq, hr, hs⟩ := hdone hold
    refine ⟨parent, child, ?_, ?_, hr, hs⟩
    · simpa only [hrootTicket] using hp
    · simpa only [hchildTicket] using hq

/-- R10a W R2 discharge from a full physical-to-ticket
lineage: a represented, genuinely reachable physical root
B/DONE/F accepting edge has matching done/returned tickets.
The actual wGenuineAcceptance flag is therefore true; no
assumption about a forged local S6 is substituted.
Consumer: the root outgoing case of CleanInvariant preservation. -/
theorem bankWordRenewalFrontierHardAcceptOfTicketLineage {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hlineage : BankWordRenewalFrontierTicketLineage ring root z)
    (hhard :
      (bankWordEpochSelectedReceipt ring z root).serializer.hard.hardAccept =
        true) :
    bankWordHardEpochGenuine ring root
      (bankWordEpochSelectedReceipt ring z root)
      (bankWordHardEpochLedger ring root z) = true := by
  have hflags :
      ((((((postW (z.2.1 root)
          (z.2.1 (ring.rightNeighbor root))).eX.l &&
        ((z.2.1 root).ser.cert == .RUNNING)) &&
        ((z.2.1 root).ser.wphase == .VALIDATING)) &&
        ((z.2.1 root).ser.phase == .B)) &&
        ((z.2.1 root).ser.out == .DONE)) &&
        ((z.2.1 (ring.rightNeighbor root)).ser.phase == .F)) =
          true := hhard
  simp only [Bool.and_eq_true] at hflags
  obtain ⟨⟨⟨⟨⟨_, hcertFlag⟩, hvalidFlag⟩,
    hphaseFlag⟩, houtFlag⟩, htailFlag⟩ := hflags
  have hcert : (z.2.1 root).ser.cert = .RUNNING := by
    cases hc : (z.2.1 root).ser.cert <;>
      simp [hc] at hcertFlag ⊢
  have hvalid : (z.2.1 root).ser.wphase = .VALIDATING := by
    cases hv : (z.2.1 root).ser.wphase <;>
      simp [hv] at hvalidFlag ⊢
  have hphase : (z.2.1 root).ser.phase = .B := by
    cases hp : (z.2.1 root).ser.phase <;>
      simp [hp] at hphaseFlag ⊢
  have hout : (z.2.1 root).ser.out = .DONE := by
    cases ho : (z.2.1 root).ser.out <;>
      simp [ho] at houtFlag ⊢
  have htail :
      (z.2.1 (ring.rightNeighbor root)).ser.phase = .F := by
    cases hf : (z.2.1 (ring.rightNeighbor root)).ser.phase <;>
      simp [hf] at htailFlag ⊢
  obtain ⟨parent, child, hp, hq, hrequested, hstarted⟩ :=
    hlineage.2.2 ⟨hcert, hvalid, hphase, hout, htail⟩
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 root) :=
    ((bankWordSerializerRootClassClosed
      ring hn hbank root).2 z.2.1 hclass root).2
  have hpost := clockPostOutgoing ring root z.2.1 root
    (by omega : 2 ≤ n) hfixed rfl
  have hrow := bankWordRootHardAcceptRowSsix
    (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
    hpost.1 hpost.2 hhard
  change (wGenuineAcceptance root root
    (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
    ((bankWordHardEpochLedger ring root z).validation root)
    ((bankWordHardEpochLedger ring root z).validation
      (ring.rightNeighbor root))).isSome = true
  unfold wGenuineAcceptance
  rw [if_pos ⟨rfl, hrow, hhard⟩]
  rw [hp, hq]
  simp [wJoinTickets, hrequested, hstarted]

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Production BANK compilation has space for the whole
prefix and its first follower target. This discharges the
geometric premise of the R10a W worker shape. -/
theorem bankWordRenewalFrontierBankRoom {n : Nat}
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    (compileAdvice (ceilLogTwo n)).t + 2 ≤ n := by
  have hq : 80 ≤ ceilLogTwo n :=
    bankWordHardEpochBankAdviceLower hbank
  have hn : 2 ≤ n := by
    by_cases hsmall : n ≤ 1
    · have hz : ceilLogTwo n = 0 := by
        unfold ceilLogTwo
        rw [if_pos hsmall]
      omega
    · omega
  have hgrowth : ∀ k : Nat, k + 4 ≤ 2 ^ (k + 2) := by
    intro k
    induction k with
    | zero =>
        change (4 : Nat) ≤ 4
        exact Nat.le_refl 4
    | succ k ih =>
        have hlinear : (k + 1) + 4 ≤ 2 * (k + 4) := by omega
        have hscaled : 2 * (k + 4) ≤
            2 * (2 ^ (k + 2)) := Nat.mul_le_mul_left 2 ih
        have hpower : (2 : Nat) ^ ((k + 1) + 2) =
            2 ^ (k + 2) * 2 := by
          have heq : (k + 1) + 2 = (k + 2) + 1 := by omega
          rw [heq]
          exact Nat.pow_succ 2 (k + 2)
        calc
          (k + 1) + 4 ≤ 2 * (k + 4) := hlinear
          _ ≤ 2 * (2 ^ (k + 2)) := hscaled
          _ = 2 ^ ((k + 1) + 2) := by
            calc
              2 * 2 ^ (k + 2) = 2 ^ (k + 2) * 2 :=
                Nat.mul_comm _ _
              _ = 2 ^ ((k + 1) + 2) := hpower.symm
  have hlower : 2 ^ (ceilLogTwo n - 1) < n :=
    (ceilLogTwo_spec n hn).1
  have hextra := hgrowth (ceilLogTwo n - 3)
  have hleft : (ceilLogTwo n - 3) + 4 =
      ceilLogTwo n + 1 := by omega
  have hright : (ceilLogTwo n - 3) + 2 =
      ceilLogTwo n - 1 := by omega
  rw [hleft, hright] at hextra
  have hroom : ceilLogTwo n + 2 ≤ n := by omega
  have hwidth : (compileAdvice (ceilLogTwo n)).t =
      ceilLogTwo (ceilLogTwo n) :=
    bankWordHardEpochBankSourceWidth hbank
  have hsmallwidth := ceilLogTwo_le_self (ceilLogTwo n)
  rw [hwidth]
  omega

/-- The genuine fresh BANK acceptance has the original
physical PREFIX host/index/free-site shape, without an
assumed ring-size inequality. Consumer: R10a W induction base. -/
theorem bankWordRenewalFrontierFreshShapeOnBank {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (seed : BankWordRenewalFreshSeed ring root s) :
    BankWordRenewalFrontierPhysicalShape ring root seed.1.1 := by
  have hq : 80 ≤ ceilLogTwo n :=
    bankWordHardEpochBankAdviceLower hbank
  have hpsi : 6 ≤ ceilLogTwo (ceilLogTwo n) :=
    ceilLogTwo_ge_six (ceilLogTwo n) (by omega : 33 ≤ ceilLogTwo n)
  have hroom := bankWordRenewalFrontierBankRoom hbank
  have hwidth := bankWordHardEpochBankSourceWidth hbank
  have hn : 5 ≤ n := by
    rw [hwidth] at hroom
    omega
  exact bankWordRenewalFrontierFreshPhysicalShape
    ring root s hbank hs hn
    (bankWordRenewalFrontierBankRoom hbank) seed

/-- For a tracked PREFIX worker satisfying the physical
shape, the next clockwise site is not the root. This is the
geometric branch exclusion needed for the P0/P2 census. -/
theorem bankWordRenewalFrontierShapePrefixNoRoot {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hshape : BankWordRenewalFrontierPhysicalShape ring root z)
    (w : WWorkerTrail n)
    (hw : z.2.2.worker = some w)
    (hphase : w.phase = .prefixRun) :
    ring.rightNeighbor w.host ≠ root := by
  obtain ⟨v, hv, hphysical⟩ := hshape
  have heq : v = w := Option.some.inj (hv.symm.trans hw)
  subst v
  rw [hphase] at hphysical
  exact bankWordRenewalFrontierPrefixNoEarlyRoot
    ring root z w hw (bankWordRenewalFrontierBankRoom hbank)
    hphysical.2.1 hphysical.2.2.2.1

/-- The source serializer's two physical hard scrub guards
are false at a non-VALIDATING selected pair with no hard S1.
Consumer: the I1 erasure branch of WOriginGhost; the remaining
global task is to establish the no-VALIDATING history invariant
after genuine S6, not to assume it from SI shape alone. -/
theorem bankWordRenewalFrontierNonvalidatingGuardsQuiet {c : Compiled}
    (x y : ProjW c)
    (hx : x.ser.wphase ≠ .VALIDATING)
    (hy : y.ser.wphase ≠ .VALIDATING)
    (hno : (serW x y).hard.hardS1 = false) :
    (serW x y).hard.hardLeft = false ∧
    (serW x y).hard.hardRight = false := by
  have hxb : (x.ser.wphase == .VALIDATING) = false := by
    simp [hx]
  have hyb : (y.ser.wphase == .VALIDATING) = false := by
    simp [hy]
  have hchallenge :
      (serW x y).hard.hardChallenge = false := by
    simp [serW, serializerStep, ProjW.lift, hxb]
  have hleft :
      (serW x y).hard.hardLeft =
        ((serW x y).hard.hardS1 ||
          (x.ser.wphase == .VALIDATING)) := rfl
  have hright :
      (serW x y).hard.hardRight =
        ((serW x y).hard.hardS1 ||
          (serW x y).hard.hardChallenge ||
          (y.ser.wphase == .VALIDATING)) := rfl
  constructor
  · rw [hleft, hno, hxb]
    rfl
  · rw [hright, hno, hchallenge, hyb]
    rfl

/-- Literal PREFIX row P1 under a clean selected follower pair:
a nonbusy PREFIX host with index below t and a free successor
advances, rather than selecting any terminal row.
Consumer: clockwise PREFIX case of the R10a W shape step. -/
theorem bankWordRenewalFrontierPrefixAdvanceRow {c : Compiled}
    (x y : ProjW c)
    (ha : (serW x y).hard.hardAccept = false)
    (hl : (serW x y).hard.hardLeft = false)
    (hr : (serW x y).hard.hardRight = false)
    (hk : x.si.kind = .PREFIX)
    (hb : x.si.busy = false)
    (hc : x.si.cur = .NONE)
    (hj : x.si.j.val < c.t)
    (hy : (postW x y).eY.l = false)
    (hf : freeSI y.si = true) :
    (workerW x y).row = "P1" := by
  simp [workerW, siStep, ProjW.lift,
    ha, hl, hr, hk, hb, hc, hj, hy, hf]

/-- At actual PREFIX index t with a free follower successor,
the row is P3, not P2: the busy BACK target is installed.
Consumer: PREFIX-to-BACK handoff in the R10a W shape step. -/
theorem bankWordRenewalFrontierPrefixHandoffRow {c : Compiled}
    (x y : ProjW c)
    (ha : (serW x y).hard.hardAccept = false)
    (hl : (serW x y).hard.hardLeft = false)
    (hr : (serW x y).hard.hardRight = false)
    (hk : x.si.kind = .PREFIX)
    (hb : x.si.busy = false)
    (hc : x.si.cur = .NONE)
    (hj : x.si.j.val = c.t)
    (hy : (postW x y).eY.l = false)
    (hf : freeSI y.si = true) :
    (workerW x y).row = "P3" := by
  simp [workerW, siStep, ProjW.lift,
    ha, hl, hr, hk, hb, hc, hj, hy, hf]

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open Classical
set_option autoImplicit false
set_option Elab.async false

/-- A visited EWord site is covered by one observed validation
stage, with the same request/start stamps as its wave.
Consumer: the R10a W S2N/S3/S5/S2R wave ledger. -/
def BankWordRenewalFrontierWaveSiteTicket {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n)
    (requestedAt startedAt : Nat)
    (i : Fin n) (stage : WValidationStage) : Prop :=
  ∃ ticket : WValidationTicket,
    wTicketAt stage
      ((bankWordHardEpochLedger ring root z).validation
        (L3.EWord.site ring root i.val)) = some ticket ∧
    ticket.requestedAt = requestedAt ∧
    ticket.startedAt = startedAt

/-- The actual W wave-lineage strengthening. Only EWord's
scrubbed prefix is constrained, not the arbitrary unvisited
physical suffix. The B/NEW, B/WAIT, B/DONE and C/PENDING,
C/INTERNAL_OK, C/LEAF_OK and returning-F subrows carry,
respectively, broadcaster, waiting, done, pending,
observedInternal, observedLeaf and returned stamps.
Consumer: R2 physical hardAccept-to-genuine converse. -/
def BankWordRenewalFrontierWaveLineage {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) : Prop :=
  BankWordRenewalFrontierTicketLineage ring root z ∧
  (((z.2.1 root).ser.cert = .RUNNING ∧
    (z.2.1 root).ser.wphase = .VALIDATING) →
    ∃ (g : L3.EWord.ValidationGhost) (req stamp : Nat),
      L3.EWord.ValidationShape ring root z.2.1 g ∧
      ∀ k : Fin n, k.val < g.scrub →
        (((z.2.1 (L3.EWord.site ring root k.val)).ser.phase = .B ∧
           (z.2.1 (L3.EWord.site ring root k.val)).ser.wphase =
             .VALIDATING) →
          BankWordRenewalFrontierWaveSiteTicket ring root z
            req stamp k
            (if (z.2.1 (L3.EWord.site ring root k.val)).ser.out =
               .NEW then .broadcaster
             else if (z.2.1 (L3.EWord.site ring root k.val)).ser.out =
               .WAIT then .waiting else .done)) ∧
        (((z.2.1 (L3.EWord.site ring root k.val)).ser.phase = .C ∧
           (z.2.1 (L3.EWord.site ring root k.val)).ser.probe =
             .PENDING ∧
           (z.2.1 (L3.EWord.site ring root k.val)).ser.wphase =
             .VALIDATING) →
          BankWordRenewalFrontierWaveSiteTicket ring root z
            req stamp k .pending) ∧
        (((z.2.1 (L3.EWord.site ring root k.val)).ser.phase = .C ∧
           (z.2.1 (L3.EWord.site ring root k.val)).ser.probe =
             .INTERNAL_OK ∧
           (z.2.1 (L3.EWord.site ring root k.val)).ser.wphase =
             .VALIDATING) →
          BankWordRenewalFrontierWaveSiteTicket ring root z
            req stamp k .observedInternal) ∧
        (((z.2.1 (L3.EWord.site ring root k.val)).ser.phase = .C ∧
           (z.2.1 (L3.EWord.site ring root k.val)).ser.probe =
             .LEAF_OK) →
          BankWordRenewalFrontierWaveSiteTicket ring root z
            req stamp k .observedLeaf) ∧
        (((z.2.1 (L3.EWord.site ring root k.val)).ser.phase = .F ∧
           g.stage = .returning ∧ g.pivot ≤ k.val) →
          BankWordRenewalFrontierWaveSiteTicket ring root z
            req stamp k .returned))

/-- Projection to the already proved root/child converse.
Consumer: the root hardAccept clause of R10a W. -/
theorem bankWordRenewalFrontierWaveImpliesRootLineage {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n)
    (h : BankWordRenewalFrontierWaveLineage ring root z) :
    BankWordRenewalFrontierTicketLineage ring root z :=
  h.1

/-- The genuine hard-S6 fresh cut has an IDLE root and no
active validating wave. The strengthened implication and the
already established root/child ticket lineage both hold.
Consumer: wave induction base on the original epoch runner. -/
theorem bankWordRenewalFrontierFreshWaveLineage {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (seed : BankWordRenewalFreshSeed ring root s) :
    BankWordRenewalFrontierWaveLineage ring root seed.1.1 := by
  have hroot := bankWordRenewalFrontierFreshTicketLineage
    ring root s hn hbank hs seed
  have hidle := bankWordRenewalFrontierFreshRootIdle
    ring root s hn hbank hs seed
  refine ⟨hroot, ?_⟩
  intro hactive
  rw [hidle] at hactive
  cases hactive.1

/-- S2N B/NEW challenge issues waiting/pending descendants of
the actual old parent ticket. No synthetic request stamp is
introduced. Consumer: forward wave challenge in R10a W. -/
theorem bankWordRenewalFrontierWaveChallengeTickets {c : Compiled}
    (stamp : Nat) (x y : ProjW c)
    (gx gy : Option WValidationTicket) (parent : WValidationTicket)
    (hrow : (serW x y).row = "S2N")
    (hnew : x.ser.out = .NEW)
    (hchild : y.ser.phase = .C)
    (hp : wParentTicket gx = some parent) :
    wValidationPair stamp x y gx gy =
      (some { parent with stage := .waiting },
       some { parent with stage := .pending }) := by
  simp [wValidationPair, hrow, hnew, hchild,
    wChallengeTickets, wTicketStage, hp]

/-- S3 C/PENDING -> C/INTERNAL_OK retags the real old pending
ticket to observedInternal with unchanged stamps.
Consumer: internal wave observation row in R10a W. -/
theorem bankWordRenewalFrontierWaveInternalObservation {c : Compiled}
    (stamp : Nat) (x y : ProjW c)
    (gx gy : Option WValidationTicket) (parent : WValidationTicket)
    (hrow : (serW x y).row = "S3")
    (hp : x.ser.probe = .PENDING)
    (hc : y.ser.phase = .C)
    (ht : wTicketAt .pending gx = some parent) :
    (wValidationPair stamp x y gx gy).1 =
      some { parent with stage := .observedInternal } := by
  simp [wValidationPair, hrow, hp, hc, wTicketStage, ht]

/-- The root-seam S5 leaf observation comes from the OLD
eligible root parent and OLD pending child with two equal
timestamps. Consumer: terminal leaf wave in R10a W. -/
theorem bankWordRenewalFrontierWaveLeafObservation {c : Compiled}
    (stamp : Nat) (x y : ProjW c)
    (gx gy : Option WValidationTicket)
    (parent child : WValidationTicket)
    (hrow : (serW x y).row = "S5")
    (hc : x.ser.phase = .C)
    (hp : x.ser.probe = .PENDING)
    (htParent : wParentTicket gy = some parent)
    (htChild : wTicketAt .pending gx = some child)
    (hr : parent.requestedAt = child.requestedAt)
    (hs : parent.startedAt = child.startedAt) :
    (wValidationPair stamp x y gx gy).1 =
      some { parent with stage := .observedLeaf } := by
  simp [wValidationPair, hrow, hc, hp, htParent, htChild,
    wJoinTickets, hr, hs, wTicketStage]

/-- S2R B/WAIT + C/INTERNAL_OK joins the waiting and observed
tickets into a done parent and broadcaster child. Both stamp
equalities are used by the literal wJoinTickets guard.
Consumer: forward internal admission in R10a W. -/
theorem bankWordRenewalFrontierWaveInternalAdmission {c : Compiled}
    (stamp : Nat) (x y : ProjW c)
    (gx gy : Option WValidationTicket)
    (parent child : WValidationTicket)
    (hrow : (serW x y).row = "S2R")
    (hw : x.ser.out = .WAIT)
    (hc : y.ser.phase = .C)
    (hi : y.ser.probe = .INTERNAL_OK)
    (htParent : wTicketAt .waiting gx = some parent)
    (htChild : wTicketAt .observedInternal gy = some child)
    (hr : parent.requestedAt = child.requestedAt)
    (hs : parent.startedAt = child.startedAt) :
    wValidationPair stamp x y gx gy =
      (some { parent with stage := .done },
       some { parent with stage := .broadcaster }) := by
  simp [wValidationPair, hrow, hw, hc, hi, wAdmitTickets,
    htParent, htChild, wJoinTickets, hr, hs, wTicketStage]

/-- S2R B/WAIT + C/LEAF_OK joins waiting and observedLeaf,
yielding done parent and returned child with equal stamps.
Consumer: turn from forward to return wave in R10a W. -/
theorem bankWordRenewalFrontierWaveLeafAdmission {c : Compiled}
    (stamp : Nat) (x y : ProjW c)
    (gx gy : Option WValidationTicket)
    (parent child : WValidationTicket)
    (hrow : (serW x y).row = "S2R")
    (hw : x.ser.out = .WAIT)
    (hc : y.ser.phase = .C)
    (hl : y.ser.probe = .LEAF_OK)
    (htParent : wTicketAt .waiting gx = some parent)
    (htChild : wTicketAt .observedLeaf gy = some child)
    (hr : parent.requestedAt = child.requestedAt)
    (hs : parent.startedAt = child.startedAt) :
    wValidationPair stamp x y gx gy =
      (some { parent with stage := .done },
       some { parent with stage := .returned }) := by
  simp [wValidationPair, hrow, hw, hc, hl, wAdmitTickets,
    htParent, htChild, wJoinTickets, hr, hs, wTicketStage]

/-- S2N B/DONE -> F returns only with an old joined
done/returned ticket, not merely a physical F responder.
Consumer: validation return sweep in R10a W. -/
theorem bankWordRenewalFrontierWaveReturnAdmission {c : Compiled}
    (stamp : Nat) (x y : ProjW c)
    (gx gy : Option WValidationTicket)
    (parent child : WValidationTicket)
    (hrow : (serW x y).row = "S2N")
    (hd : x.ser.out = .DONE)
    (hf : y.ser.phase = .F)
    (htParent : wTicketAt .done gx = some parent)
    (htChild : wTicketAt .returned gy = some child)
    (hr : parent.requestedAt = child.requestedAt)
    (hs : parent.startedAt = child.startedAt) :
    (wValidationPair stamp x y gx gy).1 =
      some { parent with stage := .returned } := by
  simp [wValidationPair, hrow, hd, hf, htParent, htChild,
    wJoinTickets, hr, hs, wTicketStage]

/-- Genuine root S2R internal admission applies to the real
selected W edge: its chronological ledger writes both
done/broadcaster tickets, not only an abstract pair.
Consumer: rooted S2R step of the R10a W wave induction. -/
theorem bankWordRenewalFrontierRootInternalAdmissionLedger {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (hn : 2 ≤ n)
    (parent child : WValidationTicket)
    (hrow :
      (bankWordEpochSelectedReceipt ring z root).serializer.row =
        "S2R")
    (hw : (z.2.1 root).ser.out = .WAIT)
    (hc : (z.2.1 (ring.rightNeighbor root)).ser.phase = .C)
    (hi : (z.2.1 (ring.rightNeighbor root)).ser.probe =
      .INTERNAL_OK)
    (htParent : wTicketAt .waiting
      ((bankWordHardEpochLedger ring root z).validation root) =
        some parent)
    (htChild : wTicketAt .observedInternal
      ((bankWordHardEpochLedger ring root z).validation
        (ring.rightNeighbor root)) = some child)
    (hr : parent.requestedAt = child.requestedAt)
    (hs : parent.startedAt = child.startedAt) :
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z root)).validation root =
        some { parent with stage := .done } ∧
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z root)).validation
        (ring.rightNeighbor root) =
          some { parent with stage := .broadcaster } := by
  have hpair :
      wValidationPair (z.2.2.clock + 1)
        (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
        ((bankWordHardEpochLedger ring root z).validation root)
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor root)) =
        (some { parent with stage := .done },
         some { parent with stage := .broadcaster }) :=
    bankWordRenewalFrontierWaveInternalAdmission
      (z.2.2.clock + 1)
      (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
      ((bankWordHardEpochLedger ring root z).validation root)
      ((bankWordHardEpochLedger ring root z).validation
        (ring.rightNeighbor root))
      parent child hrow hw hc hi htParent htChild hr hs
  have hneq : ring.rightNeighbor root ≠ root :=
    clockNeighborDifferent ring hn root
  constructor
  · rw [bankWordRootOutgoingTicketExact ring root z, hpair]
  · have htarget :
        (bankWordHardEpochLedger ring root
          (bankWordEpochNext ring root z root)).validation
            (ring.rightNeighbor root) =
        (wValidationPair (z.2.2.clock + 1)
          (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
          ((bankWordHardEpochLedger ring root z).validation root)
          ((bankWordHardEpochLedger ring root z).validation
            (ring.rightNeighbor root))).2 := by
      rw [bankWordHardEpochLedgerNext]
      simp [bankWordHardEpochStep, bankWordEpochSelectedReceipt, hneq]
    rw [htarget, hpair]

/-- Conditional R2 discharge: the new visited-site lineage
implies the old root/child lineage and thus a physical root
hardAccept has matching genuine validation stamps.
Consumer: root hard-accept branch of CleanInvariant preservation. -/
theorem bankWordRenewalFrontierWaveHardAcceptGenuine {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hwave : BankWordRenewalFrontierWaveLineage ring root z)
    (hhard :
      (bankWordEpochSelectedReceipt ring z root).serializer.hard.hardAccept =
        true) :
    bankWordHardEpochGenuine ring root
      (bankWordEpochSelectedReceipt ring z root)
      (bankWordHardEpochLedger ring root z) = true := by
  exact bankWordRenewalFrontierHardAcceptOfTicketLineage
    ring root s hn hbank hs z hz
    (bankWordRenewalFrontierWaveImpliesRootLineage
      ring root z hwave) hhard

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

/-! These are local physical
facts for the R10a W-stage transport; no whole-word preservation
or retry-success claim is made here. -/

/-- A requested root with a positive OLD lease executes the soft S1
serializer row.  Its new parent and child are CURRENT, not
VALIDATING.  Consumer: the serializer half of the worker epoch
no-hard-S1 induction (soft-lap case). -/
theorem bankWordRenewalFrontierSoftSOneDoesNotValidate
    {c : Compiled} (x y : ProjW c)
    (hx : (postW x y).eX.l = true)
    (hy : (postW x y).eY.l = false)
    (hrequested : x.ser.cert = .REQUESTED)
    (hpositive : 0 < x.siLease.val) :
    (serW x y).row = "S1" ∧
    (serW x y).hard.hardS1 = false ∧
    (serW x y).x.wphase = .CURRENT ∧
    (serW x y).y.wphase = .CURRENT := by
  have hne : x.siLease.val ≠ 0 := Nat.ne_of_gt hpositive
  simp [serW, serializerStep, ProjW.lift, serTbStar,
    hx, hy, hrequested, hne]

/-- At the returned validation frontier, a physical F child
immediately clockwise from the root forces the return pivot to
be the first follower.  Consumer: root S6 exit of EWord's
ReturnShape, before discarding validating phases. -/
theorem bankWordRenewalFrontierReturnChildForcesPivot
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (g : L3.EWord.ValidationGhost)
    (hr : L3.EWord.ReturnShape ring root p g)
    (hchild :
      (p (ring.rightNeighbor root)).ser.phase = .F) :
    g.pivot = 1 := by
  by_cases hp : g.pivot = 1
  · exact hp
  · have hlt : 1 < g.pivot := by
      have hpos := hr.pivotPositive
      omega
    have hdone := hr.completed
      (⟨1, (show 1 < n by have := hr.pivotBound; omega)⟩ : Fin n) hlt
    have hb :
        (p (ring.rightNeighbor root)).ser.phase = .B := by
      simpa only [L3.EWord.siteOne] using hdone.1
    rw [hchild] at hb
    cases hb

/-- With pivot at the first follower, the RETURN phase has
no VALIDATING phase at any physical nonroot.  The proof uses
the actual returned suffix, not merely freeSI or canonical
initial scratch. Consumer: fresh-S6 no-VALIDATING cut. -/
theorem bankWordRenewalFrontierReturnedNonrootNonvalidating
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (p : Fin n → ProjW c) (g : L3.EWord.ValidationGhost)
    (hr : L3.EWord.ReturnShape ring root p g)
    (hpivot : g.pivot = 1)
    (i : Fin n) (hi : i ≠ root) :
    (p i).ser.wphase ≠ .VALIDATING := by
  have hpositive : 0 < PPL.cyclicOffset ring root i := by
    by_cases hz : PPL.cyclicOffset ring root i = 0
    · have hrep :=
        L3.EWord.validationOffsetRepresentative ring root i
      rw [hz, L3.EWord.siteZero] at hrep
      exact False.elim (hi hrep.symm)
    · omega
  by_cases hone : PPL.cyclicOffset ring root i = 1
  · have hfirst := hr.leftmostWphase
    rw [hpivot, L3.EWord.siteOne] at hfirst
    have hrep :=
      L3.EWord.validationOffsetRepresentative ring root i
    rw [hone, L3.EWord.siteOne] at hrep
    rw [← hrep, hfirst]
    split <;> decide
  · have hgt : 1 < PPL.cyclicOffset ring root i := by
      omega
    have htail := hr.suffix
      (⟨PPL.cyclicOffset ring root i,
        L3.EWord.validationOffsetBound ring root i⟩ : Fin n)
      (by rw [hpivot]; exact hgt)
    rw [L3.EWord.validationOffsetRepresentative ring root i] at htail
    rcases htail with hf | hc
    · rw [hf.2]
      split <;> decide
    · rw [hc.2]
      decide

/-- An actual matched A0 is the worker's nominated service
and writes a completion receipt in the original WOriginGhost.
This is a one-edge necessary-hit fact, not the H-letter
counting theorem. Consumer: first-H worker nomination tally. -/
theorem bankWordRenewalFrontierAZeroNominationMatchesReceipt
    {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s)
    (e : Fin n) (w : WWorkerTrail n)
    (hw : z.1.2.2.worker = some w)
    (hphase : w.phase = .readyRun)
    (hhost : w.host = e)
    (hroot : ring.rightNeighbor e = root)
    (hrow :
      (bankWordEpochSelectedReceipt ring z.1 e).worker.row = "A0")
    (hno :
      (bankWordEpochSelectedReceipt ring z.1 e).serializer.hard.hardS1 =
        false) :
    bankWordRenewalFreshWorkerNomination ring root s z = e ∧
    BankWordRenewalCompleted
      (bankWordRenewalNext ring root s z e).1 := by
  have hcoh := bankWordRenewalFrontierLedgerGhostCoherence
    ring root s z.1 z.2.1
  have hledger :
      (bankWordHardEpochLedger ring root z.1).worker = some w := by
    rw [hcoh.2]
    exact hw
  constructor
  · simp [bankWordRenewalFreshWorkerNomination, hledger, hphase, hhost]
  · change BankWordRenewalCompleted
        (bankWordEpochNext ring root z.1 e)
    exact bankWordRenewalFrontierTrackedAZeroCompletes
      ring root z.1 e w hw hrow hno hphase hhost hroot

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open Classical
set_option autoImplicit false
set_option Elab.async false

/-!
R10a W: exact NONROOT / NON-INCOMING serializer row table.

The represented WFixedRoot class and the POST-E owner flags
give (eX.l,eY.l)=(false,false).  Therefore, rather than the
S0/S1/S2R/S5/S6/SR roots mentioned in the broad census, the
literal internal serializerStep can select only:

S2N (source B):
  * y=C, x.out=WAIT, y.probe=PENDING: tickets (gx,gy) frame;
  * y=C, x.out=WAIT, y.probe=INTERNAL_OK:
    waiting+observedInternal of equal request/start stamps join
    to (done,broadcaster); FORWARD pivot advances;
  * y=C, x.out=WAIT, y.probe=LEAF_OK:
    waiting+observedLeaf join to (done,returned); RETURN begins;
  * y=C with all other guards, or y=B with x.out != DONE:
    wChallengeTickets gx moves parent -> waiting and
    its child -> pending without changing stamps;
    a validating B/NEW challenge extends EWord scrub;
  * y=B, x.out=DONE: (gx,gy) frame; EWord covered idle row;
  * y=F, x.out=DONE: the joined done/returned ticket retags
    source returned, destination frames; RETURN pivot decreases;
  * otherwise: (gx,gy) frame or challenge as in wValidationPair.

S3 (source C):
  * x.probe=PENDING, y.phase=C:
    x pending -> observedInternal; y ticket frames; pivot fixed;
  * y.phase=B or F: y's ticket becomes none as the physical
    serializer y becomes canonical C/OFF; x ticket frames;
  * otherwise: (gx,gy) frame; pivot fixed.
S4 (source F):
  * y.phase=B or F: y canonical C/OFF, its ticket cleared;
  * otherwise both tickets frame; pivot fixed.

S7 cannot occur with INTERNAL flags because SerPhase is B/C/F.
S2R, S5, S0, S1, S6 and SR cannot occur without a post-E
root endpoint, hence are ABSENT under e != root and right(e) != root.
Every third site i with i != e and i != right(e) has identical
full physical ProjW by EWord.remoteFrame, and identical ledger
ticket by the chronological bankWordHardEpochStep equation.

For the EWord spatial classes: unvisitedSuffix touches no site
below scrub, leaving scrub/pivot and every covered ticket fixed;
coveredInside B/DONE -> B is also stationary; frontierParent
NEW challenge grows scrub, INTERNAL_OK advances pivot, LEAF_OK
begins the return; challengedChild S3 creates observedInternal;
RETURN B/DONE -> F at the pivot predecessor decreases pivot.
These last three MOVING classes still require a full
ticket/physical/ghost case induction; the concrete subcase
preservation theorems proved here must not be mistaken for it.
-/

/-- The actual W serializer on a represented nonroot/nonincoming
edge has only internal rows S2N, S3, S4.
Consumer: R10a W nonroot wave-case split. -/
theorem bankWordRenewalFrontierNonrootInternalRowClass {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (he : e ≠ root) (hj : ring.rightNeighbor e ≠ root) :
    (bankWordEpochSelectedReceipt ring z e).serializer.row = "S2N" ∨
    (bankWordEpochSelectedReceipt ring z e).serializer.row = "S3" ∨
    (bankWordEpochSelectedReceipt ring z e).serializer.row = "S4" := by
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass e).2
  have hpost := clockPostInternal ring root z.2.1 e
    (by omega : 2 ≤ n) hfixed he hj
  change (serW (z.2.1 e)
        (z.2.1 (ring.rightNeighbor e))).row = "S2N" ∨
    (serW (z.2.1 e)
        (z.2.1 (ring.rightNeighbor e))).row = "S3" ∨
    (serW (z.2.1 e)
        (z.2.1 (ring.rightNeighbor e))).row = "S4"
  cases hp : (z.2.1 e).ser.phase with
  | B =>
      left
      simp [serW, serializerStep, ProjW.lift,
        hpost.1, hpost.2, hp]
  | C =>
      right
      left
      simp [serW, serializerStep, ProjW.lift,
        hpost.1, hpost.2, hp]
  | F =>
      right
      right
      simp [serW, serializerStep, ProjW.lift,
        hpost.1, hpost.2, hp]

/-- The REAL hard-epoch fold leaves a third party's validation
ticket alone. This does not assume any ticket is genuine.
Consumer: R10a W frame branches for covered wave sites. -/
theorem bankWordRenewalFrontierWaveTicketRemoteFrame {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (e i : Fin n)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).validation i =
    (bankWordHardEpochLedger ring root z).validation i := by
  rw [bankWordHardEpochLedgerNext]
  simp [bankWordHardEpochStep, bankWordEpochSelectedReceipt,
    hi, hj]

/-- Before any validating hard S1, a physical nonroot edge
frames the root certificate and its REQUESTED ticket. It
cannot spontaneously start a wave; hence this preserves the
entire strengthened invariant, not just a scalar row equality.
Consumer: the inactive branch of R10a W nonroot closure. -/
theorem bankWordRenewalFrontierWaveInactiveNonrootStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankWordEpochState n)
    (he : e ≠ root) (hj : ring.rightNeighbor e ≠ root)
    (hlineage : BankWordRenewalFrontierWaveLineage ring root z)
    (hinactive : ¬ ((z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)) :
    BankWordRenewalFrontierWaveLineage ring root
      (bankWordEpochNext ring root z e) := by
  have hroot := bankWordHardEpochRootRemoteFrame
    ring root z e he.symm hj.symm
  have hticket := bankWordRootTicketRemoteFrame
    ring root z e he.symm hj.symm
  have hnotnext :
      ¬ (((bankWordEpochNext ring root z e).2.1 root).ser.cert =
          .RUNNING ∧
        ((bankWordEpochNext ring root z e).2.1 root).ser.wphase =
          .VALIDATING) := by
    intro hnew
    rw [hroot] at hnew
    exact hinactive hnew
  obtain ⟨hbase, _⟩ := hlineage
  obtain ⟨hreq, _, _⟩ := hbase
  unfold BankWordRenewalFrontierWaveLineage
    BankWordRenewalFrontierTicketLineage
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro hnew
    have hold : (z.2.1 root).ser.cert = .REQUESTED := by
      simpa only [hroot] using hnew
    obtain ⟨ticket, ht⟩ := hreq hold
    refine ⟨ticket, ?_⟩
    rw [hticket]
    exact ht
  · intro hnew
    exact False.elim (hnotnext ⟨hnew.1, hnew.2.1⟩)
  · intro hnew
    exact False.elim (hnotnext ⟨hnew.1, hnew.2.1⟩)
  · intro hnew
    exact False.elim (hnotnext hnew)

/-- On an actual EWord-unvisited nonroot service, neither
physical serializer nor validation ticket changes at any
scrubbed site. This statement preserves the FULL 5-clause
WaveLineage at every covered site, with the actual phiW step.
Classification is applied to each admitted witness for g.
Consumer: unvisitedSuffix case in R10a W wave induction. -/
theorem bankWordRenewalFrontierWaveUnvisitedNonrootStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (he : e ≠ root) (hj : ring.rightNeighbor e ≠ root)
    (hlineage : BankWordRenewalFrontierWaveLineage ring root z)
    (hunvisited : ∀ g : L3.EWord.ValidationGhost,
      L3.EWord.ValidationShape ring root z.2.1 g →
      L3.EWord.validationEdgeClass ring root g e =
        .unvisitedSuffix) :
    BankWordRenewalFrontierWaveLineage ring root
      (bankWordEpochNext ring root z e) := by
  by_cases hvalid :
      (z.2.1 root).ser.cert = .RUNNING ∧
        (z.2.1 root).ser.wphase = .VALIDATING
  · obtain ⟨hbase, hwave⟩ := hlineage
    obtain ⟨g, req, stamp, hshape, hsites⟩ := hwave hvalid
    have hclass := hunvisited g hshape
    have hremote :=
      L3.EWord.unvisitedSuffixRemote ring root g e hclass
    have hrepresented := bankWordEpochReachablePhysicalRootClass
      ring hn hbank root s hs z hz
    have hfixed : WFixedRoot ring root
        (phiW ring z.2.1 e) :=
      ((bankWordSerializerRootClassClosed ring hn hbank root).2
        z.2.1 hrepresented e).2
    have hno := bankWordRootNonrootHardAcceptFalse
      ring hn hbank root s hs z hz e he
    have hshapeNew :=
      L3.EWord.validationUnvisitedSuffixClass
        ring root z.2.1 g e hshape hfixed hno hclass
    have hghost := L3.EWord.unvisitedSuffixGhostUnchanged
      ring root z.2.1 g e hshape hremote
    rw [hghost] at hshapeNew
    have hshapeNext :
        L3.EWord.ValidationShape ring root
          (bankWordEpochNext ring root z e).2.1 g :=
      hshapeNew
    have hlower : 2 ≤ g.scrub := hshape.lower
    have hchildSafe : ring.rightNeighbor root ≠ e ∧
        ring.rightNeighbor root ≠ ring.rightNeighbor e := by
      have h :=
        hremote (⟨1, (show 1 < n by omega)⟩ : Fin n)
          (show 1 < g.scrub by omega)
      simpa only [L3.EWord.siteOne] using h
    have hbaseNext :=
      bankWordRenewalFrontierTicketLineageRemoteStep
        ring root e z he hj hchildSafe.1.symm
          hchildSafe.2.symm hbase
    refine ⟨hbaseNext, ?_⟩
    intro _
    refine ⟨g, req, stamp, hshapeNext, ?_⟩
    intro k hk
    have hsafe := hremote k hk
    have hsitePhysical :
        (bankWordEpochNext ring root z e).2.1
          (L3.EWord.site ring root k.val) =
        z.2.1 (L3.EWord.site ring root k.val) := by
      change (phiW ring z.2.1 e)
        (L3.EWord.site ring root k.val) =
        z.2.1 (L3.EWord.site ring root k.val)
      exact L3.EWord.remoteFrame ring z.2.1 e
        (L3.EWord.site ring root k.val) hsafe.1 hsafe.2
    have hsiteTicket := bankWordRenewalFrontierWaveTicketRemoteFrame
      ring root z e (L3.EWord.site ring root k.val)
      hsafe.1 hsafe.2
    obtain ⟨hB, hP, hI, hL, hF⟩ := hsites k hk
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro hnew
      have hold : (z.2.1 (L3.EWord.site ring root k.val)).ser.phase =
          .B ∧
        (z.2.1 (L3.EWord.site ring root k.val)).ser.wphase =
          .VALIDATING := by
        simpa only [hsitePhysical] using hnew
      have ht := hB hold
      simpa only [BankWordRenewalFrontierWaveSiteTicket,
        hsitePhysical, hsiteTicket] using ht
    · intro hnew
      have hold : (z.2.1 (L3.EWord.site ring root k.val)).ser.phase =
          .C ∧
        (z.2.1 (L3.EWord.site ring root k.val)).ser.probe =
          .PENDING ∧
        (z.2.1 (L3.EWord.site ring root k.val)).ser.wphase =
          .VALIDATING := by
        simpa only [hsitePhysical] using hnew
      have ht := hP hold
      simpa only [BankWordRenewalFrontierWaveSiteTicket,
        hsitePhysical, hsiteTicket] using ht
    · intro hnew
      have hold : (z.2.1 (L3.EWord.site ring root k.val)).ser.phase =
          .C ∧
        (z.2.1 (L3.EWord.site ring root k.val)).ser.probe =
          .INTERNAL_OK ∧
        (z.2.1 (L3.EWord.site ring root k.val)).ser.wphase =
          .VALIDATING := by
        simpa only [hsitePhysical] using hnew
      have ht := hI hold
      simpa only [BankWordRenewalFrontierWaveSiteTicket,
        hsitePhysical, hsiteTicket] using ht
    · intro hnew
      have hold : (z.2.1 (L3.EWord.site ring root k.val)).ser.phase =
          .C ∧
        (z.2.1 (L3.EWord.site ring root k.val)).ser.probe =
          .LEAF_OK := by
        simpa only [hsitePhysical] using hnew
      have ht := hL hold
      simpa only [BankWordRenewalFrontierWaveSiteTicket,
        hsitePhysical, hsiteTicket] using ht
    · intro hnew
      have hold : (z.2.1 (L3.EWord.site ring root k.val)).ser.phase =
          .F ∧ g.stage = .returning ∧ g.pivot ≤ k.val := by
        simpa only [hsitePhysical] using hnew
      have ht := hF hold
      simpa only [BankWordRenewalFrontierWaveSiteTicket,
        hsitePhysical, hsiteTicket] using ht
  · exact bankWordRenewalFrontierWaveInactiveNonrootStep
      ring root e z he hj hlineage hvalid

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open Classical
set_option autoImplicit false
set_option Elab.async false

/-- Incoming S0 creates a matching request; incoming S5 frames
the nonvalidating root and its ticket. Consumer: J-W root seam. -/
theorem bankWordRenewalWaveRootIncomingInactiveStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hpred : ring.rightNeighbor e = root)
    (hwave : BankWordRenewalFrontierWaveLineage ring root z)
    (hinactive : ¬ ((z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)) :
    BankWordRenewalFrontierWaveLineage ring root
      (bankWordEpochNext ring root z e) := by
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass e).2
  have hpost := clockPostIncoming ring root z.2.1 e
    (by omega : 2 ≤ n) hfixed hpred
  try rw [hpred] at hpost
  have hneq : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) e
  by_cases hidle : (z.2.1 root).ser.cert = .IDLE
  · have hrequest :=
      (bankWordRenewalFrontierIncomingRequestTicket
        ring root e s hn hbank hs z hz hpred hidle).2
    have hquarantine :
        ((bankWordEpochNext ring root z e).2.1 root).ser.wphase =
          .QUARANTINE := by
      change ((phiW ring z.2.1 e) root).ser.wphase =
        .QUARANTINE
      rw [← hpred, phiW_ser_target ring z.2.1 e hneq]
      simp [serW, serializerStep, ProjW.lift,
        hpost.1, hpost.2, hpred, hidle]
    unfold BankWordRenewalFrontierWaveLineage
      BankWordRenewalFrontierTicketLineage
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro _
      exact ⟨_, hrequest⟩
    · intro h
      rw [hquarantine] at h
      cases h.2.1
    · intro h
      rw [hquarantine] at h
      cases h.2.1
    · intro h
      rw [hquarantine] at h
      cases h.2
  · have hroot :
        ((bankWordEpochNext ring root z e).2.1 root).ser =
          (z.2.1 root).ser := by
      change ((phiW ring z.2.1 e) root).ser =
        (z.2.1 root).ser
      rw [← hpred, phiW_ser_target ring z.2.1 e hneq]
      simp [serW, serializerStep, ProjW.lift,
        hpost.1, hpost.2, hpred, hidle]
    have hticket :
        (bankWordHardEpochLedger ring root
          (bankWordEpochNext ring root z e)).validation root =
        (bankWordHardEpochLedger ring root z).validation root := by
      have h := bankWordRootIncomingTicketExact
        ring root z e (by omega : 2 ≤ n) hfixed hpred
      simpa [hidle] using h
    have hno :
        ¬ (((bankWordEpochNext ring root z e).2.1 root).ser.cert =
             .RUNNING ∧
           ((bankWordEpochNext ring root z e).2.1 root).ser.wphase =
             .VALIDATING) := by
      intro h
      rw [hroot] at h
      exact hinactive h
    have holdRequest := hwave.1.1
    unfold BankWordRenewalFrontierWaveLineage
      BankWordRenewalFrontierTicketLineage
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro h
      have hold : (z.2.1 root).ser.cert = .REQUESTED := by
        rw [hroot] at h
        exact h
      obtain ⟨request, ht⟩ := holdRequest hold
      exact ⟨request, by rw [hticket]; exact ht⟩
    · intro h
      exact False.elim (hno ⟨h.1, h.2.1⟩)
    · intro h
      exact False.elim (hno ⟨h.1, h.2.1⟩)
    · intro h
      exact False.elim (hno h)

/-- Root S6, whether soft or hard, exits to physical IDLE.
The hard S6's genuineness is certified at the OLD state by
bankWordRenewalFrontierWaveHardAcceptGenuine.
Consumer: terminal outgoing branch of J-W. -/
theorem bankWordRenewalWaveRootOutgoingFinishStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hcert : (z.2.1 root).ser.cert ≠ .REQUESTED)
    (hphase : (z.2.1 root).ser.phase = .B)
    (hout : (z.2.1 root).ser.out = .DONE)
    (hchild :
      (z.2.1 (ring.rightNeighbor root)).ser.phase = .F) :
    BankWordRenewalFrontierWaveLineage ring root
      (bankWordEpochNext ring root z root) := by
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 root) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass root).2
  have hpost := clockPostOutgoing ring root z.2.1 root
    (by omega : 2 ≤ n) hfixed rfl
  have hsix := serRootOutgoingDone
    (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
    hpost.1 hpost.2 hcert hphase hout hchild
  have hidle :
      ((bankWordEpochNext ring root z root).2.1 root).ser.cert =
        .IDLE := by
    change ((phiW ring z.2.1 root) root).ser.cert = .IDLE
    rw [phiW_ser_source]
    exact hsix.2.1
  unfold BankWordRenewalFrontierWaveLineage
    BankWordRenewalFrontierTicketLineage
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro h
    rw [hidle] at h
    cases h
  · intro h
    rw [hidle] at h
    cases h.1
  · intro h
    rw [hidle] at h
    cases h.1
  · intro h
    rw [hidle] at h
    cases h.1

/-- A positive-lease root S1 becomes RUNNING/CURRENT, so the
attempted soft start is not a hard validation wave.
Consumer: root outgoing soft S1 branch of J-W. -/
theorem bankWordRenewalWaveRootOutgoingSoftStartStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hrequested : (z.2.1 root).ser.cert = .REQUESTED)
    (hpositive : 0 < (z.2.1 root).siLease.val) :
    BankWordRenewalFrontierWaveLineage ring root
      (bankWordEpochNext ring root z root) := by
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 root) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass root).2
  have hpost := clockPostOutgoing ring root z.2.1 root
    (by omega : 2 ≤ n) hfixed rfl
  have hsoft := bankWordRenewalFrontierSoftSOneDoesNotValidate
    (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
    hpost.1 hpost.2 hrequested hpositive
  have hstart := serRootOutgoingStart
    (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
    hpost.1 hpost.2 hrequested
  have hrun :
      ((bankWordEpochNext ring root z root).2.1 root).ser.cert =
        .RUNNING := by
    change ((phiW ring z.2.1 root) root).ser.cert = .RUNNING
    rw [phiW_ser_source]
    exact hstart.2.1
  have hcurrent :
      ((bankWordEpochNext ring root z root).2.1 root).ser.wphase =
        .CURRENT := by
    change ((phiW ring z.2.1 root) root).ser.wphase = .CURRENT
    rw [phiW_ser_source]
    exact hsoft.2.2.1
  unfold BankWordRenewalFrontierWaveLineage
    BankWordRenewalFrontierTicketLineage
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro h
    rw [hrun] at h
    cases h
  · intro h
    rw [hcurrent] at h
    cases h.2.1
  · intro h
    rw [hcurrent] at h
    cases h.2.1
  · intro h
    rw [hcurrent] at h
    cases h.2

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open Classical

/-- Literal ROOT_OUT continuation of a soft B/CURRENT episode:
a RUNNING B cannot issue another S1; an outgoing row other
than its S6 terminal keeps the root B/RUNNING/CURRENT.
This is the root-outgoing component of the intended all-edge
episode step and the pendingSoft pairing proof.
Consumer: J-C and repair.tex 1062--1065. -/
theorem bankWordRenewalSoftRootEpisodeStep
    {c : Compiled} (x y : ProjW c)
    (hx : (postW x y).eX.l = true)
    (hy : (postW x y).eY.l = false)
    (hrun : x.ser.cert = .RUNNING)
    (hb : x.ser.phase = .B)
    (hcurrent : x.ser.wphase = .CURRENT) :
    (serW x y).row ≠ "S1" ∧
    (serW x y).hard.hardS1 = false ∧
    ((serW x y).row ≠ "S6" →
      (serW x y).x.cert = .RUNNING ∧
      (serW x y).x.phase = .B ∧
      (serW x y).x.wphase = .CURRENT) := by
  cases hout : x.ser.out <;>
    cases hchild : y.ser.phase <;>
    cases hprobe : y.ser.probe <;>
    simp [serW, serializerStep, ProjW.lift,
      serChallengeWrite,
      hx, hy, hrun, hb, hcurrent,
      hout, hchild, hprobe]

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open Classical
set_option autoImplicit false
set_option Elab.async false

/-- A reachable represented zero-lease S1 establishes the complete fresh
two-site wave, including the historical waiting/pending tickets with one
common request/start stamp. Consumer: the hard-start branch of root
outgoing J-W transport and the paper's R10a validation cut. -/
theorem bankWordRenewalWaveRootOutgoingHardStartStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hwave : BankWordRenewalFrontierWaveLineage ring root z)
    (hrequested : (z.2.1 root).ser.cert = .REQUESTED)
    (hzero : (z.2.1 root).siLease.val = 0) :
    BankWordRenewalFrontierWaveLineage ring root
      (bankWordEpochNext ring root z root) := by
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 root) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass root).2
  have hpost := clockPostOutgoing ring root z.2.1 root
    (by omega : 2 ≤ n) hfixed rfl
  have hshape : L3.EWord.ValidationShape ring root
      (bankWordEpochNext ring root z root).2.1
        L3.EWord.freshGhost := by
    change L3.EWord.ValidationShape ring root
      (phiW ring z.2.1 root) L3.EWord.freshGhost
    exact L3.EWord.freshStartWholeRing ring root z.2.1
      (by omega : 3 ≤ n) hpost.1 hpost.2
      hrequested hzero hfixed
  obtain ⟨_, _, hsourceB, hsourceWait, hsourceRun,
      hsourceValid, hchildC, hchildPending, hchildValid⟩ :=
    L3.EWord.freshStartPair
      (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
      hpost.1 hpost.2 hrequested hzero
  have hne : ring.rightNeighbor root ≠ root :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) root
  have hrootB :
      ((bankWordEpochNext ring root z root).2.1 root).ser.phase =
        .B := by
    change ((phiW ring z.2.1 root) root).ser.phase = .B
    rw [L3.EWord.phiSource]
    exact hsourceB
  have hrootWait :
      ((bankWordEpochNext ring root z root).2.1 root).ser.out =
        .WAIT := by
    change ((phiW ring z.2.1 root) root).ser.out = .WAIT
    rw [L3.EWord.phiSource]
    exact hsourceWait
  have hrootRun :
      ((bankWordEpochNext ring root z root).2.1 root).ser.cert =
        .RUNNING := by
    change ((phiW ring z.2.1 root) root).ser.cert = .RUNNING
    rw [L3.EWord.phiSource]
    exact hsourceRun
  have hrootValid :
      ((bankWordEpochNext ring root z root).2.1 root).ser.wphase =
        .VALIDATING := by
    change ((phiW ring z.2.1 root) root).ser.wphase = .VALIDATING
    rw [L3.EWord.phiSource]
    exact hsourceValid
  have hchildPhase :
      ((bankWordEpochNext ring root z root).2.1
        (ring.rightNeighbor root)).ser.phase = .C := by
    change ((phiW ring z.2.1 root)
      (ring.rightNeighbor root)).ser.phase = .C
    rw [L3.EWord.phiResponder ring z.2.1 root hne]
    exact hchildC
  have hchildProbe :
      ((bankWordEpochNext ring root z root).2.1
        (ring.rightNeighbor root)).ser.probe = .PENDING := by
    change ((phiW ring z.2.1 root)
      (ring.rightNeighbor root)).ser.probe = .PENDING
    rw [L3.EWord.phiResponder ring z.2.1 root hne]
    exact hchildPending
  have hchildValidating :
      ((bankWordEpochNext ring root z root).2.1
        (ring.rightNeighbor root)).ser.wphase = .VALIDATING := by
    change ((phiW ring z.2.1 root)
      (ring.rightNeighbor root)).ser.wphase = .VALIDATING
    rw [L3.EWord.phiResponder ring z.2.1 root hne]
    exact hchildValid
  obtain ⟨request, htRoot, htChild, _⟩ :=
    bankWordRenewalFrontierHardStartTicketPair
      ring root s hn hbank hs z hz hwave.1 hrequested hzero
  have hbase : BankWordRenewalFrontierTicketLineage ring root
      (bankWordEpochNext ring root z root) := by
    unfold BankWordRenewalFrontierTicketLineage
    refine ⟨?_, ?_, ?_⟩
    · intro h
      rw [hrootRun] at h
      cases h
    · intro _
      refine ⟨{ requestedAt := request.requestedAt, startedAt := z.2.2.clock + 1, stage := .waiting },
              { requestedAt := request.requestedAt, startedAt := z.2.2.clock + 1, stage := .pending }, ?_, ?_, rfl, rfl⟩
      · rw [htRoot]
        rfl
      · rw [htChild]
        rfl
    · intro h
      have hd := h.2.2.2.1
      rw [hrootWait] at hd
      cases hd
  refine ⟨hbase, ?_⟩
  intro _
  refine ⟨L3.EWord.freshGhost, request.requestedAt,
    z.2.2.clock + 1, hshape, ?_⟩
  intro k hk
  have hklt : k.val < 2 := by
    simpa [L3.EWord.freshGhost] using hk
  have hcases : k.val = 0 ∨ k.val = 1 := by omega
  rcases hcases with hzeroIndex | honeIndex
  · have hsite : L3.EWord.site ring root k.val = root := by
      rw [hzeroIndex, L3.EWord.siteZero]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro _
      unfold BankWordRenewalFrontierWaveSiteTicket
      refine ⟨{ requestedAt := request.requestedAt, startedAt := z.2.2.clock + 1, stage := .waiting }, ?_, rfl, rfl⟩
      simp [hsite, hrootWait, htRoot, wTicketAt]
    · intro h
      have hp := h.1
      rw [hsite, hrootB] at hp
      cases hp
    · intro h
      have hp := h.1
      rw [hsite, hrootB] at hp
      cases hp
    · intro h
      have hp := h.1
      rw [hsite, hrootB] at hp
      cases hp
    · intro h
      have hp := h.1
      rw [hsite, hrootB] at hp
      cases hp
  · have hsite :
        L3.EWord.site ring root k.val =
          ring.rightNeighbor root := by
      rw [honeIndex, L3.EWord.siteOne]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro h
      have hp := h.1
      rw [hsite, hchildPhase] at hp
      cases hp
    · intro _
      unfold BankWordRenewalFrontierWaveSiteTicket
      refine ⟨{ requestedAt := request.requestedAt, startedAt := z.2.2.clock + 1, stage := .pending }, ?_, rfl, rfl⟩
      simp [hsite, htChild, wTicketAt]
    · intro h
      have hp := h.2.1
      rw [hsite, hchildProbe] at hp
      cases hp
    · intro h
      have hp := h.2
      rw [hsite, hchildProbe] at hp
      cases hp
    · intro h
      have hp := h.1
      rw [hsite, hchildPhase] at hp
      cases hp

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open Classical
set_option autoImplicit false
set_option Elab.async false

/-- The active incoming-root S5 seam preserves the EWord physical
wave, the root ticket and every ticket before the terminal site.
The terminal source ticket is intentionally excluded here: its
PENDING-to-LEAF_OK transition requires the parent/child join below.
Consumer: root incoming J-W case split, paper R10a terminal seam. -/
theorem bankWordRenewalWaveRootIncomingActiveFrameStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hpred : ring.rightNeighbor e = root)
    (g : L3.EWord.ValidationGhost)
    (hshape : L3.EWord.ValidationShape ring root z.2.1 g) :
    L3.EWord.ValidationShape ring root
      (bankWordEpochNext ring root z e).2.1 g ∧
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).validation root =
        (bankWordHardEpochLedger ring root z).validation root ∧
    ∀ k : Fin n, k.val < g.scrub → k.val ≠ n - 1 →
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z e)).validation
          (L3.EWord.site ring root k.val) =
      (bankWordHardEpochLedger ring root z).validation
          (L3.EWord.site ring root k.val) := by
  have hinj : Function.Injective ring.rightNeighbor := by
    intro a b hab
    apply Fin.ext
    have hv := congrArg Fin.val hab
    change (a.val + 1) % n = (b.val + 1) % n at hv
    by_cases ha : a.val + 1 < n
    · by_cases hb : b.val + 1 < n
      · rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv
        omega
      · have hbeq : b.val + 1 = n := by omega
        rw [Nat.mod_eq_of_lt ha, hbeq, Nat.mod_self] at hv
        omega
    · have haeq : a.val + 1 = n := by omega
      by_cases hb : b.val + 1 < n
      · rw [haeq, Nat.mod_self, Nat.mod_eq_of_lt hb] at hv
        omega
      · omega
  have he : e = L3.EWord.site ring root (n - 1) := by
    apply hinj
    rw [hpred]
    exact (L3.EWord.validationSeamNeighbor ring root
      (L3.EWord.site ring root (n - 1)) rfl).symm
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass e).2
  have hpost := clockPostIncoming ring root z.2.1 e
    (by omega : 2 ≤ n) hfixed hpred
  have hno : (serW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).hard.hardAccept = false :=
    L3.EWord.nonrootNoAccept
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e)) hpost.1
  have hseam :
      L3.EWord.validationEdgeClass ring root g e =
        .rootSeam := by
    simp [L3.EWord.validationEdgeClass, he]
  have hghost : L3.EWord.validationGhostStep ring root
      z.2.1 g e = g :=
    L3.EWord.validationSeamGhostFixed
      ring root z.2.1 g e hshape hfixed he
  have hphysical : L3.EWord.ValidationShape ring root
      (bankWordEpochNext ring root z e).2.1 g := by
    change L3.EWord.ValidationShape ring root (phiW ring z.2.1 e) g
    have h := L3.EWord.validationRootSeamClass
      ring root z.2.1 g e hshape hfixed hno hseam
    rw [hghost] at h
    exact h
  have hnotIdle : (z.2.1 root).ser.cert ≠ .IDLE := by
    rw [hshape.rootRunning]
    decide
  have hrootFrame :
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z e)).validation root =
        (bankWordHardEpochLedger ring root z).validation root := by
    have h := bankWordRootIncomingTicketExact
      ring root z e (by omega : 2 ≤ n) hfixed hpred
    simpa [hnotIdle] using h
  refine ⟨hphysical, hrootFrame, ?_⟩
  intro k hk hnotLast
  by_cases hzero : k.val = 0
  · have hsite : L3.EWord.site ring root k.val = root := by
      rw [hzero, L3.EWord.siteZero]
    rw [hsite]
    exact hrootFrame
  · have hsiteNeSource :
        L3.EWord.site ring root k.val ≠ e := by
      intro heq
      have hsame :
          L3.EWord.site ring root k.val =
            L3.EWord.site ring root (n - 1) :=
        heq.trans he
      have hi := L3.EWord.validationSiteInjective
        ring root k.val (n - 1) k.isLt
          (by omega : n - 1 < n) hsame
      exact hnotLast hi
    have hsiteNeRoot :
        L3.EWord.site ring root k.val ≠ root := by
      intro heq
      have hsame :
          L3.EWord.site ring root k.val =
            L3.EWord.site ring root 0 :=
        heq.trans (L3.EWord.siteZero ring root).symm
      have hi := L3.EWord.validationSiteInjective
        ring root k.val 0 k.isLt (by omega : 0 < n) hsame
      exact hzero hi
    exact bankWordRenewalFrontierWaveTicketRemoteFrame
      ring root z e (L3.EWord.site ring root k.val)
      hsiteNeSource (by rw [hpred]; exact hsiteNeRoot)

/-- An actual reachable incoming S5 at C/PENDING with the
same historical root parent and leaf child writes observedLeaf
to the terminal source. Unlike a mere physical LEAF_OK byte,
the conclusion depends on the join of OLD tickets.
Consumer: last covered-site S5 in the incoming J-W step. -/
theorem bankWordRenewalWaveRootIncomingLeafStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hpred : ring.rightNeighbor e = root)
    (hrun : (z.2.1 root).ser.cert = .RUNNING)
    (hsource : (z.2.1 e).ser.phase = .C)
    (hpending : (z.2.1 e).ser.probe = .PENDING)
    (parent child : WValidationTicket)
    (hparent : wParentTicket
      ((bankWordHardEpochLedger ring root z).validation root) =
        some parent)
    (hchild : wTicketAt .pending
      ((bankWordHardEpochLedger ring root z).validation e) =
        some child)
    (hrequest : parent.requestedAt = child.requestedAt)
    (hstamp : parent.startedAt = child.startedAt) :
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).validation e =
        some { parent with stage := .observedLeaf } := by
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass e).2
  have hpost := clockPostIncoming ring root z.2.1 e
    (by omega : 2 ≤ n) hfixed hpred
  have hnotIdle :
      (z.2.1 (ring.rightNeighbor e)).ser.cert ≠ .IDLE := by
    rw [hpred]
    rw [hrun]
    decide
  have hrow : (serW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).row = "S5" :=
    (serRootIncomingNonidle
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      hpost.1 hpost.2 hnotIdle).1
  have hlocal := bankWordRenewalFrontierWaveLeafObservation
    (z.2.2.clock + 1)
    (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
    ((bankWordHardEpochLedger ring root z).validation e)
    ((bankWordHardEpochLedger ring root z).validation root)
    parent child hrow hsource hpending
    (by simpa only [hpred] using hparent)
    hchild hrequest hstamp
  rw [bankWordHardEpochLedgerNext]
  change (if e = e then
      (wValidationPair (z.2.2.clock + 1)
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        ((bankWordHardEpochLedger ring root z).validation e)
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor e))).1
     else if e = ring.rightNeighbor e then
      (wValidationPair (z.2.2.clock + 1)
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        ((bankWordHardEpochLedger ring root z).validation e)
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor e))).2
     else (bankWordHardEpochLedger ring root z).validation e) =
        some { parent with stage := .observedLeaf }
  exact (if_pos rfl).trans (by simpa only [hpred] using hlocal)

end L3.RenewalReferenceClock



namespace L3.RenewalReferenceClock

open Classical
set_option autoImplicit false
set_option Elab.async false

/-- Root S2R, B/NEW challenging a C responder: the actual
chronological ledger writes waiting/pending descendants of the
same OLD parent. This is not a whole-wave movement theorem.
Consumer: first challenge arm of root outgoing J-W. -/
theorem bankWordRenewalWaveRootOutgoingChallengeStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n)
    (hn : 2 ≤ n)
    (hrow :
      (bankWordEpochSelectedReceipt ring z root).serializer.row =
        "S2R")
    (hnew : (z.2.1 root).ser.out = .NEW)
    (hchildC :
      (z.2.1 (ring.rightNeighbor root)).ser.phase = .C)
    (parent : WValidationTicket)
    (hparent : wParentTicket
      ((bankWordHardEpochLedger ring root z).validation root) =
        some parent) :
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z root)).validation root =
        some { parent with stage := .waiting } ∧
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z root)).validation
        (ring.rightNeighbor root) =
        some { parent with stage := .pending } := by
  change (serW (z.2.1 root)
    (z.2.1 (ring.rightNeighbor root))).row = "S2R" at hrow
  have hpair :
      wValidationPair (z.2.2.clock + 1)
        (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
        ((bankWordHardEpochLedger ring root z).validation root)
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor root)) =
      (some { parent with stage := .waiting },
       some { parent with stage := .pending }) := by
    simp [wValidationPair, hrow, hnew, hchildC,
      wChallengeTickets, wTicketStage, hparent]
  have hne : ring.rightNeighbor root ≠ root :=
    clockNeighborDifferent ring hn root
  have htarget :
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z root)).validation
          (ring.rightNeighbor root) =
        (wValidationPair (z.2.2.clock + 1)
          (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
          ((bankWordHardEpochLedger ring root z).validation root)
          ((bankWordHardEpochLedger ring root z).validation
            (ring.rightNeighbor root))).2 := by
    rw [bankWordHardEpochLedgerNext]
    simp [bankWordHardEpochStep, bankWordEpochSelectedReceipt, hne]
  constructor
  · rw [bankWordRootOutgoingTicketExact ring root z, hpair]
  · rw [htarget, hpair]

/-- The actual root S2R leaf-admission row writes a DONE root
and a RETURNED first follower; the join requires equal old
request/start stamps, not just the physical LEAF_OK flag.
Consumer: root outgoing turn-to-return arm of J-W. -/
theorem bankWordRenewalWaveRootOutgoingLeafStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n)
    (hn : 2 ≤ n)
    (hrow :
      (bankWordEpochSelectedReceipt ring z root).serializer.row =
        "S2R")
    (hw : (z.2.1 root).ser.out = .WAIT)
    (hc : (z.2.1 (ring.rightNeighbor root)).ser.phase = .C)
    (hl :
      (z.2.1 (ring.rightNeighbor root)).ser.probe = .LEAF_OK)
    (parent child : WValidationTicket)
    (htParent : wTicketAt .waiting
      ((bankWordHardEpochLedger ring root z).validation root) =
        some parent)
    (htChild : wTicketAt .observedLeaf
      ((bankWordHardEpochLedger ring root z).validation
        (ring.rightNeighbor root)) = some child)
    (hrequest : parent.requestedAt = child.requestedAt)
    (hstamp : parent.startedAt = child.startedAt) :
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z root)).validation root =
        some { parent with stage := .done } ∧
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z root)).validation
        (ring.rightNeighbor root) =
        some { parent with stage := .returned } := by
  have hpair := bankWordRenewalFrontierWaveLeafAdmission
    (z.2.2.clock + 1)
    (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
    ((bankWordHardEpochLedger ring root z).validation root)
    ((bankWordHardEpochLedger ring root z).validation
      (ring.rightNeighbor root))
    parent child hrow hw hc hl
    htParent htChild hrequest hstamp
  have hne : ring.rightNeighbor root ≠ root :=
    clockNeighborDifferent ring hn root
  have htarget :
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z root)).validation
          (ring.rightNeighbor root) =
        (wValidationPair (z.2.2.clock + 1)
          (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
          ((bankWordHardEpochLedger ring root z).validation root)
          ((bankWordHardEpochLedger ring root z).validation
            (ring.rightNeighbor root))).2 := by
    rw [bankWordHardEpochLedgerNext]
    simp [bankWordHardEpochStep, bankWordEpochSelectedReceipt, hne]
  constructor
  · rw [bankWordRootOutgoingTicketExact ring root z, hpair]
  · rw [htarget, hpair]

/-- At the genuine RETURN pivot strictly beyond the first
follower, root B/DONE -> B is S2R, not S6. It preserves the
EWord physical shape and both historical endpoint tickets.
Consumer: root outgoing RETURN-pivot idle branch of J-W. -/
theorem bankWordRenewalWaveRootOutgoingReturnPivotStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (g : L3.EWord.ValidationGhost)
    (hshape : L3.EWord.ValidationShape ring root z.2.1 g)
    (hr : L3.EWord.ReturnShape ring root z.2.1 g)
    (hpivot : 1 < g.pivot) :
    L3.EWord.ValidationShape ring root
      (bankWordEpochNext ring root z root).2.1
        (L3.EWord.validationGhostStep ring root z.2.1 g root) ∧
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z root)).validation root =
        (bankWordHardEpochLedger ring root z).validation root ∧
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z root)).validation
        (ring.rightNeighbor root) =
        (bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor root) := by
  have hdoneRoot := hr.completed
    (⟨0, (show 0 < n by omega)⟩ : Fin n)
    (by have := hr.pivotPositive; omega)
  have hdoneChild := hr.completed
    (⟨1, (show 1 < n by omega)⟩ : Fin n)
    (by omega)
  have hrootB : (z.2.1 root).ser.phase = .B := by
    simpa only [L3.EWord.siteZero] using hdoneRoot.1
  have hout : (z.2.1 root).ser.out = .DONE := by
    simpa only [L3.EWord.siteZero] using hdoneRoot.2.1
  have hchildB :
      (z.2.1 (ring.rightNeighbor root)).ser.phase = .B := by
    simpa only [L3.EWord.siteOne] using hdoneChild.1
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 root) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass root).2
  have hpost := clockPostOutgoing ring root z.2.1 root
    (by omega : 2 ≤ n) hfixed rfl
  have hno : (serW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).hard.hardAccept = false :=
    L3.EWord.childBNoAccept
      (z.2.1 root) (z.2.1 (ring.rightNeighbor root)) hchildB
  have hrow : (serW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).row = "S2R" :=
    (L3.EWord.validationRootDoneDoneSerFrame
      (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
      hpost.1 hpost.2 hshape.rootRunning
      hrootB hout hchildB).1
  have hpair :
      wValidationPair (z.2.2.clock + 1)
        (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
        ((bankWordHardEpochLedger ring root z).validation root)
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor root)) =
      ((bankWordHardEpochLedger ring root z).validation root,
       (bankWordHardEpochLedger ring root z).validation
         (ring.rightNeighbor root)) := by
    simp [wValidationPair, hrow, hout, hchildB]
  have hne : ring.rightNeighbor root ≠ root :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) root
  have htarget :
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z root)).validation
          (ring.rightNeighbor root) =
        (wValidationPair (z.2.2.clock + 1)
          (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
          ((bankWordHardEpochLedger ring root z).validation root)
          ((bankWordHardEpochLedger ring root z).validation
            (ring.rightNeighbor root))).2 := by
    rw [bankWordHardEpochLedgerNext]
    simp [bankWordHardEpochStep, bankWordEpochSelectedReceipt, hne]
  refine ⟨?_, ?_, ?_⟩
  · change L3.EWord.ValidationShape ring root
      (phiW ring z.2.1 root)
        (L3.EWord.validationGhostStep ring root z.2.1 g root)
    exact L3.EWord.validationCoveredRootDoneDoneClass
      ring root z.2.1 g hshape hfixed hno hrootB hout hchildB
  · rw [bankWordRootOutgoingTicketExact ring root z, hpair]
  · rw [htarget, hpair]

/-- The proved root S1 and S6 branches assemble on the real
epoch successor, including the hard zero-lease S1 case.
S2R and SR are deliberately outside this disjunction.
Consumer: completed portions of outgoing J-W induction. -/
theorem bankWordRenewalWaveRootOutgoingStartFinishStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hwave : BankWordRenewalFrontierWaveLineage ring root z)
    (hcase :
      (z.2.1 root).ser.cert = .REQUESTED ∨
      ((z.2.1 root).ser.cert ≠ .REQUESTED ∧
       (z.2.1 root).ser.phase = .B ∧
       (z.2.1 root).ser.out = .DONE ∧
       (z.2.1 (ring.rightNeighbor root)).ser.phase = .F)) :
    BankWordRenewalFrontierWaveLineage ring root
      (bankWordEpochNext ring root z root) := by
  rcases hcase with hrequested | hfinish
  · by_cases hzero : (z.2.1 root).siLease.val = 0
    · exact bankWordRenewalWaveRootOutgoingHardStartStep
        ring root s hn hbank hs z hz hwave hrequested hzero
    · have hpositive : 0 < (z.2.1 root).siLease.val := by omega
      exact bankWordRenewalWaveRootOutgoingSoftStartStep
        ring root s hn hbank hs z hz hrequested hpositive
  · exact bankWordRenewalWaveRootOutgoingFinishStep
      ring root s hn hbank hs z hz hfinish.1
        hfinish.2.1 hfinish.2.2.1 hfinish.2.2.2

end L3.RenewalReferenceClock



namespace L3.RenewalReferenceClock

open Classical
set_option autoImplicit false
set_option Elab.async false

/-- On a represented RUNNING root, the actual S2R B/DONE -> B
pair is stationary in the FULL five-clause wave-lineage invariant:
the two selected serializer records and tickets frame, all other
sites are remote, and EWord's validation ghost is unchanged.
Consumer: covered root S2R arm of J-W and paper return-pivot row. -/
theorem bankWordRenewalWaveRootOutgoingCoveredFrameStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hwave : BankWordRenewalFrontierWaveLineage ring root z)
    (hrun : (z.2.1 root).ser.cert = .RUNNING)
    (hrootB : (z.2.1 root).ser.phase = .B)
    (hout : (z.2.1 root).ser.out = .DONE)
    (hchildB :
      (z.2.1 (ring.rightNeighbor root)).ser.phase = .B) :
    BankWordRenewalFrontierWaveLineage ring root
      (bankWordEpochNext ring root z root) := by
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 root) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass root).2
  have hpost := clockPostOutgoing ring root z.2.1 root
    (by omega : 2 ≤ n) hfixed rfl
  have hrow := L3.EWord.validationRootDoneDoneSerFrame
    (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
    hpost.1 hpost.2 hrun hrootB hout hchildB
  have hne : ring.rightNeighbor root ≠ root :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) root
  have hrootSer :
      ((bankWordEpochNext ring root z root).2.1 root).ser =
        (z.2.1 root).ser := by
    change ((phiW ring z.2.1 root) root).ser =
      (z.2.1 root).ser
    rw [phiW_ser_source]
    exact hrow.2.1
  have hchildSer :
      ((bankWordEpochNext ring root z root).2.1
        (ring.rightNeighbor root)).ser =
        (z.2.1 (ring.rightNeighbor root)).ser := by
    change ((phiW ring z.2.1 root)
      (ring.rightNeighbor root)).ser =
        (z.2.1 (ring.rightNeighbor root)).ser
    rw [phiW_ser_target ring z.2.1 root hne]
    exact hrow.2.2
  have hpair :
      wValidationPair (z.2.2.clock + 1)
        (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
        ((bankWordHardEpochLedger ring root z).validation root)
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor root)) =
      ((bankWordHardEpochLedger ring root z).validation root,
       (bankWordHardEpochLedger ring root z).validation
         (ring.rightNeighbor root)) := by
    simp [wValidationPair, hrow.1, hout, hchildB]
  have hrootTicket :
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z root)).validation root =
        (bankWordHardEpochLedger ring root z).validation root := by
    rw [bankWordRootOutgoingTicketExact ring root z, hpair]
  have hchildTicket :
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z root)).validation
          (ring.rightNeighbor root) =
        (bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor root) := by
    rw [bankWordHardEpochLedgerNext]
    simp [bankWordHardEpochStep, bankWordEpochSelectedReceipt,
      hne, hpair]
  obtain ⟨hrequested, hpending, hdone⟩ := hwave.1
  have hbase : BankWordRenewalFrontierTicketLineage ring root
      (bankWordEpochNext ring root z root) := by
    unfold BankWordRenewalFrontierTicketLineage
    refine ⟨?_, ?_, ?_⟩
    · intro hnew
      have hold : (z.2.1 root).ser.cert = .REQUESTED := by
        simpa only [hrootSer] using hnew
      obtain ⟨ticket, ht⟩ := hrequested hold
      exact ⟨ticket, by rw [hrootTicket]; exact ht⟩
    · intro hnew
      have hold :
          (z.2.1 root).ser.cert = .RUNNING ∧
          (z.2.1 root).ser.wphase = .VALIDATING ∧
          (z.2.1 root).ser.phase = .B ∧
          (z.2.1 root).ser.out = .WAIT ∧
          (z.2.1 (ring.rightNeighbor root)).ser.phase = .C ∧
          (z.2.1 (ring.rightNeighbor root)).ser.probe =
            .PENDING := by
        simpa only [hrootSer, hchildSer] using hnew
      obtain ⟨parent, child, hp, hc, hr, hs⟩ := hpending hold
      refine ⟨parent, child, ?_, ?_, hr, hs⟩
      · rw [hrootTicket]
        exact hp
      · rw [hchildTicket]
        exact hc
    · intro hnew
      have hold :
          (z.2.1 root).ser.cert = .RUNNING ∧
          (z.2.1 root).ser.wphase = .VALIDATING ∧
          (z.2.1 root).ser.phase = .B ∧
          (z.2.1 root).ser.out = .DONE ∧
          (z.2.1 (ring.rightNeighbor root)).ser.phase = .F := by
        simpa only [hrootSer, hchildSer] using hnew
      obtain ⟨parent, child, hp, hc, hr, hs⟩ := hdone hold
      refine ⟨parent, child, ?_, ?_, hr, hs⟩
      · rw [hrootTicket]
        exact hp
      · rw [hchildTicket]
        exact hc
  refine ⟨hbase, ?_⟩
  intro hactive
  have holdActive :
      (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING := by
    simpa only [hrootSer] using hactive
  obtain ⟨g, req, stamp, hshape, hsites⟩ :=
    hwave.2 holdActive
  have hno : (serW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).hard.hardAccept = false :=
    L3.EWord.childBNoAccept
      (z.2.1 root) (z.2.1 (ring.rightNeighbor root)) hchildB
  have hstart := L3.EWord.validationParentHardStartFalse
    ring root z.2.1 g root hshape hfixed
  have hghost := L3.EWord.internalDoneDoneGhostFixed
    ring root z.2.1 g root hstart hout hchildB
  have hshapeNext : L3.EWord.ValidationShape ring root
      (bankWordEpochNext ring root z root).2.1 g := by
    change L3.EWord.ValidationShape ring root
      (phiW ring z.2.1 root) g
    have h := L3.EWord.validationCoveredRootDoneDoneClass
      ring root z.2.1 g hshape hfixed hno hrootB hout hchildB
    rw [hghost] at h
    exact h
  refine ⟨g, req, stamp, hshapeNext, ?_⟩
  intro k hk
  have hsiteSer :
      ((bankWordEpochNext ring root z root).2.1
        (L3.EWord.site ring root k.val)).ser =
      (z.2.1 (L3.EWord.site ring root k.val)).ser := by
    by_cases hrootSite : L3.EWord.site ring root k.val = root
    · rw [hrootSite]
      exact hrootSer
    · by_cases hchildSite :
          L3.EWord.site ring root k.val =
            ring.rightNeighbor root
      · rw [hchildSite]
        exact hchildSer
      · change ((phiW ring z.2.1 root)
          (L3.EWord.site ring root k.val)).ser =
          (z.2.1 (L3.EWord.site ring root k.val)).ser
        exact phiW_ser_remote ring z.2.1 root
          (L3.EWord.site ring root k.val)
          hrootSite hchildSite
  have hsiteTicket :
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z root)).validation
          (L3.EWord.site ring root k.val) =
      (bankWordHardEpochLedger ring root z).validation
          (L3.EWord.site ring root k.val) := by
    by_cases hrootSite : L3.EWord.site ring root k.val = root
    · rw [hrootSite]
      exact hrootTicket
    · by_cases hchildSite :
          L3.EWord.site ring root k.val =
            ring.rightNeighbor root
      · rw [hchildSite]
        exact hchildTicket
      · exact bankWordRenewalFrontierWaveTicketRemoteFrame
          ring root z root (L3.EWord.site ring root k.val)
          hrootSite hchildSite
  obtain ⟨hB, hP, hI, hL, hF⟩ := hsites k hk
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hnew
    have hold :
        (z.2.1 (L3.EWord.site ring root k.val)).ser.phase = .B ∧
        (z.2.1 (L3.EWord.site ring root k.val)).ser.wphase =
          .VALIDATING := by
      simpa only [hsiteSer] using hnew
    have ht := hB hold
    simpa only [BankWordRenewalFrontierWaveSiteTicket,
      hsiteSer, hsiteTicket] using ht
  · intro hnew
    have hold :
        (z.2.1 (L3.EWord.site ring root k.val)).ser.phase = .C ∧
        (z.2.1 (L3.EWord.site ring root k.val)).ser.probe =
          .PENDING ∧
        (z.2.1 (L3.EWord.site ring root k.val)).ser.wphase =
          .VALIDATING := by
      simpa only [hsiteSer] using hnew
    have ht := hP hold
    simpa only [BankWordRenewalFrontierWaveSiteTicket,
      hsiteSer, hsiteTicket] using ht
  · intro hnew
    have hold :
        (z.2.1 (L3.EWord.site ring root k.val)).ser.phase = .C ∧
        (z.2.1 (L3.EWord.site ring root k.val)).ser.probe =
          .INTERNAL_OK ∧
        (z.2.1 (L3.EWord.site ring root k.val)).ser.wphase =
          .VALIDATING := by
      simpa only [hsiteSer] using hnew
    have ht := hI hold
    simpa only [BankWordRenewalFrontierWaveSiteTicket,
      hsiteSer, hsiteTicket] using ht
  · intro hnew
    have hold :
        (z.2.1 (L3.EWord.site ring root k.val)).ser.phase = .C ∧
        (z.2.1 (L3.EWord.site ring root k.val)).ser.probe =
          .LEAF_OK := by
      simpa only [hsiteSer] using hnew
    have ht := hL hold
    simpa only [BankWordRenewalFrontierWaveSiteTicket,
      hsiteSer, hsiteTicket] using ht
  · intro hnew
    have hold :
        (z.2.1 (L3.EWord.site ring root k.val)).ser.phase = .F ∧
        g.stage = .returning ∧ g.pivot ≤ k.val := by
      simpa only [hsiteSer] using hnew
    have ht := hF hold
    simpa only [BankWordRenewalFrontierWaveSiteTicket,
      hsiteSer, hsiteTicket] using ht

end L3.RenewalReferenceClock



namespace L3.RenewalReferenceClock

open Classical
set_option autoImplicit false
set_option Elab.async false

/-- At a covered, physically VALIDATING terminal C/PENDING source,
the old full J-W witness supplies both the DONE root parent and the
PENDING last child with the same two stamps. The actual S5 receipt
therefore writes an observedLeaf descendant, rather than accepting a
merely physical LEAF_OK. The all-shapes scrub=n guard is explicit:
an unvisited inherited C/PENDING is not part of this claim.
Consumer: active incoming S5 terminal join in J-W, paper leaf seam. -/
theorem bankWordRenewalWaveRootIncomingCoveredLeafStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hwave : BankWordRenewalFrontierWaveLineage ring root z)
    (hactive : (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)
    (hseam : e = L3.EWord.site ring root (n - 1))
    (hcovered : ∀ g : L3.EWord.ValidationGhost,
      L3.EWord.ValidationShape ring root z.2.1 g →
        g.scrub = n)
    (hsourceC : (z.2.1 e).ser.phase = .C)
    (hsourcePending : (z.2.1 e).ser.probe = .PENDING)
    (hsourceValid : (z.2.1 e).ser.wphase = .VALIDATING) :
    ∃ req stamp : Nat,
      BankWordRenewalFrontierWaveSiteTicket ring root
        (bankWordEpochNext ring root z e) req stamp
        (⟨n - 1, (show n - 1 < n by omega)⟩ : Fin n)
        .observedLeaf := by
  obtain ⟨g, req, stamp, hshape, hsites⟩ := hwave.2 hactive
  have hscrub : g.scrub = n := hcovered g hshape
  have hforward : L3.EWord.ForwardShape ring root z.2.1 g := by
    rcases hshape.stageShape with hf | hr
    · exact hf
    · by_cases hpivot : g.pivot = n - 1
      · have hlastF : (z.2.1 e).ser.phase = .F := by
          rw [hseam]
          have h := hr.leftmostF
          rw [hpivot] at h
          exact h
        rw [hsourceC] at hlastF
        cases hlastF
      · have hlt : g.pivot < n - 1 := by
          have := hr.pivotBound
          omega
        have hlast := hr.suffix
          (⟨n - 1, (show n - 1 < n by omega)⟩ : Fin n) hlt
        rcases hlast with hf | hc
        · have hlastF : (z.2.1 e).ser.phase = .F := by
            rw [hseam]
            exact hf.1
          rw [hsourceC] at hlastF
          cases hlastF
        · have hlastOff : (z.2.1 e).ser.wphase = .OFF := by
            rw [hseam]
            exact hc.2
          rw [hsourceValid] at hlastOff
          cases hlastOff
  have hpivotPositive : 0 < g.pivot := by
    rcases hforward.currentObligation with hnew | hwait
    · exact hnew.1
    · have heq := hwait.2.1
      omega
  have hdoneRoot := hforward.completed
    (⟨0, (show 0 < n by omega)⟩ : Fin n)
    (by omega)
  have houtDone : (z.2.1 root).ser.out = .DONE := by
    simpa only [L3.EWord.siteZero] using hdoneRoot.2.1
  have hrootOld :
      BankWordRenewalFrontierWaveSiteTicket ring root z
        req stamp (⟨0, (show 0 < n by omega)⟩ : Fin n)
        .done := by
    have hraw := (hsites
      (⟨0, (show 0 < n by omega)⟩ : Fin n)
      (by rw [hscrub]; omega)).1
        ⟨hdoneRoot.1, hdoneRoot.2.2⟩
    simpa [L3.EWord.siteZero, houtDone] using hraw
  obtain ⟨parent, htDone, hpReq, hpStamp⟩ := hrootOld
  have hparent : wParentTicket
      ((bankWordHardEpochLedger ring root z).validation root) =
        some parent := by
    have htDone' : wTicketAt .done
        ((bankWordHardEpochLedger ring root z).validation root) =
          some parent := by
      simpa only [L3.EWord.siteZero] using htDone
    cases ht : (bankWordHardEpochLedger ring root z).validation root with
    | none =>
        simp [wTicketAt, ht] at htDone'
    | some t =>
        by_cases hd : t.stage = .done
        · have heq : t = parent := by
            simpa [wTicketAt, ht, hd] using htDone'
          subst t
          simp [wParentTicket, ht, hd]
        · simp [wTicketAt, ht, hd] at htDone'
  have hlastState :
      (z.2.1 (L3.EWord.site ring root (n - 1))).ser.phase = .C ∧
      (z.2.1 (L3.EWord.site ring root (n - 1))).ser.probe =
        .PENDING ∧
      (z.2.1 (L3.EWord.site ring root (n - 1))).ser.wphase =
        .VALIDATING := by
    rw [← hseam]
    exact ⟨hsourceC, hsourcePending, hsourceValid⟩
  have hlastOld :
      BankWordRenewalFrontierWaveSiteTicket ring root z
        req stamp
        (⟨n - 1, (show n - 1 < n by omega)⟩ : Fin n)
        .pending :=
    (hsites
      (⟨n - 1, (show n - 1 < n by omega)⟩ : Fin n)
      (by rw [hscrub]; omega)).2.1 hlastState
  obtain ⟨child, htPending, hcReq, hcStamp⟩ := hlastOld
  have hchild : wTicketAt .pending
      ((bankWordHardEpochLedger ring root z).validation e) =
        some child := by
    simpa only [← hseam] using htPending
  have hrequestedSame :
      parent.requestedAt = child.requestedAt :=
    hpReq.trans hcReq.symm
  have hstartedSame :
      parent.startedAt = child.startedAt :=
    hpStamp.trans hcStamp.symm
  have hwrite := bankWordRenewalWaveRootIncomingLeafStep
    ring root e s hn hbank hs z hz
    (L3.EWord.validationSeamNeighbor ring root e hseam)
    hactive.1 hsourceC hsourcePending parent child
    hparent hchild hrequestedSame hstartedSame
  refine ⟨req, stamp, ?_⟩
  unfold BankWordRenewalFrontierWaveSiteTicket
  refine ⟨{ parent with stage := .observedLeaf }, ?_, ?_, ?_⟩
  · rw [← hseam, hwrite]
    rfl
  · exact hpReq
  · exact hpStamp

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open Classical
set_option autoImplicit false
set_option Elab.async false

/-- If the current EWord scrub prefix ends before the incoming
root seam, S5 preserves every historical validation ticket
actually required by that prefix, as well as its entire EWord
physical shape. The final, unvisited site is deliberately not
claimed to have a pending ticket. Consumer: the short-prefix
branch of bankWordRenewalWaveRootIncomingStep, J-W. -/
theorem bankWordRenewalWaveRootIncomingShortCoveredFrameStep
    {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hpred : ring.rightNeighbor e = root)
    (g : L3.EWord.ValidationGhost)
    (hshape : L3.EWord.ValidationShape ring root z.2.1 g)
    (hshort : g.scrub < n) :
    L3.EWord.ValidationShape ring root
      (bankWordEpochNext ring root z e).2.1 g ∧
    ∀ k : Fin n, k.val < g.scrub →
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z e)).validation
          (L3.EWord.site ring root k.val) =
      (bankWordHardEpochLedger ring root z).validation
          (L3.EWord.site ring root k.val) := by
  have hframe := bankWordRenewalWaveRootIncomingActiveFrameStep
    ring root e s hn hbank hs z hz hpred g hshape
  refine ⟨hframe.1, ?_⟩
  intro k hk
  exact hframe.2.2 k hk (by omega)

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open Classical
set_option autoImplicit false
set_option Elab.async false

/-- In a real EWord shape, a VALIDATING terminal C cannot
belong to the return suffix: its last site is F or C/OFF.
Thus the selected full-coverage S5 pending observation belongs
to the forward stage. Consumer: covered-forward incoming S5 join. -/
theorem bankWordRenewalWaveRootIncomingPendingForwardShape
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root e : Fin n)
    (p : Fin n → ProjW c)
    (g : L3.EWord.ValidationGhost)
    (hshape : L3.EWord.ValidationShape ring root p g)
    (hseam : e = L3.EWord.site ring root (n - 1))
    (hsourceC : (p e).ser.phase = .C)
    (hsourceValid : (p e).ser.wphase = .VALIDATING) :
    L3.EWord.ForwardShape ring root p g := by
  rcases hshape.stageShape with hf | hr
  · exact hf
  · by_cases hpivot : g.pivot = n - 1
    · have hlastF : (p e).ser.phase = .F := by
        have h := hr.leftmostF
        rw [hpivot] at h
        simpa only [← hseam] using h
      rw [hsourceC] at hlastF
      cases hlastF
    · have hlt : g.pivot < n - 1 := by
        have hbound := hr.pivotBound
        omega
      have hlast := hr.suffix
        (⟨n - 1, (show n - 1 < n by omega)⟩ : Fin n) hlt
      rcases hlast with hf | hc
      · have hlastF : (p e).ser.phase = .F := by
          simpa only [← hseam] using hf.1
        rw [hsourceC] at hlastF
        cases hlastF
      · have hlastOff : (p e).ser.wphase = .OFF := by
          simpa only [← hseam] using hc.2
        rw [hsourceValid] at hlastOff
        cases hlastOff

/-- Covered forward incoming S5: use the SAME ValidationGhost
selected from the OLD WaveLineage, rather than a global
forall-shapes coverage hypothesis. Its visited root DONE and
last-child PENDING tickets supply one matching requested/start
pair, hence S5 records a real observedLeaf receipt.
Consumer: covered-forward case of the root incoming J-W step,
repair.tex R10a leaf seam. -/
theorem bankWordRenewalWaveRootIncomingSelectedForwardLeafStep
    {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hwave : BankWordRenewalFrontierWaveLineage ring root z)
    (hactive : (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)
    (hseam : e = L3.EWord.site ring root (n - 1))
    (hcovered :
      (Classical.choose (hwave.2 hactive)).scrub = n)
    (hsourceC : (z.2.1 e).ser.phase = .C)
    (hsourcePending : (z.2.1 e).ser.probe = .PENDING)
    (hsourceValid : (z.2.1 e).ser.wphase = .VALIDATING) :
    ∃ req stamp : Nat,
      BankWordRenewalFrontierWaveSiteTicket ring root
        (bankWordEpochNext ring root z e) req stamp
        (⟨n - 1, (show n - 1 < n by omega)⟩ : Fin n)
        .observedLeaf := by
  obtain ⟨req, stamp, hshape, hsites⟩ :=
    Classical.choose_spec (hwave.2 hactive)
  have hforward :
      L3.EWord.ForwardShape ring root z.2.1
        (Classical.choose (hwave.2 hactive)) :=
    bankWordRenewalWaveRootIncomingPendingForwardShape
      ring root e z.2.1
      (Classical.choose (hwave.2 hactive))
      hshape hseam hsourceC hsourceValid
  have hpivotPositive :
      0 < (Classical.choose (hwave.2 hactive)).pivot := by
    rcases hforward.currentObligation with hnew | hwait
    · exact hnew.1
    · have hbalance := hwait.2.1
      omega
  have hdoneRoot := hforward.completed
    (⟨0, (show 0 < n by omega)⟩ : Fin n) hpivotPositive
  have houtDone : (z.2.1 root).ser.out = .DONE := by
    simpa only [L3.EWord.siteZero] using hdoneRoot.2.1
  have hrootOld :
      BankWordRenewalFrontierWaveSiteTicket ring root z
        req stamp (⟨0, (show 0 < n by omega)⟩ : Fin n)
        .done := by
    have hraw := (hsites
      (⟨0, (show 0 < n by omega)⟩ : Fin n)
      (by rw [hcovered]; omega)).1
      ⟨hdoneRoot.1, hdoneRoot.2.2⟩
    simpa [L3.EWord.siteZero, houtDone] using hraw
  obtain ⟨parent, htDone, hpReq, hpStamp⟩ := hrootOld
  have hparent : wParentTicket
      ((bankWordHardEpochLedger ring root z).validation root) =
        some parent := by
    have htDone' : wTicketAt .done
        ((bankWordHardEpochLedger ring root z).validation root) =
          some parent := by
      simpa only [L3.EWord.siteZero] using htDone
    cases ht :
        (bankWordHardEpochLedger ring root z).validation root with
    | none =>
        simp [wTicketAt, ht] at htDone'
    | some t =>
        by_cases hd : t.stage = .done
        · have heq : t = parent := by
            simpa [wTicketAt, ht, hd] using htDone'
          subst t
          simp [wParentTicket, ht, hd]
        · simp [wTicketAt, ht, hd] at htDone'
  have hlastState :
      (z.2.1 (L3.EWord.site ring root (n - 1))).ser.phase = .C ∧
      (z.2.1 (L3.EWord.site ring root (n - 1))).ser.probe =
        .PENDING ∧
      (z.2.1 (L3.EWord.site ring root (n - 1))).ser.wphase =
        .VALIDATING := by
    rw [← hseam]
    exact ⟨hsourceC, hsourcePending, hsourceValid⟩
  have hlastOld :
      BankWordRenewalFrontierWaveSiteTicket ring root z
        req stamp
        (⟨n - 1, (show n - 1 < n by omega)⟩ : Fin n)
        .pending :=
    (hsites
      (⟨n - 1, (show n - 1 < n by omega)⟩ : Fin n)
      (by rw [hcovered]; omega)).2.1 hlastState
  obtain ⟨child, htPending, hcReq, hcStamp⟩ := hlastOld
  have hchild : wTicketAt .pending
      ((bankWordHardEpochLedger ring root z).validation e) =
        some child := by
    simpa only [← hseam] using htPending
  have hreqSame : parent.requestedAt = child.requestedAt :=
    hpReq.trans hcReq.symm
  have hstampSame : parent.startedAt = child.startedAt :=
    hpStamp.trans hcStamp.symm
  have hwrite := bankWordRenewalWaveRootIncomingLeafStep
    ring root e s hn hbank hs z hz
    (L3.EWord.validationSeamNeighbor ring root e hseam)
    hactive.1 hsourceC hsourcePending parent child
    hparent hchild hreqSame hstampSame
  refine ⟨req, stamp, ?_⟩
  unfold BankWordRenewalFrontierWaveSiteTicket
  refine ⟨{ parent with stage := .observedLeaf }, ?_, hpReq, hpStamp⟩
  rw [← hseam, hwrite]
  rfl

end L3.RenewalReferenceClock


namespace L3.RenewalReferenceClock

open Classical
set_option autoImplicit false
set_option Elab.async false


/-- A physically returned wave has last site F or C/OFF. If its
C suffix does not carry the exceptional stale PENDING probe,
the actual incoming S5 preserves the historical terminal ticket
exactly. This uses the literal old-pair wValidationPair and the
real chronological bankWordEpochNext, not EWord physical transport
alone. Consumer: guarded RETURN branch of the incoming J-W step;
the C/OFF/PENDING exclusion remains a separate causal obligation. -/
theorem bankWordRenewalWaveRootIncomingReturnNonpendingTicketStep
    {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hpred : ring.rightNeighbor e = root)
    (hrun : (z.2.1 root).ser.cert = .RUNNING)
    (g : L3.EWord.ValidationGhost)
    (hreturn : L3.EWord.ReturnShape ring root z.2.1 g)
    (hseam : e = L3.EWord.site ring root (n - 1))
    (hquiet :
      (z.2.1 e).ser.phase = .C →
        (z.2.1 e).ser.probe ≠ .PENDING) :
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).validation e =
      (bankWordHardEpochLedger ring root z).validation e := by
  have hphase :
      (z.2.1 e).ser.phase = .F ∨
      (z.2.1 e).ser.phase = .C := by
    by_cases hpivot : g.pivot = n - 1
    · left
      have hf := hreturn.leftmostF
      rw [hpivot] at hf
      simpa only [← hseam] using hf
    · have hlt : g.pivot < n - 1 := by
        have hbound := hreturn.pivotBound
        omega
      have hlast := hreturn.suffix
        (⟨n - 1, (show n - 1 < n by omega)⟩ : Fin n) hlt
      rcases hlast with hf | hc
      · left
        simpa only [← hseam] using hf.1
      · right
        simpa only [← hseam] using hc.1
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass e).2
  have hpost := clockPostIncoming ring root z.2.1 e
    (by omega : 2 ≤ n) hfixed hpred
  have hnotIdle :
      (z.2.1 (ring.rightNeighbor e)).ser.cert ≠ .IDLE := by
    rw [hpred, hrun]
    decide
  have hrow :
      (serW (z.2.1 e)
        (z.2.1 (ring.rightNeighbor e))).row = "S5" :=
    (serRootIncomingNonidle
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      hpost.1 hpost.2 hnotIdle).1
  have hpair :
      (wValidationPair (z.2.2.clock + 1)
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        ((bankWordHardEpochLedger ring root z).validation e)
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor e))).1 =
        (bankWordHardEpochLedger ring root z).validation e := by
    rcases hphase with hf | hc
    · simp [wValidationPair, hrow, hf]
    · have hp : (z.2.1 e).ser.probe ≠ .PENDING := hquiet hc
      simp [wValidationPair, hrow, hc, hp]
  rw [bankWordHardEpochLedgerNext]
  change (if e = e then
      (wValidationPair (z.2.2.clock + 1)
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        ((bankWordHardEpochLedger ring root z).validation e)
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor e))).1
    else if e = ring.rightNeighbor e then
      (wValidationPair (z.2.2.clock + 1)
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        ((bankWordHardEpochLedger ring root z).validation e)
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor e))).2
    else (bankWordHardEpochLedger ring root z).validation e) =
      (bankWordHardEpochLedger ring root z).validation e
  exact (if_pos rfl).trans hpair

/-- On the same RETURN seam, F is untouched and C with a
non-PENDING probe is untouched by literal S5. This is stronger
than the EWord ReturnShape grammar, which checks only phase and
wphase at a C suffix. Consumer: historical/physical site-frame
assembly for the guarded root incoming RETURN branch of J-W. -/
theorem bankWordRenewalWaveRootIncomingReturnNonpendingSerializerStep
    {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hpred : ring.rightNeighbor e = root)
    (hrun : (z.2.1 root).ser.cert = .RUNNING)
    (g : L3.EWord.ValidationGhost)
    (hreturn : L3.EWord.ReturnShape ring root z.2.1 g)
    (hseam : e = L3.EWord.site ring root (n - 1))
    (hquiet :
      (z.2.1 e).ser.phase = .C →
        (z.2.1 e).ser.probe ≠ .PENDING) :
    ((bankWordEpochNext ring root z e).2.1 e).ser =
      (z.2.1 e).ser := by
  have hphase :
      (z.2.1 e).ser.phase = .F ∨
      (z.2.1 e).ser.phase = .C := by
    by_cases hpivot : g.pivot = n - 1
    · left
      have hf := hreturn.leftmostF
      rw [hpivot] at hf
      simpa only [← hseam] using hf
    · have hlt : g.pivot < n - 1 := by
        have hbound := hreturn.pivotBound
        omega
      have hlast := hreturn.suffix
        (⟨n - 1, (show n - 1 < n by omega)⟩ : Fin n) hlt
      rcases hlast with hf | hc
      · left
        simpa only [← hseam] using hf.1
      · right
        simpa only [← hseam] using hc.1
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass e).2
  have hpost := clockPostIncoming ring root z.2.1 e
    (by omega : 2 ≤ n) hfixed hpred
  have hnotIdle :
      (z.2.1 (ring.rightNeighbor e)).ser.cert ≠ .IDLE := by
    rw [hpred, hrun]
    decide
  change ((phiW ring z.2.1 e) e).ser = (z.2.1 e).ser
  rw [phiW_ser_source]
  rcases hphase with hf | hc
  · exact L3.EWord.validationSeamFSer
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      hpost.1 hpost.2
      (by simpa only [hpred] using hrun) hf
  · have hp : (z.2.1 e).ser.probe ≠ .PENDING :=
      hquiet hc
    cases hprobe : (z.2.1 e).ser.probe with
    | NONE =>
        simp [serW, serializerStep, ProjW.lift,
          hpost.1, hpost.2, hnotIdle, hc, hprobe]
    | PENDING =>
        exact False.elim (hp hprobe)
    | INTERNAL_OK =>
        simp [serW, serializerStep, ProjW.lift,
          hpost.1, hpost.2, hnotIdle, hc, hprobe]
    | LEAF_OK =>
        simp [serW, serializerStep, ProjW.lift,
          hpost.1, hpost.2, hnotIdle, hc, hprobe]


/-- Full covered RETURN wave-lineage transport on the actual
incoming-root S5 edge, conditional only on exclusion of the
C/OFF/PENDING terminal-probe hazard. The OLD chosen g, req and
stamp remain unchanged; all five covered-site clauses are
transported by real serializer/ticket frames, including the
returned F suffix. Consumer: RETURN arm of the proposed
bankWordRenewalWaveRootIncomingStep (once hquiet is derived
from reachable wave provenance). -/
theorem bankWordRenewalWaveRootIncomingGuardedReturnStep
    {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hpred : ring.rightNeighbor e = root)
    (hwave : BankWordRenewalFrontierWaveLineage ring root z)
    (hactive : (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)
    (hreturn :
      L3.EWord.ReturnShape ring root z.2.1
        (Classical.choose (hwave.2 hactive)))
    (hquiet :
      (z.2.1 e).ser.phase = .C →
        (z.2.1 e).ser.probe ≠ .PENDING) :
    BankWordRenewalFrontierWaveLineage ring root
      (bankWordEpochNext ring root z e) := by
  obtain ⟨req, stamp, hshape, hsites⟩ :=
    Classical.choose_spec (hwave.2 hactive)
  have hinj : Function.Injective ring.rightNeighbor := by
    intro a b hab
    apply Fin.ext
    have hv := congrArg Fin.val hab
    change (a.val + 1) % n = (b.val + 1) % n at hv
    by_cases ha : a.val + 1 < n
    · by_cases hb : b.val + 1 < n
      · rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv
        omega
      · have hbeq : b.val + 1 = n := by omega
        rw [Nat.mod_eq_of_lt ha, hbeq, Nat.mod_self] at hv
        omega
    · have haeq : a.val + 1 = n := by omega
      by_cases hb : b.val + 1 < n
      · rw [haeq, Nat.mod_self, Nat.mod_eq_of_lt hb] at hv
        omega
      · omega
  have hseam : e = L3.EWord.site ring root (n - 1) := by
    apply hinj
    rw [hpred]
    exact (L3.EWord.validationSeamNeighbor ring root
      (L3.EWord.site ring root (n - 1)) rfl).symm
  have hframe := bankWordRenewalWaveRootIncomingActiveFrameStep
    ring root e s hn hbank hs z hz hpred
    (Classical.choose (hwave.2 hactive)) hshape
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass e).2
  have hpost := clockPostIncoming ring root z.2.1 e
    (by omega : 2 ≤ n) hfixed hpred
  have hearly := L3.EWord.validationSeamEarlySer
    ring root z.2.1 e (by omega : 3 ≤ n)
    hseam hpost.1 hpost.2
    (by simpa only [hpred] using hactive.1)
  have hrootSer :
      ((bankWordEpochNext ring root z e).2.1 root).ser =
        (z.2.1 root).ser := by
    change ((phiW ring z.2.1 e) root).ser =
      (z.2.1 root).ser
    simpa only [L3.EWord.siteZero] using
      (hearly 0 (by omega))
  have hchildSer :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor root)).ser =
        (z.2.1 (ring.rightNeighbor root)).ser := by
    change ((phiW ring z.2.1 e)
      (ring.rightNeighbor root)).ser =
      (z.2.1 (ring.rightNeighbor root)).ser
    simpa only [L3.EWord.siteOne] using
      (hearly 1 (by omega))
  have hrootTicket :
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z e)).validation root =
        (bankWordHardEpochLedger ring root z).validation root :=
    hframe.2.1
  have hchildTicket :
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z e)).validation
          (ring.rightNeighbor root) =
        (bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor root) := by
    have ht := hframe.2.2
      (⟨1, (show 1 < n by omega)⟩ : Fin n)
      (by have hlo := hshape.lower; try simp only [Fin.val_mk]; omega)
      (by try simp only [Fin.val_mk]; omega)
    simpa only [L3.EWord.siteOne] using ht
  have hsourceSer :=
    bankWordRenewalWaveRootIncomingReturnNonpendingSerializerStep
      ring root e s hn hbank hs z hz hpred hactive.1
      (Classical.choose (hwave.2 hactive))
      hreturn hseam hquiet
  have hsourceTicket :=
    bankWordRenewalWaveRootIncomingReturnNonpendingTicketStep
      ring root e s hn hbank hs z hz hpred hactive.1
      (Classical.choose (hwave.2 hactive))
      hreturn hseam hquiet
  have hsiteSer (k : Fin n) :
      ((bankWordEpochNext ring root z e).2.1
        (L3.EWord.site ring root k.val)).ser =
      (z.2.1 (L3.EWord.site ring root k.val)).ser := by
    by_cases hlast : k.val = n - 1
    · have hsite :
          L3.EWord.site ring root k.val = e := by
        rw [hlast]
        exact hseam.symm
      rw [hsite]
      exact hsourceSer
    · have hkearly : k.val + 1 < n := by
        have hkBound := k.isLt
        omega
      change ((phiW ring z.2.1 e)
        (L3.EWord.site ring root k.val)).ser =
        (z.2.1 (L3.EWord.site ring root k.val)).ser
      exact hearly k.val hkearly
  have hsiteTicket (k : Fin n)
      (hk : k.val < (Classical.choose (hwave.2 hactive)).scrub) :
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z e)).validation
          (L3.EWord.site ring root k.val) =
      (bankWordHardEpochLedger ring root z).validation
          (L3.EWord.site ring root k.val) := by
    by_cases hlast : k.val = n - 1
    · have hsite :
          L3.EWord.site ring root k.val = e := by
        rw [hlast]
        exact hseam.symm
      rw [hsite]
      exact hsourceTicket
    · exact hframe.2.2 k hk hlast
  obtain ⟨hrequested, hpending, hdone⟩ := hwave.1
  have hbase : BankWordRenewalFrontierTicketLineage ring root
      (bankWordEpochNext ring root z e) := by
    unfold BankWordRenewalFrontierTicketLineage
    refine ⟨?_, ?_, ?_⟩
    · intro hnew
      rw [hrootSer, hactive.1] at hnew
      cases hnew
    · intro hnew
      have hold :
          (z.2.1 root).ser.cert = .RUNNING ∧
          (z.2.1 root).ser.wphase = .VALIDATING ∧
          (z.2.1 root).ser.phase = .B ∧
          (z.2.1 root).ser.out = .WAIT ∧
          (z.2.1 (ring.rightNeighbor root)).ser.phase = .C ∧
          (z.2.1 (ring.rightNeighbor root)).ser.probe =
            .PENDING := by
        simpa only [hrootSer, hchildSer] using hnew
      obtain ⟨parent, child, hp, hc, hr, hs⟩ := hpending hold
      refine ⟨parent, child, ?_, ?_, hr, hs⟩
      · rw [hrootTicket]
        exact hp
      · rw [hchildTicket]
        exact hc
    · intro hnew
      have hold :
          (z.2.1 root).ser.cert = .RUNNING ∧
          (z.2.1 root).ser.wphase = .VALIDATING ∧
          (z.2.1 root).ser.phase = .B ∧
          (z.2.1 root).ser.out = .DONE ∧
          (z.2.1 (ring.rightNeighbor root)).ser.phase = .F := by
        simpa only [hrootSer, hchildSer] using hnew
      obtain ⟨parent, child, hp, hc, hr, hs⟩ := hdone hold
      refine ⟨parent, child, ?_, ?_, hr, hs⟩
      · rw [hrootTicket]
        exact hp
      · rw [hchildTicket]
        exact hc
  refine ⟨hbase, ?_⟩
  intro _
  refine ⟨Classical.choose (hwave.2 hactive),
    req, stamp, hframe.1, ?_⟩
  intro k hk
  have hser := hsiteSer k
  have ht := hsiteTicket k hk
  obtain ⟨hB, hP, hI, hL, hF⟩ := hsites k hk
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hnew
    have hold :
        (z.2.1 (L3.EWord.site ring root k.val)).ser.phase = .B ∧
        (z.2.1 (L3.EWord.site ring root k.val)).ser.wphase =
          .VALIDATING := by
      simpa only [hser] using hnew
    have hticket := hB hold
    simpa only [BankWordRenewalFrontierWaveSiteTicket,
      hser, ht] using hticket
  · intro hnew
    have hold :
        (z.2.1 (L3.EWord.site ring root k.val)).ser.phase = .C ∧
        (z.2.1 (L3.EWord.site ring root k.val)).ser.probe =
          .PENDING ∧
        (z.2.1 (L3.EWord.site ring root k.val)).ser.wphase =
          .VALIDATING := by
      simpa only [hser] using hnew
    have hticket := hP hold
    simpa only [BankWordRenewalFrontierWaveSiteTicket,
      hser, ht] using hticket
  · intro hnew
    have hold :
        (z.2.1 (L3.EWord.site ring root k.val)).ser.phase = .C ∧
        (z.2.1 (L3.EWord.site ring root k.val)).ser.probe =
          .INTERNAL_OK ∧
        (z.2.1 (L3.EWord.site ring root k.val)).ser.wphase =
          .VALIDATING := by
      simpa only [hser] using hnew
    have hticket := hI hold
    simpa only [BankWordRenewalFrontierWaveSiteTicket,
      hser, ht] using hticket
  · intro hnew
    have hold :
        (z.2.1 (L3.EWord.site ring root k.val)).ser.phase = .C ∧
        (z.2.1 (L3.EWord.site ring root k.val)).ser.probe =
          .LEAF_OK := by
      simpa only [hser] using hnew
    have hticket := hL hold
    simpa only [BankWordRenewalFrontierWaveSiteTicket,
      hser, ht] using hticket
  · intro hnew
    have hold :
        (z.2.1 (L3.EWord.site ring root k.val)).ser.phase = .F ∧
        (Classical.choose (hwave.2 hactive)).stage = .returning ∧
        (Classical.choose (hwave.2 hactive)).pivot ≤ k.val := by
      simpa only [hser] using hnew
    have hticket := hF hold
    simpa only [BankWordRenewalFrontierWaveSiteTicket,
      hser, ht] using hticket


/-- The two OLD covered wave tickets (DONE root, PENDING
terminal child) with one common req/stamp are sufficient for
the real incoming S5 to write an observedLeaf ticket for that
SAME wave. Unlike an existential-leaf conclusion, this fixes
the stamps used by the consumer's entire five-clause J-W fold.
Consumer: full covered-forward incoming-root WaveLineage step. -/
theorem bankWordRenewalWaveRootIncomingSameWaveLeafStep
    {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hpred : ring.rightNeighbor e = root)
    (hseam : e = L3.EWord.site ring root (n - 1))
    (hrun : (z.2.1 root).ser.cert = .RUNNING)
    (hsourceC : (z.2.1 e).ser.phase = .C)
    (hsourcePending : (z.2.1 e).ser.probe = .PENDING)
    (req stamp : Nat)
    (hrootOld : BankWordRenewalFrontierWaveSiteTicket
      ring root z req stamp
      (⟨0, (show 0 < n by omega)⟩ : Fin n) .done)
    (hlastOld : BankWordRenewalFrontierWaveSiteTicket
      ring root z req stamp
      (⟨n - 1, (show n - 1 < n by omega)⟩ : Fin n)
      .pending) :
    BankWordRenewalFrontierWaveSiteTicket ring root
      (bankWordEpochNext ring root z e) req stamp
      (⟨n - 1, (show n - 1 < n by omega)⟩ : Fin n)
      .observedLeaf := by
  obtain ⟨parent, htDone, hpReq, hpStamp⟩ := hrootOld
  have hparent : wParentTicket
      ((bankWordHardEpochLedger ring root z).validation root) =
        some parent := by
    have htDone' : wTicketAt .done
        ((bankWordHardEpochLedger ring root z).validation root) =
          some parent := by
      simpa only [L3.EWord.siteZero] using htDone
    cases ht :
        (bankWordHardEpochLedger ring root z).validation root with
    | none =>
        simp [wTicketAt, ht] at htDone'
    | some t =>
        by_cases hd : t.stage = .done
        · have heq : t = parent := by
            simpa [wTicketAt, ht, hd] using htDone'
          subst t
          simp [wParentTicket, ht, hd]
        · simp [wTicketAt, ht, hd] at htDone'
  obtain ⟨child, htPending, hcReq, hcStamp⟩ := hlastOld
  have hchild : wTicketAt .pending
      ((bankWordHardEpochLedger ring root z).validation e) =
        some child := by
    simpa only [← hseam] using htPending
  have hreqSame : parent.requestedAt = child.requestedAt :=
    hpReq.trans hcReq.symm
  have hstampSame : parent.startedAt = child.startedAt :=
    hpStamp.trans hcStamp.symm
  have hwrite := bankWordRenewalWaveRootIncomingLeafStep
    ring root e s hn hbank hs z hz hpred hrun
    hsourceC hsourcePending parent child
    hparent hchild hreqSame hstampSame
  unfold BankWordRenewalFrontierWaveSiteTicket
  refine ⟨{ parent with stage := .observedLeaf }, ?_, hpReq, hpStamp⟩
  rw [← hseam, hwrite]
  rfl


/-- Full five-site-clause transport for a covered FORWARD root
seam at an old C/PENDING/VALIDATING terminal. The same chosen
OLD g,req,stamp are preserved, with the new observedLeaf ticket
built by the real historical S5 join. Neither a global scrub=n
hypothesis nor a synthetic provenance reset is used.
Consumer: covered-forward arm of bankWordRenewalWaveRootIncomingStep. -/
theorem bankWordRenewalWaveRootIncomingCoveredForwardStep
    {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hpred : ring.rightNeighbor e = root)
    (hwave : BankWordRenewalFrontierWaveLineage ring root z)
    (hactive : (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)
    (hcovered :
      (Classical.choose (hwave.2 hactive)).scrub = n)
    (hsourceC : (z.2.1 e).ser.phase = .C)
    (hsourcePending : (z.2.1 e).ser.probe = .PENDING)
    (hsourceValid : (z.2.1 e).ser.wphase = .VALIDATING) :
    BankWordRenewalFrontierWaveLineage ring root
      (bankWordEpochNext ring root z e) := by
  obtain ⟨req, stamp, hshape, hsites⟩ :=
    Classical.choose_spec (hwave.2 hactive)
  have hinj : Function.Injective ring.rightNeighbor := by
    intro a b hab
    apply Fin.ext
    have hv := congrArg Fin.val hab
    change (a.val + 1) % n = (b.val + 1) % n at hv
    by_cases ha : a.val + 1 < n
    · by_cases hb : b.val + 1 < n
      · rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv
        omega
      · have hbeq : b.val + 1 = n := by omega
        rw [Nat.mod_eq_of_lt ha, hbeq, Nat.mod_self] at hv
        omega
    · have haeq : a.val + 1 = n := by omega
      by_cases hb : b.val + 1 < n
      · rw [haeq, Nat.mod_self, Nat.mod_eq_of_lt hb] at hv
        omega
      · omega
  have hseam : e = L3.EWord.site ring root (n - 1) := by
    apply hinj
    rw [hpred]
    exact (L3.EWord.validationSeamNeighbor ring root
      (L3.EWord.site ring root (n - 1)) rfl).symm
  have hforward : L3.EWord.ForwardShape ring root z.2.1
      (Classical.choose (hwave.2 hactive)) :=
    bankWordRenewalWaveRootIncomingPendingForwardShape
      ring root e z.2.1
      (Classical.choose (hwave.2 hactive))
      hshape hseam hsourceC hsourceValid
  have hpivotPositive :
      0 < (Classical.choose (hwave.2 hactive)).pivot := by
    rcases hforward.currentObligation with hnew | hwait
    · exact hnew.1
    · have hbalance := hwait.2.1
      omega
  have hdoneRoot := hforward.completed
    (⟨0, (show 0 < n by omega)⟩ : Fin n) hpivotPositive
  have houtDone : (z.2.1 root).ser.out = .DONE := by
    simpa only [L3.EWord.siteZero] using hdoneRoot.2.1
  have hrootOld :
      BankWordRenewalFrontierWaveSiteTicket ring root z
        req stamp (⟨0, (show 0 < n by omega)⟩ : Fin n)
        .done := by
    have hraw := (hsites
      (⟨0, (show 0 < n by omega)⟩ : Fin n)
      (by rw [hcovered]; omega)).1
      ⟨hdoneRoot.1, hdoneRoot.2.2⟩
    simpa [L3.EWord.siteZero, houtDone] using hraw
  have hlastState :
      (z.2.1 (L3.EWord.site ring root (n - 1))).ser.phase = .C ∧
      (z.2.1 (L3.EWord.site ring root (n - 1))).ser.probe =
        .PENDING ∧
      (z.2.1 (L3.EWord.site ring root (n - 1))).ser.wphase =
        .VALIDATING := by
    rw [← hseam]
    exact ⟨hsourceC, hsourcePending, hsourceValid⟩
  have hlastOld :
      BankWordRenewalFrontierWaveSiteTicket ring root z
        req stamp
        (⟨n - 1, (show n - 1 < n by omega)⟩ : Fin n)
        .pending :=
    (hsites
      (⟨n - 1, (show n - 1 < n by omega)⟩ : Fin n)
      (by rw [hcovered]; omega)).2.1 hlastState
  have hlastLeaf :=
    bankWordRenewalWaveRootIncomingSameWaveLeafStep
      ring root e s hn hbank hs z hz
      hpred hseam hactive.1 hsourceC hsourcePending
      req stamp hrootOld hlastOld
  have hframe := bankWordRenewalWaveRootIncomingActiveFrameStep
    ring root e s hn hbank hs z hz hpred
    (Classical.choose (hwave.2 hactive)) hshape
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass e).2
  have hpost := clockPostIncoming ring root z.2.1 e
    (by omega : 2 ≤ n) hfixed hpred
  have hearly := L3.EWord.validationSeamEarlySer
    ring root z.2.1 e (by omega : 3 ≤ n)
    hseam hpost.1 hpost.2
    (by simpa only [hpred] using hactive.1)
  have hleaf := L3.EWord.validationSeamLeafSerializer
    (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
    hpost.1 hpost.2
    (by simpa only [hpred] using hactive.1)
    hsourceC hsourcePending
  have hlastPhase :
      ((bankWordEpochNext ring root z e).2.1 e).ser.phase =
        .C := by
    change ((phiW ring z.2.1 e) e).ser.phase = .C
    rw [phiW_ser_source]
    exact hleaf.2.1
  have hlastProbe :
      ((bankWordEpochNext ring root z e).2.1 e).ser.probe =
        .LEAF_OK := by
    change ((phiW ring z.2.1 e) e).ser.probe = .LEAF_OK
    rw [phiW_ser_source]
    exact hleaf.2.2.1
  have hrootSer :
      ((bankWordEpochNext ring root z e).2.1 root).ser =
        (z.2.1 root).ser := by
    change ((phiW ring z.2.1 e) root).ser =
      (z.2.1 root).ser
    simpa only [L3.EWord.siteZero] using
      (hearly 0 (by omega))
  have hchildSer :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor root)).ser =
        (z.2.1 (ring.rightNeighbor root)).ser := by
    change ((phiW ring z.2.1 e)
      (ring.rightNeighbor root)).ser =
      (z.2.1 (ring.rightNeighbor root)).ser
    simpa only [L3.EWord.siteOne] using
      (hearly 1 (by omega))
  have hrootTicket :
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z e)).validation root =
        (bankWordHardEpochLedger ring root z).validation root :=
    hframe.2.1
  have hchildTicket :
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z e)).validation
          (ring.rightNeighbor root) =
        (bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor root) := by
    have ht := hframe.2.2
      (⟨1, (show 1 < n by omega)⟩ : Fin n)
      (by have hlo := hshape.lower; omega)
      (by try simp only [Fin.val_mk]; omega)
    simpa only [L3.EWord.siteOne] using ht
  obtain ⟨hrequested, hpending, hdone⟩ := hwave.1
  have hbase : BankWordRenewalFrontierTicketLineage ring root
      (bankWordEpochNext ring root z e) := by
    unfold BankWordRenewalFrontierTicketLineage
    refine ⟨?_, ?_, ?_⟩
    · intro hnew
      rw [hrootSer, hactive.1] at hnew
      cases hnew
    · intro hnew
      have hold :
          (z.2.1 root).ser.cert = .RUNNING ∧
          (z.2.1 root).ser.wphase = .VALIDATING ∧
          (z.2.1 root).ser.phase = .B ∧
          (z.2.1 root).ser.out = .WAIT ∧
          (z.2.1 (ring.rightNeighbor root)).ser.phase = .C ∧
          (z.2.1 (ring.rightNeighbor root)).ser.probe =
            .PENDING := by
        simpa only [hrootSer, hchildSer] using hnew
      obtain ⟨parent, child, hp, hc, hr, hs⟩ := hpending hold
      refine ⟨parent, child, ?_, ?_, hr, hs⟩
      · rw [hrootTicket]
        exact hp
      · rw [hchildTicket]
        exact hc
    · intro hnew
      have hold :
          (z.2.1 root).ser.cert = .RUNNING ∧
          (z.2.1 root).ser.wphase = .VALIDATING ∧
          (z.2.1 root).ser.phase = .B ∧
          (z.2.1 root).ser.out = .DONE ∧
          (z.2.1 (ring.rightNeighbor root)).ser.phase = .F := by
        simpa only [hrootSer, hchildSer] using hnew
      obtain ⟨parent, child, hp, hc, hr, hs⟩ := hdone hold
      refine ⟨parent, child, ?_, ?_, hr, hs⟩
      · rw [hrootTicket]
        exact hp
      · rw [hchildTicket]
        exact hc
  refine ⟨hbase, ?_⟩
  intro _
  refine ⟨Classical.choose (hwave.2 hactive),
    req, stamp, hframe.1, ?_⟩
  intro k hk
  by_cases hlast : k.val = n - 1
  · have hsite :
        L3.EWord.site ring root k.val = e := by
      rw [hlast]
      exact hseam.symm
    have hlastK :
        BankWordRenewalFrontierWaveSiteTicket ring root
          (bankWordEpochNext ring root z e) req stamp
          k .observedLeaf := by
      have hkeq :
          k = (⟨n - 1, (show n - 1 < n by omega)⟩ : Fin n) :=
        Fin.ext hlast
      rw [hkeq]
      exact hlastLeaf
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro hnew
      have hbad := hnew.1
      rw [hsite, hlastPhase] at hbad
      cases hbad
    · intro hnew
      have hbad := hnew.2.1
      rw [hsite, hlastProbe] at hbad
      cases hbad
    · intro hnew
      have hbad := hnew.2.1
      rw [hsite, hlastProbe] at hbad
      cases hbad
    · intro _
      exact hlastK
    · intro hnew
      have hbad := hnew.1
      rw [hsite, hlastPhase] at hbad
      cases hbad
  · have hkearly : k.val + 1 < n := by
      have hkBound := k.isLt
      omega
    have hsiteSer :
        ((bankWordEpochNext ring root z e).2.1
          (L3.EWord.site ring root k.val)).ser =
        (z.2.1 (L3.EWord.site ring root k.val)).ser := by
      change ((phiW ring z.2.1 e)
        (L3.EWord.site ring root k.val)).ser =
        (z.2.1 (L3.EWord.site ring root k.val)).ser
      exact hearly k.val hkearly
    have hsiteTicket := hframe.2.2 k hk hlast
    obtain ⟨hB, hP, hI, hL, hF⟩ := hsites k hk
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro hnew
      have hold :
          (z.2.1 (L3.EWord.site ring root k.val)).ser.phase = .B ∧
          (z.2.1 (L3.EWord.site ring root k.val)).ser.wphase =
            .VALIDATING := by
        simpa only [hsiteSer] using hnew
      have hticket := hB hold
      simpa only [BankWordRenewalFrontierWaveSiteTicket,
        hsiteSer, hsiteTicket] using hticket
    · intro hnew
      have hold :
          (z.2.1 (L3.EWord.site ring root k.val)).ser.phase = .C ∧
          (z.2.1 (L3.EWord.site ring root k.val)).ser.probe =
            .PENDING ∧
          (z.2.1 (L3.EWord.site ring root k.val)).ser.wphase =
            .VALIDATING := by
        simpa only [hsiteSer] using hnew
      have hticket := hP hold
      simpa only [BankWordRenewalFrontierWaveSiteTicket,
        hsiteSer, hsiteTicket] using hticket
    · intro hnew
      have hold :
          (z.2.1 (L3.EWord.site ring root k.val)).ser.phase = .C ∧
          (z.2.1 (L3.EWord.site ring root k.val)).ser.probe =
            .INTERNAL_OK ∧
          (z.2.1 (L3.EWord.site ring root k.val)).ser.wphase =
            .VALIDATING := by
        simpa only [hsiteSer] using hnew
      have hticket := hI hold
      simpa only [BankWordRenewalFrontierWaveSiteTicket,
        hsiteSer, hsiteTicket] using hticket
    · intro hnew
      have hold :
          (z.2.1 (L3.EWord.site ring root k.val)).ser.phase = .C ∧
          (z.2.1 (L3.EWord.site ring root k.val)).ser.probe =
            .LEAF_OK := by
        simpa only [hsiteSer] using hnew
      have hticket := hL hold
      simpa only [BankWordRenewalFrontierWaveSiteTicket,
        hsiteSer, hsiteTicket] using hticket
    · intro hnew
      have hold :
          (z.2.1 (L3.EWord.site ring root k.val)).ser.phase = .F ∧
          (Classical.choose (hwave.2 hactive)).stage = .returning ∧
          (Classical.choose (hwave.2 hactive)).pivot ≤ k.val := by
        simpa only [hsiteSer] using hnew
      have hticket := hF hold
      simpa only [BankWordRenewalFrontierWaveSiteTicket,
        hsiteSer, hsiteTicket] using hticket


/-- The incoming root seam preserves the FULL WaveLineage on
the OLD chosen g when its scrubbed prefix is short of the
terminal source. This upgrades the physical/ticket frame
from each site to all five historical clauses and root lineage.
Consumer: short active branch of bankWordRenewalWaveRootIncomingStep. -/
theorem bankWordRenewalWaveRootIncomingShortStep
    {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hpred : ring.rightNeighbor e = root)
    (hwave : BankWordRenewalFrontierWaveLineage ring root z)
    (hactive : (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)
    (hshort :
      (Classical.choose (hwave.2 hactive)).scrub < n) :
    BankWordRenewalFrontierWaveLineage ring root
      (bankWordEpochNext ring root z e) := by
  obtain ⟨req, stamp, hshape, hsites⟩ :=
    Classical.choose_spec (hwave.2 hactive)
  have hframe := bankWordRenewalWaveRootIncomingShortCoveredFrameStep
    ring root e s hn hbank hs z hz hpred
    (Classical.choose (hwave.2 hactive)) hshape hshort
  have hinj : Function.Injective ring.rightNeighbor := by
    intro a b hab
    apply Fin.ext
    have hv := congrArg Fin.val hab
    change (a.val + 1) % n = (b.val + 1) % n at hv
    by_cases ha : a.val + 1 < n
    · by_cases hb : b.val + 1 < n
      · rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv
        omega
      · have hbeq : b.val + 1 = n := by omega
        rw [Nat.mod_eq_of_lt ha, hbeq, Nat.mod_self] at hv
        omega
    · have haeq : a.val + 1 = n := by omega
      by_cases hb : b.val + 1 < n
      · rw [haeq, Nat.mod_self, Nat.mod_eq_of_lt hb] at hv
        omega
      · omega
  have hseam : e = L3.EWord.site ring root (n - 1) := by
    apply hinj
    rw [hpred]
    exact (L3.EWord.validationSeamNeighbor ring root
      (L3.EWord.site ring root (n - 1)) rfl).symm
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass e).2
  have hpost := clockPostIncoming ring root z.2.1 e
    (by omega : 2 ≤ n) hfixed hpred
  have hearly := L3.EWord.validationSeamEarlySer
    ring root z.2.1 e (by omega : 3 ≤ n)
    hseam hpost.1 hpost.2
    (by simpa only [hpred] using hactive.1)
  have hrootSer :
      ((bankWordEpochNext ring root z e).2.1 root).ser =
        (z.2.1 root).ser := by
    change ((phiW ring z.2.1 e) root).ser =
      (z.2.1 root).ser
    simpa only [L3.EWord.siteZero] using
      (hearly 0 (by omega))
  have hchildSer :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor root)).ser =
        (z.2.1 (ring.rightNeighbor root)).ser := by
    change ((phiW ring z.2.1 e)
      (ring.rightNeighbor root)).ser =
      (z.2.1 (ring.rightNeighbor root)).ser
    simpa only [L3.EWord.siteOne] using
      (hearly 1 (by omega))
  have hrootTicket :
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z e)).validation root =
        (bankWordHardEpochLedger ring root z).validation root := by
    have ht := hframe.2
      (⟨0, (show 0 < n by omega)⟩ : Fin n)
      (by have hl := hshape.lower; try simp only [Fin.val_mk]; omega)
    simpa only [L3.EWord.siteZero] using ht
  have hchildTicket :
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z e)).validation
          (ring.rightNeighbor root) =
        (bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor root) := by
    have ht := hframe.2
      (⟨1, (show 1 < n by omega)⟩ : Fin n)
      (by have hl := hshape.lower; try simp only [Fin.val_mk]; omega)
    simpa only [L3.EWord.siteOne] using ht
  obtain ⟨hrequested, hpending, hdone⟩ := hwave.1
  have hbase : BankWordRenewalFrontierTicketLineage ring root
      (bankWordEpochNext ring root z e) := by
    unfold BankWordRenewalFrontierTicketLineage
    refine ⟨?_, ?_, ?_⟩
    · intro hnew
      rw [hrootSer, hactive.1] at hnew
      cases hnew
    · intro hnew
      have hold :
          (z.2.1 root).ser.cert = .RUNNING ∧
          (z.2.1 root).ser.wphase = .VALIDATING ∧
          (z.2.1 root).ser.phase = .B ∧
          (z.2.1 root).ser.out = .WAIT ∧
          (z.2.1 (ring.rightNeighbor root)).ser.phase = .C ∧
          (z.2.1 (ring.rightNeighbor root)).ser.probe =
            .PENDING := by
        simpa only [hrootSer, hchildSer] using hnew
      obtain ⟨parent, child, hp, hc, hr, hs⟩ := hpending hold
      refine ⟨parent, child, ?_, ?_, hr, hs⟩
      · rw [hrootTicket]
        exact hp
      · rw [hchildTicket]
        exact hc
    · intro hnew
      have hold :
          (z.2.1 root).ser.cert = .RUNNING ∧
          (z.2.1 root).ser.wphase = .VALIDATING ∧
          (z.2.1 root).ser.phase = .B ∧
          (z.2.1 root).ser.out = .DONE ∧
          (z.2.1 (ring.rightNeighbor root)).ser.phase = .F := by
        simpa only [hrootSer, hchildSer] using hnew
      obtain ⟨parent, child, hp, hc, hr, hs⟩ := hdone hold
      refine ⟨parent, child, ?_, ?_, hr, hs⟩
      · rw [hrootTicket]
        exact hp
      · rw [hchildTicket]
        exact hc
  refine ⟨hbase, ?_⟩
  intro _
  refine ⟨Classical.choose (hwave.2 hactive),
    req, stamp, hframe.1, ?_⟩
  intro k hk
  have hkearly : k.val + 1 < n := by
    have hb := k.isLt
    omega
  have hsiteSer :
      ((bankWordEpochNext ring root z e).2.1
        (L3.EWord.site ring root k.val)).ser =
      (z.2.1 (L3.EWord.site ring root k.val)).ser := by
    change ((phiW ring z.2.1 e)
      (L3.EWord.site ring root k.val)).ser =
      (z.2.1 (L3.EWord.site ring root k.val)).ser
    exact hearly k.val hkearly
  have hsiteTicket := hframe.2 k hk
  obtain ⟨hB, hP, hI, hL, hF⟩ := hsites k hk
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hnew
    have hold :
        (z.2.1 (L3.EWord.site ring root k.val)).ser.phase = .B ∧
        (z.2.1 (L3.EWord.site ring root k.val)).ser.wphase =
          .VALIDATING := by
      simpa only [hsiteSer] using hnew
    have hticket := hB hold
    simpa only [BankWordRenewalFrontierWaveSiteTicket,
      hsiteSer, hsiteTicket] using hticket
  · intro hnew
    have hold :
        (z.2.1 (L3.EWord.site ring root k.val)).ser.phase = .C ∧
        (z.2.1 (L3.EWord.site ring root k.val)).ser.probe =
          .PENDING ∧
        (z.2.1 (L3.EWord.site ring root k.val)).ser.wphase =
          .VALIDATING := by
      simpa only [hsiteSer] using hnew
    have hticket := hP hold
    simpa only [BankWordRenewalFrontierWaveSiteTicket,
      hsiteSer, hsiteTicket] using hticket
  · intro hnew
    have hold :
        (z.2.1 (L3.EWord.site ring root k.val)).ser.phase = .C ∧
        (z.2.1 (L3.EWord.site ring root k.val)).ser.probe =
          .INTERNAL_OK ∧
        (z.2.1 (L3.EWord.site ring root k.val)).ser.wphase =
          .VALIDATING := by
      simpa only [hsiteSer] using hnew
    have hticket := hI hold
    simpa only [BankWordRenewalFrontierWaveSiteTicket,
      hsiteSer, hsiteTicket] using hticket
  · intro hnew
    have hold :
        (z.2.1 (L3.EWord.site ring root k.val)).ser.phase = .C ∧
        (z.2.1 (L3.EWord.site ring root k.val)).ser.probe =
          .LEAF_OK := by
      simpa only [hsiteSer] using hnew
    have hticket := hL hold
    simpa only [BankWordRenewalFrontierWaveSiteTicket,
      hsiteSer, hsiteTicket] using hticket
  · intro hnew
    have hold :
        (z.2.1 (L3.EWord.site ring root k.val)).ser.phase = .F ∧
        (Classical.choose (hwave.2 hactive)).stage = .returning ∧
        (Classical.choose (hwave.2 hactive)).pivot ≤ k.val := by
      simpa only [hsiteSer] using hnew
    have hticket := hF hold
    simpa only [BankWordRenewalFrontierWaveSiteTicket,
      hsiteSer, hsiteTicket] using hticket


/-- Literal S5 frames both the old terminal serializer and its
historical ticket whenever the source is F, or C with a probe
other than PENDING. Valid for any active EWord stage, not only
RETURN. Consumer: already-observed forward leaf and quiet RETURN
root-seam branches of full J-W transport. -/
theorem bankWordRenewalWaveRootIncomingQuietSourceFrame
    {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hpred : ring.rightNeighbor e = root)
    (hrun : (z.2.1 root).ser.cert = .RUNNING)
    (hsourceQuiet :
      (z.2.1 e).ser.phase = .F ∨
      ((z.2.1 e).ser.phase = .C ∧
        (z.2.1 e).ser.probe ≠ .PENDING)) :
    ((bankWordEpochNext ring root z e).2.1 e).ser =
      (z.2.1 e).ser ∧
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).validation e =
      (bankWordHardEpochLedger ring root z).validation e := by
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass e).2
  have hpost := clockPostIncoming ring root z.2.1 e
    (by omega : 2 ≤ n) hfixed hpred
  have hnotIdle :
      (z.2.1 (ring.rightNeighbor e)).ser.cert ≠ .IDLE := by
    rw [hpred, hrun]
    decide
  have hrow :
      (serW (z.2.1 e)
        (z.2.1 (ring.rightNeighbor e))).row = "S5" :=
    (serRootIncomingNonidle
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      hpost.1 hpost.2 hnotIdle).1
  have hpair :
      (wValidationPair (z.2.2.clock + 1)
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        ((bankWordHardEpochLedger ring root z).validation e)
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor e))).1 =
        (bankWordHardEpochLedger ring root z).validation e := by
    rcases hsourceQuiet with hf | ⟨hc, hp⟩
    · simp [wValidationPair, hrow, hf]
    · simp [wValidationPair, hrow, hc, hp]
  constructor
  · change ((phiW ring z.2.1 e) e).ser = (z.2.1 e).ser
    rw [phiW_ser_source]
    rcases hsourceQuiet with hf | ⟨hc, hp⟩
    · exact L3.EWord.validationSeamFSer
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        hpost.1 hpost.2
        (by simpa only [hpred] using hrun) hf
    · cases hprobe : (z.2.1 e).ser.probe with
      | NONE =>
          simp [serW, serializerStep, ProjW.lift,
            hpost.1, hpost.2, hnotIdle, hc, hprobe]
      | PENDING =>
          exact False.elim (hp hprobe)
      | INTERNAL_OK =>
          simp [serW, serializerStep, ProjW.lift,
            hpost.1, hpost.2, hnotIdle, hc, hprobe]
      | LEAF_OK =>
          simp [serW, serializerStep, ProjW.lift,
            hpost.1, hpost.2, hnotIdle, hc, hprobe]
  · rw [bankWordHardEpochLedgerNext]
    change (if e = e then
        (wValidationPair (z.2.2.clock + 1)
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          ((bankWordHardEpochLedger ring root z).validation e)
          ((bankWordHardEpochLedger ring root z).validation
            (ring.rightNeighbor e))).1
      else if e = ring.rightNeighbor e then
        (wValidationPair (z.2.2.clock + 1)
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          ((bankWordHardEpochLedger ring root z).validation e)
          ((bankWordHardEpochLedger ring root z).validation
            (ring.rightNeighbor e))).2
      else (bankWordHardEpochLedger ring root z).validation e) =
        (bankWordHardEpochLedger ring root z).validation e
    exact (if_pos rfl).trans hpair


/-- Full quiet-source wave-lineage transport on the actual
incoming-root S5 edge, conditional on the selected S5 source being F or C/non-PENDING. The OLD chosen g, req and
stamp remain unchanged; all five covered-site clauses are
transported by real serializer/ticket frames, including the
returned F suffix. Consumer: quiet FORWARD/RETURN arms of the proposed
bankWordRenewalWaveRootIncomingStep (once hquiet is derived
from reachable wave provenance). -/
theorem bankWordRenewalWaveRootIncomingQuietStep
    {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hpred : ring.rightNeighbor e = root)
    (hwave : BankWordRenewalFrontierWaveLineage ring root z)
    (hactive : (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)
    (hsourceQuiet :
      (z.2.1 e).ser.phase = .F ∨
      ((z.2.1 e).ser.phase = .C ∧
        (z.2.1 e).ser.probe ≠ .PENDING)) :
    BankWordRenewalFrontierWaveLineage ring root
      (bankWordEpochNext ring root z e) := by
  obtain ⟨req, stamp, hshape, hsites⟩ :=
    Classical.choose_spec (hwave.2 hactive)
  have hinj : Function.Injective ring.rightNeighbor := by
    intro a b hab
    apply Fin.ext
    have hv := congrArg Fin.val hab
    change (a.val + 1) % n = (b.val + 1) % n at hv
    by_cases ha : a.val + 1 < n
    · by_cases hb : b.val + 1 < n
      · rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv
        omega
      · have hbeq : b.val + 1 = n := by omega
        rw [Nat.mod_eq_of_lt ha, hbeq, Nat.mod_self] at hv
        omega
    · have haeq : a.val + 1 = n := by omega
      by_cases hb : b.val + 1 < n
      · rw [haeq, Nat.mod_self, Nat.mod_eq_of_lt hb] at hv
        omega
      · omega
  have hseam : e = L3.EWord.site ring root (n - 1) := by
    apply hinj
    rw [hpred]
    exact (L3.EWord.validationSeamNeighbor ring root
      (L3.EWord.site ring root (n - 1)) rfl).symm
  have hframe := bankWordRenewalWaveRootIncomingActiveFrameStep
    ring root e s hn hbank hs z hz hpred
    (Classical.choose (hwave.2 hactive)) hshape
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass e).2
  have hpost := clockPostIncoming ring root z.2.1 e
    (by omega : 2 ≤ n) hfixed hpred
  have hearly := L3.EWord.validationSeamEarlySer
    ring root z.2.1 e (by omega : 3 ≤ n)
    hseam hpost.1 hpost.2
    (by simpa only [hpred] using hactive.1)
  have hrootSer :
      ((bankWordEpochNext ring root z e).2.1 root).ser =
        (z.2.1 root).ser := by
    change ((phiW ring z.2.1 e) root).ser =
      (z.2.1 root).ser
    simpa only [L3.EWord.siteZero] using
      (hearly 0 (by omega))
  have hchildSer :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor root)).ser =
        (z.2.1 (ring.rightNeighbor root)).ser := by
    change ((phiW ring z.2.1 e)
      (ring.rightNeighbor root)).ser =
      (z.2.1 (ring.rightNeighbor root)).ser
    simpa only [L3.EWord.siteOne] using
      (hearly 1 (by omega))
  have hrootTicket :
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z e)).validation root =
        (bankWordHardEpochLedger ring root z).validation root :=
    hframe.2.1
  have hchildTicket :
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z e)).validation
          (ring.rightNeighbor root) =
        (bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor root) := by
    have ht := hframe.2.2
      (⟨1, (show 1 < n by omega)⟩ : Fin n)
      (by have hlo := hshape.lower; try simp only [Fin.val_mk]; omega)
      (by try simp only [Fin.val_mk]; omega)
    simpa only [L3.EWord.siteOne] using ht
  have hsourceFrames :=
    bankWordRenewalWaveRootIncomingQuietSourceFrame
      ring root e s hn hbank hs z hz hpred hactive.1
      hsourceQuiet
  have hsourceSer := hsourceFrames.1
  have hsourceTicket := hsourceFrames.2
  have hsiteSer (k : Fin n) :
      ((bankWordEpochNext ring root z e).2.1
        (L3.EWord.site ring root k.val)).ser =
      (z.2.1 (L3.EWord.site ring root k.val)).ser := by
    by_cases hlast : k.val = n - 1
    · have hsite :
          L3.EWord.site ring root k.val = e := by
        rw [hlast]
        exact hseam.symm
      rw [hsite]
      exact hsourceSer
    · have hkearly : k.val + 1 < n := by
        have hkBound := k.isLt
        omega
      change ((phiW ring z.2.1 e)
        (L3.EWord.site ring root k.val)).ser =
        (z.2.1 (L3.EWord.site ring root k.val)).ser
      exact hearly k.val hkearly
  have hsiteTicket (k : Fin n)
      (hk : k.val < (Classical.choose (hwave.2 hactive)).scrub) :
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z e)).validation
          (L3.EWord.site ring root k.val) =
      (bankWordHardEpochLedger ring root z).validation
          (L3.EWord.site ring root k.val) := by
    by_cases hlast : k.val = n - 1
    · have hsite :
          L3.EWord.site ring root k.val = e := by
        rw [hlast]
        exact hseam.symm
      rw [hsite]
      exact hsourceTicket
    · exact hframe.2.2 k hk hlast
  obtain ⟨hrequested, hpending, hdone⟩ := hwave.1
  have hbase : BankWordRenewalFrontierTicketLineage ring root
      (bankWordEpochNext ring root z e) := by
    unfold BankWordRenewalFrontierTicketLineage
    refine ⟨?_, ?_, ?_⟩
    · intro hnew
      rw [hrootSer, hactive.1] at hnew
      cases hnew
    · intro hnew
      have hold :
          (z.2.1 root).ser.cert = .RUNNING ∧
          (z.2.1 root).ser.wphase = .VALIDATING ∧
          (z.2.1 root).ser.phase = .B ∧
          (z.2.1 root).ser.out = .WAIT ∧
          (z.2.1 (ring.rightNeighbor root)).ser.phase = .C ∧
          (z.2.1 (ring.rightNeighbor root)).ser.probe =
            .PENDING := by
        simpa only [hrootSer, hchildSer] using hnew
      obtain ⟨parent, child, hp, hc, hr, hs⟩ := hpending hold
      refine ⟨parent, child, ?_, ?_, hr, hs⟩
      · rw [hrootTicket]
        exact hp
      · rw [hchildTicket]
        exact hc
    · intro hnew
      have hold :
          (z.2.1 root).ser.cert = .RUNNING ∧
          (z.2.1 root).ser.wphase = .VALIDATING ∧
          (z.2.1 root).ser.phase = .B ∧
          (z.2.1 root).ser.out = .DONE ∧
          (z.2.1 (ring.rightNeighbor root)).ser.phase = .F := by
        simpa only [hrootSer, hchildSer] using hnew
      obtain ⟨parent, child, hp, hc, hr, hs⟩ := hdone hold
      refine ⟨parent, child, ?_, ?_, hr, hs⟩
      · rw [hrootTicket]
        exact hp
      · rw [hchildTicket]
        exact hc
  refine ⟨hbase, ?_⟩
  intro _
  refine ⟨Classical.choose (hwave.2 hactive),
    req, stamp, hframe.1, ?_⟩
  intro k hk
  have hser := hsiteSer k
  have ht := hsiteTicket k hk
  obtain ⟨hB, hP, hI, hL, hF⟩ := hsites k hk
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hnew
    have hold :
        (z.2.1 (L3.EWord.site ring root k.val)).ser.phase = .B ∧
        (z.2.1 (L3.EWord.site ring root k.val)).ser.wphase =
          .VALIDATING := by
      simpa only [hser] using hnew
    have hticket := hB hold
    simpa only [BankWordRenewalFrontierWaveSiteTicket,
      hser, ht] using hticket
  · intro hnew
    have hold :
        (z.2.1 (L3.EWord.site ring root k.val)).ser.phase = .C ∧
        (z.2.1 (L3.EWord.site ring root k.val)).ser.probe =
          .PENDING ∧
        (z.2.1 (L3.EWord.site ring root k.val)).ser.wphase =
          .VALIDATING := by
      simpa only [hser] using hnew
    have hticket := hP hold
    simpa only [BankWordRenewalFrontierWaveSiteTicket,
      hser, ht] using hticket
  · intro hnew
    have hold :
        (z.2.1 (L3.EWord.site ring root k.val)).ser.phase = .C ∧
        (z.2.1 (L3.EWord.site ring root k.val)).ser.probe =
          .INTERNAL_OK ∧
        (z.2.1 (L3.EWord.site ring root k.val)).ser.wphase =
          .VALIDATING := by
      simpa only [hser] using hnew
    have hticket := hI hold
    simpa only [BankWordRenewalFrontierWaveSiteTicket,
      hser, ht] using hticket
  · intro hnew
    have hold :
        (z.2.1 (L3.EWord.site ring root k.val)).ser.phase = .C ∧
        (z.2.1 (L3.EWord.site ring root k.val)).ser.probe =
          .LEAF_OK := by
      simpa only [hser] using hnew
    have hticket := hL hold
    simpa only [BankWordRenewalFrontierWaveSiteTicket,
      hser, ht] using hticket
  · intro hnew
    have hold :
        (z.2.1 (L3.EWord.site ring root k.val)).ser.phase = .F ∧
        (Classical.choose (hwave.2 hactive)).stage = .returning ∧
        (Classical.choose (hwave.2 hactive)).pivot ≤ k.val := by
      simpa only [hser] using hnew
    have hticket := hF hold
    simpa only [BankWordRenewalFrontierWaveSiteTicket,
      hser, ht] using hticket


/-- Exhaustive incoming-root J-W assembly modulo exactly ONE
historical reachability obligation: a RETURN-wave terminal C
must not retain the stale PENDING probe with wphase OFF.
Inactive/S0 and active short prefixes use the earlier row lemmas,
covered forward C/PENDING joins through the OLD selected
g,req,stamp, covered forward C/LEAF_OK frames through S5,
and RETURN F/C quiet branches frame the entire wave.
Consumer: bankWordRenewalWaveRootIncomingStep after discharge
of the RETURN terminal causal-quietness obligation. -/
theorem bankWordRenewalWaveRootIncomingGuardedStep
    {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hpred : ring.rightNeighbor e = root)
    (hwave : BankWordRenewalFrontierWaveLineage ring root z)
    (hreturnQuiet :
      ∀ hactive :
        ((z.2.1 root).ser.cert = .RUNNING ∧
         (z.2.1 root).ser.wphase = .VALIDATING),
        L3.EWord.ReturnShape ring root z.2.1
          (Classical.choose (hwave.2 hactive)) →
        (z.2.1 e).ser.phase = .C →
        (z.2.1 e).ser.probe ≠ .PENDING) :
    BankWordRenewalFrontierWaveLineage ring root
      (bankWordEpochNext ring root z e) := by
  by_cases hactive :
      (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING
  · obtain ⟨req, stamp, hshape, hsites⟩ :=
      Classical.choose_spec (hwave.2 hactive)
    by_cases hshort :
        (Classical.choose (hwave.2 hactive)).scrub < n
    · exact bankWordRenewalWaveRootIncomingShortStep
        ring root e s hn hbank hs z hz hpred hwave hactive hshort
    · have hcovered :
          (Classical.choose (hwave.2 hactive)).scrub = n := by
        have hupper := hshape.upper
        omega
      have hinj : Function.Injective ring.rightNeighbor := by
        intro a b hab
        apply Fin.ext
        have hv := congrArg Fin.val hab
        change (a.val + 1) % n = (b.val + 1) % n at hv
        by_cases ha : a.val + 1 < n
        · by_cases hb : b.val + 1 < n
          · rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv
            omega
          · have hbeq : b.val + 1 = n := by omega
            rw [Nat.mod_eq_of_lt ha, hbeq, Nat.mod_self] at hv
            omega
        · have haeq : a.val + 1 = n := by omega
          by_cases hb : b.val + 1 < n
          · rw [haeq, Nat.mod_self, Nat.mod_eq_of_lt hb] at hv
            omega
          · omega
      have hseam : e = L3.EWord.site ring root (n - 1) := by
        apply hinj
        rw [hpred]
        exact (L3.EWord.validationSeamNeighbor ring root
          (L3.EWord.site ring root (n - 1)) rfl).symm
      rcases hshape.stageShape with hf | hr
      · rcases hf.currentObligation with hnew | hwait
        · have hbound := hf.pivotBound
          have heq := hnew.2.2
          omega
        · have hbalance := hwait.2.1
          have hindex :
              (Classical.choose (hwave.2 hactive)).pivot + 1 =
                n - 1 := by omega
          have hpc := hwait.2.2
          unfold L3.EWord.pendingChild at hpc
          obtain ⟨hchildC, hchildStatus⟩ := hpc
          have hsourceC : (z.2.1 e).ser.phase = .C := by
            rw [hseam, ← hindex]
            exact hchildC
          rcases hchildStatus with hpend | hinter | hleaf
          · have hsourcePending :
                (z.2.1 e).ser.probe = .PENDING := by
              rw [hseam, ← hindex]
              exact hpend.1
            have hsourceValid :
                (z.2.1 e).ser.wphase = .VALIDATING := by
              rw [hseam, ← hindex]
              exact hpend.2
            exact bankWordRenewalWaveRootIncomingCoveredForwardStep
              ring root e s hn hbank hs z hz hpred hwave
              hactive hcovered hsourceC
              hsourcePending hsourceValid
          · have hbad : False := by omega
            exact False.elim hbad
          · have hsourceLeaf :
                (z.2.1 e).ser.probe = .LEAF_OK := by
              rw [hseam, ← hindex]
              exact hleaf.2.1
            have hnotPending :
                (z.2.1 e).ser.probe ≠ .PENDING := by
              rw [hsourceLeaf]
              decide
            exact bankWordRenewalWaveRootIncomingQuietStep
              ring root e s hn hbank hs z hz hpred hwave
              hactive (Or.inr ⟨hsourceC, hnotPending⟩)
      · have hphase :
            (z.2.1 e).ser.phase = .F ∨
            (z.2.1 e).ser.phase = .C := by
          by_cases hpivot :
              (Classical.choose (hwave.2 hactive)).pivot = n - 1
          · left
            have hf := hr.leftmostF
            rw [hpivot] at hf
            simpa only [← hseam] using hf
          · have hlt :
                (Classical.choose (hwave.2 hactive)).pivot <
                  n - 1 := by
              have hbound := hr.pivotBound
              omega
            have hlast := hr.suffix
              (⟨n - 1, (show n - 1 < n by omega)⟩ : Fin n) hlt
            rcases hlast with hf | hc
            · left
              simpa only [← hseam] using hf.1
            · right
              simpa only [← hseam] using hc.1
        rcases hphase with hf | hc
        · exact bankWordRenewalWaveRootIncomingQuietStep
            ring root e s hn hbank hs z hz hpred hwave
            hactive (Or.inl hf)
        · have hprobe := hreturnQuiet hactive hr hc
          exact bankWordRenewalWaveRootIncomingQuietStep
            ring root e s hn hbank hs z hz hpred hwave
            hactive (Or.inr ⟨hc, hprobe⟩)
  · exact bankWordRenewalWaveRootIncomingInactiveStep
      ring root e s hn hbank hs z hz hpred hwave hactive


end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open Classical

/-- The corrected root-anchored forward CURRENT wave. In the
last-follower case PENDING/CURRENT is allowed before incoming S5.
Consumer: the S-frontier clause in repair.tex 1062-1075. -/
structure BankWordRenewalSoftForwardShape {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (p : Nat) : Prop where
  pivotBound : p + 1 < n
  completed : ∀ j : Nat, j < p →
    (z.2.1 (L3.EWord.site ring root j)).ser.phase = .B ∧
    (z.2.1 (L3.EWord.site ring root j)).ser.out = .DONE ∧
    (z.2.1 (L3.EWord.site ring root j)).ser.wphase = .CURRENT
  parentPhase :
    (z.2.1 (L3.EWord.site ring root p)).ser.phase = .B
  parentCurrent :
    (z.2.1 (L3.EWord.site ring root p)).ser.wphase = .CURRENT
  front :
    (p = 0 ∧
      (z.2.1 (L3.EWord.site ring root p)).ser.out = .WAIT ∧
      (z.2.1 (L3.EWord.site ring root (p + 1))).ser.phase = .C ∧
      (z.2.1 (L3.EWord.site ring root (p + 1))).ser.wphase =
        .CURRENT ∧
      ((z.2.1 (L3.EWord.site ring root (p + 1))).ser.probe =
          .PENDING ∨
       (z.2.1 (L3.EWord.site ring root (p + 1))).ser.probe =
          .INTERNAL_OK)) ∨
    (0 < p ∧
      ((z.2.1 (L3.EWord.site ring root p)).ser.out = .NEW ∨
       ((z.2.1 (L3.EWord.site ring root p)).ser.out = .WAIT ∧
        (((z.2.1 (L3.EWord.site ring root (p + 1))).ser.phase =
             .C ∧
           (z.2.1 (L3.EWord.site ring root (p + 1))).ser.probe =
             .PENDING ∧
           (z.2.1 (L3.EWord.site ring root (p + 1))).ser.wphase =
             .CURRENT) ∨
          (p + 2 < n ∧
           (z.2.1 (L3.EWord.site ring root (p + 1))).ser.phase =
             .C ∧
           (z.2.1 (L3.EWord.site ring root (p + 1))).ser.probe =
             .INTERNAL_OK ∧
           (z.2.1 (L3.EWord.site ring root (p + 1))).ser.wphase =
             .CURRENT) ∨
          (p + 2 = n ∧
           (z.2.1 (L3.EWord.site ring root (p + 1))).ser.phase =
             .C ∧
           (z.2.1 (L3.EWord.site ring root (p + 1))).ser.probe =
             .LEAF_OK ∧
           (z.2.1 (L3.EWord.site ring root (p + 1))).ser.wphase =
             .OFF)))))

/-- The returning wave has completed parents through q and
a leftmost F at q+1; downstream sites can be F or C/OFF.
Consumer: the soft S6 position certificate. -/
structure BankWordRenewalSoftReturnShape {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (q : Nat) : Prop where
  pivotBound : q + 1 < n
  rootRunning : (z.2.1 root).ser.cert = .RUNNING
  rootPhase : (z.2.1 root).ser.phase = .B
  rootDone : (z.2.1 root).ser.out = .DONE
  rootCurrent : (z.2.1 root).ser.wphase = .CURRENT
  completed : ∀ j : Nat, j ≤ q →
    (z.2.1 (L3.EWord.site ring root j)).ser.phase = .B ∧
    (z.2.1 (L3.EWord.site ring root j)).ser.out = .DONE ∧
    (z.2.1 (L3.EWord.site ring root j)).ser.wphase = .CURRENT
  leftmostPhase :
    (z.2.1 (L3.EWord.site ring root (q + 1))).ser.phase = .F
  leftmostWphase :
    (z.2.1 (L3.EWord.site ring root (q + 1))).ser.wphase =
      (if q + 2 = n then .OFF else .CURRENT)
  suffix : ∀ j : Nat, q + 1 < j → j < n →
    (((z.2.1 (L3.EWord.site ring root j)).ser.phase = .F ∧
       (z.2.1 (L3.EWord.site ring root j)).ser.wphase =
         (if j + 1 = n then .OFF else .CURRENT)) ∨
      ((z.2.1 (L3.EWord.site ring root j)).ser.phase = .C ∧
       (z.2.1 (L3.EWord.site ring root j)).ser.wphase = .OFF))

/-- No constraints on unrelated inherited serializer fields
when the root is not RUNNING/B/CURRENT. -/
def BankWordRenewalSoftShape {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) : Prop :=
  ((z.2.1 root).ser.cert = .RUNNING ∧
   (z.2.1 root).ser.phase = .B ∧
   (z.2.1 root).ser.wphase = .CURRENT) →
    ((∃ p : Nat, BankWordRenewalSoftForwardShape ring root z p) ∨
     (∃ q : Nat, BankWordRenewalSoftReturnShape ring root z q))

/-- State-only position, using the first root-anchored non-DONE
shape; never the maximum over arbitrary foreign CURRENT fields. -/
noncomputable def bankWordRenewalSoftRootedPosition {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) : Nat :=
  if (z.2.1 root).ser.cert = .RUNNING ∧
     (z.2.1 root).ser.phase = .B ∧
     (z.2.1 root).ser.wphase = .CURRENT then
    let k := L3.firstNonDone
      (fun j => L3.serShape
        (z.2.1 (L3.EWord.site ring root j)).ser) n 0
    if k < n then
      if (z.2.1 (L3.EWord.site ring root k)).ser.phase = .F then
        n - 1
      else if (z.2.1 (L3.EWord.site ring root k)).ser.phase = .B then
        if k = 0 then 0
        else if (z.2.1 (L3.EWord.site ring root k)).ser.out = .NEW then k
        else if (z.2.1 (L3.EWord.site ring root k)).ser.out = .WAIT
        then k + 1 else 0
      else 0
    else 0
  else 0

/-- The exact state-to-letter type used by grantDrainLabelHits
with next = bankWordRenewalNext ring root s. -/
noncomputable def bankWordRenewalSoftRootedChosen {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s) : Fin n :=
  if (z.1.2.1 root).ser.cert = .RUNNING ∧
     (z.1.2.1 root).ser.phase = .B ∧
     (z.1.2.1 root).ser.wphase = .CURRENT then
    let k := L3.firstNonDone
      (fun j => L3.serShape
        (z.1.2.1 (L3.EWord.site ring root j)).ser) n 0
    if k < n ∧
       (z.1.2.1 (L3.EWord.site ring root k)).ser.phase = .B
    then L3.EWord.site ring root k else root
  else root

/-- Initial shape-six run stops at its first other shape.
Consumer: forward/return position indices, no large powers. -/
private theorem bankWordRenewalSoftFirstNonDonePrefix
    (w : Nat → Fin 8) (p : Nat)
    (hpre : ∀ j : Nat, j < p → (w j).val = 6)
    (hstop : (w p).val ≠ 6) :
    ∀ fuel k : Nat, k ≤ p → p - k < fuel →
      L3.firstNonDone w fuel k = p := by
  intro fuel
  induction fuel with
  | zero =>
      intro k hk hlt
      omega
  | succ fuel ih =>
      intro k hk hlt
      by_cases he : k = p
      · rw [he]
        change (if (w p).val = 6 then
          L3.firstNonDone w fuel (p + 1) else p) = p
        rw [if_neg hstop]
      · have hklt : k < p := by omega
        have heq : (w k).val = 6 := hpre k hklt
        change (if (w k).val = 6 then
          L3.firstNonDone w fuel (k + 1) else k) = p
        rw [if_pos heq]
        apply ih (k + 1)
        · omega
        · omega

/-- The first non-DONE offset is the forward parent pivot.
Consumer: the predictable serializer frontier nomination. -/
theorem bankWordRenewalSoftForwardIndex {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (p : Nat)
    (h : BankWordRenewalSoftForwardShape ring root z p) :
    L3.firstNonDone
      (fun j => L3.serShape
        (z.2.1 (L3.EWord.site ring root j)).ser) n 0 = p := by
  have hpre : ∀ j : Nat, j < p →
      (L3.serShape
        (z.2.1 (L3.EWord.site ring root j)).ser).val = 6 := by
    intro j hj
    obtain ⟨hp, ho, _⟩ := h.completed j hj
    simp [L3.serShape, hp, ho]
  have hstop :
      (L3.serShape
        (z.2.1 (L3.EWord.site ring root p)).ser).val ≠ 6 := by
    rcases h.front with hzero | hpositive
    · have hw := hzero.2.1
      simp [L3.serShape, h.parentPhase, hw]
    · rcases hpositive.2 with hnew | hwait
      · simp [L3.serShape, h.parentPhase, hnew]
      · simp [L3.serShape, h.parentPhase, hwait.1]
  exact bankWordRenewalSoftFirstNonDonePrefix
    _ p hpre hstop n 0 (by have := h.pivotBound; omega) (by have := h.pivotBound; omega)

/-- The first non-DONE offset in return is the leftmost F.
Consumer: the returning-stage position at a soft S6. -/
theorem bankWordRenewalSoftReturnIndex {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (q : Nat)
    (h : BankWordRenewalSoftReturnShape ring root z q) :
    L3.firstNonDone
      (fun j => L3.serShape
        (z.2.1 (L3.EWord.site ring root j)).ser) n 0 =
      q + 1 := by
  have hpre : ∀ j : Nat, j < q + 1 →
      (L3.serShape
        (z.2.1 (L3.EWord.site ring root j)).ser).val = 6 := by
    intro j hj
    obtain ⟨hp, ho, _⟩ := h.completed j (by omega)
    simp [L3.serShape, hp, ho]
  have hstop :
      (L3.serShape
        (z.2.1 (L3.EWord.site ring root (q + 1))).ser).val ≠ 6 := by
    simp [L3.serShape, h.leftmostPhase]
  exact bankWordRenewalSoftFirstNonDonePrefix
    _ (q + 1) hpre hstop n 0 (by have := h.pivotBound; omega) (by have := h.pivotBound; omega)

/-- The genuine hard S6 cut is inactive, hence satisfies the
conditional spatial invariant and has zero rooted position.
Consumer: the fresh BANK kernel induction base. -/
theorem bankWordRenewalSoftShapeSeed {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (seed : BankWordRenewalFreshSeed ring root s) :
    BankWordRenewalSoftShape ring root seed.1.1 ∧
    bankWordRenewalSoftRootedPosition ring root seed.1.1 = 0 := by
  have hidle := bankWordRenewalFrontierFreshRootIdle
    ring root s hn hbank hs seed
  constructor
  · intro hactive
    rw [hidle] at hactive
    cases hactive.1
  · simp [bankWordRenewalSoftRootedPosition, hidle]

/-- Literal positive-lease ROOT_OUT S1, regardless of old
suffix bytes. Consumer: root entry of the soft spatial shape. -/
private theorem bankWordRenewalSoftPositiveRootStart {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (hn : 3 ≤ n)
    (hx : (postW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).eX.l = true)
    (hy : (postW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).eY.l = false)
    (hreq : (z.2.1 root).ser.cert = .REQUESTED)
    (hpositive : 0 < (z.2.1 root).siLease.val) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z root) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z root) = 0 := by
  have hne : (z.2.1 root).siLease.val ≠ 0 :=
    Nat.ne_of_gt hpositive
  have hneq : ring.rightNeighbor root ≠ root :=
    L3.EWord.rightNeighborDifferent ring (by omega) root
  have hsource :
      ((bankWordEpochNext ring root z root).2.1 root).ser =
        { (z.2.1 root).ser with
          phase := .B, out := .WAIT, cert := .RUNNING,
          wphase := .CURRENT } := by
    change ((phiW ring z.2.1 root) root).ser = _
    rw [phiW_ser_source]
    simp [serW, serializerStep, ProjW.lift,
      serTbStar, hx, hy, hreq, hne]
  have htarget :
      ((bankWordEpochNext ring root z root).2.1
          (ring.rightNeighbor root)).ser =
        { (z.2.1 (ring.rightNeighbor root)).ser with
          phase := .C, out := .NEW, probe := .PENDING,
          wphase := .CURRENT } := by
    change ((phiW ring z.2.1 root)
      (ring.rightNeighbor root)).ser = _
    rw [phiW_ser_target ring z.2.1 root hneq]
    simp [serW, serializerStep, ProjW.lift,
      serTbStar, hx, hy, hreq, hne]
  have hroot :
      ((bankWordEpochNext ring root z root).2.1 root).ser.cert =
        .RUNNING ∧
      ((bankWordEpochNext ring root z root).2.1 root).ser.phase =
        .B ∧
      ((bankWordEpochNext ring root z root).2.1 root).ser.out =
        .WAIT ∧
      ((bankWordEpochNext ring root z root).2.1 root).ser.wphase =
        .CURRENT := by
    simp [hsource]
  have hchild :
      ((bankWordEpochNext ring root z root).2.1
        (ring.rightNeighbor root)).ser.phase = .C ∧
      ((bankWordEpochNext ring root z root).2.1
        (ring.rightNeighbor root)).ser.probe = .PENDING ∧
      ((bankWordEpochNext ring root z root).2.1
        (ring.rightNeighbor root)).ser.wphase = .CURRENT := by
    simp [htarget]
  have hforward :
      BankWordRenewalSoftForwardShape ring root
        (bankWordEpochNext ring root z root) 0 := by
    refine {
      pivotBound := by omega
      completed := ?_
      parentPhase := ?_
      parentCurrent := ?_
      front := ?_ }
    · intro j hj
      omega
    · simpa only [L3.EWord.siteZero] using hroot.2.1
    · simpa only [L3.EWord.siteZero] using hroot.2.2.2
    · left
      refine ⟨rfl, ?_, ?_, ?_, ?_⟩
      · simpa only [L3.EWord.siteZero] using hroot.2.2.1
      · simpa only [Nat.zero_add, L3.EWord.siteOne] using hchild.1
      · simpa only [Nat.zero_add, L3.EWord.siteOne] using hchild.2.2
      · exact Or.inl (by simpa only [Nat.zero_add, L3.EWord.siteOne] using hchild.2.1)
  constructor
  · intro _
    exact Or.inl ⟨0, hforward⟩
  · have hidx := bankWordRenewalSoftForwardIndex
      ring root (bankWordEpochNext ring root z root) 0 hforward
    have hactive :
        ((bankWordEpochNext ring root z root).2.1 root).ser.cert =
          .RUNNING ∧
        ((bankWordEpochNext ring root z root).2.1 root).ser.phase =
          .B ∧
        ((bankWordEpochNext ring root z root).2.1 root).ser.wphase =
          .CURRENT :=
      ⟨hroot.1, hroot.2.1, hroot.2.2.2⟩
    have hnzero : 0 < n := by omega
    simp [bankWordRenewalSoftRootedPosition, hactive,
      hidx, hnzero, L3.EWord.siteZero, hroot.2.1]

/-- ROOT_OUT positive S1, zero-lease hard S1, or C/F recovery:
N holds after the row and no soft frontier position is charged.
The OLD root cannot be active in any of these cases.
Consumer: S-frontier root-entry/recovery case group. -/
theorem bankWordRenewalSoftRootEntryAndRecovery {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (hn : 3 ≤ n)
    (hx : (postW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).eX.l = true)
    (hy : (postW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).eY.l = false)
    (hcase :
      ((z.2.1 root).ser.cert = .REQUESTED ∧
        0 < (z.2.1 root).siLease.val) ∨
      ((z.2.1 root).ser.cert = .REQUESTED ∧
        (z.2.1 root).siLease.val = 0) ∨
      (((z.2.1 root).ser.cert = .IDLE ∨
        (z.2.1 root).ser.cert = .RUNNING) ∧
       ((z.2.1 root).ser.phase = .C ∨
        (z.2.1 root).ser.phase = .F))) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z root) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z root) = 0 ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z root) =
    bankWordRenewalSoftRootedPosition ring root z := by
  have holdInactive :
      ¬ ((z.2.1 root).ser.cert = .RUNNING ∧
        (z.2.1 root).ser.phase = .B ∧
        (z.2.1 root).ser.wphase = .CURRENT) := by
    intro h
    rcases hcase with hp | hz
    · rw [hp.1] at h
      cases h.1
    · rcases hz with hz | hr
      · rw [hz.1] at h
        cases h.1
      · rcases hr.2 with hc | hf
        · rw [hc] at h
          cases h.2.1
        · rw [hf] at h
          cases h.2.1
  have holdPosition :
      bankWordRenewalSoftRootedPosition ring root z = 0 := by
    simp [bankWordRenewalSoftRootedPosition, holdInactive]
  have hresult :
      BankWordRenewalSoftShape ring root
        (bankWordEpochNext ring root z root) ∧
      bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z root) = 0 := by
    rcases hcase with hp | hz
    · exact bankWordRenewalSoftPositiveRootStart
        ring root z hn hx hy hp.1 hp.2
    · rcases hz with hz | hr
      · have hhard := bankWordHardEpochZeroLeaseHardStart
          (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
          hx hy hz.1 hz.2
        have hvalid :
            ((bankWordEpochNext ring root z root).2.1 root).ser.wphase =
              .VALIDATING := by
          change ((phiW ring z.2.1 root) root).ser.wphase =
            .VALIDATING
          rw [phiW_ser_source]
          exact hhard.2.2
        have hnot :
            ¬ (((bankWordEpochNext ring root z root).2.1 root).ser.cert =
                 .RUNNING ∧
               ((bankWordEpochNext ring root z root).2.1 root).ser.phase =
                 .B ∧
               ((bankWordEpochNext ring root z root).2.1 root).ser.wphase =
                 .CURRENT) := by
          intro h
          have hc := h.2.2
          rw [hvalid] at hc
          cases hc
        constructor
        · intro h
          exact False.elim (hnot h)
        · simp [bankWordRenewalSoftRootedPosition, hnot]
      · have hrec := serRootOutgoingRecovery
          (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
          hx hy hr.1 hr.2
        have hidle :
            ((bankWordEpochNext ring root z root).2.1 root).ser.cert =
              .IDLE := by
          change ((phiW ring z.2.1 root) root).ser.cert = .IDLE
          rw [phiW_ser_source]
          exact hrec.2.1
        have hnot :
            ¬ (((bankWordEpochNext ring root z root).2.1 root).ser.cert =
                 .RUNNING ∧
               ((bankWordEpochNext ring root z root).2.1 root).ser.phase =
                 .B ∧
               ((bankWordEpochNext ring root z root).2.1 root).ser.wphase =
                 .CURRENT) := by
          intro h
          rw [hidle] at h
          cases h.1
        constructor
        · intro h
          exact False.elim (hnot h)
        · simp [bankWordRenewalSoftRootedPosition, hnot]
  exact ⟨hresult.1, hresult.2, hresult.2.trans holdPosition.symm⟩

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The additional causal serializer clause needed by the incoming
RETURN seam. It is quantified over RETURN shapes, rather than over
a particular Classical.choose witness, so that it survives changes
in the proof of the old existential wave certificate.
Consumer: the physical incoming S5 join in R10a J-W. -/
structure BankWordRenewalFrontierWaveLineageQuiet {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) : Prop where
  wave : BankWordRenewalFrontierWaveLineage ring root z
  returnSuffixQuiet :
    ∀ (hactive :
         (z.2.1 root).ser.cert = .RUNNING ∧
         (z.2.1 root).ser.wphase = .VALIDATING)
      (g : L3.EWord.ValidationGhost),
      L3.EWord.ReturnShape ring root z.2.1 g →
      ∀ k : Fin n, g.pivot < k.val →
        (z.2.1 (L3.EWord.site ring root k.val)).ser.phase = .C →
        (z.2.1 (L3.EWord.site ring root k.val)).ser.probe ≠
          .PENDING

/-- A forward B frontier and a return F frontier cannot be two
descriptions of the same physical serializer ring: their pivots
would require either B=F or NEW/WAIT=DONE.
Consumer: incoming S5 preservation of RETURN quietness when the
historically selected wave is still FORWARD. -/
private theorem bankWordRenewalWaveForwardExcludesReturn
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c)
    (gf gr : L3.EWord.ValidationGhost)
    (hf : L3.EWord.ForwardShape ring root s gf)
    (hr : L3.EWord.ReturnShape ring root s gr) : False := by
  by_cases hle : gr.pivot ≤ gf.pivot
  · by_cases heq : gr.pivot = gf.pivot
    · have hB := hf.parentB
      have hF := hr.leftmostF
      rw [heq] at hF
      rw [hF] at hB
      cases hB
    · have hlt : gr.pivot < gf.pivot := by omega
      have hB :=
        (hf.completed
          (⟨gr.pivot, hr.pivotBound⟩ : Fin n) hlt).1
      rw [hr.leftmostF] at hB
      cases hB
  · have hgt : gf.pivot < gr.pivot := by omega
    have hbound : gf.pivot < n := by
      have hp := hf.pivotBound
      omega
    have hD :=
      (hr.completed (⟨gf.pivot, hbound⟩ : Fin n) hgt).2.1
    rcases hf.currentObligation with hnew | hwait
    · have hN := hnew.2.1
      rw [hD] at hN
      cases hN
    · have hW := hwait.1
      rw [hD] at hW
      cases hW

/-- RETURN geometry only reads serializer records at the named
cyclic sites. This transports any candidate RETURN witness
backward across a physical serializer frame.
Consumer: quietness preservation at covered S2R and incoming S5. -/
private theorem bankWordRenewalWaveReturnShapeSiteFrame
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s t : Fin n → ProjW c)
    (g : L3.EWord.ValidationGhost)
    (hser : ∀ i : Nat, i < n →
      (t (L3.EWord.site ring root i)).ser =
        (s (L3.EWord.site ring root i)).ser)
    (hr : L3.EWord.ReturnShape ring root t g) :
    L3.EWord.ReturnShape ring root s g := by
  refine {
    isReturn := hr.isReturn
    covered := hr.covered
    pivotPositive := hr.pivotPositive
    pivotBound := hr.pivotBound
    completed := ?_
    leftmostF := ?_
    leftmostWphase := ?_
    suffix := ?_ }
  · intro i hi
    have hh := hr.completed i hi
    unfold L3.EWord.doneParent at hh ⊢
    simpa only [hser i.val i.isLt] using hh
  · simpa only [hser g.pivot hr.pivotBound] using hr.leftmostF
  · simpa only [hser g.pivot hr.pivotBound] using
      hr.leftmostWphase
  · intro i hi
    simpa only [hser i.val i.isLt] using hr.suffix i hi

/-- The unique source of the incoming-root edge is the
last cyclic serializer site.
Consumer: incoming S5 quietness and full source framing. -/
private theorem bankWordRenewalWaveIncomingIsSeam {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hn : 2 ≤ n)
    (hpred : ring.rightNeighbor e = root) :
    e = L3.EWord.site ring root (n - 1) := by
  have hinj : Function.Injective ring.rightNeighbor := by
    intro a b hab
    apply Fin.ext
    have hv := congrArg Fin.val hab
    change (a.val + 1) % n = (b.val + 1) % n at hv
    by_cases ha : a.val + 1 < n
    · by_cases hb : b.val + 1 < n
      · rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv
        omega
      · have hbeq : b.val + 1 = n := by omega
        rw [Nat.mod_eq_of_lt ha, hbeq, Nat.mod_self] at hv
        omega
    · have haeq : a.val + 1 = n := by omega
      by_cases hb : b.val + 1 < n
      · rw [haeq, Nat.mod_self, Nat.mod_eq_of_lt hb] at hv
        omega
      · omega
  apply hinj
  rw [hpred]
  exact (L3.EWord.validationSeamNeighbor ring root
    (L3.EWord.site ring root (n - 1)) rfl).symm

/-- A RETURN seam is either F or a quiet C, by its pivot
geometry and the new all-suffix causal clause.
Consumer: the hreturnQuiet argument of the existing guarded
incoming root theorem, and S5 physical source framing. -/
private theorem bankWordRenewalWaveReturnSeamQuiet
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c) (e : Fin n)
    (g : L3.EWord.ValidationGhost)
    (hr : L3.EWord.ReturnShape ring root s g)
    (hseam : e = L3.EWord.site ring root (n - 1))
    (hquiet : ∀ k : Fin n, g.pivot < k.val →
      (s (L3.EWord.site ring root k.val)).ser.phase = .C →
      (s (L3.EWord.site ring root k.val)).ser.probe ≠
        .PENDING) :
    (s e).ser.phase = .F ∨
      ((s e).ser.phase = .C ∧
       (s e).ser.probe ≠ .PENDING) := by
  by_cases hpivot : g.pivot = n - 1
  · left
    have hF := hr.leftmostF
    rw [hpivot] at hF
    simpa only [hseam] using hF
  · have hlt : g.pivot < n - 1 := by
      have hbound := hr.pivotBound
      omega
    have hlast := hr.suffix
      (⟨n - 1, (show n - 1 < n by omega)⟩ : Fin n)
      hlt
    rcases hlast with hF | hC
    · left
      simpa only [hseam] using hF.1
    · right
      have hc : (s e).ser.phase = .C := by
        simpa only [hseam] using hC.1
      have hq := hquiet
        (⟨n - 1, (show n - 1 < n by omega)⟩ : Fin n)
        hlt hC.1
      exact ⟨hc, by simpa only [hseam] using hq⟩

/-- An incoming-root S0 cannot manufacture an active validating
root, and S5 preserves an already non-IDLE root serializer.
Consumer: induction transport of the strengthened RETURN clause. -/
private theorem bankWordRenewalWaveRootIncomingActiveWasOld
    {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hpred : ring.rightNeighbor e = root)
    (hnew :
      ((bankWordEpochNext ring root z e).2.1 root).ser.cert =
        .RUNNING ∧
      ((bankWordEpochNext ring root z e).2.1 root).ser.wphase =
        .VALIDATING) :
    (z.2.1 root).ser.cert = .RUNNING ∧
    (z.2.1 root).ser.wphase = .VALIDATING := by
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 e) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass e).2
  have hpost := clockPostIncoming ring root z.2.1 e
    (by omega : 2 ≤ n) hfixed hpred
  have hneq : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) e
  have hpostR := hpost
  rw [hpred] at hpostR
  by_cases hidle : (z.2.1 root).ser.cert = .IDLE
  · have hquarantine :
        ((bankWordEpochNext ring root z e).2.1 root).ser.wphase =
          .QUARANTINE := by
      change ((phiW ring z.2.1 e) root).ser.wphase =
        .QUARANTINE
      rw [← hpred, phiW_ser_target ring z.2.1 e hneq]
      simp [serW, serializerStep, ProjW.lift,
        hpost.1, hpost.2, hpostR.1, hpostR.2, hpred, hidle]
    have hbad : SerWPhase.QUARANTINE = .VALIDATING :=
      hquarantine.symm.trans hnew.2
    cases hbad
  · have hroot :
        ((bankWordEpochNext ring root z e).2.1 root).ser =
          (z.2.1 root).ser := by
      change ((phiW ring z.2.1 e) root).ser =
        (z.2.1 root).ser
      rw [← hpred, phiW_ser_target ring z.2.1 e hneq]
      simp [serW, serializerStep, ProjW.lift,
        hpost.1, hpost.2, hpostR.1, hpostR.2, hpred, hidle]
    simpa only [hroot] using hnew

/-- The fresh genuine S6 cut is quiet because no validating
RETURN suffix exists yet. Consumer: the strengthening's base
case in the R10a W epoch induction. -/
theorem bankWordRenewalFrontierFreshWaveLineageQuiet {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (seed : BankWordRenewalFreshSeed ring root s) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      seed.1.1 := by
  have hbase := bankWordRenewalFrontierFreshWaveLineage
    ring root s hn hbank hs seed
  have hidle := bankWordRenewalFrontierFreshRootIdle
    ring root s hn hbank hs seed
  refine ⟨hbase, ?_⟩
  intro hactive g hr k hk hc
  rw [hidle] at hactive
  cases hactive.1

/-- A zero-lease hard S1 constructs a RUNNING B/WAIT root;
RETURN would require that same root to be B/DONE.
Consumer: strengthened J-W outgoing hard-start row. -/
theorem bankWordRenewalWaveRootOutgoingHardStartQuietStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hrequested : (z.2.1 root).ser.cert = .REQUESTED)
    (hzero : (z.2.1 root).siLease.val = 0) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z root) := by
  have hbase := bankWordRenewalWaveRootOutgoingHardStartStep
    ring root s hn hbank hs z hz hwave.wave hrequested hzero
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 root) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass root).2
  have hpost := clockPostOutgoing ring root z.2.1 root
    (by omega : 2 ≤ n) hfixed rfl
  obtain ⟨_, _, _, hwait, _, _, _, _, _⟩ :=
    L3.EWord.freshStartPair
      (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
      hpost.1 hpost.2 hrequested hzero
  have hrootWait :
      ((bankWordEpochNext ring root z root).2.1 root).ser.out =
        .WAIT := by
    change ((phiW ring z.2.1 root) root).ser.out = .WAIT
    rw [L3.EWord.phiSource]
    exact hwait
  refine ⟨hbase, ?_⟩
  intro hactive g hr k hk hc
  have hdoneRoot :
      ((bankWordEpochNext ring root z root).2.1 root).ser.out =
        .DONE := by
    have hdone := hr.completed
      (⟨0, (show 0 < n by omega)⟩ : Fin n)
      (by show 0 < g.pivot; exact hr.pivotPositive)
    simpa only [L3.EWord.siteZero] using hdone.2.1
  rw [hrootWait] at hdoneRoot
  cases hdoneRoot

/-- Outgoing S6 retires the root to IDLE, so RETURN quietness
is preserved vacuously alongside the established ticket ledger.
Consumer: strengthened J-W terminal root row. -/
theorem bankWordRenewalWaveRootOutgoingFinishQuietStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hcert : (z.2.1 root).ser.cert ≠ .REQUESTED)
    (hphase : (z.2.1 root).ser.phase = .B)
    (hout : (z.2.1 root).ser.out = .DONE)
    (hchild :
      (z.2.1 (ring.rightNeighbor root)).ser.phase = .F) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z root) := by
  have hbase := bankWordRenewalWaveRootOutgoingFinishStep
    ring root s hn hbank hs z hz hcert hphase hout hchild
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 root) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass root).2
  have hpost := clockPostOutgoing ring root z.2.1 root
    (by omega : 2 ≤ n) hfixed rfl
  have hsix := serRootOutgoingDone
    (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
    hpost.1 hpost.2 hcert hphase hout hchild
  have hidle :
      ((bankWordEpochNext ring root z root).2.1 root).ser.cert =
        .IDLE := by
    change ((phiW ring z.2.1 root) root).ser.cert = .IDLE
    rw [phiW_ser_source]
    exact hsix.2.1
  refine ⟨hbase, ?_⟩
  intro hactive g hr k hk hc
  rw [hidle] at hactive
  cases hactive.1

/-- The already-certified S2R B/DONE + B responder subrow
frames every physical serializer record. Therefore any new
RETURN witness was already a RETURN witness before that row,
and its quiet suffix transfers exactly.
Consumer: covered S2R branch of the root outgoing J-W step. -/
theorem bankWordRenewalWaveRootOutgoingCoveredQuietStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hrun : (z.2.1 root).ser.cert = .RUNNING)
    (hrootB : (z.2.1 root).ser.phase = .B)
    (hout : (z.2.1 root).ser.out = .DONE)
    (hchildB :
      (z.2.1 (ring.rightNeighbor root)).ser.phase = .B) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z root) := by
  have hbase := bankWordRenewalWaveRootOutgoingCoveredFrameStep
    ring root s hn hbank hs z hz hwave.wave
    hrun hrootB hout hchildB
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 root) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass root).2
  have hpost := clockPostOutgoing ring root z.2.1 root
    (by omega : 2 ≤ n) hfixed rfl
  have hrow := L3.EWord.validationRootDoneDoneSerFrame
    (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
    hpost.1 hpost.2 hrun hrootB hout hchildB
  have hne : ring.rightNeighbor root ≠ root :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) root
  have hserial :
      ∀ i : Fin n,
        ((bankWordEpochNext ring root z root).2.1 i).ser =
          (z.2.1 i).ser := by
    intro i
    by_cases hi : i = root
    · rw [hi]
      change ((phiW ring z.2.1 root) root).ser =
        (z.2.1 root).ser
      rw [phiW_ser_source]
      exact hrow.2.1
    · by_cases hj : i = ring.rightNeighbor root
      · rw [hj]
        change ((phiW ring z.2.1 root)
          (ring.rightNeighbor root)).ser =
            (z.2.1 (ring.rightNeighbor root)).ser
        rw [phiW_ser_target ring z.2.1 root hne]
        exact hrow.2.2
      · change
          ((if i = root then
              (pairW (z.2.1 root)
                (z.2.1 (ring.rightNeighbor root))).1
            else if i = ring.rightNeighbor root then
              (pairW (z.2.1 root)
                (z.2.1 (ring.rightNeighbor root))).2
            else z.2.1 i)).ser =
            (z.2.1 i).ser
        rw [if_neg hi, if_neg hj]
  refine ⟨hbase, ?_⟩
  intro hactive g hreturn k hk hc
  have holdActive :
      (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING := by
    simpa only [hserial root] using hactive
  have holdReturn : L3.EWord.ReturnShape ring root z.2.1 g :=
    bankWordRenewalWaveReturnShapeSiteFrame
      ring root z.2.1
      (bankWordEpochNext ring root z root).2.1 g
      (fun i _ => hserial (L3.EWord.site ring root i))
      hreturn
  have holdC :
      (z.2.1 (L3.EWord.site ring root k.val)).ser.phase =
        .C := by
    simpa only [hserial (L3.EWord.site ring root k.val)]
      using hc
  have hquiet := hwave.returnSuffixQuiet
    holdActive g holdReturn k hk holdC
  simpa only [hserial (L3.EWord.site ring root k.val)]
    using hquiet

/-- The incoming ROOT_IN edge closes the established full J-W
lineage and the new all-RETURN-suffix quietness clause without
an additional hreturnQuiet premise.
Consumer: the root incoming case of the strengthened J-W induction. -/
theorem bankWordRenewalWaveRootIncomingStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hpred : ring.rightNeighbor e = root)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z e) := by
  have hseam : e = L3.EWord.site ring root (n - 1) :=
    bankWordRenewalWaveIncomingIsSeam ring root e
      (by omega : 2 ≤ n) hpred
  have hreturnQuiet :
      ∀ hactive :
        ((z.2.1 root).ser.cert = .RUNNING ∧
         (z.2.1 root).ser.wphase = .VALIDATING),
        L3.EWord.ReturnShape ring root z.2.1
          (Classical.choose (hwave.wave.2 hactive)) →
        (z.2.1 e).ser.phase = .C →
        (z.2.1 e).ser.probe ≠ .PENDING := by
    intro hactive hreturn hsourceC
    have hstatus := bankWordRenewalWaveReturnSeamQuiet
      ring root z.2.1 e
      (Classical.choose (hwave.wave.2 hactive))
      hreturn hseam
      (fun k hk hc =>
        hwave.returnSuffixQuiet hactive
          (Classical.choose (hwave.wave.2 hactive))
          hreturn k hk hc)
    rcases hstatus with hF | hC
    · rw [hF] at hsourceC
      cases hsourceC
    · exact hC.2
  have hbase : BankWordRenewalFrontierWaveLineage ring root
      (bankWordEpochNext ring root z e) :=
    bankWordRenewalWaveRootIncomingGuardedStep
      ring root e s hn hbank hs z hz hpred hwave.wave
      hreturnQuiet
  refine ⟨hbase, ?_⟩
  intro hactiveNew gnew hreturnNew k hk hcnew
  have hactiveOld :
      (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING :=
    bankWordRenewalWaveRootIncomingActiveWasOld
      ring root e s hn hbank hs z hz hpred hactiveNew
  obtain ⟨gold, req, stamp, hshape, hsites⟩ :=
    hwave.wave.2 hactiveOld
  have hframe := bankWordRenewalWaveRootIncomingActiveFrameStep
    ring root e s hn hbank hs z hz hpred gold hshape
  rcases hshape.stageShape with hforward | hreturn
  · rcases hframe.1.stageShape with hforwardNew | hreturnNewGold
    · exact False.elim
        (bankWordRenewalWaveForwardExcludesReturn
          ring root (bankWordEpochNext ring root z e).2.1
          gold gnew hforwardNew hreturnNew)
    · have hf : gold.stage = .forward := hforward.isForward
      have hr : gold.stage = .returning :=
        hreturnNewGold.isReturn
      rw [hf] at hr
      cases hr
  · have hsourceQuiet :
        (z.2.1 e).ser.phase = .F ∨
        ((z.2.1 e).ser.phase = .C ∧
          (z.2.1 e).ser.probe ≠ .PENDING) :=
      bankWordRenewalWaveReturnSeamQuiet
        ring root z.2.1 e gold hreturn hseam
        (fun j hj hc =>
          hwave.returnSuffixQuiet hactiveOld
            gold hreturn j hj hc)
    have hsourceFrame :=
      bankWordRenewalWaveRootIncomingQuietSourceFrame
        ring root e s hn hbank hs z hz hpred
        hactiveOld.1 hsourceQuiet
    have hclass := bankWordEpochReachablePhysicalRootClass
      ring hn hbank root s hs z hz
    have hfixed : WFixedRoot ring root
        (phiW ring z.2.1 e) :=
      ((bankWordSerializerRootClassClosed ring hn hbank root).2
        z.2.1 hclass e).2
    have hpost := clockPostIncoming ring root z.2.1 e
      (by omega : 2 ≤ n) hfixed hpred
    have hearly := L3.EWord.validationSeamEarlySer
      ring root z.2.1 e (by omega : 3 ≤ n)
      hseam hpost.1 hpost.2
      (by simpa only [hpred] using hactiveOld.1)
    have hserial :
        ∀ i : Nat, i < n →
          ((bankWordEpochNext ring root z e).2.1
            (L3.EWord.site ring root i)).ser =
          (z.2.1 (L3.EWord.site ring root i)).ser := by
      intro i hi
      by_cases hearlyIndex : i + 1 < n
      · change
          ((phiW ring z.2.1 e)
            (L3.EWord.site ring root i)).ser =
          (z.2.1 (L3.EWord.site ring root i)).ser
        exact hearly i hearlyIndex
      · have hlastIndex : i = n - 1 := by omega
        rw [hlastIndex]
        simpa only [hseam] using hsourceFrame.1
    have holdReturn :
        L3.EWord.ReturnShape ring root z.2.1 gnew :=
      bankWordRenewalWaveReturnShapeSiteFrame
        ring root z.2.1
        (bankWordEpochNext ring root z e).2.1
        gnew hserial hreturnNew
    have holdC :
        (z.2.1 (L3.EWord.site ring root k.val)).ser.phase =
          .C := by
      simpa only [hserial k.val k.isLt] using hcnew
    have hq := hwave.returnSuffixQuiet
      hactiveOld gnew holdReturn k hk holdC
    simpa only [hserial k.val k.isLt] using hq

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- A positive-lease S1 starts only a CURRENT wave, not a
VALIDATING RETURN. Consumer: ROOT_OUT case of R10a J-W. -/
theorem bankWordRenewalWaveRootOutgoingSoftStartQuietStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hrequested : (z.2.1 root).ser.cert = .REQUESTED)
    (hpositive : 0 < (z.2.1 root).siLease.val) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z root) := by
  have hbase := bankWordRenewalWaveRootOutgoingSoftStartStep
    ring root s hn hbank hs z hz hrequested hpositive
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 root) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass root).2
  have hpost := clockPostOutgoing ring root z.2.1 root
    (by omega : 2 ≤ n) hfixed rfl
  have hsoft := bankWordRenewalFrontierSoftSOneDoesNotValidate
    (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
    hpost.1 hpost.2 hrequested hpositive
  have hcurrent :
      ((bankWordEpochNext ring root z root).2.1 root).ser.wphase =
        .CURRENT := by
    change ((phiW ring z.2.1 root) root).ser.wphase =
      .CURRENT
    rw [phiW_ser_source]
    exact hsoft.2.2.1
  refine ⟨hbase, ?_⟩
  intro hactive g hreturn k hk hc
  rw [hcurrent] at hactive
  cases hactive.2

/-- A C/F root recovery SR explicitly retires the root to IDLE.
Consequently no validating RETURN can remain, and all historical
lineage implications are vacuous. Consumer: ROOT_OUT SR arm. -/
theorem bankWordRenewalWaveRootOutgoingRecoveryQuietStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hcert :
      (z.2.1 root).ser.cert = .IDLE ∨
      (z.2.1 root).ser.cert = .RUNNING)
    (hphase :
      (z.2.1 root).ser.phase = .C ∨
      (z.2.1 root).ser.phase = .F) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z root) := by
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 root) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass root).2
  have hpost := clockPostOutgoing ring root z.2.1 root
    (by omega : 2 ≤ n) hfixed rfl
  have hrec := serRootOutgoingRecovery
    (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
    hpost.1 hpost.2 hcert hphase
  have hidle :
      ((bankWordEpochNext ring root z root).2.1 root).ser.cert =
        .IDLE := by
    change ((phiW ring z.2.1 root) root).ser.cert = .IDLE
    rw [phiW_ser_source]
    exact hrec.2.1
  refine ⟨?_, ?_⟩
  · unfold BankWordRenewalFrontierWaveLineage
      BankWordRenewalFrontierTicketLineage
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro h
      rw [hidle] at h
      cases h
    · intro h
      rw [hidle] at h
      cases h.1
    · intro h
      rw [hidle] at h
      cases h.1
    · intro h
      rw [hidle] at h
      cases h.1
  · intro hactive g hr k hk hc
    rw [hidle] at hactive
    cases hactive.1

/-- The root rows for which the historical wave ledger has
already been closed: hard/soft S1, S6, and B/DONE+B S2R.
This is deliberately not the remaining S2R challenge/admission
census. Consumer: ROOT_OUT partial assembly in R10a J-W. -/
theorem bankWordRenewalWaveRootOutgoingKnownRowsStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hcase :
      (z.2.1 root).ser.cert = .REQUESTED ∨
      ((z.2.1 root).ser.cert ≠ .REQUESTED ∧
       (z.2.1 root).ser.phase = .B ∧
       (z.2.1 root).ser.out = .DONE ∧
       (z.2.1 (ring.rightNeighbor root)).ser.phase = .F) ∨
      ((z.2.1 root).ser.cert = .RUNNING ∧
       (z.2.1 root).ser.phase = .B ∧
       (z.2.1 root).ser.out = .DONE ∧
       (z.2.1 (ring.rightNeighbor root)).ser.phase = .B)) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z root) := by
  rcases hcase with hrequested | hfinish | hcovered
  · by_cases hzero : (z.2.1 root).siLease.val = 0
    · exact bankWordRenewalWaveRootOutgoingHardStartQuietStep
        ring root s hn hbank hs z hz hwave
        hrequested hzero
    · have hpositive : 0 < (z.2.1 root).siLease.val := by omega
      exact bankWordRenewalWaveRootOutgoingSoftStartQuietStep
        ring root s hn hbank hs z hz hrequested hpositive
  · exact bankWordRenewalWaveRootOutgoingFinishQuietStep
      ring root s hn hbank hs z hz
      hfinish.1 hfinish.2.1 hfinish.2.2.1
      hfinish.2.2.2
  · obtain ⟨hrun, hrootB, hout, hchildB⟩ := hcovered
    exact bankWordRenewalWaveRootOutgoingCoveredQuietStep
      ring root s hn hbank hs z hz hwave
      hrun hrootB hout hchildB

/-- If neither endpoint is the root, the root cannot become
VALIDATING while previously inactive. This supplies the whole
strengthened J-W implication without any guessed worker ticket.
Consumer: inactive INTERNAL case of the epoch induction. -/
theorem bankWordRenewalWaveInternalInactiveQuietStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankWordEpochState n)
    (he : e ≠ root)
    (hj : ring.rightNeighbor e ≠ root)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hinactive :
      ¬ ((z.2.1 root).ser.cert = .RUNNING ∧
         (z.2.1 root).ser.wphase = .VALIDATING)) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z e) := by
  have hbase := bankWordRenewalFrontierWaveInactiveNonrootStep
    ring root e z he hj hwave.wave hinactive
  have hroot := bankWordHardEpochRootRemoteFrame
    ring root z e he.symm hj.symm
  refine ⟨hbase, ?_⟩
  intro hactive g hr k hk hc
  have hold :
      (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING := by
    simpa only [hroot] using hactive
  exact False.elim (hinactive hold)

/-- An unvisited nonroot pair cannot coexist with RETURN when
scrub=n: its source would be both visited and remote. For a
FORWARD witness the physical transport remains FORWARD and is
incompatible with any newly asserted RETURN shape. Consumer:
unvisitedSuffix INTERNAL class, including the strong quiet clause. -/
theorem bankWordRenewalWaveInternalUnvisitedQuietStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (he : e ≠ root)
    (hj : ring.rightNeighbor e ≠ root)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hunvisited : ∀ g : L3.EWord.ValidationGhost,
      L3.EWord.ValidationShape ring root z.2.1 g →
      L3.EWord.validationEdgeClass ring root g e =
        .unvisitedSuffix) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z e) := by
  have hbase := bankWordRenewalFrontierWaveUnvisitedNonrootStep
    ring root e s hn hbank hs z hz he hj hwave.wave
    hunvisited
  refine ⟨hbase, ?_⟩
  intro hactiveNew gnew hrnew k hk hc
  have hroot := bankWordHardEpochRootRemoteFrame
    ring root z e he.symm hj.symm
  have hactiveOld :
      (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING := by
    simpa only [hroot] using hactiveNew
  obtain ⟨g, req, stamp, hshape, hsites⟩ :=
    hwave.wave.2 hactiveOld
  have hun : L3.EWord.validationEdgeClass ring root g e =
      .unvisitedSuffix := hunvisited g hshape
  have hremote := L3.EWord.unvisitedSuffixRemote
    ring root g e hun
  have hforward : L3.EWord.ForwardShape ring root z.2.1 g := by
    rcases hshape.stageShape with hf | hr
    · exact hf
    · have hoff : PPL.cyclicOffset ring root e < n :=
        L3.EWord.validationOffsetBound ring root e
      have hnot := (hremote
        (⟨PPL.cyclicOffset ring root e, hoff⟩ : Fin n)
        (by rw [hr.covered]; exact hoff)).1
      have hloc := L3.EWord.validationOffsetRepresentative
        ring root e
      exact False.elim (hnot hloc)
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 e) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass e).2
  have hno := bankWordRootNonrootHardAcceptFalse
    ring hn hbank root s hs z hz e he
  have hghost := L3.EWord.unvisitedSuffixGhostUnchanged
    ring root z.2.1 g e hshape hremote
  have hshapeNew :
      L3.EWord.ValidationShape ring root
        (bankWordEpochNext ring root z e).2.1 g := by
    have ht := L3.EWord.validationUnvisitedSuffixClass
      ring root z.2.1 g e hshape hfixed hno hun
    rw [hghost] at ht
    exact ht
  rcases hshapeNew.stageShape with hfnew | hrnew
  · exact False.elim (bankWordRenewalWaveForwardExcludesReturn
      ring root (bankWordEpochNext ring root z e).2.1
      g gnew hfnew hrnew)
  · have hF : g.stage = .forward := hforward.isForward
    have hR : g.stage = .returning := hrnew.isReturn
    rw [hF] at hR
    cases hR

/-- If a whole selected pair frames every serializer and
historical validation ticket, and the EWord physical shape
transports without moving its ghost, then ALL five ledger
clauses and the stronger all-RETURN quiet clause frame.
Consumer: real internal B/DONE+B S2N idle subrow. -/
private theorem bankWordRenewalWaveFullFrameQuietStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankWordEpochState n)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hserial : ∀ i : Fin n,
      ((bankWordEpochNext ring root z e).2.1 i).ser =
        (z.2.1 i).ser)
    (hticket : ∀ i : Fin n,
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z e)).validation i =
      (bankWordHardEpochLedger ring root z).validation i)
    (hshape : ∀ g : L3.EWord.ValidationGhost,
      L3.EWord.ValidationShape ring root z.2.1 g →
      L3.EWord.ValidationShape ring root
        (bankWordEpochNext ring root z e).2.1 g) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z e) := by
  have hbase :
      BankWordRenewalFrontierTicketLineage ring root
        (bankWordEpochNext ring root z e) := by
    simpa only [BankWordRenewalFrontierTicketLineage,
      hserial root, hserial (ring.rightNeighbor root),
      hticket root, hticket (ring.rightNeighbor root)] using
        hwave.wave.1
  have hnewWave :
      BankWordRenewalFrontierWaveLineage ring root
        (bankWordEpochNext ring root z e) := by
    refine ⟨hbase, ?_⟩
    intro hnewActive
    have holdActive :
        (z.2.1 root).ser.cert = .RUNNING ∧
        (z.2.1 root).ser.wphase = .VALIDATING := by
      simpa only [hserial root] using hnewActive
    obtain ⟨g, req, stamp, holdShape, holdSites⟩ :=
      hwave.wave.2 holdActive
    refine ⟨g, req, stamp, hshape g holdShape, ?_⟩
    intro k hk
    simpa only [BankWordRenewalFrontierWaveSiteTicket,
      hserial (L3.EWord.site ring root k.val),
      hticket (L3.EWord.site ring root k.val)] using
        holdSites k hk
  refine ⟨hnewWave, ?_⟩
  intro hnewActive g hreturn k hk hc
  have holdActive :
      (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING := by
    simpa only [hserial root] using hnewActive
  have holdReturn : L3.EWord.ReturnShape ring root z.2.1 g :=
    bankWordRenewalWaveReturnShapeSiteFrame
      ring root z.2.1
      (bankWordEpochNext ring root z e).2.1 g
      (fun i _ => hserial (L3.EWord.site ring root i))
      hreturn
  have holdC :
      (z.2.1 (L3.EWord.site ring root k.val)).ser.phase =
        .C := by
    simpa only [hserial (L3.EWord.site ring root k.val)] using hc
  have hquiet := hwave.returnSuffixQuiet
    holdActive g holdReturn k hk holdC
  simpa only [hserial (L3.EWord.site ring root k.val)] using hquiet

/-- An INTERNAL B/DONE+B S2N service is genuinely stationary
on both serializer records and historical tickets. EWord
validationTransport and the literal stationary ghost equation
complete the whole strengthened J-W step, without assumptions
about arbitrary unvisited scratch. Consumer: coveredInside idle
arm of the INTERNAL edge induction. -/
theorem bankWordRenewalWaveInternalCoveredDoneQuietStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (he : e ≠ root)
    (hj : ring.rightNeighbor e ≠ root)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hb : (z.2.1 e).ser.phase = .B)
    (hd : (z.2.1 e).ser.out = .DONE)
    (hq : (z.2.1 (ring.rightNeighbor e)).ser.phase = .B) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z e) := by
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass e).2
  have hpost := clockPostInternal ring root z.2.1 e
    (by omega : 2 ≤ n) hfixed he hj
  have hrow : (serW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).row = "S2N" := by
    simp [serW, serializerStep, ProjW.lift,
      hpost.1, hpost.2, hb, hd, hq]
  have hser := L3.EWord.internalDoneDoneSerFrame
    (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
    hpost.1 hpost.2 hb hd hq
  have hne : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) e
  have hserial : ∀ i : Fin n,
      ((bankWordEpochNext ring root z e).2.1 i).ser =
        (z.2.1 i).ser := by
    intro i
    by_cases hi : i = e
    · rw [hi]
      change ((phiW ring z.2.1 e) e).ser = (z.2.1 e).ser
      rw [phiW_ser_source]
      exact hser.1
    · by_cases hjj : i = ring.rightNeighbor e
      · rw [hjj]
        change ((phiW ring z.2.1 e)
          (ring.rightNeighbor e)).ser =
            (z.2.1 (ring.rightNeighbor e)).ser
        rw [phiW_ser_target ring z.2.1 e hne]
        exact hser.2
      · change ((phiW ring z.2.1 e) i).ser =
          (z.2.1 i).ser
        exact phiW_ser_remote ring z.2.1 e i hi hjj
  have hpair :
      wValidationPair (z.2.2.clock + 1)
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        ((bankWordHardEpochLedger ring root z).validation e)
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor e)) =
      ((bankWordHardEpochLedger ring root z).validation e,
       (bankWordHardEpochLedger ring root z).validation
         (ring.rightNeighbor e)) := by
    simp [wValidationPair, hrow, hd, hq]
  have hticket : ∀ i : Fin n,
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z e)).validation i =
      (bankWordHardEpochLedger ring root z).validation i := by
    intro i
    rw [bankWordHardEpochLedgerNext]
    change
      (if i = e then
        (wValidationPair (z.2.2.clock + 1)
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          ((bankWordHardEpochLedger ring root z).validation e)
          ((bankWordHardEpochLedger ring root z).validation
            (ring.rightNeighbor e))).1
       else if i = ring.rightNeighbor e then
        (wValidationPair (z.2.2.clock + 1)
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          ((bankWordHardEpochLedger ring root z).validation e)
          ((bankWordHardEpochLedger ring root z).validation
            (ring.rightNeighbor e))).2
       else (bankWordHardEpochLedger ring root z).validation i) =
      (bankWordHardEpochLedger ring root z).validation i
    simp only [hpair]
    by_cases hi : i = e
    · simp [hi]
    · by_cases hjj : i = ring.rightNeighbor e
      · simp [hjj, hne]
      · simp [hi, hjj]
  have hno : (serW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).hard.hardAccept = false :=
    L3.EWord.nonrootNoAccept
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e)) hpost.1
  have hstart : (serW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).hard.hardS1 = false :=
    L3.EWord.nonrootHardStartFalse
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e)) hpost.1
  have hshape : ∀ g : L3.EWord.ValidationGhost,
      L3.EWord.ValidationShape ring root z.2.1 g →
      L3.EWord.ValidationShape ring root
        (bankWordEpochNext ring root z e).2.1 g := by
    intro g oldShape
    have hghost := L3.EWord.internalDoneDoneGhostFixed
      ring root z.2.1 g e hstart hd hq
    have ht := (L3.EWord.validationTransport
      (c := compileAdvice (ceilLogTwo n)) ring root)
        z.2.1 g e oldShape hfixed hno
    rw [hghost] at ht
    exact ht
  exact bankWordRenewalWaveFullFrameQuietStep
    ring root e z hwave hserial hticket hshape

/-- Literal internal S3/S4 preserves a quiet C source and a
quiet C-or-F responder. The only C newly written at the
responder is serCanonicalC, whose probe is NONE.
Consumer: stationary RETURN suffix S3/S4 site safety in J-W. -/
theorem bankWordRenewalWaveReturnSuffixPairQuiet {c : Compiled}
    (x y : ProjW c)
    (hx : (postW x y).eX.l = false)
    (hy : (postW x y).eY.l = false)
    (hsource :
      x.ser.phase = .F ∨
      (x.ser.phase = .C ∧ x.ser.probe ≠ .PENDING))
    (htarget :
      y.ser.phase = .F ∨
      (y.ser.phase = .C ∧ y.ser.probe ≠ .PENDING)) :
    ((serW x y).x.phase = .C →
      (serW x y).x.probe ≠ .PENDING) ∧
    ((serW x y).y.phase = .C →
      (serW x y).y.probe ≠ .PENDING) := by
  rcases hsource with hf | ⟨hc, hp⟩
  · rcases htarget with hrightF | ⟨hrightC, hrightQ⟩
    · simp [serW, serializerStep, ProjW.lift,
        serCanonicalC, hx, hy, hf, hrightF]
    · simp [serW, serializerStep, ProjW.lift,
        serCanonicalC, hx, hy, hf, hrightC, hrightQ]
  · rcases htarget with hrightF | ⟨hrightC, hrightQ⟩
    · cases hprobe : x.ser.probe <;>
        simp [serW, serializerStep, ProjW.lift,
          serCanonicalC, hx, hy, hc, hp, hrightF,
          hprobe] at hp ⊢
    · cases hprobe : x.ser.probe <;>
        simp [serW, serializerStep, ProjW.lift,
          serCanonicalC, hx, hy, hc, hp, hrightC,
          hrightQ, hprobe] at hp ⊢

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- A selected physical service updates exactly the historical
tickets of its source and right responder by the OLD
wValidationPair. Consumer: S2R/S2N/S3/S4 actual-lineage transport
in the R10a J-W edge induction. -/
theorem bankWordRenewalWaveSelectedTicketPairStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankWordEpochState n)
    (hn : 2 ≤ n) :
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).validation e =
      (wValidationPair (z.2.2.clock + 1)
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        ((bankWordHardEpochLedger ring root z).validation e)
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor e))).1 ∧
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).validation
        (ring.rightNeighbor e) =
      (wValidationPair (z.2.2.clock + 1)
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        ((bankWordHardEpochLedger ring root z).validation e)
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor e))).2 := by
  have hne : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring hn e
  constructor
  · rw [bankWordHardEpochLedgerNext]
    change
      (if e = e then
        (wValidationPair (z.2.2.clock + 1)
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          ((bankWordHardEpochLedger ring root z).validation e)
          ((bankWordHardEpochLedger ring root z).validation
            (ring.rightNeighbor e))).1
       else if e = ring.rightNeighbor e then
        (wValidationPair (z.2.2.clock + 1)
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          ((bankWordHardEpochLedger ring root z).validation e)
          ((bankWordHardEpochLedger ring root z).validation
            (ring.rightNeighbor e))).2
       else (bankWordHardEpochLedger ring root z).validation e) =
      (wValidationPair (z.2.2.clock + 1)
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        ((bankWordHardEpochLedger ring root z).validation e)
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor e))).1
    rw [if_pos rfl]
  · rw [bankWordHardEpochLedgerNext]
    change
      (if ring.rightNeighbor e = e then
        (wValidationPair (z.2.2.clock + 1)
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          ((bankWordHardEpochLedger ring root z).validation e)
          ((bankWordHardEpochLedger ring root z).validation
            (ring.rightNeighbor e))).1
       else if ring.rightNeighbor e = ring.rightNeighbor e then
        (wValidationPair (z.2.2.clock + 1)
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
          ((bankWordHardEpochLedger ring root z).validation e)
          ((bankWordHardEpochLedger ring root z).validation
            (ring.rightNeighbor e))).2
       else (bankWordHardEpochLedger ring root z).validation
         (ring.rightNeighbor e)) =
      (wValidationPair (z.2.2.clock + 1)
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        ((bankWordHardEpochLedger ring root z).validation e)
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor e))).2
    rw [if_neg hne, if_pos rfl]

theorem bankWordRenewalWaveInternalChallengeTicketStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankWordEpochState n) (hn : 2 ≤ n)
    (parent : WValidationTicket)
    (hrow :
      (bankWordEpochSelectedReceipt ring z e).serializer.row =
        "S2N")
    (hnew : (z.2.1 e).ser.out = .NEW)
    (hchild :
      (z.2.1 (ring.rightNeighbor e)).ser.phase = .C)
    (hparent : wParentTicket
      ((bankWordHardEpochLedger ring root z).validation e) =
        some parent) :
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).validation e =
        some { parent with stage := .waiting } ∧
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).validation
        (ring.rightNeighbor e) =
        some { parent with stage := .pending } := by
  change (serW (z.2.1 e)
    (z.2.1 (ring.rightNeighbor e))).row = "S2N" at hrow
  have hpair := bankWordRenewalFrontierWaveChallengeTickets
    (z.2.2.clock + 1)
    (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
    ((bankWordHardEpochLedger ring root z).validation e)
    ((bankWordHardEpochLedger ring root z).validation
      (ring.rightNeighbor e))
    parent hrow hnew hchild hparent
  have hnext := bankWordRenewalWaveSelectedTicketPairStep
    ring root e z hn
  constructor
  · rw [hnext.1, hpair]
  · rw [hnext.2, hpair]

/-- INTERNAL S2N WAIT/INTERNAL_OK joins the two old tickets
with equal request/start stamps into DONE and broadcaster.
Consumer: forward pivot-advance clause one at parent and
clause one at the new B child. -/
theorem bankWordRenewalWaveInternalAdmissionTicketStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankWordEpochState n) (hn : 2 ≤ n)
    (parent child : WValidationTicket)
    (hrow :
      (bankWordEpochSelectedReceipt ring z e).serializer.row =
        "S2N")
    (hw : (z.2.1 e).ser.out = .WAIT)
    (hc : (z.2.1 (ring.rightNeighbor e)).ser.phase = .C)
    (hi : (z.2.1 (ring.rightNeighbor e)).ser.probe =
      .INTERNAL_OK)
    (htParent : wTicketAt .waiting
      ((bankWordHardEpochLedger ring root z).validation e) =
        some parent)
    (htChild : wTicketAt .observedInternal
      ((bankWordHardEpochLedger ring root z).validation
        (ring.rightNeighbor e)) = some child)
    (hreq : parent.requestedAt = child.requestedAt)
    (hstamp : parent.startedAt = child.startedAt) :
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).validation e =
        some { parent with stage := .done } ∧
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).validation
        (ring.rightNeighbor e) =
        some { parent with stage := .broadcaster } := by
  change (serW (z.2.1 e)
    (z.2.1 (ring.rightNeighbor e))).row = "S2N" at hrow
  have hpair :
      wValidationPair (z.2.2.clock + 1)
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        ((bankWordHardEpochLedger ring root z).validation e)
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor e)) =
      (some { parent with stage := .done },
       some { parent with stage := .broadcaster }) := by
    simp [wValidationPair, hrow, hw, hc, hi, wAdmitTickets,
      htParent, htChild, wJoinTickets, hreq, hstamp,
      wTicketStage]
  have hnext := bankWordRenewalWaveSelectedTicketPairStep
    ring root e z hn
  constructor
  · rw [hnext.1, hpair]
  · rw [hnext.2, hpair]

/-- INTERNAL S2N WAIT/LEAF_OK is the forward-to-RETURN
admission; the parent becomes DONE and the last covered C
becomes returned F. This uses the OLD observedLeaf ticket,
not merely a physical LEAF_OK flag.
Consumer: the pivot-entry clause five of J-W. -/
theorem bankWordRenewalWaveInternalLeafTicketStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankWordEpochState n) (hn : 2 ≤ n)
    (parent child : WValidationTicket)
    (hrow :
      (bankWordEpochSelectedReceipt ring z e).serializer.row =
        "S2N")
    (hw : (z.2.1 e).ser.out = .WAIT)
    (hc : (z.2.1 (ring.rightNeighbor e)).ser.phase = .C)
    (hl : (z.2.1 (ring.rightNeighbor e)).ser.probe =
      .LEAF_OK)
    (htParent : wTicketAt .waiting
      ((bankWordHardEpochLedger ring root z).validation e) =
        some parent)
    (htChild : wTicketAt .observedLeaf
      ((bankWordHardEpochLedger ring root z).validation
        (ring.rightNeighbor e)) = some child)
    (hreq : parent.requestedAt = child.requestedAt)
    (hstamp : parent.startedAt = child.startedAt) :
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).validation e =
        some { parent with stage := .done } ∧
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).validation
        (ring.rightNeighbor e) =
        some { parent with stage := .returned } := by
  change (serW (z.2.1 e)
    (z.2.1 (ring.rightNeighbor e))).row = "S2N" at hrow
  have hpair :
      wValidationPair (z.2.2.clock + 1)
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        ((bankWordHardEpochLedger ring root z).validation e)
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor e)) =
      (some { parent with stage := .done },
       some { parent with stage := .returned }) := by
    simp [wValidationPair, hrow, hw, hc, hl, wAdmitTickets,
      htParent, htChild, wJoinTickets, hreq, hstamp,
      wTicketStage]
  have hnext := bankWordRenewalWaveSelectedTicketPairStep
    ring root e z hn
  constructor
  · rw [hnext.1, hpair]
  · rw [hnext.2, hpair]

/-- During RETURN, an internal B/DONE source adjacent to
a returned F successor joins their old DONE/returned tickets.
The source is retagged returned while the F successor's
ticket remains unchanged. These are exactly the two values
needed when the RETURN pivot decreases by one.
Consumer: RETURN moving S2N clause five. -/
theorem bankWordRenewalWaveReturnMoveTicketStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankWordEpochState n) (hn : 2 ≤ n)
    (parent child : WValidationTicket)
    (hrow :
      (bankWordEpochSelectedReceipt ring z e).serializer.row =
        "S2N")
    (hd : (z.2.1 e).ser.out = .DONE)
    (hf : (z.2.1 (ring.rightNeighbor e)).ser.phase = .F)
    (htParent : wTicketAt .done
      ((bankWordHardEpochLedger ring root z).validation e) =
        some parent)
    (htChild : wTicketAt .returned
      ((bankWordHardEpochLedger ring root z).validation
        (ring.rightNeighbor e)) = some child)
    (hreq : parent.requestedAt = child.requestedAt)
    (hstamp : parent.startedAt = child.startedAt) :
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).validation e =
        some { parent with stage := .returned } ∧
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).validation
        (ring.rightNeighbor e) =
        (bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor e) := by
  change (serW (z.2.1 e)
    (z.2.1 (ring.rightNeighbor e))).row = "S2N" at hrow
  have hleft := bankWordRenewalFrontierWaveReturnAdmission
    (z.2.2.clock + 1)
    (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
    ((bankWordHardEpochLedger ring root z).validation e)
    ((bankWordHardEpochLedger ring root z).validation
      (ring.rightNeighbor e))
    parent child hrow hd hf htParent htChild hreq hstamp
  have hpairRight :
      (wValidationPair (z.2.2.clock + 1)
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        ((bankWordHardEpochLedger ring root z).validation e)
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor e))).2 =
        (bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor e) := by
    simp [wValidationPair, hrow, hd, hf]
  have hnext := bankWordRenewalWaveSelectedTicketPairStep
    ring root e z hn
  constructor
  · rw [hnext.1]
    exact hleft
  · rw [hnext.2]
    exact hpairRight

/-- An internal S3 C/PENDING child observing C is re-tagged
INTERNAL_OK/observedInternal without changing either timestamp.
The responder C ticket is framed. This is the exact historical
piece needed for the forward challengedChild class, clause
three of the wave lineage. -/
theorem bankWordRenewalWaveInternalObservationTicketStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankWordEpochState n) (hn : 2 ≤ n)
    (child : WValidationTicket)
    (hrow :
      (bankWordEpochSelectedReceipt ring z e).serializer.row =
        "S3")
    (hp : (z.2.1 e).ser.probe = .PENDING)
    (hc : (z.2.1 (ring.rightNeighbor e)).ser.phase = .C)
    (htChild : wTicketAt .pending
      ((bankWordHardEpochLedger ring root z).validation e) =
        some child) :
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).validation e =
        some { child with stage := .observedInternal } ∧
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).validation
        (ring.rightNeighbor e) =
        (bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor e) := by
  change (serW (z.2.1 e)
    (z.2.1 (ring.rightNeighbor e))).row = "S3" at hrow
  have hleft := bankWordRenewalFrontierWaveInternalObservation
    (z.2.2.clock + 1)
    (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
    ((bankWordHardEpochLedger ring root z).validation e)
    ((bankWordHardEpochLedger ring root z).validation
      (ring.rightNeighbor e))
    child hrow hp hc htChild
  have hright :
      (wValidationPair (z.2.2.clock + 1)
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        ((bankWordHardEpochLedger ring root z).validation e)
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor e))).2 =
      (bankWordHardEpochLedger ring root z).validation
        (ring.rightNeighbor e) := by
    simp [wValidationPair, hrow, hc]
  have hnext := bankWordRenewalWaveSelectedTicketPairStep
    ring root e z hn
  constructor
  · rw [hnext.1]
    exact hleft
  · rw [hnext.2]
    exact hright

/-- On a nonroot S3/S4 service with C/F source and B/F
responder, the actual right record is canonical C/OFF/NONE,
the right ticket is deleted, and the left ticket frames.
This deliberately deletes an obsolete B/returned F obligation:
the new C/NONE does not trigger any of the five covered-site
ticket clauses. Consumer: S3/S4 coveredInside cleanup. -/
theorem bankWordRenewalWaveInternalCanonicalCleanupStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (he : e ≠ root)
    (hj : ring.rightNeighbor e ≠ root)
    (hsource :
      (z.2.1 e).ser.phase = .C ∨
      (z.2.1 e).ser.phase = .F)
    (htarget :
      (z.2.1 (ring.rightNeighbor e)).ser.phase = .B ∨
      (z.2.1 (ring.rightNeighbor e)).ser.phase = .F) :
    ((bankWordEpochNext ring root z e).2.1
      (ring.rightNeighbor e)).ser =
      serCanonicalC (z.2.1 (ring.rightNeighbor e)).ser ∧
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).validation
        (ring.rightNeighbor e) = none ∧
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).validation e =
        (bankWordHardEpochLedger ring root z).validation e := by
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 e) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass e).2
  have hpost := clockPostInternal ring root z.2.1 e
    (by omega : 2 ≤ n) hfixed he hj
  have hne : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) e
  have hstep :
      (serW (z.2.1 e)
        (z.2.1 (ring.rightNeighbor e))).y =
      serCanonicalC (z.2.1 (ring.rightNeighbor e)).ser ∧
      ((wValidationPair (z.2.2.clock + 1)
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        ((bankWordHardEpochLedger ring root z).validation e)
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor e))).1 =
          (bankWordHardEpochLedger ring root z).validation e) ∧
      ((wValidationPair (z.2.2.clock + 1)
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        ((bankWordHardEpochLedger ring root z).validation e)
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor e))).2 = none) := by
    rcases hsource with hC | hF
    · rcases htarget with hB | hFright
      · simp [serW, serializerStep, ProjW.lift,
          wValidationPair, serCanonicalC,
          hpost.1, hpost.2, hC, hB]
      · simp [serW, serializerStep, ProjW.lift,
          wValidationPair, serCanonicalC,
          hpost.1, hpost.2, hC, hFright]
    · rcases htarget with hB | hFright
      · simp [serW, serializerStep, ProjW.lift,
          wValidationPair, serCanonicalC,
          hpost.1, hpost.2, hF, hB]
      · simp [serW, serializerStep, ProjW.lift,
          wValidationPair, serCanonicalC,
          hpost.1, hpost.2, hF, hFright]
  have hnext := bankWordRenewalWaveSelectedTicketPairStep
    ring root e z (by omega : 2 ≤ n)
  refine ⟨?_, ?_, ?_⟩
  · change ((phiW ring z.2.1 e)
      (ring.rightNeighbor e)).ser =
      serCanonicalC (z.2.1 (ring.rightNeighbor e)).ser
    rw [phiW_ser_target ring z.2.1 e hne]
    exact hstep.1
  · rw [hnext.2]
    exact hstep.2.2
  · rw [hnext.1]
    exact hstep.2.1

/-- Two simultaneous EWord RETURN grammars for the same real
serializer ring must have the same leftmost F pivot. At the
smaller proposed pivot, one grammar says F and the other
says completed B/DONE. Consumer: all-witness quietness transport
in the moving RETURN and S3/S4 clauses of R10a J-W. -/
theorem bankWordRenewalWaveReturnPivotUnique
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW c)
    (a b : L3.EWord.ValidationGhost)
    (ha : L3.EWord.ReturnShape ring root s a)
    (hb : L3.EWord.ReturnShape ring root s b) :
    a.pivot = b.pivot := by
  by_cases hab : a.pivot < b.pivot
  · have hF := ha.leftmostF
    have hB := (hb.completed
      (⟨a.pivot, ha.pivotBound⟩ : Fin n) hab).1
    rw [hF] at hB
    cases hB
  · by_cases hba : b.pivot < a.pivot
    · have hF := hb.leftmostF
      have hB := (ha.completed
        (⟨b.pivot, hb.pivotBound⟩ : Fin n) hba).1
      rw [hF] at hB
      cases hB
    · omega

/-- Non-B internal S3/S4 suffix rows are causally quiet:
the selected C/F pair can only frame a C with non-PENDING
probe or canonicalize an F to C/NONE. Remote sites frame.
Because any new RETURN witness has the same pivot as the
preserved RETURN grammar, the result holds for ALL witnesses.
Consumer: RETURN S3/S4 quiet clause of the J-W induction. -/
theorem bankWordRenewalWaveReturnNonBPairSuffixQuiet
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW c)
    (hn : 2 ≤ n)
    (g : L3.EWord.ValidationGhost)
    (hr : L3.EWord.ReturnShape ring root s g)
    (hnewReturn :
      L3.EWord.ReturnShape ring root (phiW ring s e) g)
    (hx : (postW (s e)
      (s (ring.rightNeighbor e))).eX.l = false)
    (hy : (postW (s e)
      (s (ring.rightNeighbor e))).eY.l = false)
    (hsource : (s e).ser.phase = .F ∨
      ((s e).ser.phase = .C ∧
        (s e).ser.probe ≠ .PENDING))
    (htarget : (s (ring.rightNeighbor e)).ser.phase = .F ∨
      ((s (ring.rightNeighbor e)).ser.phase = .C ∧
        (s (ring.rightNeighbor e)).ser.probe ≠ .PENDING))
    (hquiet : ∀ k : Fin n, g.pivot < k.val →
      (s (L3.EWord.site ring root k.val)).ser.phase = .C →
      (s (L3.EWord.site ring root k.val)).ser.probe ≠
        .PENDING) :
    ∀ gnew : L3.EWord.ValidationGhost,
      L3.EWord.ReturnShape ring root (phiW ring s e) gnew →
      ∀ k : Fin n, gnew.pivot < k.val →
      ((phiW ring s e)
        (L3.EWord.site ring root k.val)).ser.phase = .C →
      ((phiW ring s e)
        (L3.EWord.site ring root k.val)).ser.probe ≠
          .PENDING := by
  have hne : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring hn e
  have hpair := bankWordRenewalWaveReturnSuffixPairQuiet
    (s e) (s (ring.rightNeighbor e))
    hx hy hsource htarget
  intro gnew hrnew k hk hc
  have hpivot := bankWordRenewalWaveReturnPivotUnique
    ring root (phiW ring s e) g gnew hnewReturn hrnew
  have hkOld : g.pivot < k.val := by
    rw [← hpivot] at hk
    exact hk
  by_cases hsrc : L3.EWord.site ring root k.val = e
  · have hser :
        ((phiW ring s e)
          (L3.EWord.site ring root k.val)).ser =
          (serW (s e) (s (ring.rightNeighbor e))).x := by
      rw [hsrc, phiW_ser_source]
    have hC :
        (serW (s e) (s (ring.rightNeighbor e))).x.phase =
          .C := by
      simpa only [hser] using hc
    have hq := hpair.1 hC
    simpa only [hser] using hq
  · by_cases hdst :
        L3.EWord.site ring root k.val =
          ring.rightNeighbor e
    · have hser :
          ((phiW ring s e)
            (L3.EWord.site ring root k.val)).ser =
            (serW (s e) (s (ring.rightNeighbor e))).y := by
        rw [hdst, phiW_ser_target ring s e hne]
      have hC :
          (serW (s e) (s (ring.rightNeighbor e))).y.phase =
            .C := by
        simpa only [hser] using hc
      have hq := hpair.2 hC
      simpa only [hser] using hq
    · have hframe := phiW_ser_remote
        ring s e (L3.EWord.site ring root k.val)
        hsrc hdst
      have holdC :
          (s (L3.EWord.site ring root k.val)).ser.phase =
            .C := by
        simpa only [hframe] using hc
      have hq := hquiet k hkOld holdC
      simpa only [hframe] using hq

/-- In the literal RETURN B/DONE→F move, the pivot decreases
one site. The new pivot is F/CURRENT, and the old pivot stays
F. No C/PENDING is written. For any RETURN witness of the
successor, pivot uniqueness reduces quietness to old suffix
sites, which are either framed or still F.
Consumer: the remaining strong quiet clause in the moving
RETURN S2N case, independently of historical ticket joins. -/
theorem bankWordRenewalWaveReturnMoveSuffixQuiet
    {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW c)
    (hn : 2 ≤ n)
    (g : L3.EWord.ValidationGhost)
    (hr : L3.EWord.ReturnShape ring root s g)
    (hnewReturn :
      L3.EWord.ReturnShape ring root (phiW ring s e)
        { g with pivot := g.pivot - 1 })
    (hp : 1 < g.pivot)
    (he : e = L3.EWord.site ring root (g.pivot - 1))
    (hx : (postW (s e)
      (s (ring.rightNeighbor e))).eX.l = false)
    (hy : (postW (s e)
      (s (ring.rightNeighbor e))).eY.l = false)
    (hb : (s e).ser.phase = .B)
    (hd : (s e).ser.out = .DONE)
    (hf : (s (ring.rightNeighbor e)).ser.phase = .F)
    (hquiet : ∀ k : Fin n, g.pivot < k.val →
      (s (L3.EWord.site ring root k.val)).ser.phase = .C →
      (s (L3.EWord.site ring root k.val)).ser.probe ≠
        .PENDING) :
    ∀ gnew : L3.EWord.ValidationGhost,
      L3.EWord.ReturnShape ring root (phiW ring s e) gnew →
      ∀ k : Fin n, gnew.pivot < k.val →
      ((phiW ring s e)
        (L3.EWord.site ring root k.val)).ser.phase = .C →
      ((phiW ring s e)
        (L3.EWord.site ring root k.val)).ser.probe ≠
          .PENDING := by
  have hpred : g.pivot - 1 + 1 = g.pivot := by omega
  have hbound : g.pivot - 1 + 1 < n := by
    have hlt := hr.pivotBound
    omega
  have hne : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring hn e
  have hj : ring.rightNeighbor e =
      L3.EWord.site ring root g.pivot := by
    have ht := L3.EWord.validationParentNeighbor
      ring root (g.pivot - 1) e he
    rw [hpred] at ht
    exact ht
  have hrow := L3.EWord.validationReturnMoveSerializer
    (s e) (s (ring.rightNeighbor e)) hx hy hb hd hf
  have htarget :
      ((phiW ring s e)
        (L3.EWord.site ring root g.pivot)).ser.phase =
          .F := by
    rw [← hj, phiW_ser_target ring s e hne, hrow.2.2.2]
    exact hf
  intro gnew hrnew k hk hc
  have hpivot := bankWordRenewalWaveReturnPivotUnique
    ring root (phiW ring s e)
    { g with pivot := g.pivot - 1 } gnew
    hnewReturn hrnew
  have hkLeft : g.pivot - 1 < k.val := by
    have ht : ({ g with pivot := g.pivot - 1 }).pivot <
        k.val := by rw [hpivot]; exact hk
    exact ht
  by_cases hpivotSite : k.val = g.pivot
  · have hsite :
        L3.EWord.site ring root k.val =
          L3.EWord.site ring root g.pivot := by
      rw [hpivotSite]
    have hwrong :
        ((phiW ring s e)
          (L3.EWord.site ring root g.pivot)).ser.phase =
            .C := by
      simpa only [hsite] using hc
    rw [htarget] at hwrong
    cases hwrong
  · have hgreater : g.pivot < k.val := by omega
    have hframe := L3.EWord.validationParentFrame
      ring root s (g.pivot - 1) e
      hbound he k.val k.isLt (by omega)
      (by rw [hpred]; omega)
    have holdC :
        (s (L3.EWord.site ring root k.val)).ser.phase =
          .C := by
      simpa only [hframe] using hc
    have hq := hquiet k hgreater holdC
    simpa only [hframe] using hq

theorem bankWordRenewalWaveInternalNonBToCQuietStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (he : e ≠ root)
    (hj : ring.rightNeighbor e ≠ root)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hsource :
      (z.2.1 e).ser.phase = .F ∨
      ((z.2.1 e).ser.phase = .C ∧
        (z.2.1 e).ser.probe ≠ .PENDING))
    (htarget :
      (z.2.1 (ring.rightNeighbor e)).ser.phase = .C) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z e) := by
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 e) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass e).2
  have hpost := clockPostInternal ring root z.2.1 e
    (by omega : 2 ≤ n) hfixed he hj
  have hserPair :
      (serW (z.2.1 e)
        (z.2.1 (ring.rightNeighbor e))).x =
          (z.2.1 e).ser ∧
      (serW (z.2.1 e)
        (z.2.1 (ring.rightNeighbor e))).y =
          (z.2.1 (ring.rightNeighbor e)).ser := by
    rcases hsource with hf | ⟨hc, hq⟩
    · exact L3.EWord.validationInternalFToCSerFrame
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        hpost.1 hpost.2 hf htarget
    · cases hp : (z.2.1 e).ser.probe with
      | NONE =>
          simp [serW, serializerStep, ProjW.lift,
            hpost.1, hpost.2, hc, hp, htarget]
      | PENDING =>
          exact False.elim (hq hp)
      | INTERNAL_OK =>
          simp [serW, serializerStep, ProjW.lift,
            hpost.1, hpost.2, hc, hp, htarget]
      | LEAF_OK =>
          simp [serW, serializerStep, ProjW.lift,
            hpost.1, hpost.2, hc, hp, htarget]
  have hpair :
      wValidationPair (z.2.2.clock + 1)
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        ((bankWordHardEpochLedger ring root z).validation e)
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor e)) =
      ((bankWordHardEpochLedger ring root z).validation e,
       (bankWordHardEpochLedger ring root z).validation
         (ring.rightNeighbor e)) := by
    rcases hsource with hf | ⟨hc, hq⟩
    · have hrow :
          (serW (z.2.1 e)
            (z.2.1 (ring.rightNeighbor e))).row = "S4" := by
        simp [serW, serializerStep, ProjW.lift,
          hpost.1, hpost.2, hf]
      simp [wValidationPair, hrow, htarget]
    · have hrow :
          (serW (z.2.1 e)
            (z.2.1 (ring.rightNeighbor e))).row = "S3" := by
        simp [serW, serializerStep, ProjW.lift,
          hpost.1, hpost.2, hc]
      simp [wValidationPair, hrow, htarget, hq]
  have hne : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) e
  have hserial : ∀ i : Fin n,
      ((bankWordEpochNext ring root z e).2.1 i).ser =
        (z.2.1 i).ser := by
    intro i
    by_cases hi : i = e
    · rw [hi]
      change ((phiW ring z.2.1 e) e).ser = (z.2.1 e).ser
      rw [phiW_ser_source]
      exact hserPair.1
    · by_cases hji : i = ring.rightNeighbor e
      · rw [hji]
        change ((phiW ring z.2.1 e)
          (ring.rightNeighbor e)).ser =
          (z.2.1 (ring.rightNeighbor e)).ser
        rw [phiW_ser_target ring z.2.1 e hne]
        exact hserPair.2
      · change ((phiW ring z.2.1 e) i).ser =
          (z.2.1 i).ser
        exact phiW_ser_remote ring z.2.1 e i hi hji
  have hselected := bankWordRenewalWaveSelectedTicketPairStep
    ring root e z (by omega : 2 ≤ n)
  have hticket : ∀ i : Fin n,
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z e)).validation i =
      (bankWordHardEpochLedger ring root z).validation i := by
    intro i
    by_cases hi : i = e
    · rw [hi, hselected.1, hpair]
    · by_cases hji : i = ring.rightNeighbor e
      · rw [hji, hselected.2, hpair]
      · exact bankWordRenewalFrontierWaveTicketRemoteFrame
          ring root z e i hi hji
  have hno : (serW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).hard.hardAccept =
        false := L3.EWord.nonrootNoAccept
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e)) hpost.1
  have hstart : (serW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).hard.hardS1 =
        false := L3.EWord.nonrootHardStartFalse
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e)) hpost.1
  have hshape : ∀ g : L3.EWord.ValidationGhost,
      L3.EWord.ValidationShape ring root z.2.1 g →
      L3.EWord.ValidationShape ring root
        (bankWordEpochNext ring root z e).2.1 g := by
    intro g hshapeOld
    have hnonB :
        (z.2.1 e).ser.phase = .C ∨
        (z.2.1 e).ser.phase = .F := by
      rcases hsource with hf | ⟨hc, hq⟩
      · exact Or.inr hf
      · exact Or.inl hc
    have hghost := L3.EWord.validationNonBGhostFixed
      ring root z.2.1 g e hstart hnonB
    have ht := (L3.EWord.validationTransport
      (c := compileAdvice (ceilLogTwo n)) ring root)
        z.2.1 g e hshapeOld hfixed hno
    rw [hghost] at ht
    exact ht
  exact bankWordRenewalWaveFullFrameQuietStep
    ring root e z hwave hserial hticket hshape

/-- Once the actual historical five-clause wave has been
transported through RETURN B/DONE→F, its additional quietness
is automatic: EWord validationTransport gives the lowered
RETURN pivot, and the literal S2N serializer cannot create a
pending C site in the suffix. This upgrade isolates the causal
quiet component from the outstanding ticket-assembly consumer
bankWordRenewalWaveInternalStep. -/
theorem bankWordRenewalWaveReturnMoveQuietUpgrade {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankWordEpochState n) (hn : 2 ≤ n)
    (g : L3.EWord.ValidationGhost)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hactive : (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)
    (hshape : L3.EWord.ValidationShape ring root z.2.1 g)
    (hr : L3.EWord.ReturnShape ring root z.2.1 g)
    (hp : 1 < g.pivot)
    (he : e = L3.EWord.site ring root (g.pivot - 1))
    (hfixed : WFixedRoot ring root (phiW ring z.2.1 e))
    (hx : (postW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).eX.l = false)
    (hy : (postW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).eY.l = false)
    (hb : (z.2.1 e).ser.phase = .B)
    (hd : (z.2.1 e).ser.out = .DONE)
    (hf : (z.2.1 (ring.rightNeighbor e)).ser.phase = .F)
    (hnewWave : BankWordRenewalFrontierWaveLineage ring root
      (bankWordEpochNext ring root z e)) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z e) := by
  have hno : (serW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).hard.hardAccept =
        false := L3.EWord.nonrootNoAccept
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e)) hx
  have hstart : (serW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).hard.hardS1 =
        false := L3.EWord.nonrootHardStartFalse
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e)) hx
  have hrow := (L3.EWord.validationReturnMoveSerializer
    (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
    hx hy hb hd hf).1
  have hghost := L3.EWord.validationReturnMoveGhost
    ring root z.2.1 g e hstart hr.isReturn
    hp he hb hd hf hrow
  have hnewShape :
      L3.EWord.ValidationShape ring root
        (bankWordEpochNext ring root z e).2.1
        { g with pivot := g.pivot - 1 } := by
    have ht := (L3.EWord.validationTransport
      (c := compileAdvice (ceilLogTwo n)) ring root)
        z.2.1 g e hshape hfixed hno
    rw [hghost] at ht
    exact ht
  have hnewReturn :
      L3.EWord.ReturnShape ring root
        (bankWordEpochNext ring root z e).2.1
        { g with pivot := g.pivot - 1 } := by
    rcases hnewShape.stageShape with hforward | hreturn
    · have hs : ({ g with pivot := g.pivot - 1 }).stage =
          .returning := hr.isReturn
      have hbad := hforward.isForward
      rw [hs] at hbad
      cases hbad
    · exact hreturn
  refine ⟨hnewWave, ?_⟩
  intro hactiveNew gnew hrnew k hk hc
  have hq := bankWordRenewalWaveReturnMoveSuffixQuiet
    ring root e z.2.1 hn g hr hnewReturn
    hp he hx hy hb hd hf
    (fun j hj hcOld =>
      hwave.returnSuffixQuiet hactive g hr j hj hcOld)
    gnew hrnew k hk hc
  exact hq

/-- On internal S3/S4 with a returned F/C pair, once the
five historical ticket clauses have been transported, the
all-witness quiet clause follows from literal serCanonicalC
and the unchanged RETURN pivot. Consumer: coveredInside
S3/S4 moving canonicalization in R10a J-W. -/
theorem bankWordRenewalWaveReturnNonBQuietUpgrade {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankWordEpochState n) (hn : 2 ≤ n)
    (g : L3.EWord.ValidationGhost)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hactive : (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)
    (hshape : L3.EWord.ValidationShape ring root z.2.1 g)
    (hr : L3.EWord.ReturnShape ring root z.2.1 g)
    (hfixed : WFixedRoot ring root (phiW ring z.2.1 e))
    (hx : (postW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).eX.l = false)
    (hy : (postW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).eY.l = false)
    (hsource :
      (z.2.1 e).ser.phase = .F ∨
      ((z.2.1 e).ser.phase = .C ∧
        (z.2.1 e).ser.probe ≠ .PENDING))
    (htarget :
      (z.2.1 (ring.rightNeighbor e)).ser.phase = .F ∨
      ((z.2.1 (ring.rightNeighbor e)).ser.phase = .C ∧
        (z.2.1 (ring.rightNeighbor e)).ser.probe ≠ .PENDING))
    (hnewWave : BankWordRenewalFrontierWaveLineage ring root
      (bankWordEpochNext ring root z e)) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z e) := by
  have hno : (serW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).hard.hardAccept =
        false := L3.EWord.nonrootNoAccept
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e)) hx
  have hstart : (serW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).hard.hardS1 =
        false := L3.EWord.nonrootHardStartFalse
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e)) hx
  have hnonB :
      (z.2.1 e).ser.phase = .C ∨
      (z.2.1 e).ser.phase = .F := by
    rcases hsource with hF | ⟨hC, hq⟩
    · exact Or.inr hF
    · exact Or.inl hC
  have hghost := L3.EWord.validationNonBGhostFixed
    ring root z.2.1 g e hstart hnonB
  have hnewShape :
      L3.EWord.ValidationShape ring root
        (bankWordEpochNext ring root z e).2.1 g := by
    have ht := (L3.EWord.validationTransport
      (c := compileAdvice (ceilLogTwo n)) ring root)
        z.2.1 g e hshape hfixed hno
    rw [hghost] at ht
    exact ht
  have hnewReturn :
      L3.EWord.ReturnShape ring root
        (bankWordEpochNext ring root z e).2.1 g := by
    rcases hnewShape.stageShape with hforward | hreturn
    · have hbad := hforward.isForward
      rw [hr.isReturn] at hbad
      cases hbad
    · exact hreturn
  refine ⟨hnewWave, ?_⟩
  intro hactiveNew gnew hrnew k hk hc
  exact bankWordRenewalWaveReturnNonBPairSuffixQuiet
    ring root e z.2.1 hn g hr hnewReturn
    hx hy hsource htarget
    (fun j hj hcOld =>
      hwave.returnSuffixQuiet hactive g hr j hj hcOld)
    gnew hrnew k hk hc
end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open Classical
set_option autoImplicit false
set_option Elab.async false

theorem bankWordRenewalWaveRootOutgoingPendingTicketStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n)
    (hn : 2 ≤ n)
    (hrow :
      (bankWordEpochSelectedReceipt ring z root).serializer.row =
        "S2R")
    (hw : (z.2.1 root).ser.out = .WAIT)
    (hc : (z.2.1 (ring.rightNeighbor root)).ser.phase = .C)
    (hp : (z.2.1 (ring.rightNeighbor root)).ser.probe =
      .PENDING) :
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z root)).validation root =
      (bankWordHardEpochLedger ring root z).validation root ∧
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z root)).validation
        (ring.rightNeighbor root) =
      (bankWordHardEpochLedger ring root z).validation
        (ring.rightNeighbor root) := by
  change (serW (z.2.1 root)
    (z.2.1 (ring.rightNeighbor root))).row = "S2R" at hrow
  have hpair :
      wValidationPair (z.2.2.clock + 1)
        (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
        ((bankWordHardEpochLedger ring root z).validation root)
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor root)) =
      ((bankWordHardEpochLedger ring root z).validation root,
       (bankWordHardEpochLedger ring root z).validation
         (ring.rightNeighbor root)) := by
    simp [wValidationPair, hrow, hw, hc, hp]
  have ht := bankWordRenewalWaveSelectedTicketPairStep
    ring root root z hn
  constructor
  · rw [ht.1, hpair]
  · rw [ht.2, hpair]


theorem bankWordRenewalWavePendingGhostFixed {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankWordEpochState n)
    (g : L3.EWord.ValidationGhost)
    (hstart :
      (serW (z.2.1 e)
        (z.2.1 (ring.rightNeighbor e))).hard.hardS1 =
          false)
    (hb : (z.2.1 e).ser.phase = .B)
    (hw : (z.2.1 e).ser.out = .WAIT)
    (hc : (z.2.1 (ring.rightNeighbor e)).ser.phase = .C)
    (hp : (z.2.1 (ring.rightNeighbor e)).ser.probe =
      .PENDING) :
    L3.EWord.validationGhostStep ring root z.2.1 g e = g := by
  cases hstage : g.stage with
  | forward =>
      by_cases he : e = L3.EWord.site ring root g.pivot
      · exact L3.EWord.validationGhostParentPendingEq
          ring root z.2.1 g e hstart hstage he hb hw hc hp
      · simp [L3.EWord.validationGhostStep, hstart, hstage,
          he]
  | returning =>
      simp [L3.EWord.validationGhostStep, hstart, hstage,
        hw]


theorem bankWordRenewalWaveRootOutgoingPendingQuietStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hrun : (z.2.1 root).ser.cert = .RUNNING)
    (hb : (z.2.1 root).ser.phase = .B)
    (hw : (z.2.1 root).ser.out = .WAIT)
    (hc : (z.2.1 (ring.rightNeighbor root)).ser.phase = .C)
    (hp : (z.2.1 (ring.rightNeighbor root)).ser.probe =
      .PENDING) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z root) := by
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 root) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass root).2
  have hpost := clockPostOutgoing ring root z.2.1 root
    (by omega : 2 ≤ n) hfixed rfl
  have hpairSer := L3.EWord.validationParentPendingWrite
    (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
    hpost.2 (by intro _; exact hrun) hb hw hc hp
  have hrow :
      (bankWordEpochSelectedReceipt ring z root).serializer.row =
        "S2R" := by
    change (serW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).row = "S2R"
    simp [serW, serializerStep, ProjW.lift,
      hpost.1, hpost.2, hrun, hb, hw, hc, hp]
  have hpairTicket :=
    bankWordRenewalWaveRootOutgoingPendingTicketStep
      ring root z (by omega : 2 ≤ n) hrow hw hc hp
  have hne : ring.rightNeighbor root ≠ root :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) root
  have hserial : ∀ i : Fin n,
      ((bankWordEpochNext ring root z root).2.1 i).ser =
        (z.2.1 i).ser := by
    intro i
    by_cases hi : i = root
    · rw [hi]
      change ((phiW ring z.2.1 root) root).ser =
        (z.2.1 root).ser
      rw [phiW_ser_source]
      exact hpairSer.1
    · by_cases hj : i = ring.rightNeighbor root
      · rw [hj]
        change ((phiW ring z.2.1 root)
          (ring.rightNeighbor root)).ser =
            (z.2.1 (ring.rightNeighbor root)).ser
        rw [phiW_ser_target ring z.2.1 root hne]
        exact hpairSer.2
      · change ((phiW ring z.2.1 root) i).ser =
          (z.2.1 i).ser
        exact phiW_ser_remote ring z.2.1 root i hi hj
  have hticket : ∀ i : Fin n,
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z root)).validation i =
      (bankWordHardEpochLedger ring root z).validation i := by
    intro i
    by_cases hi : i = root
    · rw [hi]
      exact hpairTicket.1
    · by_cases hj : i = ring.rightNeighbor root
      · rw [hj]
        exact hpairTicket.2
      · exact bankWordRenewalFrontierWaveTicketRemoteFrame
          ring root z root i hi hj
  have hno : (serW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).hard.hardAccept =
      false := L3.EWord.waitNoAccept
        (z.2.1 root) (z.2.1 (ring.rightNeighbor root)) hw
  have hshape : ∀ g : L3.EWord.ValidationGhost,
      L3.EWord.ValidationShape ring root z.2.1 g →
      L3.EWord.ValidationShape ring root
        (bankWordEpochNext ring root z root).2.1 g := by
    intro g holdShape
    have hstart := L3.EWord.validationParentHardStartFalse
      ring root z.2.1 g root holdShape hfixed
    have hghost := bankWordRenewalWavePendingGhostFixed
      ring root root z g hstart hb hw hc hp
    have ht := (L3.EWord.validationTransport
      (c := compileAdvice (ceilLogTwo n)) ring root)
        z.2.1 g root holdShape hfixed hno
    rw [hghost] at ht
    exact ht
  exact bankWordRenewalWaveFullFrameQuietStep
    ring root root z hwave hserial hticket hshape




theorem bankWordRenewalWaveInternalObservedChildQuietStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hactive : (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)
    (g : L3.EWord.ValidationGhost)
    (hg : g = Classical.choose (hwave.wave.2 hactive))
    (hforward : g.stage = .forward)
    (he : e = L3.EWord.site ring root (g.pivot + 1))
    (hbound : g.pivot + 2 < n)
    (hparentWait :
      (z.2.1 (L3.EWord.site ring root g.pivot)).ser.out =
        .WAIT)
    (hsourceC : (z.2.1 e).ser.phase = .C)
    (hsourcePending : (z.2.1 e).ser.probe = .PENDING)
    (htargetC :
      (z.2.1 (ring.rightNeighbor e)).ser.phase = .C) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z e) := by
  have hspec := Classical.choose_spec (hwave.wave.2 hactive)
  rw [← hg] at hspec
  obtain ⟨req, stamp, hshape, hsites⟩ := hspec
  have hf : L3.EWord.ForwardShape ring root z.2.1 g := by
    rcases hshape.stageShape with hf | hr
    · exact hf
    · have hbad := hr.isReturn
      rw [hforward] at hbad
      cases hbad
  have hwaitSource := L3.EWord.validationChildWaitSource
    ring root z.2.1 g hf hparentWait hbound
  have hscrub : g.scrub = g.pivot + 2 := hwaitSource.1
  have hsourceValid : (z.2.1 e).ser.wphase =
      .VALIDATING := by
    rw [he]
    exact hwaitSource.2.2.1
  have holdPending :
      BankWordRenewalFrontierWaveSiteTicket ring root z
        req stamp
        (⟨g.pivot + 1, (show g.pivot + 1 < n by omega)⟩ :
          Fin n) .pending := by
    have hticket := (hsites
      (⟨g.pivot + 1, (show g.pivot + 1 < n by omega)⟩ :
        Fin n)
      (by simp only [Fin.val_mk]; rw [hscrub]; omega)).2.1
    exact hticket
      ⟨by rw [← he]; exact hsourceC,
       by rw [← he]; exact hsourcePending,
       by rw [← he]; exact hsourceValid⟩
  obtain ⟨child, htChild, hreqChild, hstampChild⟩ :=
    holdPending
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass e).2
  have hpost := L3.EWord.validationChildPostFlags
    ring root z.2.1 g.pivot e
    (by omega : 3 ≤ n) hf.pivotBound hbound he hfixed
  have hrow := L3.EWord.validationPendingResponderSerializer
    (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
    hpost.1 hpost.2 hsourceC hsourcePending htargetC
  have hreceipt :
      (bankWordEpochSelectedReceipt ring z e).serializer.row =
        "S3" := hrow.1
  have hnextTicket := bankWordRenewalWaveInternalObservationTicketStep
    ring root e z (by omega : 2 ≤ n) child hreceipt
    hsourcePending htargetC
    (by rw [he]; simpa only [Fin.val_mk] using htChild)
  have hsrcSer :
      ((bankWordEpochNext ring root z e).2.1 e).ser.phase =
        .C ∧
      ((bankWordEpochNext ring root z e).2.1 e).ser.probe =
        .INTERNAL_OK ∧
      ((bankWordEpochNext ring root z e).2.1 e).ser.wphase =
        .VALIDATING := by
    change ((phiW ring z.2.1 e) e).ser.phase = .C ∧
      ((phiW ring z.2.1 e) e).ser.probe = .INTERNAL_OK ∧
      ((phiW ring z.2.1 e) e).ser.wphase = .VALIDATING
    rw [phiW_ser_source]
    exact ⟨hrow.2.1, hrow.2.2.1,
      hrow.2.2.2.1.trans hsourceValid⟩
  have hnewObserved :
      BankWordRenewalFrontierWaveSiteTicket ring root
        (bankWordEpochNext ring root z e) req stamp
        (⟨g.pivot + 1, (show g.pivot + 1 < n by omega)⟩ :
          Fin n) .observedInternal := by
    unfold BankWordRenewalFrontierWaveSiteTicket
    refine ⟨{ child with stage := .observedInternal },
      ?_, ?_, ?_⟩
    · simp only [Fin.val_mk, ← he, hnextTicket.1]
      rfl
    · exact hreqChild
    · exact hstampChild
  have hrootFrame :
      ((bankWordEpochNext ring root z e).2.1 root).ser =
        (z.2.1 root).ser := by
    change ((phiW ring z.2.1 e) root).ser = (z.2.1 root).ser
    exact congrArg ProjW.ser
      (L3.EWord.validationChildRootFrame
        ring root z.2.1 g.pivot e
        (by omega : 3 ≤ n) hbound he)
  have hghost := L3.EWord.validationGhostChildEq
    ring root z.2.1 g e (by omega : 3 ≤ n) hf he
  have hno : (serW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).hard.hardAccept =
      false :=
    L3.EWord.nonrootNoAccept
      (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
      hpost.1
  have hnewShape :
      L3.EWord.ValidationShape ring root
        (bankWordEpochNext ring root z e).2.1 g := by
    have ht := (L3.EWord.validationTransport
      (c := compileAdvice (ceilLogTwo n)) ring root)
        z.2.1 g e hshape hfixed hno
    rw [hghost] at ht
    exact ht
  have hnewForward :
      L3.EWord.ForwardShape ring root
        (bankWordEpochNext ring root z e).2.1 g := by
    rcases hnewShape.stageShape with hfNew | hrNew
    · exact hfNew
    · have hbad := hrNew.isReturn
      rw [hforward] at hbad
      cases hbad
  have hfirstFrame :
      g.pivot ≠ 0 →
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor root)).ser =
        (z.2.1 (ring.rightNeighbor root)).ser := by
    intro hp
    have ht := L3.EWord.validationChildFrame
      ring root z.2.1 g.pivot e hbound he 1
      (by omega : 1 < n) (by omega) (by omega)
    change ((phiW ring z.2.1 e)
      (ring.rightNeighbor root)).ser =
      (z.2.1 (ring.rightNeighbor root)).ser
    simpa only [L3.EWord.siteOne] using congrArg ProjW.ser ht
  have hbase :
      BankWordRenewalFrontierTicketLineage ring root
        (bankWordEpochNext ring root z e) := by
    unfold BankWordRenewalFrontierTicketLineage
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have hold : (z.2.1 root).ser.cert = .REQUESTED := by
        simpa only [hrootFrame] using h
      rw [hactive.1] at hold
      cases hold
    · intro h
      by_cases hpzero : g.pivot = 0
      · have hfirst : e = ring.rightNeighbor root := by
          rw [he, hpzero, L3.EWord.siteOne]
        have hwrong :
            ((bankWordEpochNext ring root z e).2.1
              (ring.rightNeighbor root)).ser.probe =
                .PENDING := h.2.2.2.2.2
        rw [← hfirst] at hwrong
        rw [hsrcSer.2.1] at hwrong
        cases hwrong
      · have hpositive : 0 < g.pivot := Nat.pos_of_ne_zero hpzero
        have hdone := hf.completed
          (⟨0, (show 0 < n by omega)⟩ : Fin n)
          hpositive
        have hrootDone : (z.2.1 root).ser.out = .DONE := by
          simpa only [L3.EWord.siteZero] using hdone.2.1
        have hwrong :
            ((bankWordEpochNext ring root z e).2.1 root).ser.out =
              .WAIT := h.2.2.2.1
        rw [hrootFrame, hrootDone] at hwrong
        cases hwrong
    · intro h
      by_cases hpzero : g.pivot = 0
      · have hrootWait : (z.2.1 root).ser.out = .WAIT := by
          simpa only [hpzero, L3.EWord.siteZero] using hparentWait
        have hwrong :
            ((bankWordEpochNext ring root z e).2.1 root).ser.out =
              .DONE := h.2.2.2.1
        rw [hrootFrame, hrootWait] at hwrong
        cases hwrong
      · have hpositive : 0 < g.pivot := Nat.pos_of_ne_zero hpzero
        have hchildB :
            (z.2.1 (ring.rightNeighbor root)).ser.phase =
              .B := by
          by_cases hpone : g.pivot = 1
          · simpa only [hpone, L3.EWord.siteOne] using
              hf.parentB
          · have hlt : 1 < g.pivot := by omega
            simpa only [L3.EWord.siteOne] using
              (hf.completed
                (⟨1, (show 1 < n by omega)⟩ : Fin n)
                hlt).1
        have hwrong :
            ((bankWordEpochNext ring root z e).2.1
              (ring.rightNeighbor root)).ser.phase = .F :=
          h.2.2.2.2
        rw [hfirstFrame hpzero, hchildB] at hwrong
        cases hwrong
  have hnextWave :
      BankWordRenewalFrontierWaveLineage ring root
        (bankWordEpochNext ring root z e) := by
    refine ⟨hbase, ?_⟩
    intro hactiveNew
    refine ⟨g, req, stamp, hnewShape, ?_⟩
    intro k hk
    by_cases hsourceIndex : k.val = g.pivot + 1
    · have hsite : L3.EWord.site ring root k.val = e := by
        rw [hsourceIndex, ← he]
      have hindex :
          k = (⟨g.pivot + 1,
            (show g.pivot + 1 < n by omega)⟩ : Fin n) := by
        apply Fin.ext
        exact hsourceIndex
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro h
        have hwrong := h.1
        rw [hsite, hsrcSer.1] at hwrong
        cases hwrong
      · intro h
        have hwrong := h.2.1
        rw [hsite, hsrcSer.2.1] at hwrong
        cases hwrong
      · intro h
        rw [hindex]
        exact hnewObserved
      · intro h
        have hwrong := h.2
        rw [hsite, hsrcSer.2.1] at hwrong
        cases hwrong
      · intro h
        have hwrong := h.1
        rw [hsite, hsrcSer.1] at hwrong
        cases hwrong
    · have hsourceNe :
          L3.EWord.site ring root k.val ≠ e := by
        intro ht
        have hsame :
            L3.EWord.site ring root k.val =
              L3.EWord.site ring root (g.pivot + 1) := by
          rw [← he]
          exact ht
        have heq := L3.EWord.validationSiteInjective
          ring root k.val (g.pivot + 1)
          k.isLt (by omega : g.pivot + 1 < n) hsame
        exact hsourceIndex heq
      have htargetNe :
          L3.EWord.site ring root k.val ≠
            ring.rightNeighbor e := by
        intro ht
        have hj := L3.EWord.validationChildNeighbor
          ring root g.pivot e he
        have hsame :
            L3.EWord.site ring root k.val =
              L3.EWord.site ring root (g.pivot + 2) := by
          rw [← hj]
          exact ht
        have heq := L3.EWord.validationSiteInjective
          ring root k.val (g.pivot + 2)
          k.isLt hbound hsame
        have hlt : k.val < g.pivot + 2 := by
          rw [← hscrub]
          exact hk
        omega
      have hser :
          ((bankWordEpochNext ring root z e).2.1
            (L3.EWord.site ring root k.val)).ser =
          (z.2.1 (L3.EWord.site ring root k.val)).ser := by
        change ((phiW ring z.2.1 e)
          (L3.EWord.site ring root k.val)).ser =
          (z.2.1 (L3.EWord.site ring root k.val)).ser
        exact phiW_ser_remote ring z.2.1 e
          (L3.EWord.site ring root k.val)
          hsourceNe htargetNe
      have hticket := bankWordRenewalFrontierWaveTicketRemoteFrame
        ring root z e (L3.EWord.site ring root k.val)
        hsourceNe htargetNe
      simpa only [BankWordRenewalFrontierWaveSiteTicket,
        hser, hticket] using hsites k hk
  refine ⟨hnextWave, ?_⟩
  intro hactiveNew gnew hreturn k hk hc
  exact False.elim (bankWordRenewalWaveForwardExcludesReturn
    ring root (bankWordEpochNext ring root z e).2.1
    g gnew hnewForward hreturn)




private theorem bankWordRenewalWaveRootOutgoingBNonterminalSerializer
    {c : Compiled} (x y : ProjW c)
    (hx : (postW x y).eX.l = true)
    (hy : (postW x y).eY.l = false)
    (hcert : x.ser.cert ≠ .REQUESTED)
    (hb : x.ser.phase = .B)
    (hnotfinish : x.ser.out ≠ .DONE ∨ y.ser.phase ≠ .F) :
    (serW x y).x.cert = x.ser.cert ∧
    (serW x y).x.wphase = x.ser.wphase := by
  cases hc : x.ser.cert with
  | REQUESTED =>
      exact False.elim (hcert hc)
  | IDLE =>
      cases ho : x.ser.out <;>
        cases hp : y.ser.phase <;>
        cases hq : y.ser.probe <;>
        simp [serW, serializerStep, ProjW.lift,
          serChallengeWrite, serEnterB, serEnterF,
          hx, hy, hc, hb, ho, hp, hq] at hnotfinish ⊢
  | RUNNING =>
      cases ho : x.ser.out <;>
        cases hp : y.ser.phase <;>
        cases hq : y.ser.probe <;>
        simp [serW, serializerStep, ProjW.lift,
          serChallengeWrite, serEnterB, serEnterF,
          hx, hy, hc, hb, ho, hp, hq] at hnotfinish ⊢


theorem bankWordRenewalWaveRootOutgoingInactiveBQuietStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hcert : (z.2.1 root).ser.cert ≠ .REQUESTED)
    (hb : (z.2.1 root).ser.phase = .B)
    (hinactive :
      ¬ ((z.2.1 root).ser.cert = .RUNNING ∧
         (z.2.1 root).ser.wphase = .VALIDATING))
    (hnotfinish :
      (z.2.1 root).ser.out ≠ .DONE ∨
      (z.2.1 (ring.rightNeighbor root)).ser.phase ≠ .F) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z root) := by
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 root) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass root).2
  have hpost := clockPostOutgoing ring root z.2.1 root
    (by omega : 2 ≤ n) hfixed rfl
  have hfields := bankWordRenewalWaveRootOutgoingBNonterminalSerializer
    (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
    hpost.1 hpost.2 hcert hb hnotfinish
  have hcertFrame :
      ((bankWordEpochNext ring root z root).2.1 root).ser.cert =
        (z.2.1 root).ser.cert := by
    change ((phiW ring z.2.1 root) root).ser.cert =
      (z.2.1 root).ser.cert
    rw [phiW_ser_source]
    exact hfields.1
  have hphaseFrame :
      ((bankWordEpochNext ring root z root).2.1 root).ser.wphase =
        (z.2.1 root).ser.wphase := by
    change ((phiW ring z.2.1 root) root).ser.wphase =
      (z.2.1 root).ser.wphase
    rw [phiW_ser_source]
    exact hfields.2
  have hnewNotRequested :
      ((bankWordEpochNext ring root z root).2.1 root).ser.cert ≠
        .REQUESTED := by
    intro h
    rw [hcertFrame] at h
    exact hcert h
  have hnewInactive :
      ¬ (((bankWordEpochNext ring root z root).2.1 root).ser.cert =
           .RUNNING ∧
         ((bankWordEpochNext ring root z root).2.1 root).ser.wphase =
           .VALIDATING) := by
    intro h
    have hold :
        (z.2.1 root).ser.cert = .RUNNING ∧
        (z.2.1 root).ser.wphase = .VALIDATING := by
      simpa only [hcertFrame, hphaseFrame] using h
    exact hinactive hold
  refine ⟨?_, ?_⟩
  · unfold BankWordRenewalFrontierWaveLineage
      BankWordRenewalFrontierTicketLineage
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro h
      exact False.elim (hnewNotRequested h)
    · intro h
      exact False.elim (hnewInactive ⟨h.1, h.2.1⟩)
    · intro h
      exact False.elim (hnewInactive ⟨h.1, h.2.1⟩)
    · intro h
      exact False.elim (hnewInactive h)
  · intro hactive g hr k hk hc
    exact False.elim (hnewInactive hactive)


theorem bankWordRenewalWaveRootOutgoingInactiveQuietStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hcase :
      (z.2.1 root).ser.cert = .REQUESTED ∨
      (((z.2.1 root).ser.cert = .IDLE ∨
         (z.2.1 root).ser.cert = .RUNNING) ∧
       ((z.2.1 root).ser.phase = .C ∨
         (z.2.1 root).ser.phase = .F)) ∨
      ((z.2.1 root).ser.cert ≠ .REQUESTED ∧
       (z.2.1 root).ser.phase = .B ∧
       ¬ ((z.2.1 root).ser.cert = .RUNNING ∧
          (z.2.1 root).ser.wphase = .VALIDATING))) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z root) := by
  rcases hcase with hrequested | hrecover | hB
  · by_cases hzero : (z.2.1 root).siLease.val = 0
    · exact bankWordRenewalWaveRootOutgoingHardStartQuietStep
        ring root s hn hbank hs z hz hwave
        hrequested hzero
    · have hpositive : 0 < (z.2.1 root).siLease.val := by omega
      exact bankWordRenewalWaveRootOutgoingSoftStartQuietStep
        ring root s hn hbank hs z hz hrequested hpositive
  · exact bankWordRenewalWaveRootOutgoingRecoveryQuietStep
      ring root s hn hbank hs z hz hrecover.1 hrecover.2
  · obtain ⟨hcert, hb, hinactive⟩ := hB
    by_cases hfinish :
        (z.2.1 root).ser.out = .DONE ∧
        (z.2.1 (ring.rightNeighbor root)).ser.phase = .F
    · exact bankWordRenewalWaveRootOutgoingFinishQuietStep
        ring root s hn hbank hs z hz
        hcert hb hfinish.1 hfinish.2
    · have hnotfinish :
          (z.2.1 root).ser.out ≠ .DONE ∨
          (z.2.1 (ring.rightNeighbor root)).ser.phase ≠ .F := by
        by_cases hd : (z.2.1 root).ser.out = .DONE
        · right
          intro hf
          exact hfinish ⟨hd, hf⟩
        · left
          exact hd
      exact bankWordRenewalWaveRootOutgoingInactiveBQuietStep
        ring root s hn hbank hs z hz
        hcert hb hinactive hnotfinish

theorem bankWordRenewalWaveInternalNewAnyResponderTicketStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankWordEpochState n)
    (hn : 2 ≤ n)
    (parent : WValidationTicket)
    (hrow :
      (bankWordEpochSelectedReceipt ring z e).serializer.row =
        "S2N")
    (hnew : (z.2.1 e).ser.out = .NEW)
    (hparent : wParentTicket
      ((bankWordHardEpochLedger ring root z).validation e) =
        some parent) :
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).validation e =
        some { parent with stage := .waiting } ∧
    (bankWordHardEpochLedger ring root
      (bankWordEpochNext ring root z e)).validation
        (ring.rightNeighbor e) =
        some { parent with stage := .pending } := by
  change (serW (z.2.1 e)
    (z.2.1 (ring.rightNeighbor e))).row = "S2N" at hrow
  have hpair :
      wValidationPair (z.2.2.clock + 1)
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        ((bankWordHardEpochLedger ring root z).validation e)
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor e)) =
      (some { parent with stage := .waiting },
       some { parent with stage := .pending }) := by
    cases htarget : (z.2.1 (ring.rightNeighbor e)).ser.phase <;>
      simp [wValidationPair, hrow, hnew, htarget,
        wChallengeTickets, wTicketStage, hparent]
  have ht := bankWordRenewalWaveSelectedTicketPairStep
    ring root e z hn
  constructor
  · rw [ht.1, hpair]
  · rw [ht.2, hpair]

theorem bankWordRenewalWaveInternalPendingQuietStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (he : e ≠ root)
    (hj : ring.rightNeighbor e ≠ root)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hb : (z.2.1 e).ser.phase = .B)
    (hw : (z.2.1 e).ser.out = .WAIT)
    (hc : (z.2.1 (ring.rightNeighbor e)).ser.phase = .C)
    (hp : (z.2.1 (ring.rightNeighbor e)).ser.probe =
      .PENDING) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z e) := by
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass e).2
  have hpost := clockPostInternal ring root z.2.1 e
    (by omega : 2 ≤ n) hfixed he hj
  have hpairSer := L3.EWord.validationParentPendingWrite
    (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
    hpost.2 (by intro h; rw [hpost.1] at h; cases h)
    hb hw hc hp
  have hrow :
      (bankWordEpochSelectedReceipt ring z e).serializer.row =
        "S2N" := by
    change (serW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).row = "S2N"
    simp [serW, serializerStep, ProjW.lift,
      hpost.1, hpost.2, hb]
  have hpairTicket :
      wValidationPair (z.2.2.clock + 1)
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        ((bankWordHardEpochLedger ring root z).validation e)
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor e)) =
      ((bankWordHardEpochLedger ring root z).validation e,
       (bankWordHardEpochLedger ring root z).validation
         (ring.rightNeighbor e)) := by
    change (serW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).row = "S2N" at hrow
    simp [wValidationPair, hrow, hw, hc, hp]
  have hne : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) e
  have hserial : ∀ i : Fin n,
      ((bankWordEpochNext ring root z e).2.1 i).ser =
        (z.2.1 i).ser := by
    intro i
    by_cases hi : i = e
    · rw [hi]
      change ((phiW ring z.2.1 e) e).ser = (z.2.1 e).ser
      rw [phiW_ser_source]
      exact hpairSer.1
    · by_cases hji : i = ring.rightNeighbor e
      · rw [hji]
        change ((phiW ring z.2.1 e)
          (ring.rightNeighbor e)).ser =
          (z.2.1 (ring.rightNeighbor e)).ser
        rw [phiW_ser_target ring z.2.1 e hne]
        exact hpairSer.2
      · change ((phiW ring z.2.1 e) i).ser =
          (z.2.1 i).ser
        exact phiW_ser_remote ring z.2.1 e i hi hji
  have hselected := bankWordRenewalWaveSelectedTicketPairStep
    ring root e z (by omega : 2 ≤ n)
  have hticket : ∀ i : Fin n,
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z e)).validation i =
      (bankWordHardEpochLedger ring root z).validation i := by
    intro i
    by_cases hi : i = e
    · rw [hi, hselected.1, hpairTicket]
    · by_cases hji : i = ring.rightNeighbor e
      · rw [hji, hselected.2, hpairTicket]
      · exact bankWordRenewalFrontierWaveTicketRemoteFrame
          ring root z e i hi hji
  have hno : (serW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).hard.hardAccept =
      false := L3.EWord.nonrootNoAccept
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e)) hpost.1
  have hstart : (serW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).hard.hardS1 =
      false := L3.EWord.nonrootHardStartFalse
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e)) hpost.1
  have hshape : ∀ g : L3.EWord.ValidationGhost,
      L3.EWord.ValidationShape ring root z.2.1 g →
      L3.EWord.ValidationShape ring root
        (bankWordEpochNext ring root z e).2.1 g := by
    intro g hshapeOld
    have hghost := bankWordRenewalWavePendingGhostFixed
      ring root e z g hstart hb hw hc hp
    have ht := (L3.EWord.validationTransport
      (c := compileAdvice (ceilLogTwo n)) ring root)
      z.2.1 g e hshapeOld hfixed hno
    rw [hghost] at ht
    exact ht
  exact bankWordRenewalWaveFullFrameQuietStep
    ring root e z hwave hserial hticket hshape


theorem bankWordRenewalWaveInternalCanonicalRootLineageStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (he : e ≠ root)
    (hj : ring.rightNeighbor e ≠ root)
    (hsource :
      (z.2.1 e).ser.phase = .C ∨
      (z.2.1 e).ser.phase = .F)
    (htarget :
      (z.2.1 (ring.rightNeighbor e)).ser.phase = .B ∨
      (z.2.1 (ring.rightNeighbor e)).ser.phase = .F) :
    BankWordRenewalFrontierTicketLineage ring root
      (bankWordEpochNext ring root z e) := by
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass e).2
  have hpost := clockPostInternal ring root z.2.1 e
    (by omega : 2 ≤ n) hfixed he hj
  have hsourceSerPair :
      (serW (z.2.1 e)
        (z.2.1 (ring.rightNeighbor e))).x =
          (z.2.1 e).ser := by
    rcases hsource with hc | hf
    · exact (L3.EWord.validationChildCanonicalSerializer
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        hpost.1 hpost.2 hc htarget).2.1
    · rcases htarget with hb | hfRight
      · simp [serW, serializerStep, ProjW.lift,
          serCanonicalC, hpost.1, hpost.2, hf, hb]
      · simp [serW, serializerStep, ProjW.lift,
          serCanonicalC, hpost.1, hpost.2, hf, hfRight]
  have hsourceLedger := (bankWordRenewalWaveInternalCanonicalCleanupStep
    ring root e s hn hbank hs z hz he hj hsource htarget).2.2
  have hrootSer :
      ((bankWordEpochNext ring root z e).2.1 root).ser =
      (z.2.1 root).ser := by
    change ((phiW ring z.2.1 e) root).ser =
      (z.2.1 root).ser
    exact phiW_ser_remote ring z.2.1 e root he.symm hj.symm
  have hrootTicket :=
    bankWordRenewalFrontierWaveTicketRemoteFrame
      ring root z e root he.symm hj.symm
  have hinj : Function.Injective ring.rightNeighbor := by
    intro a b hab
    apply Fin.ext
    have hv := congrArg Fin.val hab
    change (a.val + 1) % n = (b.val + 1) % n at hv
    by_cases ha : a.val + 1 < n
    · by_cases hb : b.val + 1 < n
      · rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv
        omega
      · have hbeq : b.val + 1 = n := by omega
        rw [Nat.mod_eq_of_lt ha, hbeq, Nat.mod_self] at hv
        omega
    · have haeq : a.val + 1 = n := by omega
      by_cases hb : b.val + 1 < n
      · rw [haeq, Nat.mod_self, Nat.mod_eq_of_lt hb] at hv
        omega
      · omega
  have hchildNotTarget :
      ring.rightNeighbor root ≠ ring.rightNeighbor e := by
    intro h
    exact he (hinj h).symm
  have hsourceFrame :
      ((bankWordEpochNext ring root z e).2.1 e).ser =
        (z.2.1 e).ser := by
    change ((phiW ring z.2.1 e) e).ser =
      (z.2.1 e).ser
    rw [phiW_ser_source]
    exact hsourceSerPair
  have hfirstSer :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor root)).ser =
        (z.2.1 (ring.rightNeighbor root)).ser := by
    by_cases hfirst : ring.rightNeighbor root = e
    · rw [hfirst]
      exact hsourceFrame
    · change ((phiW ring z.2.1 e)
        (ring.rightNeighbor root)).ser =
          (z.2.1 (ring.rightNeighbor root)).ser
      exact phiW_ser_remote ring z.2.1 e
        (ring.rightNeighbor root) hfirst hchildNotTarget
  have hfirstTicket :
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z e)).validation
          (ring.rightNeighbor root) =
        (bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor root) := by
    by_cases hfirst : ring.rightNeighbor root = e
    · rw [hfirst]
      exact hsourceLedger
    · exact bankWordRenewalFrontierWaveTicketRemoteFrame
        ring root z e (ring.rightNeighbor root)
        hfirst hchildNotTarget
  have hold := hwave.wave.1
  unfold BankWordRenewalFrontierTicketLineage at hold ⊢
  simpa only [hrootSer, hfirstSer, hrootTicket,
    hfirstTicket] using hold

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- INTERNAL S2N B/WAIT against a C/PENDING child is a literal
    serializer frame. The root-connected frontier and its already
    charged position survive this nominated-but-stalling service.
    Consumer: R10a S-frontier WAIT/PENDING row. -/
theorem bankWordRenewalSoftInternalPendingStall {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s)
    (p : Nat) (hn : 5 ≤ n) (hp : 0 < p)
    (hf : BankWordRenewalSoftForwardShape ring root z.1 p)
    (hactive :
      (z.1.2.1 root).ser.cert = .RUNNING ∧
      (z.1.2.1 root).ser.phase = .B ∧
      (z.1.2.1 root).ser.wphase = .CURRENT)
    (hwait :
      (z.1.2.1 (L3.EWord.site ring root p)).ser.out = .WAIT)
    (hchildC :
      (z.1.2.1 (L3.EWord.site ring root (p + 1))).ser.phase = .C)
    (hchildPending :
      (z.1.2.1 (L3.EWord.site ring root (p + 1))).ser.probe =
        .PENDING)
    (hx : (postW
      (z.1.2.1 (L3.EWord.site ring root p))
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root p)))).eX.l = false)
    (hy : (postW
      (z.1.2.1 (L3.EWord.site ring root p))
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root p)))).eY.l = false) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root p)) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root p)) =
      bankWordRenewalSoftRootedPosition ring root z.1 ∧
    bankWordRenewalSoftRootedChosen ring root s z =
      L3.EWord.site ring root p := by
  have hpn : p < n := by
    have hb := hf.pivotBound
    omega
  have hpnonzero : p ≠ 0 := Nat.ne_of_gt hp
  have hchildCNeighbor :
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root p))).ser.phase = .C := by
    rw [L3.EWord.siteSuccessor]
    exact hchildC
  have hchildPendingNeighbor :
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root p))).ser.probe = .PENDING := by
    rw [L3.EWord.siteSuccessor]
    exact hchildPending
  have hsourcePhase := hf.parentPhase
  have hsourceCurrent := hf.parentCurrent
  have hne :
      ring.rightNeighbor (L3.EWord.site ring root p) ≠
        L3.EWord.site ring root p :=
    L3.EWord.rightNeighborDifferent ring (by omega)
      (L3.EWord.site ring root p)
  have hpair :
      (serW (z.1.2.1 (L3.EWord.site ring root p))
        (z.1.2.1 (ring.rightNeighbor
          (L3.EWord.site ring root p)))).x =
          (z.1.2.1 (L3.EWord.site ring root p)).ser ∧
      (serW (z.1.2.1 (L3.EWord.site ring root p))
        (z.1.2.1 (ring.rightNeighbor
          (L3.EWord.site ring root p)))).y =
          (z.1.2.1 (ring.rightNeighbor
            (L3.EWord.site ring root p))).ser := by
    simp [serW, serializerStep, ProjW.lift,
      hx, hy, hsourcePhase, hsourceCurrent,
      hwait, hchildCNeighbor, hchildPendingNeighbor]
  have hserial : ∀ i : Fin n,
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root p)).2.1 i).ser =
          (z.1.2.1 i).ser := by
    intro i
    by_cases hi : i = L3.EWord.site ring root p
    · rw [hi]
      change ((phiW ring z.1.2.1
        (L3.EWord.site ring root p))
        (L3.EWord.site ring root p)).ser = _
      rw [phiW_ser_source]
      exact hpair.1
    · by_cases hj :
        i = ring.rightNeighbor (L3.EWord.site ring root p)
      · rw [hj]
        change ((phiW ring z.1.2.1
          (L3.EWord.site ring root p))
          (ring.rightNeighbor (L3.EWord.site ring root p))).ser =
            _
        rw [phiW_ser_target ring z.1.2.1
          (L3.EWord.site ring root p) hne]
        exact hpair.2
      · change ((phiW ring z.1.2.1
          (L3.EWord.site ring root p)) i).ser = _
        exact phiW_ser_remote ring z.1.2.1
          (L3.EWord.site ring root p) i hi hj
  have hfnew : BankWordRenewalSoftForwardShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root p)) p := by
    refine {
      pivotBound := hf.pivotBound
      completed := ?_
      parentPhase := ?_
      parentCurrent := ?_
      front := ?_ }
    · intro j hj
      simpa only [hserial (L3.EWord.site ring root j)]
        using hf.completed j hj
    · simpa only [hserial (L3.EWord.site ring root p)]
        using hf.parentPhase
    · simpa only [hserial (L3.EWord.site ring root p)]
        using hf.parentCurrent
    · simpa only [hserial (L3.EWord.site ring root p),
        hserial (L3.EWord.site ring root (p + 1))]
        using hf.front
  have hnextActive :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root p)).2.1 root).ser.cert =
          .RUNNING ∧
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root p)).2.1 root).ser.phase =
          .B ∧
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root p)).2.1 root).ser.wphase =
          .CURRENT := by
    simpa only [hserial root] using hactive
  have hidxOld := bankWordRenewalSoftForwardIndex
    ring root z.1 p hf
  have hidxNew := bankWordRenewalSoftForwardIndex
    ring root (bankWordEpochNext ring root z.1
      (L3.EWord.site ring root p)) p hfnew
  have hwaitNew :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root p)).2.1
          (L3.EWord.site ring root p)).ser.out = .WAIT := by
    simpa only [hserial (L3.EWord.site ring root p)] using hwait
  have hposOld :
      bankWordRenewalSoftRootedPosition ring root z.1 =
        p + 1 := by
    simp [bankWordRenewalSoftRootedPosition, hactive,
      hidxOld, hf.parentPhase, hwait, hpnonzero, hpn,
      hf.pivotBound]
  have hposNew :
      bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z.1
          (L3.EWord.site ring root p)) = p + 1 := by
    simp [bankWordRenewalSoftRootedPosition, hnextActive,
      hidxNew, hfnew.parentPhase, hwaitNew, hpnonzero, hpn,
      hf.pivotBound]
  have hchosen :
      bankWordRenewalSoftRootedChosen ring root s z =
        L3.EWord.site ring root p := by
    simp [bankWordRenewalSoftRootedChosen, hactive,
      hidxOld, hf.parentPhase, hpn, hf.pivotBound]
  exact ⟨(by intro _; exact Or.inl ⟨p, hfnew⟩),
    hposNew.trans hposOld.symm, hchosen⟩


theorem bankWordRenewalSoftRootIncomingStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankWordEpochState n) (hn : 3 ≤ n)
    (hpred : ring.rightNeighbor e = root)
    (hx : (postW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).eX.l = false)
    (hy : (postW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).eY.l = true)
    (hidle : (z.2.1 root).ser.cert = .IDLE) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z e) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z e) =
        bankWordRenewalSoftRootedPosition ring root z ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z e) = 0 := by
  have hne : ring.rightNeighbor e ≠ e :=
    L3.EWord.rightNeighborDifferent ring (by omega) e
  have hrequested :
      ((bankWordEpochNext ring root z e).2.1 root).ser.cert =
        .REQUESTED := by
    change ((phiW ring z.2.1 e) root).ser.cert = .REQUESTED
    rw [← hpred]
    rw [phiW_ser_target ring z.2.1 e hne]
    have htargetIdle :
        (z.2.1 (ring.rightNeighbor e)).ser.cert = .IDLE := by
      simpa only [hpred] using hidle
    simp [serW, serializerStep, ProjW.lift,
      hx, hy, htargetIdle]
  have holdInactive :
      ¬ ((z.2.1 root).ser.cert = .RUNNING ∧
        (z.2.1 root).ser.phase = .B ∧
        (z.2.1 root).ser.wphase = .CURRENT) := by
    intro h
    rw [hidle] at h
    cases h.1
  have hnewInactive :
      ¬ (((bankWordEpochNext ring root z e).2.1 root).ser.cert =
          .RUNNING ∧
        ((bankWordEpochNext ring root z e).2.1 root).ser.phase =
          .B ∧
        ((bankWordEpochNext ring root z e).2.1 root).ser.wphase =
          .CURRENT) := by
    intro h
    rw [hrequested] at h
    cases h.1
  have holdPos :
      bankWordRenewalSoftRootedPosition ring root z = 0 := by
    simp [bankWordRenewalSoftRootedPosition, holdInactive]
  have hnewPos :
      bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z e) = 0 := by
    simp [bankWordRenewalSoftRootedPosition, hnewInactive]
  refine ⟨?_, hnewPos.trans holdPos.symm, hnewPos⟩
  intro h
  exact False.elim (hnewInactive h)


/-- A rooted ROOT_OUT S2R starts at position zero. A pending
    observation stalls; an actual INTERNAL_OK admission completes
    the root and creates the first B/NEW frontier at offset one.
    Consumer: first charged S-frontier crossing and old-state nomination. -/
theorem bankWordRenewalSoftFirstAdmission {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s)
    (hn : 5 ≤ n)
    (hforward : BankWordRenewalSoftForwardShape ring root z.1 0)
    (hrun : (z.1.2.1 root).ser.cert = .RUNNING)
    (hx : (postW (z.1.2.1 root)
      (z.1.2.1 (ring.rightNeighbor root))).eX.l = true)
    (hy : (postW (z.1.2.1 root)
      (z.1.2.1 (ring.rightNeighbor root))).eY.l = false) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1 root) ∧
    (((z.1.2.1 (ring.rightNeighbor root)).ser.probe = .PENDING ∧
       bankWordRenewalSoftRootedPosition ring root
         (bankWordEpochNext ring root z.1 root) = 0) ∨
     ((z.1.2.1 (ring.rightNeighbor root)).ser.probe = .INTERNAL_OK ∧
       bankWordRenewalSoftRootedPosition ring root
         (bankWordEpochNext ring root z.1 root) = 1)) ∧
    bankWordRenewalSoftRootedPosition ring root z.1 = 0 ∧
    bankWordRenewalSoftRootedChosen ring root s z = root := by
  have hphase : (z.1.2.1 root).ser.phase = .B := by
    simpa only [L3.EWord.siteZero] using hforward.parentPhase
  have hcurrent : (z.1.2.1 root).ser.wphase = .CURRENT := by
    simpa only [L3.EWord.siteZero] using hforward.parentCurrent
  have hzero :
      (z.1.2.1 root).ser.out = .WAIT ∧
      (z.1.2.1 (ring.rightNeighbor root)).ser.phase = .C ∧
      (z.1.2.1 (ring.rightNeighbor root)).ser.wphase = .CURRENT ∧
      ((z.1.2.1 (ring.rightNeighbor root)).ser.probe = .PENDING ∨
       (z.1.2.1 (ring.rightNeighbor root)).ser.probe = .INTERNAL_OK) := by
    rcases hforward.front with hz | hp
    · simpa only [L3.EWord.siteZero, Nat.zero_add,
        L3.EWord.siteOne] using hz.2
    · omega
  have hout : (z.1.2.1 root).ser.out = .WAIT := hzero.1
  have hchildC :
      (z.1.2.1 (ring.rightNeighbor root)).ser.phase = .C :=
    hzero.2.1
  have hchildCurrent :
      (z.1.2.1 (ring.rightNeighbor root)).ser.wphase = .CURRENT :=
    hzero.2.2.1
  have hactive :
      (z.1.2.1 root).ser.cert = .RUNNING ∧
      (z.1.2.1 root).ser.phase = .B ∧
      (z.1.2.1 root).ser.wphase = .CURRENT :=
    ⟨hrun, hphase, hcurrent⟩
  have hnzero : 0 < n := by omega
  have hidx := bankWordRenewalSoftForwardIndex
    ring root z.1 0 hforward
  have holdPos :
      bankWordRenewalSoftRootedPosition ring root z.1 = 0 := by
    simp [bankWordRenewalSoftRootedPosition, hactive,
      hidx, hnzero, L3.EWord.siteZero, hphase]
  have hchosen :
      bankWordRenewalSoftRootedChosen ring root s z = root := by
    simp [bankWordRenewalSoftRootedChosen, hactive, hidx,
      L3.EWord.siteZero, hphase]
  have hne : ring.rightNeighbor root ≠ root :=
    L3.EWord.rightNeighborDifferent ring (by omega) root
  have hprogress :
      BankWordRenewalSoftShape ring root
        (bankWordEpochNext ring root z.1 root) ∧
      (((z.1.2.1 (ring.rightNeighbor root)).ser.probe = .PENDING ∧
         bankWordRenewalSoftRootedPosition ring root
           (bankWordEpochNext ring root z.1 root) = 0) ∨
       ((z.1.2.1 (ring.rightNeighbor root)).ser.probe = .INTERNAL_OK ∧
         bankWordRenewalSoftRootedPosition ring root
           (bankWordEpochNext ring root z.1 root) = 1)) := by
    rcases hzero.2.2.2 with hp | hi
    · have hrootSer :
          ((bankWordEpochNext ring root z.1 root).2.1 root).ser =
            (z.1.2.1 root).ser := by
        change ((phiW ring z.1.2.1 root) root).ser = _
        rw [phiW_ser_source]
        simp [serW, serializerStep, ProjW.lift,
          hx, hy, hrun, hphase, hout, hchildC, hp]
      have hchildSer :
          ((bankWordEpochNext ring root z.1 root).2.1
            (ring.rightNeighbor root)).ser =
            (z.1.2.1 (ring.rightNeighbor root)).ser := by
        change ((phiW ring z.1.2.1 root)
          (ring.rightNeighbor root)).ser = _
        rw [phiW_ser_target ring z.1.2.1 root hne]
        simp [serW, serializerStep, ProjW.lift,
          hx, hy, hrun, hphase, hout, hchildC, hp]
      have hnewForward :
          BankWordRenewalSoftForwardShape ring root
            (bankWordEpochNext ring root z.1 root) 0 := by
        refine {
          pivotBound := by omega
          completed := ?_
          parentPhase := ?_
          parentCurrent := ?_
          front := ?_ }
        · intro j hj
          omega
        · simpa only [L3.EWord.siteZero] using
            (show ((bankWordEpochNext ring root z.1 root).2.1 root).ser.phase = .B by
              rw [hrootSer]; exact hphase)
        · simpa only [L3.EWord.siteZero] using
            (show ((bankWordEpochNext ring root z.1 root).2.1 root).ser.wphase = .CURRENT by
              rw [hrootSer]; exact hcurrent)
        · left
          refine ⟨rfl, ?_, ?_, ?_, ?_⟩
          · simpa only [L3.EWord.siteZero] using
              (show ((bankWordEpochNext ring root z.1 root).2.1 root).ser.out = .WAIT by
                rw [hrootSer]; exact hout)
          · simpa only [Nat.zero_add, L3.EWord.siteOne] using
              (show ((bankWordEpochNext ring root z.1 root).2.1
                  (ring.rightNeighbor root)).ser.phase = .C by
                rw [hchildSer]; exact hchildC)
          · simpa only [Nat.zero_add, L3.EWord.siteOne] using
              (show ((bankWordEpochNext ring root z.1 root).2.1
                  (ring.rightNeighbor root)).ser.wphase = .CURRENT by
                rw [hchildSer]; exact hchildCurrent)
          · left
            simpa only [Nat.zero_add, L3.EWord.siteOne] using
              (show ((bankWordEpochNext ring root z.1 root).2.1
                  (ring.rightNeighbor root)).ser.probe = .PENDING by
                rw [hchildSer]; exact hp)
      have hnewActive :
          ((bankWordEpochNext ring root z.1 root).2.1 root).ser.cert =
            .RUNNING ∧
          ((bankWordEpochNext ring root z.1 root).2.1 root).ser.phase =
            .B ∧
          ((bankWordEpochNext ring root z.1 root).2.1 root).ser.wphase =
            .CURRENT := by
        simp [hrootSer, hrun, hphase, hcurrent]
      have hnewIndex := bankWordRenewalSoftForwardIndex
        ring root (bankWordEpochNext ring root z.1 root) 0 hnewForward
      have hnewPos :
          bankWordRenewalSoftRootedPosition ring root
            (bankWordEpochNext ring root z.1 root) = 0 := by
        simp [bankWordRenewalSoftRootedPosition, hnewActive,
          hnewIndex, hnzero, L3.EWord.siteZero, hnewForward.parentPhase]
      exact ⟨(by intro _; exact Or.inl ⟨0, hnewForward⟩),
        Or.inl ⟨hp, hnewPos⟩⟩
    · have hrootSer :
          ((bankWordEpochNext ring root z.1 root).2.1 root).ser =
            { (z.1.2.1 root).ser with out := .DONE } := by
        change ((phiW ring z.1.2.1 root) root).ser = _
        rw [phiW_ser_source]
        simp [serW, serializerStep, ProjW.lift,
          serEnterB, hx, hy, hrun, hphase, hout, hchildC, hi]
      have hchildSer :
          ((bankWordEpochNext ring root z.1 root).2.1
              (ring.rightNeighbor root)).ser =
            { (z.1.2.1 (ring.rightNeighbor root)).ser with
              phase := .B, out := .NEW, probe := .NONE,
              wphase := .CURRENT } := by
        change ((phiW ring z.1.2.1 root)
          (ring.rightNeighbor root)).ser = _
        rw [phiW_ser_target ring z.1.2.1 root hne]
        simp [serW, serializerStep, ProjW.lift,
          serEnterB, hx, hy, hrun, hphase, hout,
          hchildC, hcurrent, hi]
      have hnewForward :
          BankWordRenewalSoftForwardShape ring root
            (bankWordEpochNext ring root z.1 root) 1 := by
        refine {
          pivotBound := by omega
          completed := ?_
          parentPhase := ?_
          parentCurrent := ?_
          front := ?_ }
        · intro j hj
          have hjzero : j = 0 := by omega
          rw [hjzero, L3.EWord.siteZero]
          simp [hrootSer, hphase, hcurrent]
        · simpa only [L3.EWord.siteOne] using
            (show ((bankWordEpochNext ring root z.1 root).2.1
                (ring.rightNeighbor root)).ser.phase = .B by
              simp [hchildSer])
        · simpa only [L3.EWord.siteOne] using
            (show ((bankWordEpochNext ring root z.1 root).2.1
                (ring.rightNeighbor root)).ser.wphase = .CURRENT by
              simp [hchildSer])
        · right
          refine ⟨by omega, Or.inl ?_⟩
          simpa only [L3.EWord.siteOne] using
            (show ((bankWordEpochNext ring root z.1 root).2.1
                (ring.rightNeighbor root)).ser.out = .NEW by
              simp [hchildSer])
      have hnewActive :
          ((bankWordEpochNext ring root z.1 root).2.1 root).ser.cert =
            .RUNNING ∧
          ((bankWordEpochNext ring root z.1 root).2.1 root).ser.phase =
            .B ∧
          ((bankWordEpochNext ring root z.1 root).2.1 root).ser.wphase =
            .CURRENT := by
        simp [hrootSer, hrun, hphase, hcurrent]
      have hnewIndex := bankWordRenewalSoftForwardIndex
        ring root (bankWordEpochNext ring root z.1 root) 1 hnewForward
      have hnewPos :
          bankWordRenewalSoftRootedPosition ring root
            (bankWordEpochNext ring root z.1 root) = 1 := by
        have hone : 1 < n := by omega
        simp [bankWordRenewalSoftRootedPosition, hnewActive,
          hnewIndex, L3.EWord.siteOne, hchildSer, hone]
      exact ⟨(by intro _; exact Or.inl ⟨1, hnewForward⟩),
        Or.inr ⟨hi, hnewPos⟩⟩
  exact ⟨hprogress.1, hprogress.2, holdPos, hchosen⟩


theorem bankWordRenewalSoftPendingObservationStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s)
    (p : Nat) (hn : 5 ≤ n)
    (hf : BankWordRenewalSoftForwardShape ring root z.1 p)
    (hactive :
      (z.1.2.1 root).ser.cert = .RUNNING ∧
      (z.1.2.1 root).ser.phase = .B ∧
      (z.1.2.1 root).ser.wphase = .CURRENT)
    (hbound : p + 2 < n)
    (hwait :
      (z.1.2.1 (L3.EWord.site ring root p)).ser.out = .WAIT)
    (hchildC :
      (z.1.2.1 (L3.EWord.site ring root (p + 1))).ser.phase = .C)
    (hpending :
      (z.1.2.1 (L3.EWord.site ring root (p + 1))).ser.probe =
        .PENDING)
    (hchildCurrent :
      (z.1.2.1 (L3.EWord.site ring root (p + 1))).ser.wphase =
        .CURRENT)
    (hx : (postW
      (z.1.2.1 (L3.EWord.site ring root (p + 1)))
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root (p + 1))))).eX.l = false)
    (hy : (postW
      (z.1.2.1 (L3.EWord.site ring root (p + 1)))
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root (p + 1))))).eY.l = false) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (p + 1))) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (p + 1))) =
      bankWordRenewalSoftRootedPosition ring root z.1 ∧
    bankWordRenewalSoftRootedChosen ring root s z =
      L3.EWord.site ring root p ∧
    L3.EWord.site ring root (p + 1) ≠
      bankWordRenewalSoftRootedChosen ring root s z := by
  have hne :
      ring.rightNeighbor
        (L3.EWord.site ring root (p + 1)) ≠
        L3.EWord.site ring root (p + 1) :=
    L3.EWord.rightNeighborDifferent ring (by omega)
      (L3.EWord.site ring root (p + 1))
  have hchildPhaseNew :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (p + 1))).2.1
          (L3.EWord.site ring root (p + 1))).ser.phase = .C := by
    change ((phiW ring z.1.2.1
      (L3.EWord.site ring root (p + 1)))
      (L3.EWord.site ring root (p + 1))).ser.phase = .C
    rw [phiW_ser_source]
    cases hc :
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root (p + 1)))).ser.phase <;>
      simp [serW, serializerStep, ProjW.lift,
        hx, hy, hchildC, hpending, hc]
  have hchildCurrentNew :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (p + 1))).2.1
          (L3.EWord.site ring root (p + 1))).ser.wphase =
        .CURRENT := by
    change ((phiW ring z.1.2.1
      (L3.EWord.site ring root (p + 1)))
      (L3.EWord.site ring root (p + 1))).ser.wphase = .CURRENT
    rw [phiW_ser_source]
    cases hc :
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root (p + 1)))).ser.phase <;>
      simp [serW, serializerStep, ProjW.lift,
        hx, hy, hchildC, hpending, hchildCurrent, hc]
  have hchildProbeNew :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (p + 1))).2.1
          (L3.EWord.site ring root (p + 1))).ser.probe =
          .PENDING ∨
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (p + 1))).2.1
          (L3.EWord.site ring root (p + 1))).ser.probe =
          .INTERNAL_OK := by
    change ((phiW ring z.1.2.1
      (L3.EWord.site ring root (p + 1)))
      (L3.EWord.site ring root (p + 1))).ser.probe =
          .PENDING ∨
      ((phiW ring z.1.2.1
        (L3.EWord.site ring root (p + 1)))
        (L3.EWord.site ring root (p + 1))).ser.probe =
          .INTERNAL_OK
    rw [phiW_ser_source]
    cases hc :
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root (p + 1)))).ser.phase <;>
      simp [serW, serializerStep, ProjW.lift,
        hx, hy, hchildC, hpending, hc]
  have hframe (j : Nat) (hj : j < n)
      (hjs : j ≠ p + 1) (hjt : j ≠ p + 2) :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (p + 1))).2.1
          (L3.EWord.site ring root j)).ser =
        (z.1.2.1 (L3.EWord.site ring root j)).ser := by
    have hsourceNe :
        L3.EWord.site ring root j ≠
          L3.EWord.site ring root (p + 1) := by
      intro hh
      have hi := L3.EWord.validationSiteInjective
        ring root j (p + 1) hj (by omega) hh
      exact hjs hi
    have htargetNe :
        L3.EWord.site ring root j ≠
          ring.rightNeighbor
            (L3.EWord.site ring root (p + 1)) := by
      rw [L3.EWord.siteSuccessor]
      intro hh
      have hi := L3.EWord.validationSiteInjective
        ring root j (p + 2) hj hbound hh
      exact hjt hi
    change ((phiW ring z.1.2.1
      (L3.EWord.site ring root (p + 1)))
      (L3.EWord.site ring root j)).ser = _
    simp [phiW, projectedEdge, hsourceNe, htargetNe]
  have hrootSer :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (p + 1))).2.1 root).ser =
          (z.1.2.1 root).ser := by
    simpa only [L3.EWord.siteZero] using
      hframe 0 (by omega) (by omega) (by omega)
  have hnextActive :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (p + 1))).2.1 root).ser.cert =
          .RUNNING ∧
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (p + 1))).2.1 root).ser.phase =
          .B ∧
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (p + 1))).2.1 root).ser.wphase =
          .CURRENT := by
    simp [hrootSer, hactive.1, hactive.2.1, hactive.2.2]
  have hfnew :
      BankWordRenewalSoftForwardShape ring root
        (bankWordEpochNext ring root z.1
          (L3.EWord.site ring root (p + 1))) p := by
    refine {
      pivotBound := hf.pivotBound
      completed := ?_
      parentPhase := ?_
      parentCurrent := ?_
      front := ?_ }
    · intro j hj
      rw [hframe j (by omega) (by omega) (by omega)]
      exact hf.completed j hj
    · rw [hframe p (by omega) (by omega) (by omega)]
      exact hf.parentPhase
    · rw [hframe p (by omega) (by omega) (by omega)]
      exact hf.parentCurrent
    · by_cases hpzero : p = 0
      · left
        refine ⟨hpzero, ?_, ?_, ?_, ?_⟩
        · rw [hframe p (by omega) (by omega) (by omega)]
          exact hwait
        · exact hchildPhaseNew
        · exact hchildCurrentNew
        · exact hchildProbeNew
      · right
        refine ⟨by omega, Or.inr ⟨?_, ?_⟩⟩
        · rw [hframe p (by omega) (by omega) (by omega)]
          exact hwait
        · rcases hchildProbeNew with hpendingNew | hinternalNew
          · apply Or.inl
            exact ⟨hchildPhaseNew, hpendingNew, hchildCurrentNew⟩
          · apply Or.inr
            apply Or.inl
            exact ⟨hbound, hchildPhaseNew, hinternalNew,
              hchildCurrentNew⟩
  have hidxOld := bankWordRenewalSoftForwardIndex
    ring root z.1 p hf
  have hidxNew := bankWordRenewalSoftForwardIndex
    ring root (bankWordEpochNext ring root z.1
      (L3.EWord.site ring root (p + 1))) p hfnew
  have holdParent :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (p + 1))).2.1
          (L3.EWord.site ring root p)).ser =
        (z.1.2.1 (L3.EWord.site ring root p)).ser :=
    hframe p (by omega) (by omega) (by omega)
  have hposEqual :
      bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z.1
          (L3.EWord.site ring root (p + 1))) =
      bankWordRenewalSoftRootedPosition ring root z.1 := by
    simp [bankWordRenewalSoftRootedPosition, hactive,
      hnextActive, hidxOld, hidxNew, holdParent]
  have hchosen :
      bankWordRenewalSoftRootedChosen ring root s z =
        L3.EWord.site ring root p := by
    have hpn : p < n := by
      have hb := hf.pivotBound
      omega
    simp [bankWordRenewalSoftRootedChosen, hactive,
      hidxOld, hf.parentPhase, hf.pivotBound, hpn]
  have hdistinct :
      L3.EWord.site ring root (p + 1) ≠
        L3.EWord.site ring root p := by
    intro hh
    have hi := L3.EWord.validationSiteInjective
      ring root (p + 1) p (by omega) (by omega) hh
    omega
  exact ⟨(by intro _; exact Or.inl ⟨p, hfnew⟩),
    hposEqual, hchosen, (by rw [hchosen]; exact hdistinct)⟩


/-- INTERNAL S2N consumes a rooted C/INTERNAL_OK answer.
    It completes the old parent and admits the next B/NEW;
    the old WAIT already charged the child's position, so
    the new position is unchanged. Consumer: forward admission
    in the R10a soft serializer frontier. -/
theorem bankWordRenewalSoftInternalAdmissionStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s)
    (p : Nat) (hn : 5 ≤ n) (hp : 0 < p)
    (hf : BankWordRenewalSoftForwardShape ring root z.1 p)
    (hrun : (z.1.2.1 root).ser.cert = .RUNNING)
    (hbound : p + 2 < n)
    (hwait :
      (z.1.2.1 (L3.EWord.site ring root p)).ser.out = .WAIT)
    (hchildC :
      (z.1.2.1 (L3.EWord.site ring root (p + 1))).ser.phase = .C)
    (hchildInternal :
      (z.1.2.1 (L3.EWord.site ring root (p + 1))).ser.probe =
        .INTERNAL_OK)
    (hx : (postW
      (z.1.2.1 (L3.EWord.site ring root p))
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root p)))).eX.l = false)
    (hy : (postW
      (z.1.2.1 (L3.EWord.site ring root p))
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root p)))).eY.l = false) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root p)) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root p)) = p + 1 ∧
    bankWordRenewalSoftRootedPosition ring root z.1 = p + 1 ∧
    bankWordRenewalSoftRootedChosen ring root s z =
      L3.EWord.site ring root p := by
  have hpn : p < n := by
    have hh := hf.pivotBound
    omega
  have hpnonzero : p ≠ 0 := Nat.ne_of_gt hp
  have hsourcePhase :
      (z.1.2.1 (L3.EWord.site ring root p)).ser.phase = .B :=
    hf.parentPhase
  have hsourceCurrent :
      (z.1.2.1 (L3.EWord.site ring root p)).ser.wphase = .CURRENT :=
    hf.parentCurrent
  have hchildCNeighbor :
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root p))).ser.phase = .C := by
    rw [L3.EWord.siteSuccessor]
    exact hchildC
  have hchildInternalNeighbor :
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root p))).ser.probe =
          .INTERNAL_OK := by
    rw [L3.EWord.siteSuccessor]
    exact hchildInternal
  have hne :
      ring.rightNeighbor (L3.EWord.site ring root p) ≠
        L3.EWord.site ring root p :=
    L3.EWord.rightNeighborDifferent ring (by omega)
      (L3.EWord.site ring root p)
  have hparentSer :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root p)).2.1
          (L3.EWord.site ring root p)).ser =
        { (z.1.2.1 (L3.EWord.site ring root p)).ser with
          out := .DONE } := by
    change ((phiW ring z.1.2.1
      (L3.EWord.site ring root p))
      (L3.EWord.site ring root p)).ser = _
    rw [phiW_ser_source]
    simp [serW, serializerStep, ProjW.lift,
      serEnterB, hx, hy, hsourcePhase, hsourceCurrent,
      hwait, hchildCNeighbor, hchildInternalNeighbor]
  have hchildSer :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root p)).2.1
          (L3.EWord.site ring root (p + 1))).ser =
        { (z.1.2.1
          (L3.EWord.site ring root (p + 1))).ser with
          phase := .B, out := .NEW, probe := .NONE,
          wphase := .CURRENT } := by
    rw [← L3.EWord.siteSuccessor ring root p]
    change ((phiW ring z.1.2.1
      (L3.EWord.site ring root p))
      (ring.rightNeighbor (L3.EWord.site ring root p))).ser = _
    rw [phiW_ser_target ring z.1.2.1
      (L3.EWord.site ring root p) hne]
    simp [serW, serializerStep, ProjW.lift,
      serEnterB, hx, hy, hsourcePhase, hsourceCurrent,
      hwait, hchildCNeighbor, hchildInternalNeighbor]
  have hframe (j : Nat) (hj : j < n)
      (hjp : j ≠ p) (hjchild : j ≠ p + 1) :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root p)).2.1
          (L3.EWord.site ring root j)).ser =
        (z.1.2.1 (L3.EWord.site ring root j)).ser := by
    have hneSource :
        L3.EWord.site ring root j ≠
          L3.EWord.site ring root p := by
      intro h
      have hh := L3.EWord.validationSiteInjective
        ring root j p hj (by omega) h
      exact hjp hh
    have hneTarget :
        L3.EWord.site ring root j ≠
          ring.rightNeighbor (L3.EWord.site ring root p) := by
      rw [L3.EWord.siteSuccessor]
      intro h
      have hh := L3.EWord.validationSiteInjective
        ring root j (p + 1) hj hf.pivotBound h
      exact hjchild hh
    change ((phiW ring z.1.2.1
      (L3.EWord.site ring root p))
      (L3.EWord.site ring root j)).ser = _
    simp [phiW, projectedEdge, hneSource, hneTarget]
  have hrootSer :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root p)).2.1 root).ser =
        (z.1.2.1 root).ser := by
    simpa only [L3.EWord.siteZero] using
      hframe 0 (by omega) (by omega) (by omega)
  have hrootOld := hf.completed 0 hp
  have hrootPhase : (z.1.2.1 root).ser.phase = .B := by
    simpa only [L3.EWord.siteZero] using hrootOld.1
  have hrootCurrent : (z.1.2.1 root).ser.wphase = .CURRENT := by
    simpa only [L3.EWord.siteZero] using hrootOld.2.2
  have hactive :
      (z.1.2.1 root).ser.cert = .RUNNING ∧
      (z.1.2.1 root).ser.phase = .B ∧
      (z.1.2.1 root).ser.wphase = .CURRENT :=
    ⟨hrun, hrootPhase, hrootCurrent⟩
  have hnextActive :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root p)).2.1 root).ser.cert =
          .RUNNING ∧
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root p)).2.1 root).ser.phase =
          .B ∧
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root p)).2.1 root).ser.wphase =
          .CURRENT := by
    simp [hrootSer, hrun, hrootPhase, hrootCurrent]
  have hfnew : BankWordRenewalSoftForwardShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root p)) (p + 1) := by
    refine {
      pivotBound := hbound
      completed := ?_
      parentPhase := ?_
      parentCurrent := ?_
      front := ?_ }
    · intro j hj
      by_cases heq : j = p
      · rw [heq]
        simp [hparentSer, hf.parentPhase, hf.parentCurrent]
      · have hjlt : j < p := by omega
        rw [hframe j (by omega) heq (by omega)]
        exact hf.completed j hjlt
    · simp [hchildSer]
    · simp [hchildSer]
    · right
      refine ⟨by omega, Or.inl ?_⟩
      simp [hchildSer]
  have hidxOld := bankWordRenewalSoftForwardIndex
    ring root z.1 p hf
  have hidxNew := bankWordRenewalSoftForwardIndex
    ring root (bankWordEpochNext ring root z.1
      (L3.EWord.site ring root p)) (p + 1) hfnew
  have hposOld :
      bankWordRenewalSoftRootedPosition ring root z.1 = p + 1 := by
    simp [bankWordRenewalSoftRootedPosition, hactive,
      hidxOld, hf.parentPhase, hwait, hpnonzero, hpn, hf.pivotBound]
  have hposNew :
      bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z.1
          (L3.EWord.site ring root p)) = p + 1 := by
    simp [bankWordRenewalSoftRootedPosition, hnextActive,
      hidxNew, hfnew.parentPhase, hchildSer, hf.pivotBound, hbound]
  have hchosen :
      bankWordRenewalSoftRootedChosen ring root s z =
        L3.EWord.site ring root p := by
    simp [bankWordRenewalSoftRootedChosen, hactive,
      hidxOld, hf.parentPhase, hpn, hf.pivotBound]
  exact ⟨(by intro _; exact Or.inl ⟨p + 1, hfnew⟩),
    hposNew, hposOld, hchosen⟩


end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open Classical
set_option autoImplicit false
set_option Elab.async false

theorem bankWordRenewalWaveRootOutgoingInternalQuietStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hactive : (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)
    (hb : (z.2.1 root).ser.phase = .B)
    (hw : (z.2.1 root).ser.out = .WAIT)
    (hc : (z.2.1 (ring.rightNeighbor root)).ser.phase = .C)
    (hi : (z.2.1 (ring.rightNeighbor root)).ser.probe =
      .INTERNAL_OK) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z root) := by
  obtain ⟨g, req, stamp, hshape, hsites⟩ :=
    hwave.wave.2 hactive
  have hf : L3.EWord.ForwardShape ring root z.2.1 g := by
    rcases hshape.stageShape with hf | hr
    · exact hf
    · have hdone := hr.completed
        (⟨0, (show 0 < n by omega)⟩ : Fin n)
        hr.pivotPositive
      have hout : (z.2.1 root).ser.out = .DONE := by
        simpa only [Fin.val_mk, L3.EWord.siteZero] using hdone.2.1
      rw [hw] at hout
      cases hout
  have hpivot : g.pivot = 0 := by
    by_cases hzero : g.pivot = 0
    · exact hzero
    · have hpositive : 0 < g.pivot := Nat.pos_of_ne_zero hzero
      have hdone := hf.completed
        (⟨0, (show 0 < n by omega)⟩ : Fin n)
        hpositive
      have hout : (z.2.1 root).ser.out = .DONE := by
        simpa only [Fin.val_mk, L3.EWord.siteZero] using hdone.2.1
      rw [hw] at hout
      cases hout
  have hwaitAt :
      (z.2.1 (L3.EWord.site ring root g.pivot)).ser.out =
        .WAIT := by
    simpa only [hpivot, L3.EWord.siteZero] using hw
  have hobl := L3.EWord.validationFrontierWaitObligation
    ring root z.2.1 g hf hwaitAt
  have hscrub : g.scrub = 2 := by
    rw [hpivot] at hobl
    omega
  have hchildValid :
      (z.2.1 (ring.rightNeighbor root)).ser.wphase =
        .VALIDATING := by
    have hpc := hobl.2
    unfold L3.EWord.pendingChild at hpc
    rcases hpc.2 with hpend | hinter | hleaf
    · have hprobe :
          (z.2.1 (ring.rightNeighbor root)).ser.probe =
            .PENDING := by
        simpa [hpivot, L3.EWord.siteOne] using hpend.1
      rw [hi] at hprobe
      cases hprobe
    · simpa [hpivot, L3.EWord.siteOne] using hinter.2.2
    · have hprobe :
          (z.2.1 (ring.rightNeighbor root)).ser.probe =
            .LEAF_OK := by
        simpa [hpivot, L3.EWord.siteOne] using hleaf.2.1
      rw [hi] at hprobe
      cases hprobe
  have hrootOld :
      BankWordRenewalFrontierWaveSiteTicket ring root z req stamp
        (⟨0, (show 0 < n by omega)⟩ : Fin n)
        .waiting := by
    have ht := (hsites
      (⟨0, (show 0 < n by omega)⟩ : Fin n)
      (by simp only [Fin.val_mk]; rw [hscrub]; omega)).1
        ⟨by simpa only [Fin.val_mk, L3.EWord.siteZero] using hb,
         by simpa only [Fin.val_mk, L3.EWord.siteZero] using hactive.2⟩
    simpa [Fin.val_mk, L3.EWord.siteZero, hw] using ht
  have hchildOld :
      BankWordRenewalFrontierWaveSiteTicket ring root z req stamp
        (⟨1, (show 1 < n by omega)⟩ : Fin n)
        .observedInternal := by
    exact (hsites
      (⟨1, (show 1 < n by omega)⟩ : Fin n)
      (by simp only [Fin.val_mk]; rw [hscrub]; omega)).2.2.1
      ⟨by simpa only [Fin.val_mk, L3.EWord.siteOne] using hc,
       by simpa only [Fin.val_mk, L3.EWord.siteOne] using hi,
       by simpa only [Fin.val_mk, L3.EWord.siteOne] using hchildValid⟩
  obtain ⟨parent, htParent, hreqParent, hstampParent⟩ :=
    hrootOld
  obtain ⟨child, htChild, hreqChild, hstampChild⟩ :=
    hchildOld
  have htParentRoot : wTicketAt .waiting
      ((bankWordHardEpochLedger ring root z).validation root) =
        some parent := by
    simpa only [Fin.val_mk, L3.EWord.siteZero] using htParent
  have htChildNeighbor : wTicketAt .observedInternal
      ((bankWordHardEpochLedger ring root z).validation
        (ring.rightNeighbor root)) = some child := by
    simpa only [Fin.val_mk, L3.EWord.siteOne] using htChild
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 root) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass root).2
  have hpost := clockPostOutgoing ring root z.2.1 root
    (by omega : 2 ≤ n) hfixed rfl
  have hpairSer := L3.EWord.validationParentInternalWrite
    (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
    hpost.2 (by intro _; exact hactive.1)
    hb hw hactive.2 hc hi
  have hrow :
      (bankWordEpochSelectedReceipt ring z root).serializer.row =
        "S2R" := by
    change (serW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).row = "S2R"
    simp [serW, serializerStep, ProjW.lift,
      hpost.1, hpost.2, hactive.1, hb, hw, hc, hi]
  have hrowSer :
      (serW (z.2.1 root)
        (z.2.1 (ring.rightNeighbor root))).row = "S2R" := by
    change (serW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).row = "S2R" at hrow
    exact hrow
  have hpairTickets :
      wValidationPair (z.2.2.clock + 1)
        (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
        ((bankWordHardEpochLedger ring root z).validation root)
        ((bankWordHardEpochLedger ring root z).validation
          (ring.rightNeighbor root)) =
      (some { parent with stage := .done },
       some { parent with stage := .broadcaster }) :=
    bankWordRenewalFrontierWaveInternalAdmission
      (z.2.2.clock + 1)
      (z.2.1 root) (z.2.1 (ring.rightNeighbor root))
      ((bankWordHardEpochLedger ring root z).validation root)
      ((bankWordHardEpochLedger ring root z).validation
        (ring.rightNeighbor root))
      parent child hrowSer hw hc hi htParentRoot htChildNeighbor
      (hreqParent.trans hreqChild.symm)
      (hstampParent.trans hstampChild.symm)
  have hselected := bankWordRenewalWaveSelectedTicketPairStep
    ring root root z (by omega : 2 ≤ n)
  have hjoined :
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z root)).validation root =
        some { parent with stage := .done } ∧
      (bankWordHardEpochLedger ring root
        (bankWordEpochNext ring root z root)).validation
          (ring.rightNeighbor root) =
        some { parent with stage := .broadcaster } := by
    constructor
    · rw [hselected.1, hpairTickets]
    · rw [hselected.2, hpairTickets]
  have hne : ring.rightNeighbor root ≠ root :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) root
  have hrootSer :
      ((bankWordEpochNext ring root z root).2.1 root).ser =
        { (z.2.1 root).ser with out := .DONE } := by
    change ((phiW ring z.2.1 root) root).ser =
      { (z.2.1 root).ser with out := .DONE }
    rw [phiW_ser_source]
    exact hpairSer.1
  have hchildSer :
      ((bankWordEpochNext ring root z root).2.1
        (ring.rightNeighbor root)).ser =
        { (z.2.1 (ring.rightNeighbor root)).ser with
          phase := .B, out := .NEW, probe := .NONE,
          wphase := .VALIDATING } := by
    change ((phiW ring z.2.1 root)
      (ring.rightNeighbor root)).ser =
      { (z.2.1 (ring.rightNeighbor root)).ser with
        phase := .B, out := .NEW, probe := .NONE,
        wphase := .VALIDATING }
    rw [phiW_ser_target ring z.2.1 root hne]
    exact hpairSer.2
  have hrootRun :
      ((bankWordEpochNext ring root z root).2.1 root).ser.cert =
        .RUNNING := by
    rw [hrootSer]
    exact hactive.1
  have hrootDone :
      ((bankWordEpochNext ring root z root).2.1 root).ser.out =
        .DONE := by
    rw [hrootSer]
  have hrootB :
      ((bankWordEpochNext ring root z root).2.1 root).ser.phase =
        .B := by
    rw [hrootSer]
    exact hb
  have hchildB :
      ((bankWordEpochNext ring root z root).2.1
        (ring.rightNeighbor root)).ser.phase = .B := by
    rw [hchildSer]
  have hchildNew :
      ((bankWordEpochNext ring root z root).2.1
        (ring.rightNeighbor root)).ser.out = .NEW := by
    rw [hchildSer]
  have hrootTicketNew :
      BankWordRenewalFrontierWaveSiteTicket ring root
        (bankWordEpochNext ring root z root) req stamp
        (⟨0, (show 0 < n by omega)⟩ : Fin n)
        .done := by
    unfold BankWordRenewalFrontierWaveSiteTicket
    refine ⟨{ parent with stage := .done }, ?_, ?_, ?_⟩
    · rw [L3.EWord.siteZero, hjoined.1]
      rfl
    · exact hreqParent
    · exact hstampParent
  have hchildTicketNew :
      BankWordRenewalFrontierWaveSiteTicket ring root
        (bankWordEpochNext ring root z root) req stamp
        (⟨1, (show 1 < n by omega)⟩ : Fin n)
        .broadcaster := by
    unfold BankWordRenewalFrontierWaveSiteTicket
    refine ⟨{ parent with stage := .broadcaster }, ?_, ?_, ?_⟩
    · rw [L3.EWord.siteOne, hjoined.2]
      rfl
    · exact hreqParent
    · exact hstampParent
  have hno : (serW (z.2.1 root)
      (z.2.1 (ring.rightNeighbor root))).hard.hardAccept =
        false := L3.EWord.waitNoAccept
          (z.2.1 root) (z.2.1 (ring.rightNeighbor root)) hw
  have hstart := L3.EWord.validationParentHardStartFalse
    ring root z.2.1 g root hshape hfixed
  have hparentSite :
      root = L3.EWord.site ring root g.pivot := by
    rw [hpivot, L3.EWord.siteZero]
  have hghost := L3.EWord.validationGhostParentInternalEq
    ring root z.2.1 g root hstart hf.isForward
    hparentSite hb hw hc hi
  have hshapeNew :
      L3.EWord.ValidationShape ring root
        (bankWordEpochNext ring root z root).2.1
        { g with pivot := g.pivot + 1 } := by
    have ht := (L3.EWord.validationTransport
      (c := compileAdvice (ceilLogTwo n)) ring root)
        z.2.1 g root hshape hfixed hno
    rw [hghost] at ht
    exact ht
  have hfNew :
      L3.EWord.ForwardShape ring root
        (bankWordEpochNext ring root z root).2.1
        { g with pivot := g.pivot + 1 } := by
    rcases hshapeNew.stageShape with hforward | hreturn
    · exact hforward
    · have hstage : ({ g with pivot := g.pivot + 1 }).stage =
          .forward := hf.isForward
      have hbad := hreturn.isReturn
      rw [hstage] at hbad
      cases hbad
  have hbase :
      BankWordRenewalFrontierTicketLineage ring root
        (bankWordEpochNext ring root z root) := by
    unfold BankWordRenewalFrontierTicketLineage
    refine ⟨?_, ?_, ?_⟩
    · intro h
      rw [hrootRun] at h
      cases h
    · intro h
      have hwrong :
          ((bankWordEpochNext ring root z root).2.1 root).ser.out =
            .WAIT := h.2.2.2.1
      rw [hrootDone] at hwrong
      cases hwrong
    · intro h
      have hwrong :
          ((bankWordEpochNext ring root z root).2.1
            (ring.rightNeighbor root)).ser.phase = .F :=
        h.2.2.2.2
      rw [hchildB] at hwrong
      cases hwrong
  refine ⟨⟨hbase, ?_⟩, ?_⟩
  · intro hactiveNew
    refine ⟨{ g with pivot := g.pivot + 1 },
      req, stamp, hshapeNew, ?_⟩
    intro k hk
    have hkSmall : k.val < 2 := by
      have ht : k.val < g.scrub := hk
      rw [hscrub] at ht
      exact ht
    have hidx : k.val = 0 ∨ k.val = 1 := by omega
    rcases hidx with hzero | hone
    · have hsite : L3.EWord.site ring root k.val = root := by
        rw [hzero, L3.EWord.siteZero]
      have hindex : k =
          (⟨0, (show 0 < n by omega)⟩ : Fin n) := by
        apply Fin.ext
        simpa only [Fin.val_mk] using hzero
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro h
        rw [hindex]
        simpa [Fin.val_mk, L3.EWord.siteZero, hrootDone] using hrootTicketNew
      · intro h
        have hwrong := h.1
        rw [hsite, hrootB] at hwrong
        cases hwrong
      · intro h
        have hwrong := h.1
        rw [hsite, hrootB] at hwrong
        cases hwrong
      · intro h
        have hwrong := h.1
        rw [hsite, hrootB] at hwrong
        cases hwrong
      · intro h
        have hwrong := h.1
        rw [hsite, hrootB] at hwrong
        cases hwrong
    · have hsite :
          L3.EWord.site ring root k.val =
            ring.rightNeighbor root := by
        rw [hone, L3.EWord.siteOne]
      have hindex : k =
          (⟨1, (show 1 < n by omega)⟩ : Fin n) := by
        apply Fin.ext
        simpa only [Fin.val_mk] using hone
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro h
        rw [hindex]
        simpa [Fin.val_mk, L3.EWord.siteOne, hchildNew] using hchildTicketNew
      · intro h
        have hwrong := h.1
        rw [hsite, hchildB] at hwrong
        cases hwrong
      · intro h
        have hwrong := h.1
        rw [hsite, hchildB] at hwrong
        cases hwrong
      · intro h
        have hwrong := h.1
        rw [hsite, hchildB] at hwrong
        cases hwrong
      · intro h
        have hwrong := h.1
        rw [hsite, hchildB] at hwrong
        cases hwrong
  · intro hactiveNew gnew hreturn k hk hc
    exact False.elim (bankWordRenewalWaveForwardExcludesReturn
      ring root (bankWordEpochNext ring root z root).2.1
      { g with pivot := g.pivot + 1 } gnew hfNew hreturn)

theorem bankWordRenewalWaveRootOutgoingActiveQuietStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hactive :
      (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z root) := by
  obtain ⟨g, req, stamp, hshape, hsites⟩ :=
    hwave.wave.2 hactive
  rcases hshape.stageShape with hf | hr
  · by_cases hpivot : g.pivot = 0
    · have hrootB :
          (z.2.1 root).ser.phase = .B := by
        simpa only [hpivot, L3.EWord.siteZero] using hf.parentB
      have hrootWait :
          (z.2.1 root).ser.out = .WAIT := by
        rcases hf.currentObligation with hnew | hwait
        · have hpositive : 0 < g.pivot := hnew.1
          rw [hpivot] at hpositive
          omega
        · simpa only [hpivot, L3.EWord.siteZero] using hwait.1
      have hwaitAt :
          (z.2.1 (L3.EWord.site ring root g.pivot)).ser.out =
            .WAIT := by
        simpa only [hpivot, L3.EWord.siteZero] using hrootWait
      have hpc := (L3.EWord.validationFrontierWaitObligation
        ring root z.2.1 g hf hwaitAt).2
      unfold L3.EWord.pendingChild at hpc
      obtain ⟨hchildC, hstatus⟩ := hpc
      have hc :
          (z.2.1 (ring.rightNeighbor root)).ser.phase = .C := by
        simpa [hpivot, L3.EWord.siteOne] using hchildC
      rcases hstatus with hpend | hinter | hleaf
      · have hprobe :
            (z.2.1 (ring.rightNeighbor root)).ser.probe =
              .PENDING := by
          simpa [hpivot, L3.EWord.siteOne] using hpend.1
        exact bankWordRenewalWaveRootOutgoingPendingQuietStep
          ring root s hn hbank hs z hz hwave
          hactive.1 hrootB hrootWait hc hprobe
      · have hprobe :
            (z.2.1 (ring.rightNeighbor root)).ser.probe =
              .INTERNAL_OK := by
          simpa [hpivot, L3.EWord.siteOne] using hinter.2.1
        exact bankWordRenewalWaveRootOutgoingInternalQuietStep
          ring root s hn hbank hs z hz hwave
          hactive hrootB hrootWait hc hprobe
      · have hterminal : g.pivot + 2 = n := hleaf.1
        rw [hpivot] at hterminal
        omega
    · have hpositive : 0 < g.pivot := Nat.pos_of_ne_zero hpivot
      have hdone := hf.completed
        (⟨0, (show 0 < n by omega)⟩ : Fin n) hpositive
      have hrootB : (z.2.1 root).ser.phase = .B := by
        simpa only [L3.EWord.siteZero] using hdone.1
      have hout : (z.2.1 root).ser.out = .DONE := by
        simpa only [L3.EWord.siteZero] using hdone.2.1
      have hchildB :
          (z.2.1 (ring.rightNeighbor root)).ser.phase = .B := by
        by_cases hone : g.pivot = 1
        · simpa only [hone, L3.EWord.siteOne] using hf.parentB
        · have hlt : 1 < g.pivot := by omega
          simpa only [L3.EWord.siteOne] using
            (hf.completed
              (⟨1, (show 1 < n by omega)⟩ : Fin n) hlt).1
      exact bankWordRenewalWaveRootOutgoingCoveredQuietStep
        ring root s hn hbank hs z hz hwave
        hactive.1 hrootB hout hchildB
  · have hdone := hr.completed
      (⟨0, (show 0 < n by omega)⟩ : Fin n)
      hr.pivotPositive
    have hrootB : (z.2.1 root).ser.phase = .B := by
      simpa only [L3.EWord.siteZero] using hdone.1
    have hout : (z.2.1 root).ser.out = .DONE := by
      simpa only [L3.EWord.siteZero] using hdone.2.1
    by_cases hone : g.pivot = 1
    · have hchildF :
          (z.2.1 (ring.rightNeighbor root)).ser.phase = .F := by
        simpa only [hone, L3.EWord.siteOne] using hr.leftmostF
      have hcertNotRequested :
          (z.2.1 root).ser.cert ≠ .REQUESTED := by
        rw [hactive.1]
        decide
      exact bankWordRenewalWaveRootOutgoingFinishQuietStep
        ring root s hn hbank hs z hz
        hcertNotRequested hrootB hout hchildF
    · have hlt : 1 < g.pivot := by
        have hpositive := hr.pivotPositive
        omega
      have hchildB :
          (z.2.1 (ring.rightNeighbor root)).ser.phase = .B := by
        simpa only [L3.EWord.siteOne] using
          (hr.completed
            (⟨1, (show 1 < n by omega)⟩ : Fin n) hlt).1
      exact bankWordRenewalWaveRootOutgoingCoveredQuietStep
        ring root s hn hbank hs z hz hwave
        hactive.1 hrootB hout hchildB


theorem bankWordRenewalWaveBroadcasterIsParent
    (gx : Option WValidationTicket) (parent : WValidationTicket)
    (h : wTicketAt .broadcaster gx = some parent) :
    wParentTicket gx = some parent := by
  cases gx with
  | none =>
      change (none : Option WValidationTicket) = some parent at h
      cases h
  | some t =>
      by_cases hb : t.stage = .broadcaster
      · have hsame : t = parent := by
          simpa [wTicketAt, hb] using h
        cases hsame
        simp [wParentTicket, hb]
      · have hbad : (none : Option WValidationTicket) =
            some parent := by
          simpa [wTicketAt, hb] using h
        cases hbad

theorem bankWordRenewalWaveInternalFrontierNewQuietStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hactive : (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)
    (g : L3.EWord.ValidationGhost)
    (hg : g = Classical.choose (hwave.wave.2 hactive))
    (hforward : g.stage = .forward)
    (he : e = L3.EWord.site ring root g.pivot)
    (hnew : (z.2.1 e).ser.out = .NEW) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z e) := by
  have hspec := Classical.choose_spec (hwave.wave.2 hactive)
  rw [← hg] at hspec
  obtain ⟨req, stamp, hshape, hsites⟩ := hspec
  have hf : L3.EWord.ForwardShape ring root z.2.1 g := by
    rcases hshape.stageShape with hF | hR
    · exact hF
    · have hbad := hR.isReturn
      rw [hforward] at hbad
      cases hbad
  have hnewSite :
      (z.2.1 (L3.EWord.site ring root g.pivot)).ser.out =
        .NEW := by
    rw [← he]
    exact hnew
  have hfirst := L3.EWord.validationFrontierNewObligation
    ring root z.2.1 g hf hnewSite
  have hpositive : 0 < g.pivot := hfirst.1
  have hsc : g.scrub = g.pivot + 1 := hfirst.2
  have hpivotBound : g.pivot < n := by
    have hp := hf.pivotBound
    omega
  have hparentOld :
      BankWordRenewalFrontierWaveSiteTicket ring root z
        req stamp
        (⟨g.pivot, hpivotBound⟩ : Fin n)
        .broadcaster := by
    have ht := (hsites
      (⟨g.pivot, hpivotBound⟩ : Fin n)
      (by simp only [Fin.val_mk]; rw [hsc]; omega)).1
      ⟨by simpa only [Fin.val_mk] using hf.parentB,
       by simpa only [Fin.val_mk] using hf.parentValidating⟩
    simpa [Fin.val_mk, hnewSite] using ht
  obtain ⟨parent, htParent, hreqParent, hstampParent⟩ :=
    hparentOld
  have htParentAtE :
      wTicketAt .broadcaster
        ((bankWordHardEpochLedger ring root z).validation e) =
          some parent := by
    rw [he]
    simpa only [Fin.val_mk] using htParent
  have hparent := bankWordRenewalWaveBroadcasterIsParent
    ((bankWordHardEpochLedger ring root z).validation e)
    parent htParentAtE
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass e).2
  have hresponder : ring.rightNeighbor e =
      L3.EWord.site ring root (g.pivot + 1) :=
    L3.EWord.validationParentNeighbor
      ring root g.pivot e he
  have heNotRoot : e ≠ root := by
    rw [he]
    exact L3.EWord.validationPositiveSiteNotRoot
      ring root g.pivot hpivotBound hpositive
  have hrespNotRoot : ring.rightNeighbor e ≠ root := by
    rw [hresponder]
    exact L3.EWord.validationPositiveSiteNotRoot ring root
      (g.pivot + 1) hf.pivotBound (by omega)
  have hpost := clockPostInternal ring root z.2.1 e
    (by omega : 2 ≤ n) hfixed heNotRoot hrespNotRoot
  have hb : (z.2.1 e).ser.phase = .B := by
    rw [he]
    exact hf.parentB
  have hv : (z.2.1 e).ser.wphase = .VALIDATING := by
    rw [he]
    exact hf.parentValidating
  have hpair := L3.EWord.validationParentNewWrite
    (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
    hpost.2 (by intro h; rw [hpost.1] at h; cases h)
    hb hnew hv
  have hrow :
      (bankWordEpochSelectedReceipt ring z e).serializer.row =
        "S2N" := by
    change (serW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).row = "S2N"
    simp [serW, serializerStep, ProjW.lift,
      hpost.1, hpost.2, hb]
  have hjoined := bankWordRenewalWaveInternalNewAnyResponderTicketStep
    ring root e z (by omega : 2 ≤ n) parent
    hrow hnew hparent
  have hne : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) e
  have hsourceSer :
      ((bankWordEpochNext ring root z e).2.1 e).ser =
        { (z.2.1 e).ser with out := .WAIT } := by
    change ((phiW ring z.2.1 e) e).ser =
      { (z.2.1 e).ser with out := .WAIT }
    rw [phiW_ser_source]
    exact hpair.1
  have htargetSer :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor e)).ser =
        { (z.2.1 (ring.rightNeighbor e)).ser with
          phase := .C, out := .NEW,
          probe := .PENDING, wphase := .VALIDATING } := by
    change ((phiW ring z.2.1 e)
      (ring.rightNeighbor e)).ser =
      { (z.2.1 (ring.rightNeighbor e)).ser with
        phase := .C, out := .NEW,
        probe := .PENDING, wphase := .VALIDATING }
    rw [phiW_ser_target ring z.2.1 e hne]
    exact hpair.2
  have hsourceB :
      ((bankWordEpochNext ring root z e).2.1 e).ser.phase =
        .B := by rw [hsourceSer]; exact hb
  have hsourceWait :
      ((bankWordEpochNext ring root z e).2.1 e).ser.out =
        .WAIT := by rw [hsourceSer]
  have htargetC :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor e)).ser.phase = .C := by
    rw [htargetSer]
  have htargetPending :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor e)).ser.probe = .PENDING := by
    rw [htargetSer]
  have hsourceTicketNew :
      BankWordRenewalFrontierWaveSiteTicket ring root
        (bankWordEpochNext ring root z e) req stamp
        (⟨g.pivot, hpivotBound⟩ : Fin n) .waiting := by
    unfold BankWordRenewalFrontierWaveSiteTicket
    refine ⟨{ parent with stage := .waiting }, ?_, ?_, ?_⟩
    · simp only [Fin.val_mk, ← he, hjoined.1, wTicketAt]
      rfl
    · exact hreqParent
    · exact hstampParent
  have htargetTicketNew :
      BankWordRenewalFrontierWaveSiteTicket ring root
        (bankWordEpochNext ring root z e) req stamp
        (⟨g.pivot + 1, hf.pivotBound⟩ : Fin n)
        .pending := by
    unfold BankWordRenewalFrontierWaveSiteTicket
    refine ⟨{ parent with stage := .pending }, ?_, ?_, ?_⟩
    · simp only [Fin.val_mk, ← hresponder, hjoined.2,
        wTicketAt]
      rfl
    · exact hreqParent
    · exact hstampParent
  have hno : (serW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).hard.hardAccept =
        false := L3.EWord.nonrootNoAccept
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e)) hpost.1
  have hstart := L3.EWord.validationParentHardStartFalse
    ring root z.2.1 g e hshape hfixed
  have hhard := (L3.EWord.freshChildGuards
    (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
    hb hnew hv).1
  have hghost := L3.EWord.validationGhostParentNewEq
    ring root z.2.1 g e hstart hf.isForward he
    hb hnew hv hhard
  have hshapeNew :
      L3.EWord.ValidationShape ring root
        (bankWordEpochNext ring root z e).2.1
        { g with scrub := g.scrub + 1 } := by
    have ht := (L3.EWord.validationTransport
      (c := compileAdvice (ceilLogTwo n)) ring root)
      z.2.1 g e hshape hfixed hno
    rw [hghost] at ht
    exact ht
  have hfNew :
      L3.EWord.ForwardShape ring root
        (bankWordEpochNext ring root z e).2.1
        { g with scrub := g.scrub + 1 } := by
    rcases hshapeNew.stageShape with hfNow | hrNow
    · exact hfNow
    · have hwrong : ({ g with scrub := g.scrub + 1 }).stage =
          .forward := hf.isForward
      rw [hrNow.isReturn] at hwrong
      cases hwrong
  have hrootSer :
      ((bankWordEpochNext ring root z e).2.1 root).ser =
        (z.2.1 root).ser := by
    change ((phiW ring z.2.1 e) root).ser = (z.2.1 root).ser
    exact phiW_ser_remote ring z.2.1 e root
      heNotRoot.symm hrespNotRoot.symm
  have hrootDone : (z.2.1 root).ser.out = .DONE := by
    have hd := hf.completed
      (⟨0, (show 0 < n by omega)⟩ : Fin n) hpositive
    simpa only [L3.EWord.siteZero] using hd.2.1
  have hfirstChildB :
      ((bankWordEpochNext ring root z e).2.1
        (ring.rightNeighbor root)).ser.phase = .B := by
    by_cases hpone : g.pivot = 1
    · have hfirstSite : e = ring.rightNeighbor root := by
        rw [he, hpone, L3.EWord.siteOne]
      rw [← hfirstSite, hsourceB]
    · have hlt : 1 < g.pivot := by omega
      have holdB : (z.2.1 (ring.rightNeighbor root)).ser.phase =
          .B := by
        simpa only [L3.EWord.siteOne] using
          (hf.completed
            (⟨1, (show 1 < n by omega)⟩ : Fin n) hlt).1
      have hfr := L3.EWord.validationParentFrame
        ring root z.2.1 g.pivot e hf.pivotBound he
        1 (by omega : 1 < n) (by omega) (by omega)
      change ((phiW ring z.2.1 e)
        (ring.rightNeighbor root)).ser.phase = .B
      rw [← L3.EWord.siteOne, hfr]
      exact holdB
  have hbase :
      BankWordRenewalFrontierTicketLineage ring root
        (bankWordEpochNext ring root z e) := by
    unfold BankWordRenewalFrontierTicketLineage
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have hold : (z.2.1 root).ser.cert = .REQUESTED := by
        simpa only [hrootSer] using h
      rw [hactive.1] at hold
      cases hold
    · intro h
      have hwrong :
          ((bankWordEpochNext ring root z e).2.1 root).ser.out =
            .WAIT := h.2.2.2.1
      rw [hrootSer, hrootDone] at hwrong
      cases hwrong
    · intro h
      have hwrong :
          ((bankWordEpochNext ring root z e).2.1
            (ring.rightNeighbor root)).ser.phase = .F :=
          h.2.2.2.2
      rw [hfirstChildB] at hwrong
      cases hwrong
  have hnewWave :
      BankWordRenewalFrontierWaveLineage ring root
        (bankWordEpochNext ring root z e) := by
    refine ⟨hbase, ?_⟩
    intro hactiveNew
    refine ⟨{ g with scrub := g.scrub + 1 }, req, stamp,
      hshapeNew, ?_⟩
    intro k hk
    have hkBound : k.val < g.pivot + 2 := by
      change k.val < g.scrub + 1 at hk
      rw [hsc] at hk
      omega
    by_cases hsrcIndex : k.val = g.pivot
    · have hsite : L3.EWord.site ring root k.val = e := by
        rw [hsrcIndex, ← he]
      have hindex : k = (⟨g.pivot, hpivotBound⟩ : Fin n) := by
        apply Fin.ext
        simpa only [Fin.val_mk] using hsrcIndex
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro h
        rw [hindex]
        simpa [Fin.val_mk, ← he, hsourceWait] using
          hsourceTicketNew
      · intro h
        have hwrong := h.1
        rw [hsite, hsourceB] at hwrong
        cases hwrong
      · intro h
        have hwrong := h.1
        rw [hsite, hsourceB] at hwrong
        cases hwrong
      · intro h
        have hwrong := h.1
        rw [hsite, hsourceB] at hwrong
        cases hwrong
      · intro h
        have hwrong := h.1
        rw [hsite, hsourceB] at hwrong
        cases hwrong
    · by_cases hdstIndex : k.val = g.pivot + 1
      · have hsite :
            L3.EWord.site ring root k.val =
              ring.rightNeighbor e := by
          rw [hdstIndex, ← hresponder]
        have hindex : k =
            (⟨g.pivot + 1, hf.pivotBound⟩ : Fin n) := by
          apply Fin.ext
          simpa only [Fin.val_mk] using hdstIndex
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro h
          have hwrong := h.1
          rw [hsite, htargetC] at hwrong
          cases hwrong
        · intro h
          rw [hindex]
          exact htargetTicketNew
        · intro h
          have hwrong := h.2.1
          rw [hsite, htargetPending] at hwrong
          cases hwrong
        · intro h
          have hwrong := h.2
          rw [hsite, htargetPending] at hwrong
          cases hwrong
        · intro h
          have hwrong := h.1
          rw [hsite, htargetC] at hwrong
          cases hwrong
      · have hkOld : k.val < g.scrub := by
          rw [hsc]
          omega
        have hsrcNe : L3.EWord.site ring root k.val ≠ e := by
          intro h
          have hsame :
              L3.EWord.site ring root k.val =
                L3.EWord.site ring root g.pivot := by
            rw [← he]
            exact h
          have heq := L3.EWord.validationSiteInjective
            ring root k.val g.pivot k.isLt hpivotBound hsame
          exact hsrcIndex heq
        have hdstNe :
            L3.EWord.site ring root k.val ≠
              ring.rightNeighbor e := by
          intro h
          have hsame :
              L3.EWord.site ring root k.val =
                L3.EWord.site ring root (g.pivot + 1) := by
            rw [← hresponder]
            exact h
          have heq := L3.EWord.validationSiteInjective
            ring root k.val (g.pivot + 1) k.isLt
            hf.pivotBound hsame
          exact hdstIndex heq
        have hser :
            ((bankWordEpochNext ring root z e).2.1
              (L3.EWord.site ring root k.val)).ser =
              (z.2.1 (L3.EWord.site ring root k.val)).ser := by
          change ((phiW ring z.2.1 e)
            (L3.EWord.site ring root k.val)).ser =
            (z.2.1 (L3.EWord.site ring root k.val)).ser
          exact phiW_ser_remote ring z.2.1 e
            (L3.EWord.site ring root k.val) hsrcNe hdstNe
        have ht := bankWordRenewalFrontierWaveTicketRemoteFrame
          ring root z e (L3.EWord.site ring root k.val)
          hsrcNe hdstNe
        simpa only [BankWordRenewalFrontierWaveSiteTicket,
          hser, ht] using hsites k hkOld
  refine ⟨hnewWave, ?_⟩
  intro hactiveNew gnew hreturn k hk hc
  exact False.elim (bankWordRenewalWaveForwardExcludesReturn
    ring root (bankWordEpochNext ring root z e).2.1
    { g with scrub := g.scrub + 1 } gnew hfNew hreturn)

theorem bankWordRenewalWaveInternalCanonicalQuietStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (he : e ≠ root)
    (hj : ring.rightNeighbor e ≠ root)
    (hsource : (z.2.1 e).ser.phase = .C ∨
      (z.2.1 e).ser.phase = .F)
    (htarget :
      (z.2.1 (ring.rightNeighbor e)).ser.phase = .B ∨
      (z.2.1 (ring.rightNeighbor e)).ser.phase = .F) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z e) := by
  have hbase := bankWordRenewalWaveInternalCanonicalRootLineageStep
    ring root e s hn hbank hs z hz hwave he hj hsource htarget
  have hcleanup := bankWordRenewalWaveInternalCanonicalCleanupStep
    ring root e s hn hbank hs z hz he hj hsource htarget
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.2.1 hclass e).2
  have hpost := clockPostInternal ring root z.2.1 e
    (by omega : 2 ≤ n) hfixed he hj
  have hsrcPair :
      (serW (z.2.1 e)
        (z.2.1 (ring.rightNeighbor e))).x =
          (z.2.1 e).ser := by
    rcases hsource with hc | hf
    · exact (L3.EWord.validationChildCanonicalSerializer
        (z.2.1 e) (z.2.1 (ring.rightNeighbor e))
        hpost.1 hpost.2 hc htarget).2.1
    · rcases htarget with hb | hright
      · simp [serW, serializerStep, ProjW.lift,
          serCanonicalC, hpost.1, hpost.2, hf, hb]
      · simp [serW, serializerStep, ProjW.lift,
          serCanonicalC, hpost.1, hpost.2, hf, hright]
  have hsrcSer :
      ((bankWordEpochNext ring root z e).2.1 e).ser =
        (z.2.1 e).ser := by
    change ((phiW ring z.2.1 e) e).ser =
      (z.2.1 e).ser
    rw [phiW_ser_source]
    exact hsrcPair
  have hsrcTicket := hcleanup.2.2
  have hno : (serW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).hard.hardAccept =
        false := L3.EWord.nonrootNoAccept
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e)) hpost.1
  have hstart : (serW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).hard.hardS1 =
        false := L3.EWord.nonrootHardStartFalse
          (z.2.1 e) (z.2.1 (ring.rightNeighbor e)) hpost.1
  have hroot := bankWordHardEpochRootRemoteFrame
    ring root z e he.symm hj.symm
  have hactiveOld :
      ((bankWordEpochNext ring root z e).2.1 root).ser.cert =
         .RUNNING ∧
      ((bankWordEpochNext ring root z e).2.1 root).ser.wphase =
         .VALIDATING →
      (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING := by
    intro h
    simpa only [hroot] using h
  have hnewWave :
      BankWordRenewalFrontierWaveLineage ring root
        (bankWordEpochNext ring root z e) := by
    refine ⟨hbase, ?_⟩
    intro hnewActive
    have hactive := hactiveOld hnewActive
    obtain ⟨g, req, stamp, hshape, hsites⟩ :=
      hwave.wave.2 hactive
    have hnonB := L3.EWord.validationNonBGhostFixed
      ring root z.2.1 g e hstart hsource
    have hshapeNew :
        L3.EWord.ValidationShape ring root
          (bankWordEpochNext ring root z e).2.1 g := by
      have ht := (L3.EWord.validationTransport
        (c := compileAdvice (ceilLogTwo n)) ring root)
        z.2.1 g e hshape hfixed hno
      rw [hnonB] at ht
      exact ht
    refine ⟨g, req, stamp, hshapeNew, ?_⟩
    intro k hk
    by_cases hdst : L3.EWord.site ring root k.val =
        ring.rightNeighbor e
    · have hdestSer :
          ((bankWordEpochNext ring root z e).2.1
            (L3.EWord.site ring root k.val)).ser =
          serCanonicalC
            (z.2.1 (ring.rightNeighbor e)).ser := by
        rw [hdst]
        exact hcleanup.1
      have hdestPhase :
          ((bankWordEpochNext ring root z e).2.1
            (L3.EWord.site ring root k.val)).ser.phase = .C := by
        rw [hdestSer]
        rfl
      have hdestProbe :
          ((bankWordEpochNext ring root z e).2.1
            (L3.EWord.site ring root k.val)).ser.probe = .NONE := by
        rw [hdestSer]
        rfl
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro h
        have hb := h.1
        rw [hdestPhase] at hb
        cases hb
      · intro h
        have hp := h.2.1
        rw [hdestProbe] at hp
        cases hp
      · intro h
        have hp := h.2.1
        rw [hdestProbe] at hp
        cases hp
      · intro h
        have hp := h.2
        rw [hdestProbe] at hp
        cases hp
      · intro h
        have hb := h.1
        rw [hdestPhase] at hb
        cases hb
    · have hsiteSer :
          ((bankWordEpochNext ring root z e).2.1
            (L3.EWord.site ring root k.val)).ser =
          (z.2.1 (L3.EWord.site ring root k.val)).ser := by
        by_cases hsrc : L3.EWord.site ring root k.val = e
        · rw [hsrc]
          exact hsrcSer
        · change ((phiW ring z.2.1 e)
            (L3.EWord.site ring root k.val)).ser =
            (z.2.1 (L3.EWord.site ring root k.val)).ser
          exact phiW_ser_remote ring z.2.1 e
            (L3.EWord.site ring root k.val) hsrc hdst
      have hsiteTicket :
          (bankWordHardEpochLedger ring root
            (bankWordEpochNext ring root z e)).validation
              (L3.EWord.site ring root k.val) =
          (bankWordHardEpochLedger ring root z).validation
              (L3.EWord.site ring root k.val) := by
        by_cases hsrc : L3.EWord.site ring root k.val = e
        · rw [hsrc]
          exact hsrcTicket
        · exact bankWordRenewalFrontierWaveTicketRemoteFrame
            ring root z e (L3.EWord.site ring root k.val)
            hsrc hdst
      simpa only [BankWordRenewalFrontierWaveSiteTicket,
        hsiteSer, hsiteTicket] using hsites k hk
  refine ⟨hnewWave, ?_⟩
  intro hnewActive gnew hrnew k hk hc
  have hactive := hactiveOld hnewActive
  obtain ⟨g, req, stamp, hshape, hsites⟩ :=
    hwave.wave.2 hactive
  have hnonB := L3.EWord.validationNonBGhostFixed
    ring root z.2.1 g e hstart hsource
  have hshapeNew :
      L3.EWord.ValidationShape ring root
        (bankWordEpochNext ring root z e).2.1 g := by
    have ht := (L3.EWord.validationTransport
      (c := compileAdvice (ceilLogTwo n)) ring root)
      z.2.1 g e hshape hfixed hno
    rw [hnonB] at ht
    exact ht
  rcases hshapeNew.stageShape with hfNew | hrNew
  · exact False.elim (bankWordRenewalWaveForwardExcludesReturn
      ring root (bankWordEpochNext ring root z e).2.1
      g gnew hfNew hrnew)
  · have hpivot := bankWordRenewalWaveReturnPivotUnique
      ring root (bankWordEpochNext ring root z e).2.1
      g gnew hrNew hrnew
    have hlt : g.pivot < k.val := by
      rw [hpivot]
      exact hk
    have hreturnOld : L3.EWord.ReturnShape ring root z.2.1 g := by
      rcases hshape.stageShape with hfOld | hrOld
      · have hwrong := hfOld.isForward
        rw [hrNew.isReturn] at hwrong
        cases hwrong
      · exact hrOld
    by_cases hdst : L3.EWord.site ring root k.val =
        ring.rightNeighbor e
    · have hdestSer :
          ((bankWordEpochNext ring root z e).2.1
            (L3.EWord.site ring root k.val)).ser =
          serCanonicalC
            (z.2.1 (ring.rightNeighbor e)).ser := by
        rw [hdst]
        exact hcleanup.1
      have hq :
          ((bankWordEpochNext ring root z e).2.1
            (L3.EWord.site ring root k.val)).ser.probe = .NONE := by
        rw [hdestSer]
        rfl
      rw [hq]
      decide
    · have hframe :
          ((bankWordEpochNext ring root z e).2.1
            (L3.EWord.site ring root k.val)).ser =
          (z.2.1 (L3.EWord.site ring root k.val)).ser := by
        by_cases hsrc : L3.EWord.site ring root k.val = e
        · rw [hsrc]
          exact hsrcSer
        · change ((phiW ring z.2.1 e)
            (L3.EWord.site ring root k.val)).ser =
            (z.2.1 (L3.EWord.site ring root k.val)).ser
          exact phiW_ser_remote ring z.2.1 e
            (L3.EWord.site ring root k.val) hsrc hdst
      have holdC :
          (z.2.1 (L3.EWord.site ring root k.val)).ser.phase =
            .C := by
        simpa only [hframe] using hc
      have hq := hwave.returnSuffixQuiet
        hactive g hreturnOld k hlt holdC
      simpa only [hframe] using hq



end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

theorem bankWordRenewalSoftSuffixFrameStep {n : Nat}
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
    bankWordRenewalSoftRootedChosen ring root s z =
      L3.EWord.site ring root p := by
  have hframe (j : Nat) (hj : j ≤ p + 1) :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root k)).2.1
          (L3.EWord.site ring root j)).ser =
        (z.1.2.1 (L3.EWord.site ring root j)).ser := by
    have hjn : j < n := by omega
    have hsourceNe :
        L3.EWord.site ring root j ≠
          L3.EWord.site ring root k := by
      intro he
      have hi := L3.EWord.validationSiteInjective
        ring root j k hjn (by omega) he
      omega
    have htargetNe :
        L3.EWord.site ring root j ≠
          ring.rightNeighbor (L3.EWord.site ring root k) := by
      rw [L3.EWord.siteSuccessor]
      intro he
      have hi := L3.EWord.validationSiteInjective
        ring root j (k + 1) hjn hinside he
      omega
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
      hframe 0 (by omega)
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
    simpa only [hrootSer] using hactive
  have hfnew : BankWordRenewalSoftForwardShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root k)) p := by
    refine {
      pivotBound := hf.pivotBound
      completed := ?_
      parentPhase := ?_
      parentCurrent := ?_
      front := ?_ }
    · intro j hj
      simpa only [hframe j (by omega)] using
        hf.completed j hj
    · simpa only [hframe p (by omega)] using
        hf.parentPhase
    · simpa only [hframe p (by omega)] using
        hf.parentCurrent
    · simpa only [hframe p (by omega),
        hframe (p + 1) (by omega)] using hf.front
  have hidxOld := bankWordRenewalSoftForwardIndex
    ring root z.1 p hf
  have hidxNew := bankWordRenewalSoftForwardIndex
    ring root (bankWordEpochNext ring root z.1
      (L3.EWord.site ring root k)) p hfnew
  have hparentFrame :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root k)).2.1
          (L3.EWord.site ring root p)).ser =
        (z.1.2.1 (L3.EWord.site ring root p)).ser :=
    hframe p (by omega)
  have hposEqual :
      bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z.1
          (L3.EWord.site ring root k)) =
      bankWordRenewalSoftRootedPosition ring root z.1 := by
    simp [bankWordRenewalSoftRootedPosition, hactive,
      hnextActive, hidxOld, hidxNew, hparentFrame]
  have hchosen :
      bankWordRenewalSoftRootedChosen ring root s z =
        L3.EWord.site ring root p := by
    have hpn : p < n := by
      have hb := hf.pivotBound
      omega
    simp [bankWordRenewalSoftRootedChosen, hactive,
      hidxOld, hf.parentPhase, hpn]
  exact ⟨(by intro _; exact Or.inl ⟨p, hfnew⟩),
    hposEqual, hchosen⟩

/-- Active ROOT_IN S5 with a foreign B at the seam converts only
    that terminal B to canonical C. If the rooted forward frontier
    has not reached the leaf, its parent, child, position, and
    nomination remain unchanged. Consumer: the foreign-B S5 case
    of the R10a rooted frontier induction. -/
theorem bankWordRenewalSoftRootIncomingForeignBStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s)
    (p : Nat) (hn : 5 ≤ n)
    (hf : BankWordRenewalSoftForwardShape ring root z.1 p)
    (hactive :
      (z.1.2.1 root).ser.cert = .RUNNING ∧
      (z.1.2.1 root).ser.phase = .B ∧
      (z.1.2.1 root).ser.wphase = .CURRENT)
    (hbeforeLeaf : p + 2 < n)
    (hforeignB :
      (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.phase = .B)
    (hx : (postW
      (z.1.2.1 (L3.EWord.site ring root (n - 1)))
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root (n - 1))))).eX.l = false)
    (hy : (postW
      (z.1.2.1 (L3.EWord.site ring root (n - 1)))
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root (n - 1))))).eY.l = true) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))) =
      bankWordRenewalSoftRootedPosition ring root z.1 ∧
    bankWordRenewalSoftRootedChosen ring root s z =
      L3.EWord.site ring root p ∧
    ((bankWordEpochNext ring root z.1
      (L3.EWord.site ring root (n - 1))).2.1
        (L3.EWord.site ring root (n - 1))).ser.phase = .C := by
  have hseam :
      ring.rightNeighbor (L3.EWord.site ring root (n - 1)) =
        root :=
    L3.EWord.validationSeamNeighbor ring root
      (L3.EWord.site ring root (n - 1)) rfl
  have hne :
      ring.rightNeighbor (L3.EWord.site ring root (n - 1)) ≠
        L3.EWord.site ring root (n - 1) :=
    L3.EWord.rightNeighborDifferent ring (by omega)
      (L3.EWord.site ring root (n - 1))
  have hrootRunningNeighbor :
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root (n - 1)))).ser.cert =
          .RUNNING := by
    rw [hseam]
    exact hactive.1
  have hsourceSer :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1
          (L3.EWord.site ring root (n - 1))).ser =
        serCanonicalC
          (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser := by
    change ((phiW ring z.1.2.1
      (L3.EWord.site ring root (n - 1)))
      (L3.EWord.site ring root (n - 1))).ser = _
    rw [phiW_ser_source]
    simp [serW, serializerStep, ProjW.lift,
      serCanonicalC, hx, hy, hrootRunningNeighbor, hforeignB]
  have hrootSerNeighbor :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1
          (ring.rightNeighbor
            (L3.EWord.site ring root (n - 1)))).ser =
        (z.1.2.1 (ring.rightNeighbor
          (L3.EWord.site ring root (n - 1)))).ser := by
    change ((phiW ring z.1.2.1
      (L3.EWord.site ring root (n - 1)))
      (ring.rightNeighbor
        (L3.EWord.site ring root (n - 1)))).ser = _
    rw [phiW_ser_target ring z.1.2.1
      (L3.EWord.site ring root (n - 1)) hne]
    simp [serW, serializerStep, ProjW.lift,
      hx, hy, hrootRunningNeighbor, hforeignB]
  have hrootSer :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1 root).ser =
        (z.1.2.1 root).ser := by
    simpa only [hseam] using hrootSerNeighbor
  have hframe (j : Nat) (hj : j < n)
      (hjzero : j ≠ 0) (hjlast : j ≠ n - 1) :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1
          (L3.EWord.site ring root j)).ser =
        (z.1.2.1 (L3.EWord.site ring root j)).ser := by
    have hneSource :
        L3.EWord.site ring root j ≠
          L3.EWord.site ring root (n - 1) := by
      intro he
      have hi := L3.EWord.validationSiteInjective
        ring root j (n - 1) hj (by omega) he
      exact hjlast hi
    have hneTarget :
        L3.EWord.site ring root j ≠
          ring.rightNeighbor
            (L3.EWord.site ring root (n - 1)) := by
      rw [hseam]
      intro he
      have hi := L3.EWord.validationSiteInjective
        ring root j 0 hj (by omega)
        (he.trans (L3.EWord.siteZero ring root).symm)
      exact hjzero hi
    change ((phiW ring z.1.2.1
      (L3.EWord.site ring root (n - 1)))
      (L3.EWord.site ring root j)).ser = _
    exact phiW_ser_remote ring z.1.2.1
      (L3.EWord.site ring root (n - 1))
      (L3.EWord.site ring root j) hneSource hneTarget
  have hprefix (j : Nat) (hj : j ≤ p + 1) :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1
          (L3.EWord.site ring root j)).ser =
        (z.1.2.1 (L3.EWord.site ring root j)).ser := by
    by_cases hz : j = 0
    · rw [hz, L3.EWord.siteZero]
      exact hrootSer
    · exact hframe j (by omega) hz (by omega)
  have hnextActive :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1 root).ser.cert =
          .RUNNING ∧
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1 root).ser.phase =
          .B ∧
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1 root).ser.wphase =
          .CURRENT := by
    simpa only [hrootSer] using hactive
  have hfnew : BankWordRenewalSoftForwardShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))) p := by
    refine {
      pivotBound := hf.pivotBound
      completed := ?_
      parentPhase := ?_
      parentCurrent := ?_
      front := ?_ }
    · intro j hj
      simpa only [hprefix j (by omega)] using
        hf.completed j hj
    · simpa only [hprefix p (by omega)] using
        hf.parentPhase
    · simpa only [hprefix p (by omega)] using
        hf.parentCurrent
    · simpa only [hprefix p (by omega),
        hprefix (p + 1) (by omega)] using hf.front
  have hidxOld := bankWordRenewalSoftForwardIndex
    ring root z.1 p hf
  have hidxNew := bankWordRenewalSoftForwardIndex
    ring root (bankWordEpochNext ring root z.1
      (L3.EWord.site ring root (n - 1))) p hfnew
  have hparentFrame :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1
          (L3.EWord.site ring root p)).ser =
        (z.1.2.1 (L3.EWord.site ring root p)).ser :=
    hprefix p (by omega)
  have hposEqual :
      bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z.1
          (L3.EWord.site ring root (n - 1))) =
      bankWordRenewalSoftRootedPosition ring root z.1 := by
    simp [bankWordRenewalSoftRootedPosition, hactive,
      hnextActive, hidxOld, hidxNew, hparentFrame]
  have hchosen :
      bankWordRenewalSoftRootedChosen ring root s z =
        L3.EWord.site ring root p := by
    have hpn : p < n := by
      have hh := hf.pivotBound
      omega
    simp [bankWordRenewalSoftRootedChosen, hactive,
      hidxOld, hf.parentPhase, hpn]
  refine ⟨(by intro _; exact Or.inl ⟨p, hfnew⟩),
    hposEqual, hchosen, ?_⟩
  simp [hsourceSer, serCanonicalC]

/-- At the true terminal forward child, S2N consumes LEAF_OK,
    marks its rooted parent DONE, and converts the last follower
    into F/OFF. This is the first return shape; the paid position
    remains n-1. Consumer: the forward-to-return transition of
    the R10a S-frontier. -/
theorem bankWordRenewalSoftLeafAdmissionStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s)
    (hn : 5 ≤ n)
    (hf : BankWordRenewalSoftForwardShape ring root z.1 (n - 2))
    (hrun : (z.1.2.1 root).ser.cert = .RUNNING)
    (hwait :
      (z.1.2.1 (L3.EWord.site ring root (n - 2))).ser.out =
        .WAIT)
    (hchildC :
      (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.phase =
        .C)
    (hchildLeaf :
      (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.probe =
        .LEAF_OK)
    (hchildOff :
      (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.wphase =
        .OFF)
    (hx : (postW
      (z.1.2.1 (L3.EWord.site ring root (n - 2)))
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root (n - 2))))).eX.l = false)
    (hy : (postW
      (z.1.2.1 (L3.EWord.site ring root (n - 2)))
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root (n - 2))))).eY.l = false) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 2))) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 2))) = n - 1 ∧
    bankWordRenewalSoftRootedPosition ring root z.1 = n - 1 ∧
    bankWordRenewalSoftRootedChosen ring root s z =
      L3.EWord.site ring root (n - 2) := by
  have hnsub : n - 2 + 1 = n - 1 := by omega
  have hnn : n - 2 + 2 = n := by omega
  have hpnonzero : n - 2 ≠ 0 := by omega
  have hpn : n - 2 < n := by omega
  have hsourcePhase :
      (z.1.2.1 (L3.EWord.site ring root (n - 2))).ser.phase =
        .B :=
    hf.parentPhase
  have hsourceCurrent :
      (z.1.2.1 (L3.EWord.site ring root (n - 2))).ser.wphase =
        .CURRENT :=
    hf.parentCurrent
  have hchildCNeighbor :
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root (n - 2)))).ser.phase = .C := by
    rw [L3.EWord.siteSuccessor, hnsub]
    exact hchildC
  have hchildLeafNeighbor :
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root (n - 2)))).ser.probe =
          .LEAF_OK := by
    rw [L3.EWord.siteSuccessor, hnsub]
    exact hchildLeaf
  have hne :
      ring.rightNeighbor (L3.EWord.site ring root (n - 2)) ≠
        L3.EWord.site ring root (n - 2) :=
    L3.EWord.rightNeighborDifferent ring (by omega)
      (L3.EWord.site ring root (n - 2))
  have hparentSer :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 2))).2.1
          (L3.EWord.site ring root (n - 2))).ser =
        { (z.1.2.1 (L3.EWord.site ring root (n - 2))).ser with
          out := .DONE } := by
    change ((phiW ring z.1.2.1
      (L3.EWord.site ring root (n - 2)))
      (L3.EWord.site ring root (n - 2))).ser = _
    rw [phiW_ser_source]
    simp [serW, serializerStep, ProjW.lift, serEnterF,
      hx, hy, hsourcePhase, hsourceCurrent, hwait,
      hchildCNeighbor, hchildLeafNeighbor]
  have hchildSer :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 2))).2.1
          (L3.EWord.site ring root (n - 1))).ser =
        { (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser with
          phase := .F, probe := .NONE } := by
    rw [← hnsub, ← L3.EWord.siteSuccessor ring root (n - 2)]
    change ((phiW ring z.1.2.1
      (L3.EWord.site ring root (n - 2)))
      (ring.rightNeighbor
        (L3.EWord.site ring root (n - 2)))).ser = _
    rw [phiW_ser_target ring z.1.2.1
      (L3.EWord.site ring root (n - 2)) hne]
    simp [serW, serializerStep, ProjW.lift, serEnterF,
      hx, hy, hsourcePhase, hsourceCurrent, hwait,
      hchildCNeighbor, hchildLeafNeighbor]
  have hframe (j : Nat) (hj : j < n)
      (hjparent : j ≠ n - 2) (hjchild : j ≠ n - 1) :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 2))).2.1
          (L3.EWord.site ring root j)).ser =
        (z.1.2.1 (L3.EWord.site ring root j)).ser := by
    have hneSource :
        L3.EWord.site ring root j ≠
          L3.EWord.site ring root (n - 2) := by
      intro he
      have hi := L3.EWord.validationSiteInjective
        ring root j (n - 2) hj (by omega) he
      exact hjparent hi
    have hneTarget :
        L3.EWord.site ring root j ≠
          ring.rightNeighbor (L3.EWord.site ring root (n - 2)) := by
      rw [L3.EWord.siteSuccessor, hnsub]
      intro he
      have hi := L3.EWord.validationSiteInjective
        ring root j (n - 1) hj (by omega) he
      exact hjchild hi
    change ((phiW ring z.1.2.1
      (L3.EWord.site ring root (n - 2)))
      (L3.EWord.site ring root j)).ser = _
    exact phiW_ser_remote ring z.1.2.1
      (L3.EWord.site ring root (n - 2))
      (L3.EWord.site ring root j) hneSource hneTarget
  have hrootSer :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 2))).2.1 root).ser =
        (z.1.2.1 root).ser := by
    simpa only [L3.EWord.siteZero] using
      hframe 0 (by omega) (by omega) (by omega)
  have hrootOld := hf.completed 0 (by omega)
  have hrootPhase : (z.1.2.1 root).ser.phase = .B := by
    simpa only [L3.EWord.siteZero] using hrootOld.1
  have hrootDone : (z.1.2.1 root).ser.out = .DONE := by
    simpa only [L3.EWord.siteZero] using hrootOld.2.1
  have hrootCurrent : (z.1.2.1 root).ser.wphase = .CURRENT := by
    simpa only [L3.EWord.siteZero] using hrootOld.2.2
  have hactive :
      (z.1.2.1 root).ser.cert = .RUNNING ∧
      (z.1.2.1 root).ser.phase = .B ∧
      (z.1.2.1 root).ser.wphase = .CURRENT :=
    ⟨hrun, hrootPhase, hrootCurrent⟩
  have hnextRoot :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 2))).2.1 root).ser.cert =
          .RUNNING ∧
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 2))).2.1 root).ser.phase =
          .B ∧
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 2))).2.1 root).ser.out =
          .DONE ∧
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 2))).2.1 root).ser.wphase =
          .CURRENT := by
    simp [hrootSer, hrun, hrootPhase, hrootDone, hrootCurrent]
  have hnextActive :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 2))).2.1 root).ser.cert =
          .RUNNING ∧
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 2))).2.1 root).ser.phase =
          .B ∧
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 2))).2.1 root).ser.wphase =
          .CURRENT :=
    ⟨hnextRoot.1, hnextRoot.2.1, hnextRoot.2.2.2⟩
  have hrnew : BankWordRenewalSoftReturnShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 2))) (n - 2) := by
    refine {
      pivotBound := by omega
      rootRunning := hnextRoot.1
      rootPhase := hnextRoot.2.1
      rootDone := hnextRoot.2.2.1
      rootCurrent := hnextRoot.2.2.2
      completed := ?_
      leftmostPhase := ?_
      leftmostWphase := ?_
      suffix := ?_ }
    · intro j hj
      by_cases heq : j = n - 2
      · rw [heq]
        simp [hparentSer, hf.parentPhase, hf.parentCurrent]
      · have hlt : j < n - 2 := by omega
        rw [hframe j (by omega) heq (by omega)]
        exact hf.completed j hlt
    · rw [hnsub]
      simp [hchildSer]
    · rw [hnsub]
      simp [hnn, hchildSer, hchildOff]
    · intro j hj hjn
      omega
  have hidxOld := bankWordRenewalSoftForwardIndex
    ring root z.1 (n - 2) hf
  have hidxNew := bankWordRenewalSoftReturnIndex
    ring root (bankWordEpochNext ring root z.1
      (L3.EWord.site ring root (n - 2))) (n - 2) hrnew
  have hposOld :
      bankWordRenewalSoftRootedPosition ring root z.1 =
        n - 1 := by
    have heq :
        bankWordRenewalSoftRootedPosition ring root z.1 =
          n - 2 + 1 := by
      simp [bankWordRenewalSoftRootedPosition, hactive,
        hidxOld, hpn, hpnonzero, hf.parentPhase, hwait]
    exact heq.trans hnsub
  have hposNew :
      bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z.1
          (L3.EWord.site ring root (n - 2))) = n - 1 := by
    have hleafBound : n - 2 + 1 < n := by omega
    simp [bankWordRenewalSoftRootedPosition, hnextActive,
      hidxNew, hleafBound, hrnew.leftmostPhase]
  have hchosen :
      bankWordRenewalSoftRootedChosen ring root s z =
        L3.EWord.site ring root (n - 2) := by
    simp [bankWordRenewalSoftRootedChosen, hactive,
      hidxOld, hf.parentPhase, hpn]
  exact ⟨(by intro _; exact Or.inr ⟨n - 2, hrnew⟩),
    hposNew, hposOld, hchosen⟩

theorem bankWordRenewalSoftCoveredDoneFrameStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankWordEpochState n) (hn : 5 ≤ n)
    (hsourceB : (z.2.1 e).ser.phase = .B)
    (hsourceDone : (z.2.1 e).ser.out = .DONE)
    (htargetB : (z.2.1 (ring.rightNeighbor e)).ser.phase = .B)
    (hx : (postW (z.2.1 e)
      (z.2.1 (ring.rightNeighbor e))).eX.l = false)
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
      hx, hy, hsourceB, hsourceDone, htargetB]
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

/-- ROOT_OUT soft S6 from the first returning F resets the root
    to IDLE/CURRENT. The OLD state has paid position n-1 and
    nominates root, whereas the successor has position zero.
    Consumer: terminal-reset exception in the R10a position ledger. -/
theorem bankWordRenewalSoftRootOutgoingFinishStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s)
    (hn : 5 ≤ n)
    (hr : BankWordRenewalSoftReturnShape ring root z.1 0)
    (hx : (postW (z.1.2.1 root)
      (z.1.2.1 (ring.rightNeighbor root))).eX.l = true)
    (hy : (postW (z.1.2.1 root)
      (z.1.2.1 (ring.rightNeighbor root))).eY.l = false) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1 root) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1 root) = 0 ∧
    bankWordRenewalSoftRootedPosition ring root z.1 = n - 1 ∧
    bankWordRenewalSoftRootedChosen ring root s z = root ∧
    ((bankWordEpochNext ring root z.1 root).2.1 root).ser.cert =
      .IDLE := by
  have hchildF :
      (z.1.2.1 (ring.rightNeighbor root)).ser.phase = .F := by
    simpa only [Nat.zero_add, L3.EWord.siteOne] using
      hr.leftmostPhase
  have hsourceSer :
      ((bankWordEpochNext ring root z.1 root).2.1 root).ser =
        { (z.1.2.1 root).ser with
          phase := .C, out := .NEW, cert := .IDLE,
          wphase := .CURRENT } := by
    change ((phiW ring z.1.2.1 root) root).ser = _
    rw [phiW_ser_source]
    simp [serW, serializerStep, ProjW.lift,
      hx, hy, hr.rootRunning, hr.rootPhase,
      hr.rootDone, hr.rootCurrent, hchildF]
  have hidle :
      ((bankWordEpochNext ring root z.1 root).2.1 root).ser.cert =
        .IDLE := by
    simp [hsourceSer]
  have hshapeNew :
      BankWordRenewalSoftShape ring root
        (bankWordEpochNext ring root z.1 root) := by
    intro h
    rw [hidle] at h
    cases h.1
  have hposNew :
      bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z.1 root) = 0 := by
    simp [bankWordRenewalSoftRootedPosition, hidle]
  have hactive :
      (z.1.2.1 root).ser.cert = .RUNNING ∧
      (z.1.2.1 root).ser.phase = .B ∧
      (z.1.2.1 root).ser.wphase = .CURRENT :=
    ⟨hr.rootRunning, hr.rootPhase, hr.rootCurrent⟩
  have hidxOld := bankWordRenewalSoftReturnIndex
    ring root z.1 0 hr
  have hposOld :
      bankWordRenewalSoftRootedPosition ring root z.1 =
        n - 1 := by
    simp [bankWordRenewalSoftRootedPosition, hactive,
      hidxOld, hr.pivotBound, hr.leftmostPhase]
  have hchosen :
      bankWordRenewalSoftRootedChosen ring root s z = root := by
    simp [bankWordRenewalSoftRootedChosen, hactive,
      hidxOld, hr.pivotBound, hr.leftmostPhase]
  exact ⟨hshapeNew, hposNew, hposOld, hchosen, hidle⟩

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open Classical

/-- An INTERNAL B/NEW source challenges any OLD destination phase.
    Its rooted position increases from p to p+1 on the chosen edge,
    independent of foreign CURRENT B/NEW records downstream.
    Consumer: soft S2N first challenge of the rooted frontier. -/
theorem bankWordRenewalSoftForwardChallengeStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s)
    (p : Nat) (hn : 5 ≤ n) (hp : 0 < p)
    (hf : BankWordRenewalSoftForwardShape ring root z.1 p)
    (hrun : (z.1.2.1 root).ser.cert = .RUNNING)
    (hnew :
      (z.1.2.1 (L3.EWord.site ring root p)).ser.out = .NEW)
    (hx : (postW
      (z.1.2.1 (L3.EWord.site ring root p))
      (z.1.2.1 (ring.rightNeighbor (L3.EWord.site ring root p)))).eX.l =
        false)
    (hy : (postW
      (z.1.2.1 (L3.EWord.site ring root p))
      (z.1.2.1 (ring.rightNeighbor (L3.EWord.site ring root p)))).eY.l =
        false) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root p)) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root p)) = p + 1 ∧
    bankWordRenewalSoftRootedPosition ring root z.1 = p ∧
    bankWordRenewalSoftRootedChosen ring root s z =
      L3.EWord.site ring root p := by
  have hpn : p < n := by
    have hh := hf.pivotBound
    omega
  have hpnonzero : p ≠ 0 := Nat.ne_of_gt hp
  have hsourcePhase :
      (z.1.2.1 (L3.EWord.site ring root p)).ser.phase = .B :=
    hf.parentPhase
  have hsourceCurrent :
      (z.1.2.1 (L3.EWord.site ring root p)).ser.wphase = .CURRENT :=
    hf.parentCurrent
  have hne :
      ring.rightNeighbor (L3.EWord.site ring root p) ≠
        L3.EWord.site ring root p :=
    L3.EWord.rightNeighborDifferent ring (by omega)
      (L3.EWord.site ring root p)
  have hparentSer :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root p)).2.1
          (L3.EWord.site ring root p)).ser =
        { (z.1.2.1 (L3.EWord.site ring root p)).ser with
          out := .WAIT } := by
    change ((phiW ring z.1.2.1
      (L3.EWord.site ring root p))
      (L3.EWord.site ring root p)).ser = _
    rw [phiW_ser_source]
    cases hc :
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root p))).ser.phase <;>
      simp [serW, serializerStep, ProjW.lift,
        serChallengeWrite, hx, hy, hsourcePhase,
        hsourceCurrent, hnew, hc]
  have hchildSer :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root p)).2.1
          (L3.EWord.site ring root (p + 1))).ser =
        { (z.1.2.1
          (L3.EWord.site ring root (p + 1))).ser with
          phase := .C, out := .NEW, probe := .PENDING,
          wphase := .CURRENT } := by
    rw [← L3.EWord.siteSuccessor ring root p]
    change ((phiW ring z.1.2.1
      (L3.EWord.site ring root p))
      (ring.rightNeighbor (L3.EWord.site ring root p))).ser = _
    rw [phiW_ser_target ring z.1.2.1
      (L3.EWord.site ring root p) hne]
    cases hc :
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root p))).ser.phase <;>
      simp [serW, serializerStep, ProjW.lift,
        serChallengeWrite, hx, hy, hsourcePhase,
        hsourceCurrent, hnew, hc]
  have hframe (j : Nat) (hj : j < n)
      (hjp : j ≠ p) (hjchild : j ≠ p + 1) :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root p)).2.1
          (L3.EWord.site ring root j)).ser =
        (z.1.2.1 (L3.EWord.site ring root j)).ser := by
    have hneSource :
        L3.EWord.site ring root j ≠
          L3.EWord.site ring root p := by
      intro h
      have hh := L3.EWord.validationSiteInjective
        ring root j p hj (by have := hf.pivotBound; omega) h
      exact hjp hh
    have hneTarget :
        L3.EWord.site ring root j ≠
          ring.rightNeighbor (L3.EWord.site ring root p) := by
      rw [L3.EWord.siteSuccessor]
      intro h
      have hh := L3.EWord.validationSiteInjective
        ring root j (p + 1) hj hf.pivotBound h
      exact hjchild hh
    change ((phiW ring z.1.2.1
      (L3.EWord.site ring root p))
      (L3.EWord.site ring root j)).ser = _
    simp [phiW, projectedEdge, hneSource, hneTarget]
  have hrootSer :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root p)).2.1 root).ser =
        (z.1.2.1 root).ser := by
    simpa only [L3.EWord.siteZero] using
      hframe 0 (by omega) (by omega) (by omega)
  have hrootOld := hf.completed 0 hp
  have hrootPhase : (z.1.2.1 root).ser.phase = .B := by
    simpa only [L3.EWord.siteZero] using hrootOld.1
  have hrootCurrent : (z.1.2.1 root).ser.wphase = .CURRENT := by
    simpa only [L3.EWord.siteZero] using hrootOld.2.2
  have hactive :
      (z.1.2.1 root).ser.cert = .RUNNING ∧
      (z.1.2.1 root).ser.phase = .B ∧
      (z.1.2.1 root).ser.wphase = .CURRENT :=
    ⟨hrun, hrootPhase, hrootCurrent⟩
  have hnextActive :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root p)).2.1 root).ser.cert =
          .RUNNING ∧
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root p)).2.1 root).ser.phase =
          .B ∧
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root p)).2.1 root).ser.wphase =
          .CURRENT := by
    simp [hrootSer, hrun, hrootPhase, hrootCurrent]
  have hfnew : BankWordRenewalSoftForwardShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root p)) p := by
    refine {
      pivotBound := hf.pivotBound
      completed := ?_
      parentPhase := ?_
      parentCurrent := ?_
      front := ?_ }
    · intro j hj
      rw [hframe j (by omega) (by omega) (by omega)]
      exact hf.completed j hj
    · rw [hparentSer]
      exact hf.parentPhase
    · rw [hparentSer]
      exact hf.parentCurrent
    · right
      refine ⟨hp, Or.inr ⟨?_, Or.inl ?_⟩⟩
      · rw [hparentSer]
      · simp [hchildSer]
  have hidxOld := bankWordRenewalSoftForwardIndex
    ring root z.1 p hf
  have hidxNew := bankWordRenewalSoftForwardIndex
    ring root (bankWordEpochNext ring root z.1
      (L3.EWord.site ring root p)) p hfnew
  have hposOld :
      bankWordRenewalSoftRootedPosition ring root z.1 = p := by
    simp [bankWordRenewalSoftRootedPosition, hactive,
      hidxOld, hf.parentPhase, hnew, hpnonzero, hpn, hf.pivotBound]
  have hposNew :
      bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z.1
          (L3.EWord.site ring root p)) = p + 1 := by
    simp [bankWordRenewalSoftRootedPosition, hnextActive,
      hidxNew, hfnew.parentPhase, hparentSer,
      hsourcePhase, hpnonzero, hpn, hf.pivotBound]
  have hchosen :
      bankWordRenewalSoftRootedChosen ring root s z =
        L3.EWord.site ring root p := by
    simp [bankWordRenewalSoftRootedChosen, hactive,
      hidxOld, hf.parentPhase, hpn, hf.pivotBound]
  exact ⟨(by intro _; exact Or.inl ⟨p, hfnew⟩),
    hposNew, hposOld, hchosen⟩

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open Classical

/-- A nonroot B/DONE predecessor of the leftmost returning F
    becomes F/CURRENT on its S2N service. The root-connected
    return pivot retreats by one while its already-paid position
    remains n-1. Consumer: the backward S-frontier S2N row. -/
theorem bankWordRenewalSoftReturnStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s)
    (q : Nat) (hn : 5 ≤ n) (hq : 0 < q)
    (hr : BankWordRenewalSoftReturnShape ring root z.1 q)
    (hx : (postW
      (z.1.2.1 (L3.EWord.site ring root q))
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root q)))).eX.l = false)
    (hy : (postW
      (z.1.2.1 (L3.EWord.site ring root q))
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root q)))).eY.l = false) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root q)) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root q)) =
      bankWordRenewalSoftRootedPosition ring root z.1 ∧
    bankWordRenewalSoftRootedPosition ring root z.1 = n - 1 ∧
    bankWordRenewalSoftRootedChosen ring root s z = root := by
  have hbound : q + 1 < n := hr.pivotBound
  have hqsub : q - 1 + 1 = q := by omega
  have hqnext : q - 1 + 2 = q + 1 := by omega
  have hqNotLast : q + 1 ≠ n := by omega
  have hsourceOld := hr.completed q (by omega)
  have hsourcePhase :
      (z.1.2.1 (L3.EWord.site ring root q)).ser.phase = .B :=
    hsourceOld.1
  have hsourceDone :
      (z.1.2.1 (L3.EWord.site ring root q)).ser.out = .DONE :=
    hsourceOld.2.1
  have hsourceCurrent :
      (z.1.2.1 (L3.EWord.site ring root q)).ser.wphase =
        .CURRENT :=
    hsourceOld.2.2
  have hchildFNeighbor :
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root q))).ser.phase = .F := by
    rw [L3.EWord.siteSuccessor]
    exact hr.leftmostPhase
  have hne :
      ring.rightNeighbor (L3.EWord.site ring root q) ≠
        L3.EWord.site ring root q :=
    L3.EWord.rightNeighborDifferent ring (by omega)
      (L3.EWord.site ring root q)
  have hparentSer :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root q)).2.1
          (L3.EWord.site ring root q)).ser =
        { (z.1.2.1 (L3.EWord.site ring root q)).ser with
          phase := .F, probe := .NONE, wphase := .CURRENT } := by
    change ((phiW ring z.1.2.1
      (L3.EWord.site ring root q))
      (L3.EWord.site ring root q)).ser = _
    rw [phiW_ser_source]
    simp [serW, serializerStep, ProjW.lift, serEnterF,
      hx, hy, hsourcePhase, hsourceDone, hsourceCurrent,
      hchildFNeighbor]
  have hchildSer :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root q)).2.1
          (L3.EWord.site ring root (q + 1))).ser =
        (z.1.2.1 (L3.EWord.site ring root (q + 1))).ser := by
    rw [← L3.EWord.siteSuccessor ring root q]
    change ((phiW ring z.1.2.1
      (L3.EWord.site ring root q))
      (ring.rightNeighbor (L3.EWord.site ring root q))).ser = _
    rw [phiW_ser_target ring z.1.2.1
      (L3.EWord.site ring root q) hne]
    simp [serW, serializerStep, ProjW.lift, serEnterF,
      hx, hy, hsourcePhase, hsourceDone, hsourceCurrent,
      hchildFNeighbor]
  have hframe (j : Nat) (hj : j < n)
      (hjq : j ≠ q) (hjchild : j ≠ q + 1) :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root q)).2.1
          (L3.EWord.site ring root j)).ser =
        (z.1.2.1 (L3.EWord.site ring root j)).ser := by
    have hneSource :
        L3.EWord.site ring root j ≠
          L3.EWord.site ring root q := by
      intro he
      have hi := L3.EWord.validationSiteInjective
        ring root j q hj (by omega) he
      exact hjq hi
    have hneTarget :
        L3.EWord.site ring root j ≠
          ring.rightNeighbor (L3.EWord.site ring root q) := by
      rw [L3.EWord.siteSuccessor]
      intro he
      have hi := L3.EWord.validationSiteInjective
        ring root j (q + 1) hj hr.pivotBound he
      exact hjchild hi
    change ((phiW ring z.1.2.1
      (L3.EWord.site ring root q))
      (L3.EWord.site ring root j)).ser = _
    exact phiW_ser_remote ring z.1.2.1
      (L3.EWord.site ring root q)
      (L3.EWord.site ring root j) hneSource hneTarget
  have hrootSer :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root q)).2.1 root).ser =
        (z.1.2.1 root).ser := by
    have hzeroN : 0 < n := by omega
    have hzeroQ : 0 ≠ q := by omega
    have hzeroNext : 0 ≠ q + 1 := by omega
    simpa only [L3.EWord.siteZero] using
      hframe 0 hzeroN hzeroQ hzeroNext
  have hactive :
      (z.1.2.1 root).ser.cert = .RUNNING ∧
      (z.1.2.1 root).ser.phase = .B ∧
      (z.1.2.1 root).ser.wphase = .CURRENT :=
    ⟨hr.rootRunning, hr.rootPhase, hr.rootCurrent⟩
  have hnextActive :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root q)).2.1 root).ser.cert =
          .RUNNING ∧
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root q)).2.1 root).ser.phase =
          .B ∧
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root q)).2.1 root).ser.wphase =
          .CURRENT := by
    simpa only [hrootSer] using hactive
  have hrnew : BankWordRenewalSoftReturnShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root q)) (q - 1) := by
    refine {
      pivotBound := by omega
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
      have hjn : j < n := by omega
      have hjq : j ≠ q := by omega
      have hjnext : j ≠ q + 1 := by omega
      rw [hframe j hjn hjq hjnext]
      exact hr.completed j (by omega)
    · rw [hqsub]
      simp [hparentSer]
    · rw [hqsub]
      simp [hparentSer, hqnext, hqNotLast]
    · intro j hj hjn
      by_cases heq : j = q + 1
      · rw [heq]
        left
        constructor
        · simpa only [hchildSer] using hr.leftmostPhase
        · simpa only [hchildSer] using hr.leftmostWphase
      · have hjq : j ≠ q := by omega
        have hjframe := hframe j hjn hjq heq
        simpa only [hjframe] using
          hr.suffix j (by omega) hjn
  have hidxOld := bankWordRenewalSoftReturnIndex
    ring root z.1 q hr
  have hidxNew := bankWordRenewalSoftReturnIndex
    ring root (bankWordEpochNext ring root z.1
      (L3.EWord.site ring root q)) (q - 1) hrnew
  have hposOld :
      bankWordRenewalSoftRootedPosition ring root z.1 =
        n - 1 := by
    simp [bankWordRenewalSoftRootedPosition, hactive,
      hidxOld, hr.pivotBound, hr.leftmostPhase]
  have hposNew :
      bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z.1
          (L3.EWord.site ring root q)) = n - 1 := by
    simp [bankWordRenewalSoftRootedPosition, hnextActive,
      hidxNew, hrnew.pivotBound, hrnew.leftmostPhase]
  have hchosen :
      bankWordRenewalSoftRootedChosen ring root s z = root := by
    simp [bankWordRenewalSoftRootedChosen, hactive,
      hidxOld, hr.pivotBound, hr.leftmostPhase]
  exact ⟨(by intro _; exact Or.inr ⟨q - 1, hrnew⟩),
    hposNew.trans hposOld.symm, hposOld, hchosen⟩

/-- At an active last-forward-parent ROOT_IN S5, the C/PENDING
    leaf becomes C/LEAF_OK/OFF; the same root-anchored forward
    pivot and the already charged last position persist.
    Consumer: the R10a terminal soft S-frontier seam. -/
theorem bankWordRenewalSoftRootIncomingLeafStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s)
    (hn : 5 ≤ n)
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
        .PENDING)
    (hx : (postW
      (z.1.2.1 (L3.EWord.site ring root (n - 1)))
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root (n - 1))))).eX.l = false)
    (hy : (postW
      (z.1.2.1 (L3.EWord.site ring root (n - 1)))
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root (n - 1))))).eY.l = true) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))) ∧
    ((bankWordEpochNext ring root z.1
      (L3.EWord.site ring root (n - 1))).2.1
        (L3.EWord.site ring root (n - 1))).ser.probe =
          .LEAF_OK ∧
    ((bankWordEpochNext ring root z.1
      (L3.EWord.site ring root (n - 1))).2.1
        (L3.EWord.site ring root (n - 1))).ser.wphase =
          .OFF ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))) =
      bankWordRenewalSoftRootedPosition ring root z.1 ∧
    bankWordRenewalSoftRootedPosition ring root z.1 =
      n - 1 ∧
    bankWordRenewalSoftRootedChosen ring root s z =
      L3.EWord.site ring root (n - 2) := by
  have hseam :
      ring.rightNeighbor (L3.EWord.site ring root (n - 1)) =
        root :=
    L3.EWord.validationSeamNeighbor ring root
      (L3.EWord.site ring root (n - 1)) rfl
  have hne :
      ring.rightNeighbor (L3.EWord.site ring root (n - 1)) ≠
        L3.EWord.site ring root (n - 1) :=
    L3.EWord.rightNeighborDifferent ring (by omega)
      (L3.EWord.site ring root (n - 1))
  have hnsub : n - 2 + 1 = n - 1 := by omega
  have hnn : n - 2 + 2 = n := by omega
  have hrootRunningNeighbor :
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root (n - 1)))).ser.cert =
          .RUNNING := by
    rw [hseam]
    exact hrun
  have hleafSer :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1
          (L3.EWord.site ring root (n - 1))).ser =
        { (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser with
          probe := .LEAF_OK, wphase := .OFF } := by
    change ((phiW ring z.1.2.1
      (L3.EWord.site ring root (n - 1)))
      (L3.EWord.site ring root (n - 1))).ser = _
    rw [phiW_ser_source]
    simp [serW, serializerStep, ProjW.lift,
      hx, hy, hrootRunningNeighbor,
      hchildC, hchildPending]
  have hleafPhaseNew :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1
          (L3.EWord.site ring root (n - 1))).ser.phase = .C := by
    simp [hleafSer, hchildC]
  have hleafProbeNew :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1
          (L3.EWord.site ring root (n - 1))).ser.probe =
          .LEAF_OK := by
    simp [hleafSer]
  have hleafOffNew :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1
          (L3.EWord.site ring root (n - 1))).ser.wphase =
          .OFF := by
    simp [hleafSer]
  have hrootSerNeighbor :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1
          (ring.rightNeighbor
            (L3.EWord.site ring root (n - 1)))).ser =
        (z.1.2.1 (ring.rightNeighbor
          (L3.EWord.site ring root (n - 1)))).ser := by
    change ((phiW ring z.1.2.1
      (L3.EWord.site ring root (n - 1)))
      (ring.rightNeighbor
        (L3.EWord.site ring root (n - 1)))).ser = _
    rw [phiW_ser_target ring z.1.2.1
      (L3.EWord.site ring root (n - 1)) hne]
    simp [serW, serializerStep, ProjW.lift,
      hx, hy, hrootRunningNeighbor,
      hchildC, hchildPending]
  have hrootSer :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1 root).ser =
          (z.1.2.1 root).ser := by
    simpa only [hseam] using hrootSerNeighbor
  have hframe (j : Nat) (hj : j < n)
      (hjzero : j ≠ 0) (hjlast : j ≠ n - 1) :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1
          (L3.EWord.site ring root j)).ser =
        (z.1.2.1 (L3.EWord.site ring root j)).ser := by
    have hneSource :
        L3.EWord.site ring root j ≠
          L3.EWord.site ring root (n - 1) := by
      intro hh
      have hi := L3.EWord.validationSiteInjective
        ring root j (n - 1) hj (by omega) hh
      exact hjlast hi
    have hneTarget :
        L3.EWord.site ring root j ≠
          ring.rightNeighbor
            (L3.EWord.site ring root (n - 1)) := by
      rw [hseam]
      intro hh
      have hi := L3.EWord.validationSiteInjective
        ring root j 0 hj (by omega)
        (hh.trans (L3.EWord.siteZero ring root).symm)
      exact hjzero hi
    change ((phiW ring z.1.2.1
      (L3.EWord.site ring root (n - 1)))
      (L3.EWord.site ring root j)).ser = _
    exact phiW_ser_remote ring z.1.2.1
      (L3.EWord.site ring root (n - 1))
      (L3.EWord.site ring root j) hneSource hneTarget
  have hrootOld := hf.completed 0 (by omega)
  have hrootPhase : (z.1.2.1 root).ser.phase = .B := by
    simpa only [L3.EWord.siteZero] using hrootOld.1
  have hrootCurrent : (z.1.2.1 root).ser.wphase = .CURRENT := by
    simpa only [L3.EWord.siteZero] using hrootOld.2.2
  have hactive :
      (z.1.2.1 root).ser.cert = .RUNNING ∧
      (z.1.2.1 root).ser.phase = .B ∧
      (z.1.2.1 root).ser.wphase = .CURRENT :=
    ⟨hrun, hrootPhase, hrootCurrent⟩
  have hnextActive :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1 root).ser.cert =
          .RUNNING ∧
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1 root).ser.phase =
          .B ∧
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1 root).ser.wphase =
          .CURRENT := by
    simp [hrootSer, hrun, hrootPhase, hrootCurrent]
  have hparentSer :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1
          (L3.EWord.site ring root (n - 2))).ser =
        (z.1.2.1 (L3.EWord.site ring root (n - 2))).ser :=
    hframe (n - 2) (by omega) (by omega) (by omega)
  have hfnew : BankWordRenewalSoftForwardShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))) (n - 2) := by
    refine {
      pivotBound := hf.pivotBound
      completed := ?_
      parentPhase := ?_
      parentCurrent := ?_
      front := ?_ }
    · intro j hj
      by_cases hjzero : j = 0
      · rw [hjzero, L3.EWord.siteZero]
        have hrootCompleted :
            (z.1.2.1 root).ser.phase = .B ∧
            (z.1.2.1 root).ser.out = .DONE ∧
            (z.1.2.1 root).ser.wphase = .CURRENT := by
          simpa only [L3.EWord.siteZero] using
            hf.completed 0 (by omega)
        simpa only [hrootSer] using hrootCompleted
      · rw [hframe j (by omega) hjzero (by omega)]
        exact hf.completed j hj
    · rw [hparentSer]
      exact hf.parentPhase
    · rw [hparentSer]
      exact hf.parentCurrent
    · right
      refine ⟨by omega, Or.inr ⟨?_, Or.inr (Or.inr ?_)⟩⟩
      · rw [hparentSer]
        exact hwait
      · refine ⟨hnn, ?_, ?_, ?_⟩
        · rw [hnsub]
          exact hleafPhaseNew
        · rw [hnsub]
          exact hleafProbeNew
        · rw [hnsub]
          exact hleafOffNew
  have hidxOld := bankWordRenewalSoftForwardIndex
    ring root z.1 (n - 2) hf
  have hidxNew := bankWordRenewalSoftForwardIndex
    ring root (bankWordEpochNext ring root z.1
      (L3.EWord.site ring root (n - 1))) (n - 2) hfnew
  have hpn : n - 2 < n := by omega
  have hpnonzero : n - 2 ≠ 0 := by omega
  have hposOld :
      bankWordRenewalSoftRootedPosition ring root z.1 =
        n - 1 := by
    have heq :
        bankWordRenewalSoftRootedPosition ring root z.1 =
          n - 2 + 1 := by
      simp [bankWordRenewalSoftRootedPosition, hactive,
        hidxOld, hpn, hpnonzero, hf.parentPhase, hwait]
    exact heq.trans hnsub
  have hposNew :
      bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z.1
          (L3.EWord.site ring root (n - 1))) = n - 1 := by
    have heq :
        bankWordRenewalSoftRootedPosition ring root
          (bankWordEpochNext ring root z.1
            (L3.EWord.site ring root (n - 1))) =
            n - 2 + 1 := by
      simp [bankWordRenewalSoftRootedPosition, hnextActive,
        hidxNew, hpn, hpnonzero, hparentSer,
        hf.parentPhase, hwait]
    exact heq.trans hnsub
  have hchosen :
      bankWordRenewalSoftRootedChosen ring root s z =
        L3.EWord.site ring root (n - 2) := by
    have hpn : n - 2 < n := by omega
    simp [bankWordRenewalSoftRootedChosen, hactive,
      hidxOld, hf.parentPhase, hpn]
  refine ⟨(by intro _; exact Or.inl ⟨n - 2, hfnew⟩),
    ?_, ?_, hposNew.trans hposOld.symm, hposOld, hchosen⟩
  · exact hleafProbeNew
  · exact hleafOffNew

/-- ROOT_IN S5 preserves a rooted returning wave even at its
    terminal F or a C/OFF suffix site. This uses only the literal
    S5 source sanitization and framed RUNNING root; no global
    CURRENT uniqueness is assumed. Consumer: incoming-return
    case of the R10a soft shape induction. -/
theorem bankWordRenewalSoftRootIncomingReturnStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s)
    (q : Nat) (hn : 5 ≤ n)
    (hr : BankWordRenewalSoftReturnShape ring root z.1 q)
    (hx : (postW
      (z.1.2.1 (L3.EWord.site ring root (n - 1)))
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root (n - 1))))).eX.l = false)
    (hy : (postW
      (z.1.2.1 (L3.EWord.site ring root (n - 1)))
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root (n - 1))))).eY.l = true) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))) =
      bankWordRenewalSoftRootedPosition ring root z.1 ∧
    bankWordRenewalSoftRootedChosen ring root s z = root := by
  have hseam :
      ring.rightNeighbor (L3.EWord.site ring root (n - 1)) =
        root :=
    L3.EWord.validationSeamNeighbor ring root
      (L3.EWord.site ring root (n - 1)) rfl
  have hne :
      ring.rightNeighbor (L3.EWord.site ring root (n - 1)) ≠
        L3.EWord.site ring root (n - 1) :=
    L3.EWord.rightNeighborDifferent ring (by omega)
      (L3.EWord.site ring root (n - 1))
  have hqbound : q + 1 < n := hr.pivotBound
  have hlastPlus : n - 1 + 1 = n := by omega
  have hrootRunningNeighbor :
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root (n - 1)))).ser.cert =
          .RUNNING := by
    rw [hseam]
    exact hr.rootRunning
  have hsourceOld :
      ((z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.phase =
          .F ∧
        (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.wphase =
          .OFF) ∨
      ((z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.phase =
          .C ∧
        (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.wphase =
          .OFF) := by
    by_cases hlast : q + 1 = n - 1
    · left
      have hqend : q + 2 = n := by omega
      constructor
      · simpa only [hlast] using hr.leftmostPhase
      · simpa [hlast, hqend] using hr.leftmostWphase
    · have hbefore : q + 1 < n - 1 := by
        have hh := hr.pivotBound
        omega
      have hsuf := hr.suffix (n - 1) hbefore (by omega)
      rcases hsuf with hf | hc
      · exact Or.inl ⟨hf.1, (by simpa [hlastPlus] using hf.2)⟩
      · exact Or.inr hc
  have hsourceFFrame
      (hf :
        (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.phase =
          .F) :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1
          (L3.EWord.site ring root (n - 1))).ser =
        (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser := by
    change ((phiW ring z.1.2.1
      (L3.EWord.site ring root (n - 1)))
      (L3.EWord.site ring root (n - 1))).ser = _
    rw [phiW_ser_source]
    simp [serW, serializerStep, ProjW.lift,
      hx, hy, hrootRunningNeighbor, hf]
  have hsourceNew :
      (((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1
          (L3.EWord.site ring root (n - 1))).ser.phase = .F ∧
       ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1
          (L3.EWord.site ring root (n - 1))).ser.wphase = .OFF) ∨
      (((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1
          (L3.EWord.site ring root (n - 1))).ser.phase = .C ∧
       ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1
          (L3.EWord.site ring root (n - 1))).ser.wphase = .OFF) := by
    rcases hsourceOld with hf | hc
    · left
      simpa only [hsourceFFrame hf.1] using hf
    · right
      constructor
      · change ((phiW ring z.1.2.1
          (L3.EWord.site ring root (n - 1)))
          (L3.EWord.site ring root (n - 1))).ser.phase = .C
        rw [phiW_ser_source]
        simp [serW, serializerStep, ProjW.lift,
          hx, hy, hrootRunningNeighbor, hc.1, hc.2] <;>
          split <;> simp [hc.1, hc.2]
      · change ((phiW ring z.1.2.1
          (L3.EWord.site ring root (n - 1)))
          (L3.EWord.site ring root (n - 1))).ser.wphase = .OFF
        rw [phiW_ser_source]
        simp [serW, serializerStep, ProjW.lift,
          hx, hy, hrootRunningNeighbor, hc.1, hc.2] <;>
          split <;> simp [hc.1, hc.2]
  have hrootSerNeighbor :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1
          (ring.rightNeighbor
            (L3.EWord.site ring root (n - 1)))).ser =
        (z.1.2.1 (ring.rightNeighbor
          (L3.EWord.site ring root (n - 1)))).ser := by
    change ((phiW ring z.1.2.1
      (L3.EWord.site ring root (n - 1)))
      (ring.rightNeighbor
        (L3.EWord.site ring root (n - 1)))).ser = _
    rw [phiW_ser_target ring z.1.2.1
      (L3.EWord.site ring root (n - 1)) hne]
    rcases hsourceOld with hf | hc
    · simp [serW, serializerStep, ProjW.lift,
        hx, hy, hrootRunningNeighbor, hf.1]
    · simp [serW, serializerStep, ProjW.lift,
        hx, hy, hrootRunningNeighbor, hc.1]
  have hrootSer :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1 root).ser =
        (z.1.2.1 root).ser := by
    simpa only [hseam] using hrootSerNeighbor
  have hframe (j : Nat) (hj : j < n)
      (hjzero : j ≠ 0) (hjlast : j ≠ n - 1) :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1
          (L3.EWord.site ring root j)).ser =
        (z.1.2.1 (L3.EWord.site ring root j)).ser := by
    have hneSource :
        L3.EWord.site ring root j ≠
          L3.EWord.site ring root (n - 1) := by
      intro he
      have hi := L3.EWord.validationSiteInjective
        ring root j (n - 1) hj (by omega) he
      exact hjlast hi
    have hneTarget :
        L3.EWord.site ring root j ≠
          ring.rightNeighbor
            (L3.EWord.site ring root (n - 1)) := by
      rw [hseam]
      intro he
      have hi := L3.EWord.validationSiteInjective
        ring root j 0 hj (by omega)
        (he.trans (L3.EWord.siteZero ring root).symm)
      exact hjzero hi
    change ((phiW ring z.1.2.1
      (L3.EWord.site ring root (n - 1)))
      (L3.EWord.site ring root j)).ser = _
    exact phiW_ser_remote ring z.1.2.1
      (L3.EWord.site ring root (n - 1))
      (L3.EWord.site ring root j) hneSource hneTarget
  have hnextActive :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1 root).ser.cert =
          .RUNNING ∧
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1 root).ser.phase =
          .B ∧
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1 root).ser.wphase =
          .CURRENT := by
    simp [hrootSer, hr.rootRunning, hr.rootPhase, hr.rootCurrent]
  have hrnew : BankWordRenewalSoftReturnShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))) q := by
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
      by_cases hjzero : j = 0
      · rw [hjzero, L3.EWord.siteZero]
        have hrootCompleted :
            (z.1.2.1 root).ser.phase = .B ∧
            (z.1.2.1 root).ser.out = .DONE ∧
            (z.1.2.1 root).ser.wphase = .CURRENT :=
          ⟨hr.rootPhase, hr.rootDone, hr.rootCurrent⟩
        simpa only [hrootSer] using hrootCompleted
      · have hjn : j < n := by omega
        have hjlast : j ≠ n - 1 := by omega
        rw [hframe j hjn hjzero hjlast]
        exact hr.completed j hj
    · by_cases hlast : q + 1 = n - 1
      · have hf :
            (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.phase =
              .F := by
          simpa only [hlast] using hr.leftmostPhase
        rw [hlast, hsourceFFrame hf]
        exact hf
      · have hnotZero : q + 1 ≠ 0 := by omega
        rw [hframe (q + 1) hqbound hnotZero hlast]
        exact hr.leftmostPhase
    · by_cases hlast : q + 1 = n - 1
      · have hf :
            (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.phase =
              .F := by
          simpa only [hlast] using hr.leftmostPhase
        have hqend : q + 2 = n := by omega
        have hoff :
            (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.wphase =
              .OFF := by
          simpa [hlast, hqend] using hr.leftmostWphase
        rw [hlast, hsourceFFrame hf]
        simp [hqend, hoff]
      · have hnotZero : q + 1 ≠ 0 := by omega
        rw [hframe (q + 1) hqbound hnotZero hlast]
        exact hr.leftmostWphase
    · intro j hj hjn
      by_cases hlast : j = n - 1
      · rw [hlast]
        simpa [hlastPlus] using hsourceNew
      · have hjzero : j ≠ 0 := by omega
        rw [hframe j hjn hjzero hlast]
        exact hr.suffix j hj hjn
  have hactive :
      (z.1.2.1 root).ser.cert = .RUNNING ∧
      (z.1.2.1 root).ser.phase = .B ∧
      (z.1.2.1 root).ser.wphase = .CURRENT :=
    ⟨hr.rootRunning, hr.rootPhase, hr.rootCurrent⟩
  have hidxOld := bankWordRenewalSoftReturnIndex
    ring root z.1 q hr
  have hidxNew := bankWordRenewalSoftReturnIndex
    ring root (bankWordEpochNext ring root z.1
      (L3.EWord.site ring root (n - 1))) q hrnew
  have hposOld :
      bankWordRenewalSoftRootedPosition ring root z.1 =
        n - 1 := by
    simp [bankWordRenewalSoftRootedPosition, hactive,
      hidxOld, hr.pivotBound, hr.leftmostPhase]
  have hposNew :
      bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z.1
          (L3.EWord.site ring root (n - 1))) = n - 1 := by
    simp [bankWordRenewalSoftRootedPosition, hnextActive,
      hidxNew, hrnew.pivotBound, hrnew.leftmostPhase]
  have hchosen :
      bankWordRenewalSoftRootedChosen ring root s z = root := by
    simp [bankWordRenewalSoftRootedChosen, hactive,
      hidxOld, hr.pivotBound, hr.leftmostPhase]
  exact ⟨(by intro _; exact Or.inr ⟨q, hrnew⟩),
    hposNew.trans hposOld.symm, hchosen⟩

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Every selected physical source has one rooted offset. Consumer:
    the source-index split in the R10a S-frontier all-edge step. -/
theorem bankWordRenewalSoftSourceOffset {n : Nat}
    (ring : DirectedRing n) (root e : Fin n) :
    ∃ k : Nat, k < n ∧ e = L3.EWord.site ring root k := by
  exact ⟨PPL.cyclicOffset ring root e,
    L3.EWord.validationOffsetBound ring root e,
    (L3.EWord.validationOffsetRepresentative ring root e).symm⟩

/-- The ROOT_OUT, ROOT_IN, and INTERNAL physical source
    alternatives are exhaustive and mutually separated by
    rooted offset. Consumer: the primary S-frontier case split. -/
theorem bankWordRenewalSoftEdgeGeometry {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hn : 5 ≤ n) :
    e = root ∨
    (e = L3.EWord.site ring root (n - 1) ∧
      ring.rightNeighbor e = root) ∨
    (∃ k : Nat, 0 < k ∧ k + 1 < n ∧
      e = L3.EWord.site ring root k ∧
      e ≠ root ∧ ring.rightNeighbor e ≠ root) := by
  obtain ⟨k, hk, he⟩ :=
    bankWordRenewalSoftSourceOffset ring root e
  by_cases hz : k = 0
  · left
    calc
      e = L3.EWord.site ring root k := he
      _ = L3.EWord.site ring root 0 := by rw [hz]
      _ = root := L3.EWord.siteZero ring root
  · by_cases hseam : k + 1 = n
    · right
      left
      have hlast : k = n - 1 := by omega
      have heLast : e = L3.EWord.site ring root (n - 1) := by
        simpa only [hlast] using he
      exact ⟨heLast,
        L3.EWord.validationSeamNeighbor ring root e heLast⟩
    · right
      right
      have hpositive : 0 < k := by omega
      have hknext : k + 1 < n := by omega
      have hsourceNonroot : e ≠ root := by
        rw [he]
        exact L3.EWord.validationPositiveSiteNotRoot
          ring root k hk hpositive
      have htargetNonroot : ring.rightNeighbor e ≠ root := by
        rw [he, L3.EWord.siteSuccessor]
        exact L3.EWord.validationPositiveSiteNotRoot
          ring root (k + 1) hknext (by omega)
      exact ⟨k, hpositive, hknext, he,
        hsourceNonroot, htargetNonroot⟩

/-- For a reachable post-S1 state, exactly one physical owner
    flag pair is active. No serializer row is assumed in this
    case split. Consumer: feeding all soft S-frontier row lemmas
    their literal postW flags. -/
theorem bankWordRenewalSoftOwnerFlags {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordRenewalPostSOne ring root s)
    (e : Fin n) :
    (e = root ∧
      (postW (z.1.2.1 e)
        (z.1.2.1 (ring.rightNeighbor e))).eX.l = true ∧
      (postW (z.1.2.1 e)
        (z.1.2.1 (ring.rightNeighbor e))).eY.l = false) ∨
    (e ≠ root ∧ ring.rightNeighbor e = root ∧
      (postW (z.1.2.1 e)
        (z.1.2.1 (ring.rightNeighbor e))).eX.l = false ∧
      (postW (z.1.2.1 e)
        (z.1.2.1 (ring.rightNeighbor e))).eY.l = true) ∨
    (e ≠ root ∧ ring.rightNeighbor e ≠ root ∧
      (postW (z.1.2.1 e)
        (z.1.2.1 (ring.rightNeighbor e))).eX.l = false ∧
      (postW (z.1.2.1 e)
        (z.1.2.1 (ring.rightNeighbor e))).eY.l = false) := by
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z.1 z.2.1
  have hfixed : WFixedRoot ring root (phiW ring z.1.2.1 e) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.1.2.1 hclass e).2
  by_cases he : e = root
  · subst e
    have hpost := clockPostOutgoing ring root z.1.2.1 root
      (by omega : 2 ≤ n) hfixed rfl
    exact Or.inl ⟨rfl, hpost.1, hpost.2⟩
  · by_cases hj : ring.rightNeighbor e = root
    · have hpost := clockPostIncoming ring root z.1.2.1 e
        (by omega : 2 ≤ n) hfixed hj
      exact Or.inr (Or.inl ⟨he, hj, hpost.1, hpost.2⟩)
    · have hpost := clockPostInternal ring root z.1.2.1 e
        (by omega : 2 ≤ n) hfixed he hj
      exact Or.inr (Or.inr ⟨he, hj, hpost.1, hpost.2⟩)

/-- A forward B/DONE source strictly inside the covered rooted
    prefix sees another B (including the pivot) at its successor.
    Both endpoints are nonroot. Consumer: INTERNAL S2N
    B/DONE+B physical frame row. -/
theorem bankWordRenewalSoftForwardCoveredSource {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (p k : Nat)
    (hf : BankWordRenewalSoftForwardShape ring root z p)
    (hkpositive : 0 < k) (hcovered : k + 1 ≤ p) :
    (z.2.1 (L3.EWord.site ring root k)).ser.phase = .B ∧
    (z.2.1 (L3.EWord.site ring root k)).ser.out = .DONE ∧
    (z.2.1 (L3.EWord.site ring root k)).ser.wphase = .CURRENT ∧
    (z.2.1 (ring.rightNeighbor
      (L3.EWord.site ring root k))).ser.phase = .B ∧
    L3.EWord.site ring root k ≠ root ∧
    ring.rightNeighbor (L3.EWord.site ring root k) ≠ root := by
  have hk : k < n := by
    have hb := hf.pivotBound
    omega
  have hknext : k + 1 < n := by
    have hb := hf.pivotBound
    omega
  have hsource := hf.completed k (by omega)
  have htarget :
      (z.2.1 (L3.EWord.site ring root (k + 1))).ser.phase =
        .B := by
    by_cases hlast : k + 1 = p
    · rw [hlast]
      exact hf.parentPhase
    · exact (hf.completed (k + 1) (by omega)).1
  have hsourceNe :=
    L3.EWord.validationPositiveSiteNotRoot
      ring root k hk hkpositive
  have htargetNe :=
    L3.EWord.validationPositiveSiteNotRoot
      ring root (k + 1) hknext (by omega)
  refine ⟨hsource.1, hsource.2.1, hsource.2.2, ?_,
    hsourceNe, ?_⟩
  · rw [L3.EWord.siteSuccessor]
    exact htarget
  · rw [L3.EWord.siteSuccessor]
    exact htargetNe

/-- The covered part of a returning soft lap is likewise a
    contiguous B/DONE prefix; no arbitrary CURRENT site enters
    this claim. Consumer: INTERNAL return-prefix S2N frame. -/
theorem bankWordRenewalSoftReturnCoveredSource {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n) (q k : Nat)
    (hr : BankWordRenewalSoftReturnShape ring root z q)
    (hkpositive : 0 < k) (hcovered : k + 1 ≤ q) :
    (z.2.1 (L3.EWord.site ring root k)).ser.phase = .B ∧
    (z.2.1 (L3.EWord.site ring root k)).ser.out = .DONE ∧
    (z.2.1 (ring.rightNeighbor
      (L3.EWord.site ring root k))).ser.phase = .B ∧
    L3.EWord.site ring root k ≠ root ∧
    ring.rightNeighbor (L3.EWord.site ring root k) ≠ root := by
  have hk : k < n := by
    have hb := hr.pivotBound
    omega
  have hknext : k + 1 < n := by
    have hb := hr.pivotBound
    omega
  have hsource := hr.completed k (by omega)
  have htarget := hr.completed (k + 1) (by omega)
  have hsourceNe :=
    L3.EWord.validationPositiveSiteNotRoot
      ring root k hk hkpositive
  have htargetNe :=
    L3.EWord.validationPositiveSiteNotRoot
      ring root (k + 1) hknext (by omega)
  refine ⟨hsource.1, hsource.2.1, ?_, hsourceNe, ?_⟩
  · rw [L3.EWord.siteSuccessor]
    exact htarget.1
  · rw [L3.EWord.siteSuccessor]
    exact htargetNe

theorem bankWordRenewalSoftIncomingRowCensus {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordRenewalPostSOne ring root s)
    (hpred : ring.rightNeighbor e = root) :
    ((z.1.2.1 root).ser.cert = .IDLE ∧
      (bankWordEpochSelectedReceipt ring z.1 e).serializer.row =
        "S0") ∨
    ((z.1.2.1 root).ser.cert ≠ .IDLE ∧
      (bankWordEpochSelectedReceipt ring z.1 e).serializer.row =
        "S5") := by
  have hclass := bankWordEpochReachablePhysicalRootClass
    ring hn hbank root s hs z.1 z.2.1
  have hfixed : WFixedRoot ring root (phiW ring z.1.2.1 e) :=
    ((bankWordSerializerRootClassClosed ring hn hbank root).2
      z.1.2.1 hclass e).2
  have hpost := clockPostIncoming ring root z.1.2.1 e
    (by omega : 2 ≤ n) hfixed hpred
  by_cases hidle : (z.1.2.1 root).ser.cert = .IDLE
  · left
    constructor
    · exact hidle
    · have hcert :
          (z.1.2.1 (ring.rightNeighbor e)).ser.cert =
            .IDLE := by
        simpa only [hpred] using hidle
      change (serW (z.1.2.1 e)
        (z.1.2.1 (ring.rightNeighbor e))).row = "S0"
      simp [serW, serializerStep, ProjW.lift,
        hpost.1, hpost.2, hcert]
  · right
    constructor
    · exact hidle
    · have hcert :
          (z.1.2.1 (ring.rightNeighbor e)).ser.cert ≠
            .IDLE := by
        simpa only [hpred] using hidle
      change (serW (z.1.2.1 e)
        (z.1.2.1 (ring.rightNeighbor e))).row = "S5"
      simp [serW, serializerStep, ProjW.lift,
        hpost.1, hpost.2, hcert]

/-- In the forward soft wave, the old-state nominated source
    is the first rooted B pivot, not an inherited foreign B/NEW.
    Consumer: positive-position charge in the S-frontier. -/
theorem bankWordRenewalSoftForwardNomination {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s)
    (p : Nat)
    (hf : BankWordRenewalSoftForwardShape ring root z.1 p)
    (hactive :
      (z.1.2.1 root).ser.cert = .RUNNING ∧
      (z.1.2.1 root).ser.phase = .B ∧
      (z.1.2.1 root).ser.wphase = .CURRENT) :
    bankWordRenewalSoftRootedChosen ring root s z =
      L3.EWord.site ring root p := by
  have hp : p < n := by
    have hb := hf.pivotBound
    omega
  have hidx := bankWordRenewalSoftForwardIndex
    ring root z.1 p hf
  simp [bankWordRenewalSoftRootedChosen, hactive,
    hidx, hf.parentPhase, hp]

/-- During a returning soft wave the nomination is the
    fallback root, independently of the leftmost F offset.
    Consumer: the zero-charge backward S2N cases. -/
theorem bankWordRenewalSoftReturnNomination {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s)
    (q : Nat)
    (hr : BankWordRenewalSoftReturnShape ring root z.1 q) :
    bankWordRenewalSoftRootedChosen ring root s z = root := by
  have hactive :
      (z.1.2.1 root).ser.cert = .RUNNING ∧
      (z.1.2.1 root).ser.phase = .B ∧
      (z.1.2.1 root).ser.wphase = .CURRENT :=
    ⟨hr.rootRunning, hr.rootPhase, hr.rootCurrent⟩
  have hidx := bankWordRenewalSoftReturnIndex
    ring root z.1 q hr
  simp [bankWordRenewalSoftRootedChosen, hactive,
    hidx, hr.pivotBound, hr.leftmostPhase]

theorem bankWordRenewalSoftInternalFlags {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordRenewalPostSOne ring root s)
    (he : e ≠ root) (hj : ring.rightNeighbor e ≠ root) :
    (postW (z.1.2.1 e)
      (z.1.2.1 (ring.rightNeighbor e))).eX.l = false ∧
    (postW (z.1.2.1 e)
      (z.1.2.1 (ring.rightNeighbor e))).eY.l = false := by
  rcases bankWordRenewalSoftOwnerFlags
      ring root s hn hbank hs z e with ho | hi | ht
  · exact False.elim (he ho.1)
  · exact False.elim (hj hi.2.1)
  · exact ⟨ht.2.2.1, ht.2.2.2⟩

/-- The actual ROOT_IN native flags, not a paper annotation.
    Consumer: S0/S5 soft-frontier seam rows. -/
theorem bankWordRenewalSoftIncomingFlags {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordRenewalPostSOne ring root s)
    (he : e ≠ root) (hpred : ring.rightNeighbor e = root) :
    (postW (z.1.2.1 e)
      (z.1.2.1 (ring.rightNeighbor e))).eX.l = false ∧
    (postW (z.1.2.1 e)
      (z.1.2.1 (ring.rightNeighbor e))).eY.l = true := by
  rcases bankWordRenewalSoftOwnerFlags
      ring root s hn hbank hs z e with ho | hi | ht
  · exact False.elim (he ho.1)
  · exact ⟨hi.2.2.1, hi.2.2.2⟩
  · exact False.elim (ht.2.1 hpred)

/-- Native ROOT_OUT service flags at the selected root.
    Consumer: S1/SR/S2R/S6 soft-frontier case routing. -/
theorem bankWordRenewalSoftOutgoingFlags {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordRenewalPostSOne ring root s) :
    (postW (z.1.2.1 root)
      (z.1.2.1 (ring.rightNeighbor root))).eX.l = true ∧
    (postW (z.1.2.1 root)
      (z.1.2.1 (ring.rightNeighbor root))).eY.l = false := by
  rcases bankWordRenewalSoftOwnerFlags
      ring root s hn hbank hs z root with ho | hi | ht
  · exact ⟨ho.2.1, ho.2.2⟩
  · exact False.elim (hi.1 rfl)
  · exact False.elim (ht.1 rfl)

/-- Every covered forward INTERNAL B/DONE+B service is a true
    serializer frame, and it cannot be the nominated positive-
    increment edge. Consumer: covered-prefix branch of the
    R10a one-edge position/nomination theorem. -/
theorem bankWordRenewalSoftForwardCoveredStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordRenewalPostSOne ring root s)
    (p k : Nat)
    (hf : BankWordRenewalSoftForwardShape ring root z.1 p)
    (hactive :
      (z.1.2.1 root).ser.cert = .RUNNING ∧
      (z.1.2.1 root).ser.phase = .B ∧
      (z.1.2.1 root).ser.wphase = .CURRENT)
    (hshape : BankWordRenewalSoftShape ring root z.1)
    (hkpositive : 0 < k) (hcovered : k + 1 ≤ p) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root k)) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root k)) =
      bankWordRenewalSoftRootedPosition ring root z.1 ∧
    L3.EWord.site ring root k ≠
      bankWordRenewalSoftRootedChosen ring root s z := by
  obtain ⟨hb, hd, _, hchildB, he, hj⟩ :=
    bankWordRenewalSoftForwardCoveredSource
      ring root z.1 p k hf hkpositive hcovered
  have hflags := bankWordRenewalSoftInternalFlags
    ring root (L3.EWord.site ring root k)
    s hn hbank hs z he hj
  have hframe := bankWordRenewalSoftCoveredDoneFrameStep
    ring root (L3.EWord.site ring root k)
    z.1 hn hb hd hchildB hflags.1 hflags.2 hshape
  have hchosen := bankWordRenewalSoftForwardNomination
    ring root s z p hf hactive
  have hneq :
      L3.EWord.site ring root k ≠
        L3.EWord.site ring root p := by
    intro h
    have hk : k < n := by
      have hp := hf.pivotBound
      omega
    have hp : p < n := by
      have hpivot := hf.pivotBound
      omega
    have heq := L3.EWord.validationSiteInjective
      ring root k p hk hp h
    omega
  refine ⟨hframe.1, hframe.2, ?_⟩
  rw [hchosen]
  exact hneq

/-- The return prefix is also a true B/DONE+B internal frame
    and its source differs from the fallback-root nomination.
    Consumer: RETURN covered-prefix all-edge case. -/
theorem bankWordRenewalSoftReturnCoveredStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordRenewalPostSOne ring root s)
    (q k : Nat)
    (hr : BankWordRenewalSoftReturnShape ring root z.1 q)
    (hshape : BankWordRenewalSoftShape ring root z.1)
    (hkpositive : 0 < k) (hcovered : k + 1 ≤ q) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root k)) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root k)) =
      bankWordRenewalSoftRootedPosition ring root z.1 ∧
    L3.EWord.site ring root k ≠
      bankWordRenewalSoftRootedChosen ring root s z := by
  obtain ⟨hb, hd, hchildB, he, hj⟩ :=
    bankWordRenewalSoftReturnCoveredSource
      ring root z.1 q k hr hkpositive hcovered
  have hflags := bankWordRenewalSoftInternalFlags
    ring root (L3.EWord.site ring root k)
    s hn hbank hs z he hj
  have hframe := bankWordRenewalSoftCoveredDoneFrameStep
    ring root (L3.EWord.site ring root k)
    z.1 hn hb hd hchildB hflags.1 hflags.2 hshape
  have hchosen := bankWordRenewalSoftReturnNomination
    ring root s z q hr
  refine ⟨hframe.1, hframe.2, ?_⟩
  rw [hchosen]
  exact he

theorem bankWordRenewalSoftReturnEdgeCases {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankWordEpochState n)
    (q : Nat) (hn : 5 ≤ n)
    (hr : BankWordRenewalSoftReturnShape ring root z q) :
    e = root ∨
    (e = L3.EWord.site ring root (n - 1) ∧
      ring.rightNeighbor e = root) ∨
    (∃ k : Nat, 0 < k ∧ k + 1 < n ∧
      e = L3.EWord.site ring root k ∧
      ((k + 1 ≤ q ∧
         (z.2.1 (L3.EWord.site ring root k)).ser.phase = .B ∧
         (z.2.1 (L3.EWord.site ring root k)).ser.out = .DONE ∧
         (z.2.1 (ring.rightNeighbor
           (L3.EWord.site ring root k))).ser.phase = .B) ∨
       (k = q ∧
         (z.2.1 (L3.EWord.site ring root k)).ser.phase = .B ∧
         (z.2.1 (L3.EWord.site ring root k)).ser.out = .DONE ∧
         (z.2.1 (ring.rightNeighbor
           (L3.EWord.site ring root k))).ser.phase = .F) ∨
       (q < k ∧
         (((z.2.1 (L3.EWord.site ring root k)).ser.phase = .F ∧
           (z.2.1 (L3.EWord.site ring root k)).ser.wphase =
             (if k + 1 = n then .OFF else .CURRENT)) ∨
          ((z.2.1 (L3.EWord.site ring root k)).ser.phase = .C ∧
           (z.2.1 (L3.EWord.site ring root k)).ser.wphase =
             .OFF))))) := by
  rcases bankWordRenewalSoftEdgeGeometry ring root e hn with
    hroot | hseam | hinter
  · exact Or.inl hroot
  · exact Or.inr (Or.inl hseam)
  · rcases hinter with ⟨k, hkpositive, hknext, he, _, _⟩
    right
    right
    refine ⟨k, hkpositive, hknext, he, ?_⟩
    by_cases hcovered : k + 1 ≤ q
    · left
      obtain ⟨hb, hd, hc, _, _⟩ :=
        bankWordRenewalSoftReturnCoveredSource
          ring root z q k hr hkpositive hcovered
      exact ⟨hcovered, hb, hd, hc⟩
    · right
      by_cases hpivot : k = q
      · left
        have hsource := hr.completed q (by omega)
        have htarget :
            (z.2.1 (ring.rightNeighbor
              (L3.EWord.site ring root k))).ser.phase =
              .F := by
          rw [hpivot, L3.EWord.siteSuccessor]
          exact hr.leftmostPhase
        refine ⟨hpivot, ?_, ?_, htarget⟩
        · simpa only [hpivot] using hsource.1
        · simpa only [hpivot] using hsource.2.1
      · right
        have hafter : q < k := by omega
        refine ⟨hafter, ?_⟩
        by_cases hfirst : k = q + 1
        · left
          constructor
          · rw [hfirst]
            exact hr.leftmostPhase
          · rw [hfirst]
            exact hr.leftmostWphase
        · exact hr.suffix k (by omega) (by omega)

theorem bankWordRenewalSoftShapeWordFromSeed {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (hstep : ∀ (z : BankWordRenewalPostSOne ring root s)
      (e : Fin n), BankWordRenewalSoftShape ring root z.1 →
      BankWordRenewalSoftShape ring root
        (bankWordEpochNext ring root z.1 e))
    (seed : BankWordRenewalFreshSeed ring root s)
    (word : List (Fin n)) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochRun ring root seed.1.1 word) := by
  have hrun :
      ∀ (w : List (Fin n))
        (z : BankWordRenewalPostSOne ring root s),
        BankWordRenewalSoftShape ring root z.1 →
        BankWordRenewalSoftShape ring root
          (bankWordEpochRun ring root z.1 w) := by
    intro w
    induction w with
    | nil =>
        intro z hz
        exact hz
    | cons e tail ih =>
        intro z hz
        change BankWordRenewalSoftShape ring root
          (bankWordEpochRun ring root
            (bankWordEpochNext ring root z.1 e) tail)
        exact ih (bankWordRenewalNext ring root s z e)
          (hstep z e hz)
  exact hrun word seed.1
    (bankWordRenewalSoftShapeSeed
      ring root s hn hbank hs seed).1

/-- All remote INTERNAL interactions preserve an inactive root
    and hence the conditional rooted soft shape. This rules out
    spontaneous creation of A(z) away from the root.
    Consumer: inactive INTERNAL branch of R10a S-frontier. -/
theorem bankWordRenewalSoftInactiveInternalStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankWordEpochState n)
    (he : e ≠ root) (hj : ring.rightNeighbor e ≠ root)
    (hinactive :
      ¬ ((z.2.1 root).ser.cert = .RUNNING ∧
        (z.2.1 root).ser.phase = .B ∧
        (z.2.1 root).ser.wphase = .CURRENT)) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z e) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z e) =
      bankWordRenewalSoftRootedPosition ring root z := by
  have hroot := bankWordHardEpochRootRemoteFrame
    ring root z e he.symm hj.symm
  have hnextInactive :
      ¬ (((bankWordEpochNext ring root z e).2.1 root).ser.cert =
          .RUNNING ∧
        ((bankWordEpochNext ring root z e).2.1 root).ser.phase =
          .B ∧
        ((bankWordEpochNext ring root z e).2.1 root).ser.wphase =
          .CURRENT) := by
    intro h
    exact hinactive (by simpa only [hroot] using h)
  have hposOld :
      bankWordRenewalSoftRootedPosition ring root z = 0 := by
    simp [bankWordRenewalSoftRootedPosition, hinactive]
  have hposNew :
      bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z e) = 0 := by
    simp [bankWordRenewalSoftRootedPosition, hnextInactive]
  exact ⟨(by intro h; exact False.elim (hnextInactive h)),
    hposNew.trans hposOld.symm⟩

/-- An actual positive return pivot is an INTERNAL S2N
    B/DONE-to-F transition. It preserves the paid position,
    so any nonzero-position-change implication is vacuous.
    Consumer: returning-parent branch of R10a S-frontier. -/
theorem bankWordRenewalSoftReturnParentStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordRenewalPostSOne ring root s)
    (q : Nat) (hq : 0 < q)
    (hr : BankWordRenewalSoftReturnShape ring root z.1 q) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root q)) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root q)) ≤
      bankWordRenewalSoftRootedPosition ring root z.1 + 1 ∧
    (bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z.1
          (L3.EWord.site ring root q)) ≠
      bankWordRenewalSoftRootedPosition ring root z.1 →
      L3.EWord.site ring root q =
        bankWordRenewalSoftRootedChosen ring root s z) := by
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
  have hflags := bankWordRenewalSoftInternalFlags
    ring root (L3.EWord.site ring root q)
    s hn hbank hs z hsourceNonroot htargetNonroot
  have hstep := bankWordRenewalSoftReturnStep
    ring root s z q hn hq hr hflags.1 hflags.2
  refine ⟨hstep.1, ?_, ?_⟩
  · rw [hstep.2.1]
    omega
  · intro hne
    exact False.elim (hne hstep.2.1)

theorem bankWordRenewalSoftRootFirstStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordRenewalPostSOne ring root s)
    (hf : BankWordRenewalSoftForwardShape ring root z.1 0)
    (hrun : (z.1.2.1 root).ser.cert = .RUNNING) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1 root) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1 root) ≤
      bankWordRenewalSoftRootedPosition ring root z.1 + 1 ∧
    (bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z.1 root) ≠
      bankWordRenewalSoftRootedPosition ring root z.1 →
      root = bankWordRenewalSoftRootedChosen ring root s z) := by
  have hflags := bankWordRenewalSoftOutgoingFlags
    ring root s hn hbank hs z
  have hstep := bankWordRenewalSoftFirstAdmission
    ring root s z hn hf hrun hflags.1 hflags.2
  have hbound :
      bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z.1 root) ≤
      bankWordRenewalSoftRootedPosition ring root z.1 + 1 := by
    rcases hstep.2.1 with hpending | hinternal
    · rw [hpending.2, hstep.2.2.1]
      omega
    · rw [hinternal.2, hstep.2.2.1]
      omega
  exact ⟨hstep.1, hbound,
    (by intro _; exact hstep.2.2.2.symm)⟩

/-- An actual soft ROOT_OUT S6 from the last return pivot
    resets position to zero and closes the active root.
    The only decreasing position service is itself nominated
    by the fallback root. Consumer: R10a lap-end boundary. -/
theorem bankWordRenewalSoftRootFinishStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordRenewalPostSOne ring root s)
    (hr : BankWordRenewalSoftReturnShape ring root z.1 0) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1 root) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1 root) ≤
      bankWordRenewalSoftRootedPosition ring root z.1 + 1 ∧
    (bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z.1 root) ≠
      bankWordRenewalSoftRootedPosition ring root z.1 →
      root = bankWordRenewalSoftRootedChosen ring root s z) := by
  have hflags := bankWordRenewalSoftOutgoingFlags
    ring root s hn hbank hs z
  have hstep := bankWordRenewalSoftRootOutgoingFinishStep
    ring root s z hn hr hflags.1 hflags.2
  refine ⟨hstep.1, ?_, ?_⟩
  · rw [hstep.2.1, hstep.2.2.1]
    omega
  · intro _
    exact hstep.2.2.2.1.symm

/-- Native ROOT_OUT requested starts or C/F recoveries
    cannot debit a new frontier position. Consumer: the
    nonactive ROOT_OUT S1 and SR branch of R10a. -/
theorem bankWordRenewalSoftRootEntryStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordRenewalPostSOne ring root s)
    (hcase :
      ((z.1.2.1 root).ser.cert = .REQUESTED ∧
        0 < (z.1.2.1 root).siLease.val) ∨
      ((z.1.2.1 root).ser.cert = .REQUESTED ∧
        (z.1.2.1 root).siLease.val = 0) ∨
      (((z.1.2.1 root).ser.cert = .IDLE ∨
        (z.1.2.1 root).ser.cert = .RUNNING) ∧
       ((z.1.2.1 root).ser.phase = .C ∨
        (z.1.2.1 root).ser.phase = .F))) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1 root) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1 root) =
      bankWordRenewalSoftRootedPosition ring root z.1 := by
  have hflags := bankWordRenewalSoftOutgoingFlags
    ring root s hn hbank hs z
  have hstep := bankWordRenewalSoftRootEntryAndRecovery
    ring root z.1 (by omega : 3 ≤ n)
    hflags.1 hflags.2 hcase
  exact ⟨hstep.1, hstep.2.2⟩

theorem bankWordRenewalSoftInactiveIncomingStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankWordSerializerRootClass ring hbank root s)
    (z : BankWordRenewalPostSOne ring root s)
    (he : e ≠ root) (hpred : ring.rightNeighbor e = root)
    (hnotIdle : (z.1.2.1 root).ser.cert ≠ .IDLE)
    (hinactive :
      ¬ ((z.1.2.1 root).ser.cert = .RUNNING ∧
        (z.1.2.1 root).ser.phase = .B ∧
        (z.1.2.1 root).ser.wphase = .CURRENT)) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1 e) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1 e) =
      bankWordRenewalSoftRootedPosition ring root z.1 := by
  have hflags := bankWordRenewalSoftIncomingFlags
    ring root e s hn hbank hs z he hpred
  have hne : ring.rightNeighbor e ≠ e :=
    L3.EWord.rightNeighborDifferent ring (by omega) e
  have hcert :
      (z.1.2.1 (ring.rightNeighbor e)).ser.cert ≠ .IDLE := by
    simpa only [hpred] using hnotIdle
  have hrootSerNeighbor :
      ((bankWordEpochNext ring root z.1 e).2.1
        (ring.rightNeighbor e)).ser =
      (z.1.2.1 (ring.rightNeighbor e)).ser := by
    change ((phiW ring z.1.2.1 e)
      (ring.rightNeighbor e)).ser = _
    rw [phiW_ser_target ring z.1.2.1 e hne]
    simp [serW, serializerStep, ProjW.lift,
      hflags.1, hflags.2, hcert]
  have hrootSer :
      ((bankWordEpochNext ring root z.1 e).2.1 root).ser =
        (z.1.2.1 root).ser := by
    simpa only [hpred] using hrootSerNeighbor
  have hnextInactive :
      ¬ (((bankWordEpochNext ring root z.1 e).2.1 root).ser.cert =
          .RUNNING ∧
        ((bankWordEpochNext ring root z.1 e).2.1 root).ser.phase =
          .B ∧
        ((bankWordEpochNext ring root z.1 e).2.1 root).ser.wphase =
          .CURRENT) := by
    intro h
    exact hinactive (by simpa only [hrootSer] using h)
  have hposOld :
      bankWordRenewalSoftRootedPosition ring root z.1 = 0 := by
    simp [bankWordRenewalSoftRootedPosition, hinactive]
  have hposNew :
      bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z.1 e) = 0 := by
    simp [bankWordRenewalSoftRootedPosition, hnextInactive]
  exact ⟨(by intro h; exact False.elim (hnextInactive h)),
    hposNew.trans hposOld.symm⟩

end L3.RenewalReferenceClock

namespace L3.RenewalReferenceClock







theorem bankWordRenewalSoftForwardSeamOutsideFront {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s)
    (p : Nat) (hn : 5 ≤ n)
    (hf : BankWordRenewalSoftForwardShape ring root z.1 p)
    (hactive :
      (z.1.2.1 root).ser.cert = .RUNNING ∧
      (z.1.2.1 root).ser.phase = .B ∧
      (z.1.2.1 root).ser.wphase = .CURRENT)
    (hbeforeLeaf : p + 2 < n)
    (hx : (postW
      (z.1.2.1 (L3.EWord.site ring root (n - 1)))
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root (n - 1))))).eX.l = false)
    (hy : (postW
      (z.1.2.1 (L3.EWord.site ring root (n - 1)))
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root (n - 1))))).eY.l = true) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))) =
      bankWordRenewalSoftRootedPosition ring root z.1 ∧
    bankWordRenewalSoftRootedChosen ring root s z =
      L3.EWord.site ring root p := by
  have hseam :
      ring.rightNeighbor (L3.EWord.site ring root (n - 1)) =
        root :=
    L3.EWord.validationSeamNeighbor ring root
      (L3.EWord.site ring root (n - 1)) rfl
  have hne :
      ring.rightNeighbor (L3.EWord.site ring root (n - 1)) ≠
        L3.EWord.site ring root (n - 1) :=
    L3.EWord.rightNeighborDifferent ring (by omega)
      (L3.EWord.site ring root (n - 1))
  have hrootRunningNeighbor :
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root (n - 1)))).ser.cert =
          .RUNNING := by
    rw [hseam]
    exact hactive.1
  have hrootSerNeighbor :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1
          (ring.rightNeighbor
            (L3.EWord.site ring root (n - 1)))).ser =
        (z.1.2.1 (ring.rightNeighbor
          (L3.EWord.site ring root (n - 1)))).ser := by
    change ((phiW ring z.1.2.1
      (L3.EWord.site ring root (n - 1)))
      (ring.rightNeighbor
        (L3.EWord.site ring root (n - 1)))).ser = _
    rw [phiW_ser_target ring z.1.2.1
      (L3.EWord.site ring root (n - 1)) hne]
    cases hphase :
      (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.phase <;>
      simp [serW, serializerStep, ProjW.lift,
        hx, hy, hrootRunningNeighbor, hphase]
  have hrootSer :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1 root).ser =
        (z.1.2.1 root).ser := by
    simpa only [hseam] using hrootSerNeighbor
  have hframe (j : Nat) (hj : j < n)
      (hjzero : j ≠ 0) (hjlast : j ≠ n - 1) :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1
          (L3.EWord.site ring root j)).ser =
        (z.1.2.1 (L3.EWord.site ring root j)).ser := by
    have hneSource :
        L3.EWord.site ring root j ≠
          L3.EWord.site ring root (n - 1) := by
      intro he
      have hi := L3.EWord.validationSiteInjective
        ring root j (n - 1) hj (by omega) he
      exact hjlast hi
    have hneTarget :
        L3.EWord.site ring root j ≠
          ring.rightNeighbor
            (L3.EWord.site ring root (n - 1)) := by
      rw [hseam]
      intro he
      have hi := L3.EWord.validationSiteInjective
        ring root j 0 hj (by omega)
        (he.trans (L3.EWord.siteZero ring root).symm)
      exact hjzero hi
    change ((phiW ring z.1.2.1
      (L3.EWord.site ring root (n - 1)))
      (L3.EWord.site ring root j)).ser = _
    exact phiW_ser_remote ring z.1.2.1
      (L3.EWord.site ring root (n - 1))
      (L3.EWord.site ring root j) hneSource hneTarget
  have hprefix (j : Nat) (hj : j ≤ p + 1) :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1
          (L3.EWord.site ring root j)).ser =
        (z.1.2.1 (L3.EWord.site ring root j)).ser := by
    by_cases hz : j = 0
    · rw [hz, L3.EWord.siteZero]
      exact hrootSer
    · exact hframe j (by omega) hz (by omega)
  have hnextActive :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1 root).ser.cert =
          .RUNNING ∧
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1 root).ser.phase =
          .B ∧
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1 root).ser.wphase =
          .CURRENT := by
    simpa only [hrootSer] using hactive
  have hfnew : BankWordRenewalSoftForwardShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))) p := by
    refine {
      pivotBound := hf.pivotBound
      completed := ?_
      parentPhase := ?_
      parentCurrent := ?_
      front := ?_ }
    · intro j hj
      simpa only [hprefix j (by omega)] using
        hf.completed j hj
    · simpa only [hprefix p (by omega)] using
        hf.parentPhase
    · simpa only [hprefix p (by omega)] using
        hf.parentCurrent
    · simpa only [hprefix p (by omega),
        hprefix (p + 1) (by omega)] using hf.front
  have hidxOld := bankWordRenewalSoftForwardIndex
    ring root z.1 p hf
  have hidxNew := bankWordRenewalSoftForwardIndex
    ring root (bankWordEpochNext ring root z.1
      (L3.EWord.site ring root (n - 1))) p hfnew
  have hparentFrame :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1
          (L3.EWord.site ring root p)).ser =
        (z.1.2.1 (L3.EWord.site ring root p)).ser :=
    hprefix p (by omega)
  have hposEqual :
      bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z.1
          (L3.EWord.site ring root (n - 1))) =
      bankWordRenewalSoftRootedPosition ring root z.1 := by
    simp [bankWordRenewalSoftRootedPosition, hactive,
      hnextActive, hidxOld, hidxNew, hparentFrame]
  have hchosen :
      bankWordRenewalSoftRootedChosen ring root s z =
        L3.EWord.site ring root p := by
    have hpn : p < n := by
      have hh := hf.pivotBound
      omega
    simp [bankWordRenewalSoftRootedChosen, hactive,
      hidxOld, hf.parentPhase, hpn]
  exact ⟨(by intro _; exact Or.inl ⟨p, hfnew⟩),
    hposEqual, hchosen⟩

/-- At the last forward parent, an old B/NEW cursor imposes
    no constraint on the terminal child. Every incoming S5,
    including a foreign B cleanup or a pending C leaf update,
    preserves the rooted NEW frontier. Consumer: terminal NEW
    ROOT_IN all-edge class of the R10a S-frontier. -/
theorem bankWordRenewalSoftTerminalNewIncomingStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s)
    (p : Nat) (hn : 5 ≤ n)
    (hf : BankWordRenewalSoftForwardShape ring root z.1 p)
    (hactive :
      (z.1.2.1 root).ser.cert = .RUNNING ∧
      (z.1.2.1 root).ser.phase = .B ∧
      (z.1.2.1 root).ser.wphase = .CURRENT)
    (hterminal : p + 2 = n)
    (hnew : (z.1.2.1 (L3.EWord.site ring root p)).ser.out = .NEW)
    (hx : (postW
      (z.1.2.1 (L3.EWord.site ring root (n - 1)))
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root (n - 1))))).eX.l = false)
    (hy : (postW
      (z.1.2.1 (L3.EWord.site ring root (n - 1)))
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root (n - 1))))).eY.l = true) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))) =
      bankWordRenewalSoftRootedPosition ring root z.1 ∧
    bankWordRenewalSoftRootedChosen ring root s z =
      L3.EWord.site ring root p := by
  have hseam :
      ring.rightNeighbor (L3.EWord.site ring root (n - 1)) =
        root :=
    L3.EWord.validationSeamNeighbor ring root
      (L3.EWord.site ring root (n - 1)) rfl
  have hne :
      ring.rightNeighbor (L3.EWord.site ring root (n - 1)) ≠
        L3.EWord.site ring root (n - 1) :=
    L3.EWord.rightNeighborDifferent ring (by omega)
      (L3.EWord.site ring root (n - 1))
  have hrootRunningNeighbor :
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root (n - 1)))).ser.cert =
          .RUNNING := by
    rw [hseam]
    exact hactive.1
  have hrootSerNeighbor :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1
          (ring.rightNeighbor
            (L3.EWord.site ring root (n - 1)))).ser =
        (z.1.2.1 (ring.rightNeighbor
          (L3.EWord.site ring root (n - 1)))).ser := by
    change ((phiW ring z.1.2.1
      (L3.EWord.site ring root (n - 1)))
      (ring.rightNeighbor
        (L3.EWord.site ring root (n - 1)))).ser = _
    rw [phiW_ser_target ring z.1.2.1
      (L3.EWord.site ring root (n - 1)) hne]
    cases hphase :
      (z.1.2.1 (L3.EWord.site ring root (n - 1))).ser.phase <;>
      simp [serW, serializerStep, ProjW.lift,
        hx, hy, hrootRunningNeighbor, hphase]
  have hrootSer :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1 root).ser =
        (z.1.2.1 root).ser := by
    simpa only [hseam] using hrootSerNeighbor
  have hframe (j : Nat) (hj : j < n)
      (hjzero : j ≠ 0) (hjlast : j ≠ n - 1) :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1
          (L3.EWord.site ring root j)).ser =
        (z.1.2.1 (L3.EWord.site ring root j)).ser := by
    have hneSource :
        L3.EWord.site ring root j ≠
          L3.EWord.site ring root (n - 1) := by
      intro he
      have hi := L3.EWord.validationSiteInjective
        ring root j (n - 1) hj (by omega) he
      exact hjlast hi
    have hneTarget :
        L3.EWord.site ring root j ≠
          ring.rightNeighbor
            (L3.EWord.site ring root (n - 1)) := by
      rw [hseam]
      intro he
      have hi := L3.EWord.validationSiteInjective
        ring root j 0 hj (by omega)
        (he.trans (L3.EWord.siteZero ring root).symm)
      exact hjzero hi
    change ((phiW ring z.1.2.1
      (L3.EWord.site ring root (n - 1)))
      (L3.EWord.site ring root j)).ser = _
    exact phiW_ser_remote ring z.1.2.1
      (L3.EWord.site ring root (n - 1))
      (L3.EWord.site ring root j) hneSource hneTarget
  have hprefix (j : Nat) (hj : j ≤ p) :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1
          (L3.EWord.site ring root j)).ser =
        (z.1.2.1 (L3.EWord.site ring root j)).ser := by
    by_cases hz : j = 0
    · rw [hz, L3.EWord.siteZero]
      exact hrootSer
    · exact hframe j (by omega) hz (by omega)
  have hnextActive :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1 root).ser.cert =
          .RUNNING ∧
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1 root).ser.phase =
          .B ∧
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1 root).ser.wphase =
          .CURRENT := by
    simpa only [hrootSer] using hactive
  have hfnew : BankWordRenewalSoftForwardShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))) p := by
    refine {
      pivotBound := hf.pivotBound
      completed := ?_
      parentPhase := ?_
      parentCurrent := ?_
      front := ?_ }
    · intro j hj
      simpa only [hprefix j (by omega)] using
        hf.completed j hj
    · simpa only [hprefix p (by omega)] using
        hf.parentPhase
    · simpa only [hprefix p (by omega)] using
        hf.parentCurrent
    · right
      refine ⟨by omega, Or.inl ?_⟩
      simpa only [hprefix p (by omega)] using hnew
  have hidxOld := bankWordRenewalSoftForwardIndex
    ring root z.1 p hf
  have hidxNew := bankWordRenewalSoftForwardIndex
    ring root (bankWordEpochNext ring root z.1
      (L3.EWord.site ring root (n - 1))) p hfnew
  have hparentFrame :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (n - 1))).2.1
          (L3.EWord.site ring root p)).ser =
        (z.1.2.1 (L3.EWord.site ring root p)).ser :=
    hprefix p (by omega)
  have hposEqual :
      bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z.1
          (L3.EWord.site ring root (n - 1))) =
      bankWordRenewalSoftRootedPosition ring root z.1 := by
    simp [bankWordRenewalSoftRootedPosition, hactive,
      hnextActive, hidxOld, hidxNew, hparentFrame]
  have hchosen :
      bankWordRenewalSoftRootedChosen ring root s z =
        L3.EWord.site ring root p := by
    have hpn : p < n := by
      have hh := hf.pivotBound
      omega
    simp [bankWordRenewalSoftRootedChosen, hactive,
      hidxOld, hf.parentPhase, hpn]
  exact ⟨(by intro _; exact Or.inl ⟨p, hfnew⟩),
    hposEqual, hchosen⟩

/-- An INTERNAL S3 on an observed C/INTERNAL_OK child
    leaves that child and the rooted WAIT parent unchanged,
    although it may canonicalize an inherited B/F responder.
    Consumer: observed-child S3 stall, with zero frontier charge. -/
theorem bankWordRenewalSoftInternalAnsweredChildStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s)
    (p : Nat) (hn : 5 ≤ n)
    (hf : BankWordRenewalSoftForwardShape ring root z.1 p)
    (hactive :
      (z.1.2.1 root).ser.cert = .RUNNING ∧
      (z.1.2.1 root).ser.phase = .B ∧
      (z.1.2.1 root).ser.wphase = .CURRENT)
    (hbound : p + 2 < n)
    (hwait :
      (z.1.2.1 (L3.EWord.site ring root p)).ser.out = .WAIT)
    (hchildC :
      (z.1.2.1 (L3.EWord.site ring root (p + 1))).ser.phase = .C)
    (hanswered :
      (z.1.2.1 (L3.EWord.site ring root (p + 1))).ser.probe =
        .INTERNAL_OK)
    (hchildCurrent :
      (z.1.2.1 (L3.EWord.site ring root (p + 1))).ser.wphase =
        .CURRENT)
    (hx : (postW
      (z.1.2.1 (L3.EWord.site ring root (p + 1)))
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root (p + 1))))).eX.l = false)
    (hy : (postW
      (z.1.2.1 (L3.EWord.site ring root (p + 1)))
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root (p + 1))))).eY.l = false) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (p + 1))) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (p + 1))) =
      bankWordRenewalSoftRootedPosition ring root z.1 ∧
    bankWordRenewalSoftRootedChosen ring root s z =
      L3.EWord.site ring root p ∧
    L3.EWord.site ring root (p + 1) ≠
      bankWordRenewalSoftRootedChosen ring root s z := by
  have hne :
      ring.rightNeighbor
        (L3.EWord.site ring root (p + 1)) ≠
        L3.EWord.site ring root (p + 1) :=
    L3.EWord.rightNeighborDifferent ring (by omega)
      (L3.EWord.site ring root (p + 1))
  have hchildSer :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (p + 1))).2.1
          (L3.EWord.site ring root (p + 1))).ser =
        (z.1.2.1 (L3.EWord.site ring root (p + 1))).ser := by
    change ((phiW ring z.1.2.1
      (L3.EWord.site ring root (p + 1)))
      (L3.EWord.site ring root (p + 1))).ser = _
    rw [phiW_ser_source]
    cases hc :
      (z.1.2.1 (ring.rightNeighbor
        (L3.EWord.site ring root (p + 1)))).ser.phase <;>
      simp [serW, serializerStep, ProjW.lift,
        hx, hy, hchildC, hanswered, hc]
  have hchildPhaseNew :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (p + 1))).2.1
          (L3.EWord.site ring root (p + 1))).ser.phase = .C := by
    simpa only [hchildSer] using hchildC
  have hchildCurrentNew :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (p + 1))).2.1
          (L3.EWord.site ring root (p + 1))).ser.wphase =
        .CURRENT := by
    simpa only [hchildSer] using hchildCurrent
  have hchildProbeNew :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (p + 1))).2.1
          (L3.EWord.site ring root (p + 1))).ser.probe =
          .INTERNAL_OK := by
    simpa only [hchildSer] using hanswered
  have hframe (j : Nat) (hj : j < n)
      (hjs : j ≠ p + 1) (hjt : j ≠ p + 2) :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (p + 1))).2.1
          (L3.EWord.site ring root j)).ser =
        (z.1.2.1 (L3.EWord.site ring root j)).ser := by
    have hsourceNe :
        L3.EWord.site ring root j ≠
          L3.EWord.site ring root (p + 1) := by
      intro hh
      have hi := L3.EWord.validationSiteInjective
        ring root j (p + 1) hj (by omega) hh
      exact hjs hi
    have htargetNe :
        L3.EWord.site ring root j ≠
          ring.rightNeighbor
            (L3.EWord.site ring root (p + 1)) := by
      rw [L3.EWord.siteSuccessor]
      intro hh
      have hi := L3.EWord.validationSiteInjective
        ring root j (p + 2) hj hbound hh
      exact hjt hi
    change ((phiW ring z.1.2.1
      (L3.EWord.site ring root (p + 1)))
      (L3.EWord.site ring root j)).ser = _
    simp [phiW, projectedEdge, hsourceNe, htargetNe]
  have hrootSer :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (p + 1))).2.1 root).ser =
          (z.1.2.1 root).ser := by
    simpa only [L3.EWord.siteZero] using
      hframe 0 (by omega) (by omega) (by omega)
  have hnextActive :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (p + 1))).2.1 root).ser.cert =
          .RUNNING ∧
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (p + 1))).2.1 root).ser.phase =
          .B ∧
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (p + 1))).2.1 root).ser.wphase =
          .CURRENT := by
    simp [hrootSer, hactive.1, hactive.2.1, hactive.2.2]
  have hfnew :
      BankWordRenewalSoftForwardShape ring root
        (bankWordEpochNext ring root z.1
          (L3.EWord.site ring root (p + 1))) p := by
    refine {
      pivotBound := hf.pivotBound
      completed := ?_
      parentPhase := ?_
      parentCurrent := ?_
      front := ?_ }
    · intro j hj
      rw [hframe j (by omega) (by omega) (by omega)]
      exact hf.completed j hj
    · rw [hframe p (by omega) (by omega) (by omega)]
      exact hf.parentPhase
    · rw [hframe p (by omega) (by omega) (by omega)]
      exact hf.parentCurrent
    · by_cases hpzero : p = 0
      · left
        refine ⟨hpzero, ?_, ?_, ?_, ?_⟩
        · rw [hframe p (by omega) (by omega) (by omega)]
          exact hwait
        · exact hchildPhaseNew
        · exact hchildCurrentNew
        · exact Or.inr hchildProbeNew
      · right
        refine ⟨by omega, Or.inr ⟨?_, ?_⟩⟩
        · rw [hframe p (by omega) (by omega) (by omega)]
          exact hwait
        · exact Or.inr (Or.inl
            ⟨hbound, hchildPhaseNew, hchildProbeNew,
              hchildCurrentNew⟩)
  have hidxOld := bankWordRenewalSoftForwardIndex
    ring root z.1 p hf
  have hidxNew := bankWordRenewalSoftForwardIndex
    ring root (bankWordEpochNext ring root z.1
      (L3.EWord.site ring root (p + 1))) p hfnew
  have holdParent :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root (p + 1))).2.1
          (L3.EWord.site ring root p)).ser =
        (z.1.2.1 (L3.EWord.site ring root p)).ser :=
    hframe p (by omega) (by omega) (by omega)
  have hposEqual :
      bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z.1
          (L3.EWord.site ring root (p + 1))) =
      bankWordRenewalSoftRootedPosition ring root z.1 := by
    simp [bankWordRenewalSoftRootedPosition, hactive,
      hnextActive, hidxOld, hidxNew, holdParent]
  have hchosen :
      bankWordRenewalSoftRootedChosen ring root s z =
        L3.EWord.site ring root p := by
    have hpn : p < n := by
      have hb := hf.pivotBound
      omega
    simp [bankWordRenewalSoftRootedChosen, hactive,
      hidxOld, hf.parentPhase, hf.pivotBound, hpn]
  have hdistinct :
      L3.EWord.site ring root (p + 1) ≠
        L3.EWord.site ring root p := by
    intro hh
    have hi := L3.EWord.validationSiteInjective
      ring root (p + 1) p (by omega) (by omega) hh
    omega
  exact ⟨(by intro _; exact Or.inl ⟨p, hfnew⟩),
    hposEqual, hchosen, (by rw [hchosen]; exact hdistinct)⟩


theorem bankWordRenewalSoftForwardNewChildStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (z : BankWordRenewalPostSOne ring root s)
    (p k : Nat)
    (hf : BankWordRenewalSoftForwardShape ring root z.1 p)
    (hactive :
      (z.1.2.1 root).ser.cert = .RUNNING ∧
      (z.1.2.1 root).ser.phase = .B ∧
      (z.1.2.1 root).ser.wphase = .CURRENT)
    (hfar : p < k)
    (hnew : (z.1.2.1 (L3.EWord.site ring root p)).ser.out = .NEW)
    (hinside : k + 1 < n) :
    BankWordRenewalSoftShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root k)) ∧
    bankWordRenewalSoftRootedPosition ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root k)) =
      bankWordRenewalSoftRootedPosition ring root z.1 ∧
    bankWordRenewalSoftRootedChosen ring root s z =
      L3.EWord.site ring root p := by
  have hpositive : 0 < p := by
    rcases hf.front with hzero | hpos
    · have hbad := hzero.2.1.symm.trans hnew
      cases hbad
    · exact hpos.1
  have hframe (j : Nat) (hj : j ≤ p) :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root k)).2.1
          (L3.EWord.site ring root j)).ser =
        (z.1.2.1 (L3.EWord.site ring root j)).ser := by
    have hjn : j < n := by omega
    have hsourceNe :
        L3.EWord.site ring root j ≠
          L3.EWord.site ring root k := by
      intro he
      have hi := L3.EWord.validationSiteInjective
        ring root j k hjn (by omega) he
      omega
    have htargetNe :
        L3.EWord.site ring root j ≠
          ring.rightNeighbor (L3.EWord.site ring root k) := by
      rw [L3.EWord.siteSuccessor]
      intro he
      have hi := L3.EWord.validationSiteInjective
        ring root j (k + 1) hjn hinside he
      omega
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
      hframe 0 (by omega)
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
    simpa only [hrootSer] using hactive
  have hfnew : BankWordRenewalSoftForwardShape ring root
      (bankWordEpochNext ring root z.1
        (L3.EWord.site ring root k)) p := by
    refine {
      pivotBound := hf.pivotBound
      completed := ?_
      parentPhase := ?_
      parentCurrent := ?_
      front := ?_ }
    · intro j hj
      simpa only [hframe j (by omega)] using
        hf.completed j hj
    · simpa only [hframe p (by omega)] using
        hf.parentPhase
    · simpa only [hframe p (by omega)] using
        hf.parentCurrent
    · right
      refine ⟨hpositive, Or.inl ?_⟩
      simpa only [hframe p (by omega)] using hnew
  have hidxOld := bankWordRenewalSoftForwardIndex
    ring root z.1 p hf
  have hidxNew := bankWordRenewalSoftForwardIndex
    ring root (bankWordEpochNext ring root z.1
      (L3.EWord.site ring root k)) p hfnew
  have hparentFrame :
      ((bankWordEpochNext ring root z.1
        (L3.EWord.site ring root k)).2.1
          (L3.EWord.site ring root p)).ser =
        (z.1.2.1 (L3.EWord.site ring root p)).ser :=
    hframe p (by omega)
  have hposEqual :
      bankWordRenewalSoftRootedPosition ring root
        (bankWordEpochNext ring root z.1
          (L3.EWord.site ring root k)) =
      bankWordRenewalSoftRootedPosition ring root z.1 := by
    simp [bankWordRenewalSoftRootedPosition, hactive,
      hnextActive, hidxOld, hidxNew, hparentFrame]
  have hchosen :
      bankWordRenewalSoftRootedChosen ring root s z =
        L3.EWord.site ring root p := by
    have hpn : p < n := by
      have hb := hf.pivotBound
      omega
    simp [bankWordRenewalSoftRootedChosen, hactive,
      hidxOld, hf.parentPhase, hpn]
  exact ⟨(by intro _; exact Or.inl ⟨p, hfnew⟩),
    hposEqual, hchosen⟩



end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierPrefixTerminalRetires
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierDoneClearsIncomingLease
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierFreshBankPrepared
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierFreshBankCleanOfRootClass
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierFreshBankForeignFree
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierHardStartReadsZero
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierHardStartNeedsSoftFinishes
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierIoneAuthorityCensus
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierPrefixShortDoneRetires
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierNonrootLedgerStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierHardEpochRemoteStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierLedgerGhostCoherence
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierFreshWorkerWitness
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierPhysicalFrame
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierIoneEpochDisjointFrame
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierTrackedAZeroCompletes
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierFreeSourceNoDone
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierFreshIncomingNoDone
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierNonrootWorkerDoneEquation
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierIncomingReadyReceiptDone
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierFreshRootIdle
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierFreshNoImmediateHardAccept
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierFreshPhysicalShape
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierPrefixNoEarlyRoot
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierFreshTicketLineage
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierIncomingRequestTicket
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierHardStartTicketPair
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierTicketLineageRemoteStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierHardAcceptOfTicketLineage
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierBankRoom
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierFreshShapeOnBank
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierShapePrefixNoRoot
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierNonvalidatingGuardsQuiet
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierPrefixAdvanceRow
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierPrefixHandoffRow
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierWaveImpliesRootLineage
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierFreshWaveLineage
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierWaveChallengeTickets
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierWaveInternalObservation
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierWaveLeafObservation
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierWaveInternalAdmission
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierWaveLeafAdmission
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierWaveReturnAdmission
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierRootInternalAdmissionLedger
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierWaveHardAcceptGenuine
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierSoftSOneDoesNotValidate
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierReturnChildForcesPivot
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierReturnedNonrootNonvalidating
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierAZeroNominationMatchesReceipt
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierNonrootInternalRowClass
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierWaveTicketRemoteFrame
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierWaveInactiveNonrootStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierWaveUnvisitedNonrootStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootIncomingInactiveStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootOutgoingFinishStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootOutgoingSoftStartStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftRootEpisodeStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootOutgoingHardStartStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootIncomingActiveFrameStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootIncomingLeafStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootOutgoingChallengeStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootOutgoingLeafStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootOutgoingReturnPivotStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootOutgoingStartFinishStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootOutgoingCoveredFrameStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootIncomingCoveredLeafStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootIncomingShortCoveredFrameStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootIncomingPendingForwardShape
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootIncomingSelectedForwardLeafStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootIncomingReturnNonpendingTicketStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootIncomingReturnNonpendingSerializerStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootIncomingGuardedReturnStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootIncomingSameWaveLeafStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootIncomingCoveredForwardStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootIncomingShortStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootIncomingQuietSourceFrame
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootIncomingQuietStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootIncomingGuardedStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftForwardIndex
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftReturnIndex
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftShapeSeed
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftRootEntryAndRecovery
#print axioms L3.RenewalReferenceClock.bankWordRenewalFrontierFreshWaveLineageQuiet
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootOutgoingHardStartQuietStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootOutgoingFinishQuietStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootOutgoingCoveredQuietStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootIncomingStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootOutgoingSoftStartQuietStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootOutgoingRecoveryQuietStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootOutgoingKnownRowsStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveInternalInactiveQuietStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveInternalUnvisitedQuietStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveInternalCoveredDoneQuietStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveReturnSuffixPairQuiet
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveSelectedTicketPairStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveInternalChallengeTicketStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveInternalAdmissionTicketStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveInternalLeafTicketStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveReturnMoveTicketStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveInternalObservationTicketStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveInternalCanonicalCleanupStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveReturnPivotUnique
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveReturnNonBPairSuffixQuiet
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveReturnMoveSuffixQuiet
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveInternalNonBToCQuietStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveReturnMoveQuietUpgrade
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveReturnNonBQuietUpgrade
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootOutgoingPendingTicketStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWavePendingGhostFixed
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootOutgoingPendingQuietStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveInternalObservedChildQuietStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootOutgoingInactiveBQuietStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootOutgoingInactiveQuietStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveInternalNewAnyResponderTicketStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveInternalPendingQuietStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveInternalCanonicalRootLineageStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftInternalPendingStall
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftRootIncomingStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftFirstAdmission
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftPendingObservationStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftInternalAdmissionStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootOutgoingInternalQuietStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveRootOutgoingActiveQuietStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveBroadcasterIsParent
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveInternalFrontierNewQuietStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalWaveInternalCanonicalQuietStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftSuffixFrameStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftRootIncomingForeignBStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftLeafAdmissionStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftCoveredDoneFrameStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftRootOutgoingFinishStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftForwardChallengeStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftReturnStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftRootIncomingLeafStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftRootIncomingReturnStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftSourceOffset
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftEdgeGeometry
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftOwnerFlags
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftForwardCoveredSource
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftReturnCoveredSource
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftIncomingRowCensus
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftForwardNomination
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftReturnNomination
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftInternalFlags
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftIncomingFlags
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftOutgoingFlags
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftForwardCoveredStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftReturnCoveredStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftReturnEdgeCases
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftShapeWordFromSeed
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftInactiveInternalStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftReturnParentStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftRootFirstStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftRootFinishStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftRootEntryStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftInactiveIncomingStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftForwardSeamOutsideFront
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftTerminalNewIncomingStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftInternalAnsweredChildStep
#print axioms L3.RenewalReferenceClock.bankWordRenewalSoftForwardNewChildStep
