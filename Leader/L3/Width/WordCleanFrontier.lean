import Leader.L3.Width.WordCleanBand

/-!
# Width W clean clock, part 2: the renewal frontier

Ported BankWordRenewalFrontier declarations (fresh prefix shape, wave rows).
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

/-- Width port of `bankWordRenewalFrontierFreshBankPrepared`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordPassValuesBase`, `widthWordRenewalFrontierFreshPhysicalShape`, `widthWordRetryPrefixInvariantSeed`.
 A genuine hard acceptance on the compiled BANK branch
physically installs the canonical prefix at the selected root
and reloads precisely the lease L used by the renewal argument.
Consumer: the first prefix/lease cut in repair.tex R10a W. -/
theorem widthWordRenewalFrontierFreshBankPrepared {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hsmallFive : 5 ≤ n)
    (seed : BankWordRenewalFreshSeed ring root s) :
    (seed.1.1.2.1 root).si =
      launchPrefix (compileAdvice (ceilLogTwo n)).t ∧
    (seed.1.1.2.1 root).siLease.val =
      widthWordRenewalLease n := by
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
    (widthWordHardEpochBankLeaseMaximum hsmallFive)⟩

end

section
open Classical

/-- Width port of `bankWordRenewalFrontierFreshBankForeignFree`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalFrontierFreshPhysicalShape`.
 A genuinely accepted root in the represented fixed-root
BANK class has no surviving physical foreign SI cursor.
This imports the verified ticket-origin to EWord hard-scrub
bridge; it does not assume empty initial private scratch.
Consumer: the starting case of the no-hard-S1 worker census. -/
theorem widthWordRenewalFrontierFreshBankForeignFree {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (seed : BankWordRenewalFreshSeed ring root s) :
    ∀ i : Fin n, i ≠ root →
      freeSI (seed.1.1.2.1 i).si = true := by
  obtain ⟨pre, e, hgen, heq⟩ := seed.2
  have horigin := widthWordRootDoneOriginReachable
    ring hn hsmallFive root s hs pre.1 pre.2.1
  have hfree := widthWordRootDoneOriginGenuineClean
    ring hn hsmallFive root s hs pre.1 horigin e hgen
  have hstate := congrArg
    (fun v : BankWordRenewalPostSOne ring root s => v.1) heq
  change
    ∀ i : Fin n, i ≠ root →
      freeSI
        (((bankWordRenewalNext ring root s pre e).1.2.1 i).si) =
          true at hfree
  rw [hstate] at hfree
  exact hfree

end

section
open Classical

/-- Width port of `bankWordRenewalFrontierFreshRootIdle`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalSoftShapeSeed`, `widthWordRetryPrefixInvariantSeed`.
 R10a W R2 base: the physically selected genuine hard S6
returns the root serializer certificate to IDLE, not RUNNING.
Consumer: impossibility of another hard S6 on the first service
after the fresh cut. -/
theorem widthWordRenewalFrontierFreshRootIdle
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (seed : BankWordRenewalFreshSeed ring root s) :
    (seed.1.1.2.1 root).ser.cert = .IDLE := by
  obtain ⟨pre, e, hgen, heq⟩ := seed.2
  have hidle := widthWordHardEpochSelectedGenuineRootIdle
    ring hn hsmallFive root s hs pre.1 pre.2.1 e hgen
  have hstate := congrArg
    (fun v : BankWordRenewalPostSOne ring root s => v.1) heq
  change
    ((bankWordRenewalNext ring root s pre e).1.2.1 root).ser.cert =
      .IDLE at hidle
  rw [hstate] at hidle
  exact hidle

end

section
open Classical

/-- Width port of `bankWordRenewalFrontierFreshPhysicalShape`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalFrontierFreshShapeOnBank`.
 The actual accepted BANK cut has the shape above. The
geometric inequality is explicit; it has not been derived here
from the BANK compiler guard. Consumer: prefix half of the
uninterrupted-worker induction in repair.tex R10a W. -/
theorem widthWordRenewalFrontierFreshPhysicalShape {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (hn : 5 ≤ n)
    (hgeom : (compileAdvice (ceilLogTwo n)).t + 2 ≤ n)
    (seed : BankWordRenewalFreshSeed ring root s) :
    BankWordRenewalFrontierPhysicalShape ring root seed.1.1 := by
  obtain ⟨w, hw, hp, hh, ht, hi⟩ :=
    bankWordRenewalFrontierFreshWorkerWitness ring root s seed
  have hphysical :=
    (widthWordRenewalFrontierFreshBankPrepared
      ring root s hsmallFive seed).1
  have hfree :=
    widthWordRenewalFrontierFreshBankForeignFree
      ring root s hn hsmallFive hs seed
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

end

section
open Classical

/-- Width port of `bankWordRenewalFrontierIncomingRequestTicket`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveRootIncomingInactiveStep`.
 Actual S0 incoming-root service creates the REQUESTED root
and a matching .requested chronological ticket, including on
arbitrary inherited private serializer scratch.
Consumer: first obligation of R2 ticket-lineage propagation. -/
theorem widthWordRenewalFrontierIncomingRequestTicket {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 e) :=
    ((widthWordSerializerRootClassClosed
      ring hn hsmallFive root).2 z.2.1 hclass e).2
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

end

section
open Classical

/-- Width port of `bankWordRenewalFrontierHardStartTicketPair`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveRootOutgoingHardStartStep`.
 The actual hard S1 is ticketed whenever the REQUESTED
portion of the proposed lineage holds. Its source creates
a waiting parent and a pending first-child ticket with the
same request/start stamps. Consumer: the R2 validating
S1-to-S2R lineage establishment, not an assumed S6 success. -/
theorem widthWordRenewalFrontierHardStartTicketPair {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 root) :=
    ((widthWordSerializerRootClassClosed
      ring hn hsmallFive root).2 z.2.1 hclass root).2
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

end

section
open Classical

/-- Width port of `bankWordRenewalFrontierHardAcceptOfTicketLineage`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalFrontierWaveHardAcceptGenuine`.
 R10a W R2 discharge from a full physical-to-ticket
lineage: a represented, genuinely reachable physical root
B/DONE/F accepting edge has matching done/returned tickets.
The actual wGenuineAcceptance flag is therefore true; no
assumption about a forged local S6 is substituted.
Consumer: the root outgoing case of CleanInvariant preservation. -/
theorem widthWordRenewalFrontierHardAcceptOfTicketLineage {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 root) :=
    ((widthWordSerializerRootClassClosed
      ring hn hsmallFive root).2 z.2.1 hclass root).2
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

end

section
open Classical

/-- Width port of `bankWordRenewalFrontierFreshShapeOnBank`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordPassShapeAtFreshSeed`.
 The genuine fresh BANK acceptance has the original
physical PREFIX host/index/free-site shape, without an
assumed ring-size inequality. Consumer: R10a W induction base. -/
theorem widthWordRenewalFrontierFreshShapeOnBank {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (seed : BankWordRenewalFreshSeed ring root s) :
    BankWordRenewalFrontierPhysicalShape ring root seed.1.1 :=
  widthWordRenewalFrontierFreshPhysicalShape
    ring root s hsmallFive hs hsmallFive
    (widthWordRenewalFrontierBankRoom hsmallFive) seed

end

section
open Classical

/-- Width port of `bankWordRenewalFrontierShapePrefixNoRoot`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordPassIncomingDoneCompletes`, `widthWordPassPrefixStep`, `widthWordPassValuesPoneStep`.
 For a tracked PREFIX worker satisfying the physical
shape, the next clockwise site is not the root. This is the
geometric branch exclusion needed for the P0/P2 census. -/
theorem widthWordRenewalFrontierShapePrefixNoRoot {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankWordEpochState n)
    (hsmallFive : 5 ≤ n)
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
    ring root z w hw (widthWordRenewalFrontierBankRoom hsmallFive)
    hphysical.2.1 hphysical.2.2.2.1

end

section
open Classical

/-- Width port of `bankWordRenewalFrontierWaveHardAcceptGenuine`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordEpochLapInvariantStep`.
 Conditional R2 discharge: the new visited-site lineage
implies the old root/child lineage and thus a physical root
hardAccept has matching genuine validation stamps.
Consumer: root hard-accept branch of CleanInvariant preservation. -/
theorem widthWordRenewalFrontierWaveHardAcceptGenuine {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hwave : BankWordRenewalFrontierWaveLineage ring root z)
    (hhard :
      (bankWordEpochSelectedReceipt ring z root).serializer.hard.hardAccept =
        true) :
    bankWordHardEpochGenuine ring root
      (bankWordEpochSelectedReceipt ring z root)
      (bankWordHardEpochLedger ring root z) = true := by
  exact widthWordRenewalFrontierHardAcceptOfTicketLineage
    ring root s hn hsmallFive hs z hz
    (bankWordRenewalFrontierWaveImpliesRootLineage
      ring root z hwave) hhard

end

section
open Classical

/-- Width port of `bankWordRenewalFrontierWaveUnvisitedNonrootStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveInternalUnvisitedQuietStep`.
 On an actual EWord-unvisited nonroot service, neither
physical serializer nor validation ticket changes at any
scrubbed site. This statement preserves the FULL 5-clause
WaveLineage at every covered site, with the actual phiW step.
Classification is applied to each admitted witness for g.
Consumer: unvisitedSuffix case in R10a W wave induction. -/
theorem widthWordRenewalFrontierWaveUnvisitedNonrootStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
    have hrepresented := widthWordEpochReachablePhysicalRootClass
      ring hn hsmallFive root s hs z hz
    have hfixed : WFixedRoot ring root
        (phiW ring z.2.1 e) :=
      ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
        z.2.1 hrepresented e).2
    have hno := widthWordRootNonrootHardAcceptFalse
      ring hn hsmallFive root s hs z hz e he
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

end

section
open Classical

/-- Width port of `bankWordRenewalWaveRootIncomingInactiveStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveRootIncomingGuardedStep`.
 Incoming S0 creates a matching request; incoming S5 frames
the nonvalidating root and its ticket. Consumer: J-W root seam. -/
theorem widthWordRenewalWaveRootIncomingInactiveStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hpred : ring.rightNeighbor e = root)
    (hwave : BankWordRenewalFrontierWaveLineage ring root z)
    (hinactive : ¬ ((z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING)) :
    BankWordRenewalFrontierWaveLineage ring root
      (bankWordEpochNext ring root z e) := by
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
      z.2.1 hclass e).2
  have hpost := clockPostIncoming ring root z.2.1 e
    (by omega : 2 ≤ n) hfixed hpred
  try rw [hpred] at hpost
  have hneq : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) e
  by_cases hidle : (z.2.1 root).ser.cert = .IDLE
  · have hrequest :=
      (widthWordRenewalFrontierIncomingRequestTicket
        ring root e s hn hsmallFive hs z hz hpred hidle).2
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

end

section
open Classical

/-- Width port of `bankWordRenewalWaveRootOutgoingFinishStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveRootOutgoingFinishQuietStep`.
 Root S6, whether soft or hard, exits to physical IDLE.
The hard S6's genuineness is certified at the OLD state by
bankWordRenewalFrontierWaveHardAcceptGenuine.
Consumer: terminal outgoing branch of J-W. -/
theorem widthWordRenewalWaveRootOutgoingFinishStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hcert : (z.2.1 root).ser.cert ≠ .REQUESTED)
    (hphase : (z.2.1 root).ser.phase = .B)
    (hout : (z.2.1 root).ser.out = .DONE)
    (hchild :
      (z.2.1 (ring.rightNeighbor root)).ser.phase = .F) :
    BankWordRenewalFrontierWaveLineage ring root
      (bankWordEpochNext ring root z root) := by
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 root) :=
    ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
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

end

section
open Classical

/-- Width port of `bankWordRenewalWaveRootOutgoingSoftStartStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveRootOutgoingSoftStartQuietStep`.
 A positive-lease root S1 becomes RUNNING/CURRENT, so the
attempted soft start is not a hard validation wave.
Consumer: root outgoing soft S1 branch of J-W. -/
theorem widthWordRenewalWaveRootOutgoingSoftStartStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hrequested : (z.2.1 root).ser.cert = .REQUESTED)
    (hpositive : 0 < (z.2.1 root).siLease.val) :
    BankWordRenewalFrontierWaveLineage ring root
      (bankWordEpochNext ring root z root) := by
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 root) :=
    ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
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

end

section
open Classical

/-- Width port of `bankWordRenewalWaveRootOutgoingHardStartStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveRootOutgoingHardStartQuietStep`.
 A reachable represented zero-lease S1 establishes the complete fresh
two-site wave, including the historical waiting/pending tickets with one
common request/start stamp. Consumer: the hard-start branch of root
outgoing J-W transport and the paper's R10a validation cut. -/
theorem widthWordRenewalWaveRootOutgoingHardStartStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hwave : BankWordRenewalFrontierWaveLineage ring root z)
    (hrequested : (z.2.1 root).ser.cert = .REQUESTED)
    (hzero : (z.2.1 root).siLease.val = 0) :
    BankWordRenewalFrontierWaveLineage ring root
      (bankWordEpochNext ring root z root) := by
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 root) :=
    ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
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
    widthWordRenewalFrontierHardStartTicketPair
      ring root s hn hsmallFive hs z hz hwave.1 hrequested hzero
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

end

section
open Classical

/-- Width port of `bankWordRenewalWaveRootIncomingActiveFrameStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveRootIncomingCoveredForwardStep`, `widthWordRenewalWaveRootIncomingQuietStep`, `widthWordRenewalWaveRootIncomingShortCoveredFrameStep`.
 The active incoming-root S5 seam preserves the EWord physical
wave, the root ticket and every ticket before the terminal site.
The terminal source ticket is intentionally excluded here: its
PENDING-to-LEAF_OK transition requires the parent/child join below.
Consumer: root incoming J-W case split, paper R10a terminal seam. -/
theorem widthWordRenewalWaveRootIncomingActiveFrameStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
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

end

section
open Classical

/-- Width port of `bankWordRenewalWaveRootIncomingLeafStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveRootIncomingSameWaveLeafStep`.
 An actual reachable incoming S5 at C/PENDING with the
same historical root parent and leaf child writes observedLeaf
to the terminal source. Unlike a mere physical LEAF_OK byte,
the conclusion depends on the join of OLD tickets.
Consumer: last covered-site S5 in the incoming J-W step. -/
theorem widthWordRenewalWaveRootIncomingLeafStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
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

end

section
open Classical

/-- Width port of `bankWordRenewalWaveRootOutgoingCoveredFrameStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveRootOutgoingCoveredQuietStep`.
 On a represented RUNNING root, the actual S2R B/DONE -> B
pair is stationary in the FULL five-clause wave-lineage invariant:
the two selected serializer records and tickets frame, all other
sites are remote, and EWord's validation ghost is unchanged.
Consumer: covered root S2R arm of J-W and paper return-pivot row. -/
theorem widthWordRenewalWaveRootOutgoingCoveredFrameStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 root) :=
    ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
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

end

section
open Classical

/-- Width port of `bankWordRenewalWaveRootIncomingShortCoveredFrameStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveRootIncomingShortStep`.
 If the current EWord scrub prefix ends before the incoming
root seam, S5 preserves every historical validation ticket
actually required by that prefix, as well as its entire EWord
physical shape. The final, unvisited site is deliberately not
claimed to have a pending ticket. Consumer: the short-prefix
branch of widthWordRenewalWaveRootIncomingStep, J-W. -/
theorem widthWordRenewalWaveRootIncomingShortCoveredFrameStep
    {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
  have hframe := widthWordRenewalWaveRootIncomingActiveFrameStep
    ring root e s hn hsmallFive hs z hz hpred g hshape
  refine ⟨hframe.1, ?_⟩
  intro k hk
  exact hframe.2.2 k hk (by omega)

end

section
open Classical

/-- Width port of `bankWordRenewalWaveRootIncomingSameWaveLeafStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveRootIncomingCoveredForwardStep`.
 The two OLD covered wave tickets (DONE root, PENDING
terminal child) with one common req/stamp are sufficient for
the real incoming S5 to write an observedLeaf ticket for that
SAME wave. Unlike an existential-leaf conclusion, this fixes
the stamps used by the consumer's entire five-clause J-W fold.
Consumer: full covered-forward incoming-root WaveLineage step. -/
theorem widthWordRenewalWaveRootIncomingSameWaveLeafStep
    {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
  have hwrite := widthWordRenewalWaveRootIncomingLeafStep
    ring root e s hn hsmallFive hs z hz hpred hrun
    hsourceC hsourcePending parent child
    hparent hchild hreqSame hstampSame
  unfold BankWordRenewalFrontierWaveSiteTicket
  refine ⟨{ parent with stage := .observedLeaf }, ?_, hpReq, hpStamp⟩
  rw [← hseam, hwrite]
  rfl

end

section
open Classical

/-- Width port of `bankWordRenewalWaveRootIncomingCoveredForwardStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveRootIncomingGuardedStep`.
 Full five-site-clause transport for a covered FORWARD root
seam at an old C/PENDING/VALIDATING terminal. The same chosen
OLD g,req,stamp are preserved, with the new observedLeaf ticket
built by the real historical S5 join. Neither a global scrub=n
hypothesis nor a synthetic provenance reset is used.
Consumer: covered-forward arm of bankWordRenewalWaveRootIncomingStep. -/
theorem widthWordRenewalWaveRootIncomingCoveredForwardStep
    {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
    widthWordRenewalWaveRootIncomingSameWaveLeafStep
      ring root e s hn hsmallFive hs z hz
      hpred hseam hactive.1 hsourceC hsourcePending
      req stamp hrootOld hlastOld
  have hframe := widthWordRenewalWaveRootIncomingActiveFrameStep
    ring root e s hn hsmallFive hs z hz hpred
    (Classical.choose (hwave.2 hactive)) hshape
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
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

end

section
open Classical

/-- Width port of `bankWordRenewalWaveRootIncomingShortStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveRootIncomingGuardedStep`.
 The incoming root seam preserves the FULL WaveLineage on
the OLD chosen g when its scrubbed prefix is short of the
terminal source. This upgrades the physical/ticket frame
from each site to all five historical clauses and root lineage.
Consumer: short active branch of bankWordRenewalWaveRootIncomingStep. -/
theorem widthWordRenewalWaveRootIncomingShortStep
    {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
  have hframe := widthWordRenewalWaveRootIncomingShortCoveredFrameStep
    ring root e s hn hsmallFive hs z hz hpred
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
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
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

end

section
open Classical

/-- Width port of `bankWordRenewalWaveRootIncomingQuietSourceFrame`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveRootIncomingQuietStep`, `widthWordRenewalWaveRootIncomingStep`.
 Literal S5 frames both the old terminal serializer and its
historical ticket whenever the source is F, or C with a probe
other than PENDING. Valid for any active EWord stage, not only
RETURN. Consumer: already-observed forward leaf and quiet RETURN
root-seam branches of full J-W transport. -/
theorem widthWordRenewalWaveRootIncomingQuietSourceFrame
    {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
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

end

section
open Classical

/-- Width port of `bankWordRenewalWaveRootIncomingQuietStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveRootIncomingGuardedStep`.
 Full quiet-source wave-lineage transport on the actual
incoming-root S5 edge, conditional on the selected S5 source being F or C/non-PENDING. The OLD chosen g, req and
stamp remain unchanged; all five covered-site clauses are
transported by real serializer/ticket frames, including the
returned F suffix. Consumer: quiet FORWARD/RETURN arms of the proposed
widthWordRenewalWaveRootIncomingStep (once hquiet is derived
from reachable wave provenance). -/
theorem widthWordRenewalWaveRootIncomingQuietStep
    {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
  have hframe := widthWordRenewalWaveRootIncomingActiveFrameStep
    ring root e s hn hsmallFive hs z hz hpred
    (Classical.choose (hwave.2 hactive)) hshape
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
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
    widthWordRenewalWaveRootIncomingQuietSourceFrame
      ring root e s hn hsmallFive hs z hz hpred hactive.1
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

end

section
open Classical

/-- Width port of `bankWordRenewalWaveRootIncomingGuardedStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveRootIncomingStep`.
 Exhaustive incoming-root J-W assembly modulo exactly ONE
historical reachability obligation: a RETURN-wave terminal C
must not retain the stale PENDING probe with wphase OFF.
Inactive/S0 uses widthWordRenewalWaveRootIncomingInactiveStep, active short
prefixes use widthWordRenewalWaveRootIncomingShortStep,
covered forward C/PENDING joins through the OLD selected
g,req,stamp, covered forward C/LEAF_OK frames through S5,
and RETURN F/C quiet branches frame the entire wave.
Consumer: widthWordRenewalWaveRootIncomingStep after discharge
of the RETURN terminal causal-quietness obligation. -/
theorem widthWordRenewalWaveRootIncomingGuardedStep
    {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
    · exact widthWordRenewalWaveRootIncomingShortStep
        ring root e s hn hsmallFive hs z hz hpred hwave hactive hshort
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
            exact widthWordRenewalWaveRootIncomingCoveredForwardStep
              ring root e s hn hsmallFive hs z hz hpred hwave
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
            exact widthWordRenewalWaveRootIncomingQuietStep
              ring root e s hn hsmallFive hs z hz hpred hwave
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
        · exact widthWordRenewalWaveRootIncomingQuietStep
            ring root e s hn hsmallFive hs z hz hpred hwave
            hactive (Or.inl hf)
        · have hprobe := hreturnQuiet hactive hr hc
          exact widthWordRenewalWaveRootIncomingQuietStep
            ring root e s hn hsmallFive hs z hz hpred hwave
            hactive (Or.inr ⟨hc, hprobe⟩)
  · exact widthWordRenewalWaveRootIncomingInactiveStep
      ring root e s hn hsmallFive hs z hz hpred hwave hactive

end

section
open Classical

/-- Width port of `bankWordRenewalSoftShapeSeed`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRetryPrefixInvariantSeed`.
 The genuine hard S6 cut is inactive, hence satisfies the
conditional spatial invariant and has zero rooted position.
Consumer: the fresh BANK kernel induction base. -/
theorem widthWordRenewalSoftShapeSeed {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (seed : BankWordRenewalFreshSeed ring root s) :
    BankWordRenewalSoftShape ring root seed.1.1 ∧
    bankWordRenewalSoftRootedPosition ring root seed.1.1 = 0 := by
  have hidle := widthWordRenewalFrontierFreshRootIdle
    ring root s hn hsmallFive hs seed
  constructor
  · intro hactive
    rw [hidle] at hactive
    cases hactive.1
  · simp [bankWordRenewalSoftRootedPosition, hidle]

end

section
open Classical

/-- Width port of `bankWordRenewalWaveForwardExcludesReturn`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveInternalCanonicalQuietStep`, `widthWordRenewalWaveInternalFrontierNewQuietStep`, `widthWordRenewalWaveInternalObservedChildQuietStep`.
 A forward B frontier and a return F frontier cannot be two
descriptions of the same physical serializer ring: their pivots
would require either B=F or NEW/WAIT=DONE.
Consumer: incoming S5 preservation of RETURN quietness when the
historically selected wave is still FORWARD. -/
theorem widthWordRenewalWaveForwardExcludesReturn
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

end

section
open Classical

/-- Width port of `bankWordRenewalWaveReturnShapeSiteFrame`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveFullFrameQuietStep`, `widthWordRenewalWaveRootIncomingStep`, `widthWordRenewalWaveRootOutgoingCoveredQuietStep`.
 RETURN geometry only reads serializer records at the named
cyclic sites. This transports any candidate RETURN witness
backward across a physical serializer frame.
Consumer: quietness preservation at covered S2R and incoming S5. -/
theorem widthWordRenewalWaveReturnShapeSiteFrame
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

end

section
open Classical

/-- Width port of `bankWordRenewalWaveIncomingIsSeam`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveRootIncomingStep`.
 The unique source of the incoming-root edge is the
last cyclic serializer site.
Consumer: incoming S5 quietness and full source framing. -/
theorem widthWordRenewalWaveIncomingIsSeam {n : Nat}
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

end

section
open Classical

/-- Width port of `bankWordRenewalWaveReturnSeamQuiet`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveRootIncomingStep`.
 A RETURN seam is either F or a quiet C, by its pivot
geometry and the new all-suffix causal clause.
Consumer: the hreturnQuiet argument of the existing guarded
incoming root theorem, and S5 physical source framing. -/
theorem widthWordRenewalWaveReturnSeamQuiet
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

end

section
open Classical

/-- Width port of `bankWordRenewalWaveRootIncomingActiveWasOld`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveRootIncomingStep`.
 An incoming-root S0 cannot manufacture an active validating
root, and S5 preserves an already non-IDLE root serializer.
Consumer: induction transport of the strengthened RETURN clause. -/
theorem widthWordRenewalWaveRootIncomingActiveWasOld
    {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 e) :=
    ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
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

end

section
open Classical

/-- Width port of `bankWordRenewalWaveRootOutgoingHardStartQuietStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveRootOutgoingKnownRowsStep`.
 A zero-lease hard S1 constructs a RUNNING B/WAIT root;
RETURN would require that same root to be B/DONE.
Consumer: strengthened J-W outgoing hard-start row. -/
theorem widthWordRenewalWaveRootOutgoingHardStartQuietStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z)
    (hrequested : (z.2.1 root).ser.cert = .REQUESTED)
    (hzero : (z.2.1 root).siLease.val = 0) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z root) := by
  have hbase := widthWordRenewalWaveRootOutgoingHardStartStep
    ring root s hn hsmallFive hs z hz hwave.wave hrequested hzero
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 root) :=
    ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
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

end

section
open Classical

/-- Width port of `bankWordRenewalWaveRootOutgoingFinishQuietStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveRootOutgoingActiveQuietStep`, `widthWordRenewalWaveRootOutgoingKnownRowsStep`.
 Outgoing S6 retires the root to IDLE, so RETURN quietness
is preserved vacuously alongside the established ticket ledger.
Consumer: strengthened J-W terminal root row. -/
theorem widthWordRenewalWaveRootOutgoingFinishQuietStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hcert : (z.2.1 root).ser.cert ≠ .REQUESTED)
    (hphase : (z.2.1 root).ser.phase = .B)
    (hout : (z.2.1 root).ser.out = .DONE)
    (hchild :
      (z.2.1 (ring.rightNeighbor root)).ser.phase = .F) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z root) := by
  have hbase := widthWordRenewalWaveRootOutgoingFinishStep
    ring root s hn hsmallFive hs z hz hcert hphase hout hchild
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 root) :=
    ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
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

end

section
open Classical

/-- Width port of `bankWordRenewalWaveRootOutgoingCoveredQuietStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveRootOutgoingActiveQuietStep`, `widthWordRenewalWaveRootOutgoingKnownRowsStep`.
 The already-certified S2R B/DONE + B responder subrow
frames every physical serializer record. Therefore any new
RETURN witness was already a RETURN witness before that row,
and its quiet suffix transfers exactly.
Consumer: covered S2R branch of the root outgoing J-W step. -/
theorem widthWordRenewalWaveRootOutgoingCoveredQuietStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
  have hbase := widthWordRenewalWaveRootOutgoingCoveredFrameStep
    ring root s hn hsmallFive hs z hz hwave.wave
    hrun hrootB hout hchildB
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 root) :=
    ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
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
    widthWordRenewalWaveReturnShapeSiteFrame
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

end

section
open Classical

/-- Width port of `bankWordRenewalWaveRootIncomingStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalLineageQuietStepOfMovingRows`.
 The incoming ROOT_IN edge closes the established full J-W
lineage and the new all-RETURN-suffix quietness clause without
an additional hreturnQuiet premise.
Consumer: the root incoming case of the strengthened J-W induction. -/
theorem widthWordRenewalWaveRootIncomingStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hpred : ring.rightNeighbor e = root)
    (hwave : BankWordRenewalFrontierWaveLineageQuiet ring root z) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z e) := by
  have hseam : e = L3.EWord.site ring root (n - 1) :=
    widthWordRenewalWaveIncomingIsSeam ring root e
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
    have hstatus := widthWordRenewalWaveReturnSeamQuiet
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
    widthWordRenewalWaveRootIncomingGuardedStep
      ring root e s hn hsmallFive hs z hz hpred hwave.wave
      hreturnQuiet
  refine ⟨hbase, ?_⟩
  intro hactiveNew gnew hreturnNew k hk hcnew
  have hactiveOld :
      (z.2.1 root).ser.cert = .RUNNING ∧
      (z.2.1 root).ser.wphase = .VALIDATING :=
    widthWordRenewalWaveRootIncomingActiveWasOld
      ring root e s hn hsmallFive hs z hz hpred hactiveNew
  obtain ⟨gold, req, stamp, hshape, hsites⟩ :=
    hwave.wave.2 hactiveOld
  have hframe := widthWordRenewalWaveRootIncomingActiveFrameStep
    ring root e s hn hsmallFive hs z hz hpred gold hshape
  rcases hshape.stageShape with hforward | hreturn
  · rcases hframe.1.stageShape with hforwardNew | hreturnNewGold
    · exact False.elim
        (widthWordRenewalWaveForwardExcludesReturn
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
      widthWordRenewalWaveReturnSeamQuiet
        ring root z.2.1 e gold hreturn hseam
        (fun j hj hc =>
          hwave.returnSuffixQuiet hactiveOld
            gold hreturn j hj hc)
    have hsourceFrame :=
      widthWordRenewalWaveRootIncomingQuietSourceFrame
        ring root e s hn hsmallFive hs z hz hpred
        hactiveOld.1 hsourceQuiet
    have hclass := widthWordEpochReachablePhysicalRootClass
      ring hn hsmallFive root s hs z hz
    have hfixed : WFixedRoot ring root
        (phiW ring z.2.1 e) :=
      ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
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
      widthWordRenewalWaveReturnShapeSiteFrame
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

end

section
open Classical

/-- Width port of `bankWordRenewalWaveRootOutgoingSoftStartQuietStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveRootOutgoingKnownRowsStep`.
 A positive-lease S1 starts only a CURRENT wave, not a
VALIDATING RETURN. Consumer: ROOT_OUT case of R10a J-W. -/
theorem widthWordRenewalWaveRootOutgoingSoftStartQuietStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordEpochState n)
    (hz : BankWordEpochReachable ring root s z)
    (hrequested : (z.2.1 root).ser.cert = .REQUESTED)
    (hpositive : 0 < (z.2.1 root).siLease.val) :
    BankWordRenewalFrontierWaveLineageQuiet ring root
      (bankWordEpochNext ring root z root) := by
  have hbase := widthWordRenewalWaveRootOutgoingSoftStartStep
    ring root s hn hsmallFive hs z hz hrequested hpositive
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 root) :=
    ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
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

end

section
open Classical

/-- Width port of `bankWordRenewalWaveRootOutgoingKnownRowsStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalLineageQuietStepOfMovingRows`.
 The root rows for which the historical wave ledger has
already been closed: hard/soft S1, S6, and B/DONE+B S2R.
This is deliberately not the remaining S2R challenge/admission
census. Consumer: ROOT_OUT partial assembly in R10a J-W. -/
theorem widthWordRenewalWaveRootOutgoingKnownRowsStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
    · exact widthWordRenewalWaveRootOutgoingHardStartQuietStep
        ring root s hn hsmallFive hs z hz hwave
        hrequested hzero
    · have hpositive : 0 < (z.2.1 root).siLease.val := by omega
      exact widthWordRenewalWaveRootOutgoingSoftStartQuietStep
        ring root s hn hsmallFive hs z hz hrequested hpositive
  · exact widthWordRenewalWaveRootOutgoingFinishQuietStep
      ring root s hn hsmallFive hs z hz
      hfinish.1 hfinish.2.1 hfinish.2.2.1
      hfinish.2.2.2
  · obtain ⟨hrun, hrootB, hout, hchildB⟩ := hcovered
    exact widthWordRenewalWaveRootOutgoingCoveredQuietStep
      ring root s hn hsmallFive hs z hz hwave
      hrun hrootB hout hchildB

end

section
open Classical

/-- Width port of `bankWordRenewalWaveInternalUnvisitedQuietStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalLineageQuietStepOfMovingRows`.
 An unvisited nonroot pair cannot coexist with RETURN when
scrub=n: its source would be both visited and remote. For a
FORWARD witness the physical transport remains FORWARD and is
incompatible with any newly asserted RETURN shape. Consumer:
unvisitedSuffix INTERNAL class, including the strong quiet clause. -/
theorem widthWordRenewalWaveInternalUnvisitedQuietStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
  have hbase := widthWordRenewalFrontierWaveUnvisitedNonrootStep
    ring root e s hn hsmallFive hs z hz he hj hwave.wave
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
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 e) :=
    ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
      z.2.1 hclass e).2
  have hno := widthWordRootNonrootHardAcceptFalse
    ring hn hsmallFive root s hs z hz e he
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
  · exact False.elim (widthWordRenewalWaveForwardExcludesReturn
      ring root (bankWordEpochNext ring root z e).2.1
      g gnew hfnew hrnew)
  · have hF : g.stage = .forward := hforward.isForward
    have hR : g.stage = .returning := hrnew.isReturn
    rw [hF] at hR
    cases hR

end

section
open Classical

/-- Width port of `bankWordRenewalWaveFullFrameQuietStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveInternalCoveredDoneQuietStep`, `widthWordRenewalWaveInternalNonBToCQuietStep`, `widthWordRenewalWaveInternalPendingQuietStep`.
 If a whole selected pair frames every serializer and
historical validation ticket, and the EWord physical shape
transports without moving its ghost, then ALL five ledger
clauses and the stronger all-RETURN quiet clause frame.
Consumer: real internal B/DONE+B S2N idle subrow. -/
theorem widthWordRenewalWaveFullFrameQuietStep {n : Nat}
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
    widthWordRenewalWaveReturnShapeSiteFrame
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

end

section
open Classical

/-- Width port of `bankWordRenewalWaveInternalCoveredDoneQuietStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalLineageQuietStepOfMovingRows`.
 An INTERNAL B/DONE+B S2N service is genuinely stationary
on both serializer records and historical tickets. EWord
validationTransport and the literal stationary ghost equation
complete the whole strengthened J-W step, without assumptions
about arbitrary unvisited scratch. Consumer: coveredInside idle
arm of the INTERNAL edge induction. -/
theorem widthWordRenewalWaveInternalCoveredDoneQuietStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
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
  exact widthWordRenewalWaveFullFrameQuietStep
    ring root e z hwave hserial hticket hshape

end

section
open Classical

/-- Width port of `bankWordRenewalWaveInternalCanonicalCleanupStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveInternalCanonicalQuietStep`, `widthWordRenewalWaveInternalCanonicalRootLineageStep`.
 On a nonroot S3/S4 service with C/F source and B/F
responder, the actual right record is canonical C/OFF/NONE,
the right ticket is deleted, and the left ticket frames.
This deliberately deletes an obsolete B/returned F obligation:
the new C/NONE does not trigger any of the five covered-site
ticket clauses. Consumer: S3/S4 coveredInside cleanup. -/
theorem widthWordRenewalWaveInternalCanonicalCleanupStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 e) :=
    ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
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

end

section
open Classical

/-- Width port of `bankWordRenewalWaveInternalNonBToCQuietStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveInternalChallengedChildQuietStep`, `widthWordRenewalWaveInternalReturnCoveredQuietStep`. -/
theorem widthWordRenewalWaveInternalNonBToCQuietStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 e) :=
    ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
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
  exact widthWordRenewalWaveFullFrameQuietStep
    ring root e z hwave hserial hticket hshape

end

section
open Classical

/-- Width port of `bankWordRenewalWaveRootOutgoingPendingQuietStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveRootOutgoingActiveQuietStep`. -/
theorem widthWordRenewalWaveRootOutgoingPendingQuietStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 root) :=
    ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
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
  exact widthWordRenewalWaveFullFrameQuietStep
    ring root root z hwave hserial hticket hshape

end

section
open Classical

/-- Width port of `bankWordRenewalWaveInternalObservedChildQuietStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveInternalChallengedChildQuietStep`. -/
theorem widthWordRenewalWaveInternalObservedChildQuietStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
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
  exact False.elim (widthWordRenewalWaveForwardExcludesReturn
    ring root (bankWordEpochNext ring root z e).2.1
    g gnew hnewForward hreturn)

end

section
open Classical

/-- Width port of `bankWordRenewalWaveInternalPendingQuietStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveInternalFrontierParentQuietStep`. -/
theorem widthWordRenewalWaveInternalPendingQuietStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
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
  exact widthWordRenewalWaveFullFrameQuietStep
    ring root e z hwave hserial hticket hshape

end

section
open Classical

/-- Width port of `bankWordRenewalWaveInternalCanonicalRootLineageStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveInternalCanonicalQuietStep`. -/
theorem widthWordRenewalWaveInternalCanonicalRootLineageStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
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
  have hsourceLedger := (widthWordRenewalWaveInternalCanonicalCleanupStep
    ring root e s hn hsmallFive hs z hz he hj hsource htarget).2.2
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

end

section
open Classical

/-- Width port of `bankWordRenewalWaveRootOutgoingInternalQuietStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveRootOutgoingActiveQuietStep`. -/
theorem widthWordRenewalWaveRootOutgoingInternalQuietStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root
      (phiW ring z.2.1 root) :=
    ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
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
    exact False.elim (widthWordRenewalWaveForwardExcludesReturn
      ring root (bankWordEpochNext ring root z root).2.1
      { g with pivot := g.pivot + 1 } gnew hfNew hreturn)

end

section
open Classical

/-- Width port of `bankWordRenewalWaveRootOutgoingActiveQuietStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalLineageRootMovingStepHolds`. -/
theorem widthWordRenewalWaveRootOutgoingActiveQuietStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
        exact widthWordRenewalWaveRootOutgoingPendingQuietStep
          ring root s hn hsmallFive hs z hz hwave
          hactive.1 hrootB hrootWait hc hprobe
      · have hprobe :
            (z.2.1 (ring.rightNeighbor root)).ser.probe =
              .INTERNAL_OK := by
          simpa [hpivot, L3.EWord.siteOne] using hinter.2.1
        exact widthWordRenewalWaveRootOutgoingInternalQuietStep
          ring root s hn hsmallFive hs z hz hwave
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
      exact widthWordRenewalWaveRootOutgoingCoveredQuietStep
        ring root s hn hsmallFive hs z hz hwave
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
      exact widthWordRenewalWaveRootOutgoingFinishQuietStep
        ring root s hn hsmallFive hs z hz
        hcertNotRequested hrootB hout hchildF
    · have hlt : 1 < g.pivot := by
        have hpositive := hr.pivotPositive
        omega
      have hchildB :
          (z.2.1 (ring.rightNeighbor root)).ser.phase = .B := by
        simpa only [L3.EWord.siteOne] using
          (hr.completed
            (⟨1, (show 1 < n by omega)⟩ : Fin n) hlt).1
      exact widthWordRenewalWaveRootOutgoingCoveredQuietStep
        ring root s hn hsmallFive hs z hz hwave
        hactive.1 hrootB hout hchildB

end

section
open Classical

/-- Width port of `bankWordRenewalWaveInternalFrontierNewQuietStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveInternalFrontierParentQuietStep`. -/
theorem widthWordRenewalWaveInternalFrontierNewQuietStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
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
  exact False.elim (widthWordRenewalWaveForwardExcludesReturn
    ring root (bankWordEpochNext ring root z e).2.1
    { g with scrub := g.scrub + 1 } gnew hfNew hreturn)

end

section
open Classical

/-- Width port of `bankWordRenewalWaveInternalCanonicalQuietStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalWaveInternalChallengedChildQuietStep`, `widthWordRenewalWaveInternalReturnCoveredQuietStep`. -/
theorem widthWordRenewalWaveInternalCanonicalQuietStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
  have hbase := widthWordRenewalWaveInternalCanonicalRootLineageStep
    ring root e s hn hsmallFive hs z hz hwave he hj hsource htarget
  have hcleanup := widthWordRenewalWaveInternalCanonicalCleanupStep
    ring root e s hn hsmallFive hs z hz he hj hsource htarget
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z hz
  have hfixed : WFixedRoot ring root (phiW ring z.2.1 e) :=
    ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
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
  · exact False.elim (widthWordRenewalWaveForwardExcludesReturn
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

end

section
open Classical

/-- Width port of `bankWordRenewalSoftOwnerFlags`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalSoftIncomingFlags`, `widthWordRenewalSoftInternalFlags`, `widthWordRenewalSoftOutgoingFlags`.
 For a reachable post-S1 state, exactly one physical owner
    flag pair is active. No serializer row is assumed in this
    case split. Consumer: feeding all soft S-frontier row lemmas
    their literal postW flags. -/
theorem widthWordRenewalSoftOwnerFlags {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z.1 z.2.1
  have hfixed : WFixedRoot ring root (phiW ring z.1.2.1 e) :=
    ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
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

end

section
open Classical

/-- Width port of `bankWordRenewalSoftIncomingRowCensus`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalSoftReturnIncomingStep`. -/
theorem widthWordRenewalSoftIncomingRowCensus {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordRenewalPostSOne ring root s)
    (hpred : ring.rightNeighbor e = root) :
    ((z.1.2.1 root).ser.cert = .IDLE ∧
      (bankWordEpochSelectedReceipt ring z.1 e).serializer.row =
        "S0") ∨
    ((z.1.2.1 root).ser.cert ≠ .IDLE ∧
      (bankWordEpochSelectedReceipt ring z.1 e).serializer.row =
        "S5") := by
  have hclass := widthWordEpochReachablePhysicalRootClass
    ring hn hsmallFive root s hs z.1 z.2.1
  have hfixed : WFixedRoot ring root (phiW ring z.1.2.1 e) :=
    ((widthWordSerializerRootClassClosed ring hn hsmallFive root).2
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

end

section
open Classical

/-- Width port of `bankWordRenewalSoftInternalFlags`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalSoftForwardAllEdgesStep`, `widthWordRenewalSoftForwardCoveredStep`, `widthWordRenewalSoftForwardParentStep`. -/
theorem widthWordRenewalSoftInternalFlags {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordRenewalPostSOne ring root s)
    (he : e ≠ root) (hj : ring.rightNeighbor e ≠ root) :
    (postW (z.1.2.1 e)
      (z.1.2.1 (ring.rightNeighbor e))).eX.l = false ∧
    (postW (z.1.2.1 e)
      (z.1.2.1 (ring.rightNeighbor e))).eY.l = false := by
  rcases widthWordRenewalSoftOwnerFlags
      ring root s hn hsmallFive hs z e with ho | hi | ht
  · exact False.elim (he ho.1)
  · exact False.elim (hj hi.2.1)
  · exact ⟨ht.2.2.1, ht.2.2.2⟩

end

section
open Classical

/-- Width port of `bankWordRenewalSoftIncomingFlags`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalSoftForwardAllEdgesStep`, `widthWordRenewalSoftForwardLeafSeamStep`, `widthWordRenewalSoftInactiveAllEdgesStep`.
 The actual ROOT_IN native flags, not a paper annotation.
    Consumer: S0/S5 soft-frontier seam rows. -/
theorem widthWordRenewalSoftIncomingFlags {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordRenewalPostSOne ring root s)
    (he : e ≠ root) (hpred : ring.rightNeighbor e = root) :
    (postW (z.1.2.1 e)
      (z.1.2.1 (ring.rightNeighbor e))).eX.l = false ∧
    (postW (z.1.2.1 e)
      (z.1.2.1 (ring.rightNeighbor e))).eY.l = true := by
  rcases widthWordRenewalSoftOwnerFlags
      ring root s hn hsmallFive hs z e with ho | hi | ht
  · exact False.elim (he ho.1)
  · exact ⟨hi.2.2.1, hi.2.2.2⟩
  · exact False.elim (ht.2.1 hpred)

end

section
open Classical

/-- Width port of `bankWordRenewalSoftOutgoingFlags`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalSoftForwardAllEdgesStep`, `widthWordRenewalSoftInactiveRootOutgoingBStep`, `widthWordRenewalSoftReturnAllEdgesStep`.
 Native ROOT_OUT service flags at the selected root.
    Consumer: S1/SR/S2R/S6 soft-frontier case routing. -/
theorem widthWordRenewalSoftOutgoingFlags {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
    (z : BankWordRenewalPostSOne ring root s) :
    (postW (z.1.2.1 root)
      (z.1.2.1 (ring.rightNeighbor root))).eX.l = true ∧
    (postW (z.1.2.1 root)
      (z.1.2.1 (ring.rightNeighbor root))).eY.l = false := by
  rcases widthWordRenewalSoftOwnerFlags
      ring root s hn hsmallFive hs z root with ho | hi | ht
  · exact ⟨ho.2.1, ho.2.2⟩
  · exact False.elim (hi.1 rfl)
  · exact False.elim (ht.1 rfl)

end

section
open Classical

/-- Width port of `bankWordRenewalSoftForwardCoveredStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalSoftForwardAllEdgesStep`.
 Every covered forward INTERNAL B/DONE+B service is a true
    serializer frame, and it cannot be the nominated positive-
    increment edge. Consumer: covered-prefix branch of the
    R10a one-edge position/nomination theorem. -/
theorem widthWordRenewalSoftForwardCoveredStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
  have hflags := widthWordRenewalSoftInternalFlags
    ring root (L3.EWord.site ring root k)
    s hn hsmallFive hs z he hj
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

end

section
open Classical

/-- Width port of `bankWordRenewalSoftReturnCoveredStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalSoftReturnAllEdgesStep`.
 The return prefix is also a true B/DONE+B internal frame
    and its source differs from the fallback-root nomination.
    Consumer: RETURN covered-prefix all-edge case. -/
theorem widthWordRenewalSoftReturnCoveredStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
  have hflags := widthWordRenewalSoftInternalFlags
    ring root (L3.EWord.site ring root k)
    s hn hsmallFive hs z he hj
  have hframe := bankWordRenewalSoftCoveredDoneFrameStep
    ring root (L3.EWord.site ring root k)
    z.1 hn hb hd hchildB hflags.1 hflags.2 hshape
  have hchosen := bankWordRenewalSoftReturnNomination
    ring root s z q hr
  refine ⟨hframe.1, hframe.2, ?_⟩
  rw [hchosen]
  exact he

end

section
open Classical

/-- Width port of `bankWordRenewalSoftReturnParentStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalSoftReturnAllEdgesStep`.
 An actual positive return pivot is an INTERNAL S2N
    B/DONE-to-F transition. It preserves the paid position,
    so any nonzero-position-change implication is vacuous.
    Consumer: returning-parent branch of R10a S-frontier. -/
theorem widthWordRenewalSoftReturnParentStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
  have hflags := widthWordRenewalSoftInternalFlags
    ring root (L3.EWord.site ring root q)
    s hn hsmallFive hs z hsourceNonroot htargetNonroot
  have hstep := bankWordRenewalSoftReturnStep
    ring root s z q hn hq hr hflags.1 hflags.2
  refine ⟨hstep.1, ?_, ?_⟩
  · rw [hstep.2.1]
    omega
  · intro hne
    exact False.elim (hne hstep.2.1)

end

section
open Classical

/-- Width port of `bankWordRenewalSoftRootFirstStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalSoftForwardAllEdgesStep`. -/
theorem widthWordRenewalSoftRootFirstStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
  have hflags := widthWordRenewalSoftOutgoingFlags
    ring root s hn hsmallFive hs z
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

end

section
open Classical

/-- Width port of `bankWordRenewalSoftRootFinishStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalSoftReturnAllEdgesStep`.
 An actual soft ROOT_OUT S6 from the last return pivot
    resets position to zero and closes the active root.
    The only decreasing position service is itself nominated
    by the fallback root. Consumer: R10a lap-end boundary. -/
theorem widthWordRenewalSoftRootFinishStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
  have hflags := widthWordRenewalSoftOutgoingFlags
    ring root s hn hsmallFive hs z
  have hstep := bankWordRenewalSoftRootOutgoingFinishStep
    ring root s z hn hr hflags.1 hflags.2
  refine ⟨hstep.1, ?_, ?_⟩
  · rw [hstep.2.1, hstep.2.2.1]
    omega
  · intro _
    exact hstep.2.2.2.1.symm

end

section
open Classical

/-- Width port of `bankWordRenewalSoftRootEntryStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalSoftInactiveAllEdgesStep`.
 Native ROOT_OUT requested starts or C/F recoveries
    cannot debit a new frontier position. Consumer: the
    nonactive ROOT_OUT S1 and SR branch of R10a. -/
theorem widthWordRenewalSoftRootEntryStep {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
  have hflags := widthWordRenewalSoftOutgoingFlags
    ring root s hn hsmallFive hs z
  have hstep := bankWordRenewalSoftRootEntryAndRecovery
    ring root z.1 (by omega : 3 ≤ n)
    hflags.1 hflags.2 hcase
  exact ⟨hstep.1, hstep.2.2⟩

end

section
open Classical

/-- Width port of `bankWordRenewalSoftInactiveIncomingStep`: the BANK band premise is replaced by `5 ≤ n`, and the renewal constants are those of the compiled width t (lease 8t+4, quota 2t+1). Consumer: `widthWordRenewalSoftInactiveAllEdgesStep`. -/
theorem widthWordRenewalSoftInactiveIncomingStep {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (s : Fin n → ProjW (compileAdvice (ceilLogTwo n)))
    (hn : 5 ≤ n)
    (hsmallFive : 5 ≤ n)
    (hs : WidthWordSerializerRootClass ring hsmallFive root s)
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
  have hflags := widthWordRenewalSoftIncomingFlags
    ring root e s hn hsmallFive hs z he hpred
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

end

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.widthWordRenewalFrontierFreshBankPrepared
#print axioms L3.RenewalReferenceClock.widthWordRenewalFrontierFreshBankForeignFree
#print axioms L3.RenewalReferenceClock.widthWordRenewalFrontierFreshRootIdle
#print axioms L3.RenewalReferenceClock.widthWordRenewalFrontierFreshPhysicalShape
#print axioms L3.RenewalReferenceClock.widthWordRenewalFrontierIncomingRequestTicket
#print axioms L3.RenewalReferenceClock.widthWordRenewalFrontierHardStartTicketPair
#print axioms L3.RenewalReferenceClock.widthWordRenewalFrontierHardAcceptOfTicketLineage
#print axioms L3.RenewalReferenceClock.widthWordRenewalFrontierFreshShapeOnBank
#print axioms L3.RenewalReferenceClock.widthWordRenewalFrontierShapePrefixNoRoot
#print axioms L3.RenewalReferenceClock.widthWordRenewalFrontierWaveHardAcceptGenuine
#print axioms L3.RenewalReferenceClock.widthWordRenewalFrontierWaveUnvisitedNonrootStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveRootIncomingInactiveStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveRootOutgoingFinishStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveRootOutgoingSoftStartStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveRootOutgoingHardStartStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveRootIncomingActiveFrameStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveRootIncomingLeafStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveRootOutgoingCoveredFrameStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveRootIncomingShortCoveredFrameStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveRootIncomingSameWaveLeafStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveRootIncomingCoveredForwardStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveRootIncomingShortStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveRootIncomingQuietSourceFrame
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveRootIncomingQuietStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveRootIncomingGuardedStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalSoftShapeSeed
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveForwardExcludesReturn
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveReturnShapeSiteFrame
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveIncomingIsSeam
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveReturnSeamQuiet
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveRootIncomingActiveWasOld
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveRootOutgoingHardStartQuietStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveRootOutgoingFinishQuietStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveRootOutgoingCoveredQuietStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveRootIncomingStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveRootOutgoingSoftStartQuietStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveRootOutgoingKnownRowsStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveInternalUnvisitedQuietStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveFullFrameQuietStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveInternalCoveredDoneQuietStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveInternalCanonicalCleanupStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveInternalNonBToCQuietStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveRootOutgoingPendingQuietStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveInternalObservedChildQuietStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveInternalPendingQuietStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveInternalCanonicalRootLineageStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveRootOutgoingInternalQuietStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveRootOutgoingActiveQuietStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveInternalFrontierNewQuietStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalWaveInternalCanonicalQuietStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalSoftOwnerFlags
#print axioms L3.RenewalReferenceClock.widthWordRenewalSoftIncomingRowCensus
#print axioms L3.RenewalReferenceClock.widthWordRenewalSoftInternalFlags
#print axioms L3.RenewalReferenceClock.widthWordRenewalSoftIncomingFlags
#print axioms L3.RenewalReferenceClock.widthWordRenewalSoftOutgoingFlags
#print axioms L3.RenewalReferenceClock.widthWordRenewalSoftForwardCoveredStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalSoftReturnCoveredStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalSoftReturnParentStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalSoftRootFirstStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalSoftRootFinishStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalSoftRootEntryStep
#print axioms L3.RenewalReferenceClock.widthWordRenewalSoftInactiveIncomingStep
