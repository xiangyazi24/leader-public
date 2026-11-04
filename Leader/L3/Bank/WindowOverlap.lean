import Leader.L3.Bank.WindowClosure

/-!
R11 group 13: global/disjoint read-set assembly and the portions of
inherited-carrier and incoming-root overlap derivable from OLD reachable J.

The selected pair is always the actual renewalBankNext edge from
rbRun ring (renewalBankStart ring seed) pre.  In particular, no
post-step BankWindowExact field is taken as a hypothesis.

The inherited compatibility theorem below establishes the non-taint
and authenticated-root consequences, NOT the still-open preservation of
every incident foreign proto/read obligation.  The incoming joint
theorem proves physical/ghost digit framing and simultaneous source
provenance, NOT the still-open complete post-J incoming-root case split.
-/

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The OLD reference used by every group-13 consumer. -/
private abbrev bankWindowOverlapBefore {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) : RenewalBankReference n :=
  rbRun ring (renewalBankStart ring seed) pre

/-- The single actual successor of the OLD snapshot. -/
private abbrev bankWindowOverlapAfter {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) (e : Fin n) : RenewalBankReference n :=
  renewalBankNext ring (bankWindowOverlapBefore ring seed pre) e

/-! Item 1: group-1 global facts and the exact disjoint read masks. -/

/-- Group-13 F/A: the global J frame and both payload fields at the
selected successor, together with the complete sixteen-field
read-set implication contract and an arbitrary disjoint site's
full physical/ghost frame.  Consumer: group-13 foreign-hit split and
bankWindowExactOverlapStep.  The read-set contract only concludes an
individual J clause when its component mask agrees. -/
theorem bankWindowOverlapGlobalAndDisjoint
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowOverlapBefore ring seed pre)) :
    BankInFlightAligned ring (bankWindowOverlapAfter ring seed pre e) ∧
    (∀ (i : Fin n) (p : RenewalBankPayload n),
      p ∈ rbSiteLivePayloads
        ((bankWindowOverlapAfter ring seed pre e).2.sites i) →
      p.origin = none → p.atoms ≠ [] ∧ p.heads = 0) ∧
    (∀ (i : Fin n) (p : RenewalBankPayload n)
      (o : RenewalBankOrigin n),
      p ∈ rbSiteLivePayloads
        ((bankWindowOverlapAfter ring seed pre e).2.sites i) →
      p.origin = some o → p.atoms = []) ∧
    BankWindowExactReadSetContract ring
      (bankWindowOverlapBefore ring seed pre)
      (bankWindowOverlapAfter ring seed pre e) ∧
    (∀ readSite : Fin n → Prop,
      (∀ z, readSite z →
        z ≠ e ∧ z ≠ ring.rightNeighbor e) →
      ∀ z, readSite z →
        (bankWindowOverlapAfter ring seed pre e).1 z =
          (bankWindowOverlapBefore ring seed pre).1 z ∧
        (bankWindowOverlapAfter ring seed pre e).2.sites z =
          (bankWindowOverlapBefore ring seed pre).2.sites z) := by
  have hf := bankWindowExactFrameStep
    ring hn hbank seed pre e hJ
  have hp := bankWindowExactSelectedPayloadStep
    ring hn hbank seed pre e hJ
  have hread := bankWindowExactReadSetTransport ring
    (bankWindowOverlapBefore ring seed pre)
    (bankWindowOverlapAfter ring seed pre e) hJ
  refine ⟨hf, hp.1, hp.2, hread, ?_⟩
  intro readSite hdisjoint z hz
  exact bankWindowExactDisjointSitesFrame ring
    (bankWindowOverlapBefore ring seed pre) e
    readSite hdisjoint z hz

/-! A real-run ReceiptInv witness also exists after the selected
edge.  This is obtained by running the proved receipt invariant over
the actual extended schedule, not by assuming post J. -/

/-- Receipt provenance on the SAME post-selected BANK reference.
Consumer: group-13 inherited/genuine carrier compatibility and
the incoming/outgoing ownership check. -/
theorem bankWindowOverlapPostReceipt
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n) :
    ReceiptInv ring seed (pre ++ [e])
      (bankWindowOverlapAfter ring seed pre e) := by
  have hreceipt := rbReceiptInvBankWordOfInv
    ring (by omega : 2 ≤ n) seed hbank (pre ++ [e])
  have hphysical :
      rbRun ring (renewalBankStart ring seed) (pre ++ [e]) =
        bankWindowOverlapAfter ring seed pre e := by
    rw [rbRunAppend]
    rfl
  rw [hphysical] at hreceipt
  exact hreceipt

/-! Item 3: consequences for inherited payloads and for any
authenticated carrier at an aligned (possibly incomplete) digit. -/

/-- Group-13 U/P/G: an unowned payload copied or retained at any
post-step worker site has the exact inherited payload shape and
cannot itself witness BankWindowTainted.  At an aligned post-step
digit, every pending receipt and genuinely originated payload has
that digit's own fixed-offset root.  No complete-window premise is
needed.  Consumer: foreign proto/orphan and comparator row splits.

This does not claim that an inherited IR/RR/CR token cannot change
another root's physical bit or token, and does not close all foreign
incident read obligations. -/
theorem bankWindowOverlapInheritedCarrierCompatibility
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowOverlapBefore ring seed pre)) :
    (∀ (z : Fin n) (p : RenewalBankPayload n),
      ((bankWindowOverlapAfter ring seed pre e).2.sites z).worker =
        .payload p →
      p.origin = none →
      p.atoms ≠ [] ∧ p.heads = 0 ∧
        ¬ BankWindowTainted (bankWindowOverlapAfter ring seed pre e) z) ∧
    (∀ (c z : Fin n) (k : Nat),
      1 ≤ k → k ≤ (compileAdvice (ceilLogTwo n)).b →
      z = Counter.site ring c k →
      ((bankWindowOverlapAfter ring seed pre e).1 z).pack.val = k →
      (∀ rho : RenewalBankReceipt n,
        ((bankWindowOverlapAfter ring seed pre e).2.sites z).worker =
          .pending rho → rho.root = c) ∧
      (∀ (p : RenewalBankPayload n) (o : RenewalBankOrigin n),
        ((bankWindowOverlapAfter ring seed pre e).2.sites z).worker =
          .payload p →
        p.origin = some o → o.root = c)) := by
  have hp := bankWindowExactSelectedPayloadStep
    ring hn hbank seed pre e hJ
  have hreceipt := bankWindowOverlapPostReceipt
    ring hn hbank seed pre e
  constructor
  · intro z p hw ho
    have hlive : p ∈ rbSiteLivePayloads
        ((bankWindowOverlapAfter ring seed pre e).2.sites z) := by
      simp [rbSiteLivePayloads, hw]
    have hshape := hp.1 z p hlive ho
    refine ⟨hshape.1, hshape.2, ?_⟩
    intro ht
    rcases ht with ⟨rho, hpend⟩ | ⟨q, o, hworker, horigin⟩
    · rw [hw] at hpend
      cases hpend
    · rw [hw] at hworker
      cases hworker
      rw [ho] at horigin
      cases horigin
  · intro c z k hk hb hsite hpack
    exact bankWindowOverlapAlignedCarrierOwnRoot ring
      seed (pre ++ [e])
      (bankWindowOverlapAfter ring seed pre e)
      hreceipt c z k hk hb hsite hpack

/-! Item 4: simultaneous incoming responder-root digit snapshot
and outgoing top-source authentication on the SAME selected pair. -/

/-- Group-13 IN/B0: on an edge whose OLD responder has PACK zero,
all digits of the incoming root retain their exact OLD physical
agents and ghost sites. If the responder PACK changes, its complete
scope, proto and orphan antecedents become false. If PACK remains
zero, a surviving source worker cannot be genuinely rooted at that
incoming responder.

Simultaneously, any source that is an OLD aligned top digit of a
second root has that second root's provenance at both the OLD and
POST source endpoints, and the two roots are distinct.  All claims
are made about ONE renewalBankNext edge; no sequential simulation
or assumed post-J field occurs.  Consumer: group-13 incoming/top
boundary and foreign-origin comparison split.

The still-unproved incoming-root phaseFlags/proto/orphan clauses when
the root's mode changes are not asserted here. -/
theorem bankWindowOverlapIncomingRootJoint
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowOverlapBefore ring seed pre)) :
    ((bankWindowOverlapBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = 0 →
    BankInFlightAligned ring (bankWindowOverlapAfter ring seed pre e) ∧
    (∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice (ceilLogTwo n)).b →
      (bankWindowOverlapAfter ring seed pre e).1
        (Counter.site ring (ring.rightNeighbor e) j) =
        (bankWindowOverlapBefore ring seed pre).1
          (Counter.site ring (ring.rightNeighbor e) j) ∧
      (bankWindowOverlapAfter ring seed pre e).2.sites
        (Counter.site ring (ring.rightNeighbor e) j) =
        (bankWindowOverlapBefore ring seed pre).2.sites
          (Counter.site ring (ring.rightNeighbor e) j)) ∧
    (((bankWindowOverlapAfter ring seed pre e).1
      (ring.rightNeighbor e)).pack.val ≠ 0 →
      ¬ BankWindowScope ring (bankWindowOverlapAfter ring seed pre e)
        (ring.rightNeighbor e) ∧
      (∀ limit : Nat,
        ¬ BankWindowProtoRun ring
          (bankWindowOverlapAfter ring seed pre e)
          (ring.rightNeighbor e) limit) ∧
      (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        ¬ BankWindowOrphanOwner ring
          (bankWindowOverlapAfter ring seed pre e)
          (ring.rightNeighbor e) j)) ∧
    (∀ (p : RenewalBankPayload n) (o : RenewalBankOrigin n),
      o.root = ring.rightNeighbor e →
      ((bankWindowOverlapAfter ring seed pre e).1
        (ring.rightNeighbor e)).pack.val = 0 →
      ((bankWindowOverlapAfter ring seed pre e).2.sites e).worker =
        .payload p →
      p.origin = some o → False) ∧
    (∀ a : Fin n,
      e = Counter.site ring a
        (compileAdvice (ceilLogTwo n)).b →
      ((bankWindowOverlapBefore ring seed pre).1 e).pack.val =
        (compileAdvice (ceilLogTwo n)).b →
      a ≠ ring.rightNeighbor e ∧
      (∀ (p : RenewalBankPayload n) (o : RenewalBankOrigin n),
        ((bankWindowOverlapBefore ring seed pre).2.sites e).worker =
          .payload p →
        p.origin = some o → o.root = a) ∧
      (∀ (p : RenewalBankPayload n) (o : RenewalBankOrigin n),
        ((bankWindowOverlapAfter ring seed pre e).2.sites e).worker =
          .payload p →
        p.origin = some o → o.root = a)) := by
  intro hy
  have hcore := bankWindowIncomingRootCoreStep
    ring hn hbank seed pre e hJ hy
  have hreceipt := rbReceiptInvBankWordOfInv
    ring (by omega : 2 ≤ n) seed hbank pre
  have hpostReceipt := bankWindowOverlapPostReceipt
    ring hn hbank seed pre e
  have hsourcePack := bankWindowClosureRepairNonresponderPackFixed
    ring (by omega : 2 ≤ n)
    (bankWindowOverlapBefore ring seed pre) e e
    (clockNeighborDifferent ring (by omega : 2 ≤ n) e).symm
  refine ⟨hcore.1, ?_, ?_, ?_, ?_⟩
  · intro j hj hb
    exact bankWindowIncomingDigitReadSetFrame ring hbank
      (bankWindowOverlapBefore ring seed pre)
      (ring.rightNeighbor e) e rfl j hj hb
  · intro hchanged
    have hx := hcore.2.2.2.2.1 hchanged
    exact ⟨hx.2.1, hx.2.2.2.1, hx.2.2.2.2.1⟩
  · intro p o horoot hpostPack hw ho
    exact bankWindowIncomingSourceNoResponderOrigin
      ring hn hbank seed pre e hy hpostPack p o horoot hw ho
  · intro a hsite htop
    have hbpos : 1 ≤ (compileAdvice (ceilLogTwo n)).b := by
      change 1 ≤ (compileAdvice (ceilLogTwo n)).s + 11
      omega
    have hne : a ≠ ring.rightNeighbor e := by
      intro ha
      have houtside :=
        bankWindowIncomingPredecessorOutsideDigits
          ring hbank (ring.rightNeighbor e) e rfl
          (compileAdvice (ceilLogTwo n)).b hbpos (Nat.le_refl _)
      apply houtside
      rw [← ha]
      exact hsite
    have holdOwn := bankWindowOverlapAlignedCarrierOwnRoot
      ring seed pre
      (bankWindowOverlapBefore ring seed pre)
      hreceipt a e (compileAdvice (ceilLogTwo n)).b
      hbpos (Nat.le_refl _) hsite htop
    have hpostTop :
        ((bankWindowOverlapAfter ring seed pre e).1 e).pack.val =
          (compileAdvice (ceilLogTwo n)).b :=
      hsourcePack.trans htop
    have hpostOwn := bankWindowOverlapAlignedCarrierOwnRoot
      ring seed (pre ++ [e])
      (bankWindowOverlapAfter ring seed pre e)
      hpostReceipt a e (compileAdvice (ceilLogTwo n)).b
      hbpos (Nat.le_refl _) hsite hpostTop
    exact ⟨hne, holdOwn.2, hpostOwn.2⟩

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Group-13 PFX, the incident *first-mismatch boundary* case.
If the selected source is the first wrong PACK site of the post
proto prefix, the source PACK read is preserved and every other
proto read is off-pair. If the selected responder is that wrong
site, the actual packNext row forces its PACK correct, contradicting
the post proto antecedent. Consequently all four J.proto clauses
hold in both boundary incidences, with no post-J hypothesis.
Consumer: the PFX case split in bankWindowExactOverlapStep.
The interior RR/IR/CR service cases are not asserted here. -/
theorem bankWindowOverlapProtoForeignInterior
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n) (limit : Nat)
    (hJ : BankWindowExact ring
      (bankWindowOverlapBefore ring seed pre))
    (hboundary :
      e = Counter.site ring root (limit + 1) ∨
      ring.rightNeighbor e = Counter.site ring root (limit + 1))
    (hproto : BankWindowProtoRun ring
      (bankWindowOverlapAfter ring seed pre e) root limit) :
    (∀ p o,
      ((bankWindowOverlapAfter ring seed pre e).2.sites root).controller =
        .active p → p.origin = some o → False) ∧
    (BankWindowInheritedController
        (bankWindowOverlapAfter ring seed pre e) root →
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        j.val + 1 ≤ limit →
        ¬ BankWindowTainted (bankWindowOverlapAfter ring seed pre e)
          (Counter.site ring root (j.val + 1))) ∧
    ((((bankWindowOverlapAfter ring seed pre e).1 root).mode =
        .RWAIT ∧
        ((bankWindowOverlapAfter ring seed pre e).2.sites root).controller =
          .waiting []) →
      ∃ j : Fin (compileAdvice (ceilLogTwo n)).b,
        j.val + 1 ≤ limit ∧
        ∃ rho : RenewalBankReceipt n,
          ((bankWindowOverlapAfter ring seed pre e).2.sites
            (Counter.site ring root (j.val + 1))).worker =
              .pending rho ∧
          ((bankWindowOverlapAfter ring seed pre e).1
            (Counter.site ring root (j.val + 1))).tok = .RR ∧
          bankWindowZeroPrefix ring
            (bankWindowOverlapAfter ring seed pre e)
            root (j.val + 1) ∧
          (∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
            k.val < j.val →
            ((bankWindowOverlapAfter ring seed pre e).1
              (Counter.site ring root (k.val + 1))).tok = .E)) ∧
    (((bankWindowOverlapAfter ring seed pre e).1 root).mode ≠ .RESET →
      ((bankWindowOverlapAfter ring seed pre e).1 root).mode ≠ .RWAIT →
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        j.val + 1 ≤ limit →
        ¬ BankWindowTainted (bankWindowOverlapAfter ring seed pre e)
          (Counter.site ring root (j.val + 1))) := by
  have hlimit : limit < (compileAdvice (ceilLogTwo n)).b := hproto.1
  rcases hboundary with hsource | hresponder
  · have hnextSite :
        ring.rightNeighbor e = Counter.site ring root (limit + 2) := by
      rw [hsource]
      rfl
    have hpack :
        bankWindowReadPackPrefix ring
          (bankWindowOverlapBefore ring seed pre)
          (bankWindowOverlapAfter ring seed pre e)
          root (limit + 1) := by
      intro k hk
      have hnot :
          Counter.site ring root k ≠ ring.rightNeighbor e := by
        rw [hnextSite]
        exact bankWindowIncidenceSiteDistinct
          ring hbank root k (limit + 2)
          (by omega) (by omega)
      exact bankWindowClosureRepairNonresponderPackFixed
        ring (by omega : 2 ≤ n)
        (bankWindowOverlapBefore ring seed pre) e
        (Counter.site ring root k) hnot
    have hrootSource : root ≠ e := by
      rw [hsource]
      have hx := bankWindowIncidenceSiteDistinct
        ring hbank root 0 (limit + 1)
        (by omega) (by omega)
      change root ≠ Counter.site ring root (limit + 1) at hx
      exact hx
    have hrootTarget : root ≠ ring.rightNeighbor e := by
      rw [hnextSite]
      have hx := bankWindowIncidenceSiteDistinct
        ring hbank root 0 (limit + 2)
        (by omega) (by omega)
      change root ≠ Counter.site ring root (limit + 2) at hx
      exact hx
    have hrootFrame := bankWindowExactOffPairFrame ring
      (bankWindowOverlapBefore ring seed pre) e root
      hrootSource hrootTarget
    have hmode : bankWindowReadMode
        (bankWindowOverlapBefore ring seed pre)
        (bankWindowOverlapAfter ring seed pre e) root :=
      congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.mode)
        hrootFrame.1
    have hcontrol : bankWindowReadController
        (bankWindowOverlapBefore ring seed pre)
        (bankWindowOverlapAfter ring seed pre e) root :=
      congrArg (fun a : RenewalBankSite n => a.controller)
        hrootFrame.2
    have hsegment :
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          bankWindowReadTok
            (bankWindowOverlapBefore ring seed pre)
            (bankWindowOverlapAfter ring seed pre e)
            (Counter.site ring root (j.val + 1)) ∧
          bankWindowReadBit
            (bankWindowOverlapBefore ring seed pre)
            (bankWindowOverlapAfter ring seed pre e)
            (Counter.site ring root (j.val + 1)) ∧
          bankWindowReadWorker
            (bankWindowOverlapBefore ring seed pre)
            (bankWindowOverlapAfter ring seed pre e)
            (Counter.site ring root (j.val + 1)) := by
      intro j hj
      have hnotSource :
          Counter.site ring root (j.val + 1) ≠ e := by
        rw [hsource]
        exact bankWindowIncidenceSiteDistinct
          ring hbank root (j.val + 1) (limit + 1)
          (by omega) (by omega)
      have hnotTarget :
          Counter.site ring root (j.val + 1) ≠
            ring.rightNeighbor e := by
        rw [hnextSite]
        exact bankWindowIncidenceSiteDistinct
          ring hbank root (j.val + 1) (limit + 2)
          (by omega) (by omega)
      have hf := bankWindowExactOffPairAtomicReads ring
        (bankWindowOverlapBefore ring seed pre) e
        (Counter.site ring root (j.val + 1))
        hnotSource hnotTarget
      exact ⟨hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.2.1⟩
    exact bankWindowProtoReadTransport ring
      (bankWindowOverlapBefore ring seed pre)
      (bankWindowOverlapAfter ring seed pre e)
      root limit hJ ⟨hpack, hmode, hcontrol, hsegment⟩ hproto
  · have hsourceSite : e = Counter.site ring root limit :=
      Counter.resetTrialSitePredecessor ring root e limit hresponder
    have hpostSource :
        ((bankWindowOverlapAfter ring seed pre e).1 e).pack.val =
          limit := by
      have hp := hproto.2.1 limit (Nat.le_refl limit)
      rw [← hsourceSite] at hp
      exact hp
    have hsourceFixed :=
      bankWindowClosureRepairNonresponderPackFixed
        ring (by omega : 2 ≤ n)
        (bankWindowOverlapBefore ring seed pre) e e
        (clockNeighborDifferent ring (by omega : 2 ≤ n) e).symm
    have hsourceOld :
        ((bankWindowOverlapBefore ring seed pre).1 e).pack.val =
          limit :=
      hsourceFixed.symm.trans hpostSource
    have hrole :
        packNext
          ((bankWindowOverlapBefore ring seed pre).1 e).pack.val
          ((bankWindowOverlapBefore ring seed pre).1
            (ring.rightNeighbor e)).pack.val
          (compileAdvice (ceilLogTwo n)).b = limit + 1 := by
      rw [hsourceOld]
      simp [packNext, hlimit]
    have hresponderPack := bankWindowExactResponderPack ring
      (bankWindowOverlapBefore ring seed pre) e
      (clockNeighborDifferent ring (by omega : 2 ≤ n) e)
    have hcorrect :
        ((bankWindowOverlapAfter ring seed pre e).1
          (Counter.site ring root (limit + 1))).pack.val =
          limit + 1 := by
      rw [← hresponder]
      exact hresponderPack.trans hrole
    exact False.elim (hproto.2.2 hcorrect)

/-- Group-13 ORPH: three genuinely incident PACK/worker cases.
(1) A stable inner-prefix edge may touch PACK-only reads but cannot
change their values; the named orphan worker remains off-pair.
(2) If the responder is the named orphan digit and is repaired
from a wrong PACK to that digit's role, it is clean, hence not tainted.
(3) If the selected source is the named orphan digit and the
responder PACK changes, changed-worker provenance is keep-or-erase;
post taint rules out erase, yielding the OLD orphan worker and
the OLD mode restriction.

Consumer: ORPH case split in bankWindowExactOverlapStep.
The stable-PACK backward-carrier case is not asserted. -/
theorem bankWindowOverlapOrphanForeignInterior
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (hJ : BankWindowExact ring
      (bankWindowOverlapBefore ring seed pre))
    (hcase :
      (∃ k : Nat, 1 ≤ k ∧ k < j.val ∧
        e = Counter.site ring root k ∧
        packNext
          ((bankWindowOverlapBefore ring seed pre).1 e).pack.val
          ((bankWindowOverlapBefore ring seed pre).1
            (ring.rightNeighbor e)).pack.val
          (compileAdvice (ceilLogTwo n)).b =
          ((bankWindowOverlapBefore ring seed pre).1
            (ring.rightNeighbor e)).pack.val) ∨
      (ring.rightNeighbor e = Counter.site ring root (j.val + 1) ∧
        ((bankWindowOverlapBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val ≠ j.val + 1) ∨
      (e = Counter.site ring root (j.val + 1) ∧
        packNext
          ((bankWindowOverlapBefore ring seed pre).1 e).pack.val
          ((bankWindowOverlapBefore ring seed pre).1
            (ring.rightNeighbor e)).pack.val
          (compileAdvice (ceilLogTwo n)).b ≠
          ((bankWindowOverlapBefore ring seed pre).1
            (ring.rightNeighbor e)).pack.val))
    (howner : BankWindowOrphanOwner ring
      (bankWindowOverlapAfter ring seed pre e) root j)
    (htainted : BankWindowTainted
      (bankWindowOverlapAfter ring seed pre e)
      (Counter.site ring root (j.val + 1))) :
    ((bankWindowOverlapAfter ring seed pre e).1 root).mode = .RESET ∨
    (((bankWindowOverlapAfter ring seed pre e).1 root).mode = .RWAIT ∧
      ((bankWindowOverlapAfter ring seed pre e).2.sites root).controller =
        .waiting []) := by
  have hjbound : j.val < (compileAdvice (ceilLogTwo n)).b := j.isLt
  have htransport :
      bankWindowReadPackPrefix ring
        (bankWindowOverlapBefore ring seed pre)
        (bankWindowOverlapAfter ring seed pre e)
        root (j.val + 1) →
      root ≠ e →
      root ≠ ring.rightNeighbor e →
      bankWindowReadWorker
        (bankWindowOverlapBefore ring seed pre)
        (bankWindowOverlapAfter ring seed pre e)
        (Counter.site ring root (j.val + 1)) →
      ((bankWindowOverlapAfter ring seed pre e).1 root).mode = .RESET ∨
      (((bankWindowOverlapAfter ring seed pre e).1 root).mode = .RWAIT ∧
        ((bankWindowOverlapAfter ring seed pre e).2.sites root).controller =
          .waiting []) := by
    intro hp hsourceRoot htargetRoot hworker
    have hf := bankWindowExactOffPairFrame ring
      (bankWindowOverlapBefore ring seed pre) e root
      hsourceRoot htargetRoot
    have hm : bankWindowReadMode
        (bankWindowOverlapBefore ring seed pre)
        (bankWindowOverlapAfter ring seed pre e) root :=
      congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.mode)
        hf.1
    have hc : bankWindowReadController
        (bankWindowOverlapBefore ring seed pre)
        (bankWindowOverlapAfter ring seed pre e) root :=
      congrArg (fun a : RenewalBankSite n => a.controller) hf.2
    exact bankWindowOrphanReadTransport ring
      (bankWindowOverlapBefore ring seed pre)
      (bankWindowOverlapAfter ring seed pre e)
      root j hJ ⟨hp, hm, hc, hworker⟩ howner htainted
  rcases hcase with ⟨k, hpositive, hk, hsource, hstable⟩ |
      ⟨hresponder, hwrong⟩ | ⟨hsource, hchanged⟩
  · have hnextSite :
        ring.rightNeighbor e = Counter.site ring root (k + 1) := by
      rw [hsource]
      rfl
    have hp : bankWindowReadPackPrefix ring
        (bankWindowOverlapBefore ring seed pre)
        (bankWindowOverlapAfter ring seed pre e)
        root (j.val + 1) := by
      intro t ht
      by_cases htk : t = k + 1
      · have hsite :
            Counter.site ring root t = ring.rightNeighbor e := by
          rw [htk, hnextSite]
        rw [hsite]
        exact (bankWindowExactResponderPack ring
          (bankWindowOverlapBefore ring seed pre) e
          (clockNeighborDifferent ring (by omega : 2 ≤ n) e)).trans
          hstable
      · have hnot :
            Counter.site ring root t ≠ ring.rightNeighbor e := by
          rw [hnextSite]
          by_cases hless : t < k + 1
          · exact bankWindowIncidenceSiteDistinct
              ring hbank root t (k + 1) hless (by omega)
          · exact (bankWindowIncidenceSiteDistinct
              ring hbank root (k + 1) t (by omega) (by omega)).symm
        exact bankWindowClosureRepairNonresponderPackFixed
          ring (by omega : 2 ≤ n)
          (bankWindowOverlapBefore ring seed pre) e
          (Counter.site ring root t) hnot
    have hrootSource : root ≠ e := by
      rw [hsource]
      have hh := bankWindowIncidenceSiteDistinct
        ring hbank root 0 k (by omega) (by omega)
      change root ≠ Counter.site ring root k at hh
      exact hh
    have hrootTarget : root ≠ ring.rightNeighbor e := by
      rw [hnextSite]
      have hh := bankWindowIncidenceSiteDistinct
        ring hbank root 0 (k + 1) (by omega) (by omega)
      change root ≠ Counter.site ring root (k + 1) at hh
      exact hh
    have hnotSource :
        Counter.site ring root (j.val + 1) ≠ e := by
      rw [hsource]
      exact (bankWindowIncidenceSiteDistinct
        ring hbank root k (j.val + 1)
        (by omega) (by omega)).symm
    have hnotTarget :
        Counter.site ring root (j.val + 1) ≠
          ring.rightNeighbor e := by
      rw [hnextSite]
      exact (bankWindowIncidenceSiteDistinct
        ring hbank root (k + 1) (j.val + 1)
        (by omega) (by omega)).symm
    have hf := (bankWindowExactOffPairFrame ring
      (bankWindowOverlapBefore ring seed pre) e
      (Counter.site ring root (j.val + 1))
      hnotSource hnotTarget).2
    have hworker : bankWindowReadWorker
        (bankWindowOverlapBefore ring seed pre)
        (bankWindowOverlapAfter ring seed pre e)
        (Counter.site ring root (j.val + 1)) :=
      congrArg (fun a : RenewalBankSite n => a.worker) hf
    exact htransport hp hrootSource hrootTarget hworker
  · have hafter :
        ((bankWindowOverlapAfter ring seed pre e).1
          (ring.rightNeighbor e)).pack.val = j.val + 1 := by
      rw [hresponder]
      exact howner.2.1
    have hclean := bankWindowClosureRepairDigitNoTaint ring
      hn hbank (bankWindowOverlapBefore ring seed pre)
      e j hwrong hafter
    have ht : BankWindowTainted
        (bankWindowOverlapAfter ring seed pre e)
        (ring.rightNeighbor e) := by
      rw [hresponder]
      exact htainted
    exact False.elim (hclean.2.2 ht)
  · have hnextSite :
        ring.rightNeighbor e = Counter.site ring root (j.val + 2) := by
      rw [hsource]
      rfl
    have hp : bankWindowReadPackPrefix ring
        (bankWindowOverlapBefore ring seed pre)
        (bankWindowOverlapAfter ring seed pre e)
        root (j.val + 1) := by
      intro t ht
      have hnot :
          Counter.site ring root t ≠ ring.rightNeighbor e := by
        rw [hnextSite]
        exact bankWindowIncidenceSiteDistinct
          ring hbank root t (j.val + 2)
          (by omega) (by omega)
      exact bankWindowClosureRepairNonresponderPackFixed
        ring (by omega : 2 ≤ n)
        (bankWindowOverlapBefore ring seed pre) e
        (Counter.site ring root t) hnot
    have hrootSource : root ≠ e := by
      rw [hsource]
      have hh := bankWindowIncidenceSiteDistinct
        ring hbank root 0 (j.val + 1)
        (by omega) (by omega)
      change root ≠ Counter.site ring root (j.val + 1) at hh
      exact hh
    have hrootTarget : root ≠ ring.rightNeighbor e := by
      rw [hnextSite]
      have hh := bankWindowIncidenceSiteDistinct
        ring hbank root 0 (j.val + 2)
        (by omega) (by omega)
      change root ≠ Counter.site ring root (j.val + 2) at hh
      exact hh
    have hchoice := bankWindowClosureChangedWorkerChoice
      ring hn hbank (bankWindowOverlapBefore ring seed pre)
      e hchanged (Counter.site ring root (j.val + 1))
    have hworker : bankWindowReadWorker
        (bankWindowOverlapBefore ring seed pre)
        (bankWindowOverlapAfter ring seed pre e)
        (Counter.site ring root (j.val + 1)) := by
      rcases hchoice with hkeep | hempty
      · exact hkeep
      · rcases htainted with ⟨rho, hpend⟩ |
          ⟨p, o, hpay, horigin⟩
        · rw [hempty] at hpend
          cases hpend
        · rw [hempty] at hpay
          cases hpay
    exact htransport hp hrootSource hrootTarget hworker

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The literal nonroot worker preimage at either selected site.
Every POST pending receipt or genuine worker has the identical OLD
worker at the source or responder. This uses all six first-match
worker wirings through the installed BANK classifiers; it does not
presume an arbitrary post-J invariant.
Consumer: group-13 ORPH stable-source and PFX taint cases. -/
theorem bankWindowOverlapNonrootPairTaintPreimage
    {n : Nat} (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e i : Fin n)
    (hnonroot : (r.1 e).pack.val ≠ 0)
    (hselected : i = e ∨ i = ring.rightNeighbor e)
    (htainted : BankWindowTainted (renewalBankNext ring r e) i) :
    BankWindowTainted r e ∨
      BankWindowTainted r (ring.rightNeighbor e) := by
  have hframe := rbReferenceSelectedPairFrame ring hn r e
  rcases hselected with hi | hi
  · subst i
    rcases htainted with ⟨rho, hpending⟩ |
        ⟨p, o, hworker, horigin⟩
    · have hs := congrArg
        (fun s : RenewalBankSite n => s.worker) hframe.2.2.1
      change ((renewalBankNext ring r e).2.sites e).worker =
        (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
          r.2 e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).1.worker at hs
      have hlocal :
          (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
            r.2 e (ring.rightNeighbor e)
            (r.1 e) (r.1 (ring.rightNeighbor e))).1.worker =
              .pending rho := hs.symm.trans hpending
      rcases rbGhostNonrootPendingOld
          (compileAdvice (ceilLogTwo n)) r.2
          e (ring.rightNeighbor e) (r.1 e)
          (r.1 (ring.rightNeighbor e))
          hnonroot rho (Or.inl hlocal) with hsrc | hdst
      · exact Or.inl (Or.inl ⟨rho, hsrc⟩)
      · exact Or.inr (Or.inl ⟨rho, hdst⟩)
    · have hs := congrArg
        (fun s : RenewalBankSite n => s.worker) hframe.2.2.1
      change ((renewalBankNext ring r e).2.sites e).worker =
        (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
          r.2 e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).1.worker at hs
      have hlocal :
          (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
            r.2 e (ring.rightNeighbor e)
            (r.1 e) (r.1 (ring.rightNeighbor e))).1.worker =
              .payload p := hs.symm.trans hworker
      rcases rbBankNonrootSelectedWorkersInherited
          (compileAdvice (ceilLogTwo n)) r.2
          e (ring.rightNeighbor e) (r.1 e)
          (r.1 (ring.rightNeighbor e))
          hnonroot p (Or.inl hlocal) with hsrc | hdst
      · exact Or.inl (Or.inr ⟨p, o, hsrc, horigin⟩)
      · exact Or.inr (Or.inr ⟨p, o, hdst, horigin⟩)
  · subst i
    rcases htainted with ⟨rho, hpending⟩ |
        ⟨p, o, hworker, horigin⟩
    · have hs := congrArg
        (fun s : RenewalBankSite n => s.worker) hframe.2.2.2
      change ((renewalBankNext ring r e).2.sites
        (ring.rightNeighbor e)).worker =
        (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
          r.2 e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).2.worker at hs
      have hlocal :
          (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
            r.2 e (ring.rightNeighbor e)
            (r.1 e) (r.1 (ring.rightNeighbor e))).2.worker =
              .pending rho := hs.symm.trans hpending
      rcases rbGhostNonrootPendingOld
          (compileAdvice (ceilLogTwo n)) r.2
          e (ring.rightNeighbor e) (r.1 e)
          (r.1 (ring.rightNeighbor e))
          hnonroot rho (Or.inr hlocal) with hsrc | hdst
      · exact Or.inl (Or.inl ⟨rho, hsrc⟩)
      · exact Or.inr (Or.inl ⟨rho, hdst⟩)
    · have hs := congrArg
        (fun s : RenewalBankSite n => s.worker) hframe.2.2.2
      change ((renewalBankNext ring r e).2.sites
        (ring.rightNeighbor e)).worker =
        (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
          r.2 e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).2.worker at hs
      have hlocal :
          (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
            r.2 e (ring.rightNeighbor e)
            (r.1 e) (r.1 (ring.rightNeighbor e))).2.worker =
              .payload p := hs.symm.trans hworker
      rcases rbBankNonrootSelectedWorkersInherited
          (compileAdvice (ceilLogTwo n)) r.2
          e (ring.rightNeighbor e) (r.1 e)
          (r.1 (ring.rightNeighbor e))
          hnonroot p (Or.inr hlocal) with hsrc | hdst
      · exact Or.inl (Or.inr ⟨p, o, hsrc, horigin⟩)
      · exact Or.inr (Or.inr ⟨p, o, hdst, horigin⟩)

/-- Every tainted worker in the real BANK run is in an actual digit
role, including pending workers. The pending half comes from
ReceiptInv.pending; the genuine half from the merged real-run
worker-band proof. Consumer: group-13 ORPH top/spacer exclusion. -/
theorem bankWindowOverlapReachableTaintedInBand
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (z : Fin n)
    (htainted : BankWindowTainted
      (bankWindowOverlapBefore ring seed pre) z) :
    1 ≤ ((bankWindowOverlapBefore ring seed pre).1 z).pack.val ∧
    ((bankWindowOverlapBefore ring seed pre).1 z).pack.val ≤
      (compileAdvice (ceilLogTwo n)).b := by
  rcases htainted with ⟨rho, hw⟩ | ⟨p, o, hw, ho⟩
  · have hreceipt := rbReceiptInvBankWordOfInv
      ring (by omega : 2 ≤ n) seed hbank pre
    obtain ⟨_, _, k, hlow, hhigh, _, hpack, _⟩ :=
      hreceipt.pending z rho hw
    rw [hpack]
    exact ⟨hlow, hhigh⟩
  · exact bankWindowOverlapGenuineWorkerInBand
      ring hn hbank seed pre z p o hw ho

theorem bankWindowOverlapProtoRRForwardFields
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n) (rho : RenewalBankReceipt n)
    (hfirst :
      1 ≤ ((bankWindowOverlapBefore ring seed pre).1 e).pack.val)
    (hinside :
      ((bankWindowOverlapBefore ring seed pre).1 e).pack.val <
        (compileAdvice (ceilLogTwo n)).b)
    (hnextRole :
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val =
      ((bankWindowOverlapBefore ring seed pre).1 e).pack.val + 1)
    (hrr : ((bankWindowOverlapBefore ring seed pre).1 e).tok = .RR)
    (hzero : ((bankWindowOverlapBefore ring seed pre).1 e).bit = false)
    (hpending :
      ((bankWindowOverlapBefore ring seed pre).2.sites e).worker =
        .pending rho) :
    ((bankWindowOverlapAfter ring seed pre e).1 e).tok = .E ∧
    ((bankWindowOverlapAfter ring seed pre e).1 e).bit = false ∧
    ((bankWindowOverlapAfter ring seed pre e).1
      (ring.rightNeighbor e)).tok = .RR ∧
    ((bankWindowOverlapAfter ring seed pre e).1
      (ring.rightNeighbor e)).bit = false ∧
    ((bankWindowOverlapAfter ring seed pre e).2.sites
      (ring.rightNeighbor e)).worker = .pending rho := by
  have hpostRole :
      packNext
        ((bankWindowOverlapBefore ring seed pre).1 e).pack.val
        ((bankWindowOverlapBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
        ((bankWindowOverlapBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val := by
    rw [hnextRole]
    simp [packNext, hinside]
  have hrow := Counter.resetTrialBankForwardSymbolic
    (bankCell ((bankWindowOverlapBefore ring seed pre).1 e)
      ((bankWindowOverlapBefore ring seed pre).1 e).pack.val)
    (bankCell ((bankWindowOverlapBefore ring seed pre).1
      (ring.rightNeighbor e))
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val)
    (compileAdvice (ceilLogTwo n)).b
    (compileAdvice (ceilLogTwo n)).theta
    hfirst hinside hnextRole hrr hzero
  have hphysical :
      (Counter.resetBankOld
        ((bankWindowOverlapBefore ring seed pre).1 e)
        ((bankWindowOverlapBefore ring seed pre).1
          (ring.rightNeighbor e))).1.tok = .E ∧
      (Counter.resetBankOld
        ((bankWindowOverlapBefore ring seed pre).1 e)
        ((bankWindowOverlapBefore ring seed pre).1
          (ring.rightNeighbor e))).1.bit = false ∧
      (Counter.resetBankOld
        ((bankWindowOverlapBefore ring seed pre).1 e)
        ((bankWindowOverlapBefore ring seed pre).1
          (ring.rightNeighbor e))).2.tok = .RR ∧
      (Counter.resetBankOld
        ((bankWindowOverlapBefore ring seed pre).1 e)
        ((bankWindowOverlapBefore ring seed pre).1
          (ring.rightNeighbor e))).2.bit = false := by
    unfold Counter.resetBankOld
    rw [hpostRole]
    exact hrow
  have htrip := bankWindowClosureSelectedBankTrip
    ring hn hbank (bankWindowOverlapBefore ring seed pre) e
  have hsrcTok := congrArg
    (fun t : Mode × Bool × BTok => t.2.2) htrip.1
  have hsrcBit := congrArg
    (fun t : Mode × Bool × BTok => t.2.1) htrip.1
  have hdestTok := congrArg
    (fun t : Mode × Bool × BTok => t.2.2) htrip.2
  have hdestBit := congrArg
    (fun t : Mode × Bool × BTok => t.2.1) htrip.2
  have hmove := bankWindowBirthPendingForwardStep
    ring (by omega : 2 ≤ n)
    (bankWindowOverlapBefore ring seed pre)
    e rho hfirst hinside hnextRole hrr hpending
  exact ⟨hsrcTok.trans hphysical.1,
    hsrcBit.trans hphysical.2.1,
    hdestTok.trans hphysical.2.2.1,
    hdestBit.trans hphysical.2.2.2,
    hmove.2⟩

end L3.BankWindow

#print axioms L3.BankWindow.bankWindowOverlapGlobalAndDisjoint
#print axioms L3.BankWindow.bankWindowOverlapPostReceipt
#print axioms L3.BankWindow.bankWindowOverlapInheritedCarrierCompatibility
#print axioms L3.BankWindow.bankWindowOverlapIncomingRootJoint
#print axioms L3.BankWindow.bankWindowOverlapProtoForeignInterior
#print axioms L3.BankWindow.bankWindowOverlapOrphanForeignInterior
#print axioms L3.BankWindow.bankWindowOverlapNonrootPairTaintPreimage
#print axioms L3.BankWindow.bankWindowOverlapReachableTaintedInBand
#print axioms L3.BankWindow.bankWindowOverlapProtoRRForwardFields
