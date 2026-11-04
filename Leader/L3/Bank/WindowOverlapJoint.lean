import Leader.L3.Bank.WindowOverlapRoot
import Leader.L3.Bank.WindowOverlapInterior
import Leader.L3.Bank.MemoryNonroot

/-!
R11 group 13: joint assembly of the root-overlap fields with the proved
stable-PACK interior producer.

BankWindowOverlapRoot.lean carries the interior producer as the binder
hbankWindowOverlapProtoInteriorAll of
bankWindowOverlapRootForeignProtoWithInterior and bankWindowOverlapRootFields;
BankWindowOverlapInterior.lean proves bankWindowOverlapProtoInteriorAll.

How the two phrasings relate. Both modules name the OLD snapshot and its
successor by file-private reducible abbreviations with the same bodies:
bankWindowRootBefore / bankWindowOverlapBefore are
rbRun ring (renewalBankStart ring seed) pre, and bankWindowRootAfter /
bankWindowOverlapAfter are renewalBankNext ring (that snapshot) e. They are
therefore definitionally equal, and this file states everything with the
public bodies. The Interior conclusion is the four-clause conjunction that
BankWindowRootForeignProtoField unfolds to (same clauses, same order, only
bound-variable names differ), so it is definitionally the Root field, not
weaker. The Root binder additionally offers the foreignness premise
root ≠ e ∧ root ≠ rightNeighbor e, which the Interior theorem does not need.
-/

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The proved stable-PACK interior producer, in exactly the shape of the
binder hbankWindowOverlapProtoInteriorAll of BankWindowOverlapRoot.lean
(the Interior conclusion is definitionally BankWindowRootForeignProtoField
at the same successor). Consumer: bankWindowOverlapRootForeignProtoJoint and
bankWindowOverlapRootJointFields. -/
theorem bankWindowOverlapJointProtoInterior {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre)) :
    ∀ (root : Fin n) (k limit : Nat),
      root ≠ e ∧ root ≠ ring.rightNeighbor e →
      e = Counter.site ring root k →
      1 ≤ k → k < limit →
      packNext
        ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val
        ((rbRun ring (renewalBankStart ring seed) pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((rbRun ring (renewalBankStart ring seed) pre).1
        (ring.rightNeighbor e)).pack.val →
      BankWindowProtoRun ring
        (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
        root limit →
      BankWindowRootForeignProtoField ring
        (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
        root limit := by
  intro root k limit _ hsource hk hinterior hstable hproto
  exact bankWindowOverlapProtoInteriorAll ring hn hbank seed pre e root k limit
    hJ hsource hk hinterior hstable hproto

/-- Every foreign-root POST J.proto field on the selected successor, with
the interior producer discharged by the proved Interior theorem.
Consumer: bankWindowOverlapRootJointFields. -/
theorem bankWindowOverlapRootForeignProtoJoint {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre)) :
    ∀ (root : Fin n) (limit : Nat),
      root ≠ e ∧ root ≠ ring.rightNeighbor e →
      BankWindowProtoRun ring
        (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
        root limit →
      BankWindowRootForeignProtoField ring
        (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
        root limit :=
  bankWindowOverlapRootForeignProtoWithInterior ring hn hbank seed pre e hJ
    (bankWindowOverlapJointProtoInterior ring hn hbank seed pre e hJ)

/-- The group-13 root-overlap post fields with the interior hypothesis
removed: global in-flight frame, both payload-shape clauses, every foreign
proto prefix, and every foreign orphan restriction on the actual selected
successor of an exact OLD BANK window. As in bankWindowOverlapRootFields,
the same-pair comparator rows and root-local wait/active clauses are not
part of this bundle. Consumer: joint assembly before bankWindowExactStep. -/
theorem bankWindowOverlapRootJointFields {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre)) :
    BankInFlightAligned ring
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) ∧
    (∀ (i : Fin n) (p : RenewalBankPayload n),
      p ∈ rbSiteLivePayloads
        ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites i) →
      p.origin = none → p.atoms ≠ [] ∧ p.heads = 0) ∧
    (∀ (i : Fin n) (p : RenewalBankPayload n)
      (o : RenewalBankOrigin n),
      p ∈ rbSiteLivePayloads
        ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites i) →
      p.origin = some o → p.atoms = []) ∧
    (∀ (root : Fin n) (limit : Nat),
      root ≠ e ∧ root ≠ ring.rightNeighbor e →
      BankWindowProtoRun ring
        (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
        root limit →
      BankWindowRootForeignProtoField ring
        (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
        root limit) ∧
    (∀ (root : Fin n)
      (j : Fin (compileAdvice (ceilLogTwo n)).b),
      root ≠ e ∧ root ≠ ring.rightNeighbor e →
      BankWindowOrphanOwner ring
        (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) root j →
      BankWindowTainted
        (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
        (Counter.site ring root (j.val + 1)) →
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1
        root).mode = .RESET ∨
      (((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1
        root).mode = .RWAIT ∧
        ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites
          root).controller = .waiting [])) :=
  bankWindowOverlapRootFields ring hn hbank seed pre e hJ
    (bankWindowOverlapJointProtoInterior ring hn hbank seed pre e hJ)

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open L3.BankComparatorExclusive
open L3.BankHeadThreshold
open L3.BankCounterRows
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Every root-indexed BankWindowExact clause, instantiated at one root.
Origin-indexed clauses (the four phase clauses and compareExact) are
taken for the origins whose root is this root. Together with the three
global clauses (frame and the two payload-shape clauses) this is exactly
BankWindowExact, by bankWindowExactOfRootFields; it splits the step
proof by the geometry of each root against the selected edge.
Consumer: bankWindowExactOfRootFields and the per-class root bundles
bankWindowOverlapOutsideRootFieldsAt and
bankWindowOverlapRootSourceForeignRootFieldsAt. -/
def BankWindowRootFieldsAt {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n) : Prop :=
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    o.root = root → BankComparatorOriginWorker ring r o i p →
      (r.1 o.root).mode ≠ .ARMED ∧
      (r.1 o.root).mode ≠ .CSTART ∧
      (r.1 o.root).mode ≠ .IWAIT) ∧
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    o.root = root → BankComparatorOriginWorker ring r o i p →
      (r.1 o.root).mode = .CWAIT →
      Counter.Complete ring r.1 o.root) ∧
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    o.root = root → BankComparatorOriginWorker ring r o i p →
      (r.1 o.root).mode = .CWAIT →
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        BankTrialLiveComparisonToken
          (r.1 (Counter.site ring o.root (j.val + 1))).tok →
        Counter.site ring o.root (j.val + 1) = i) ∧
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    o.root = root → BankComparatorOriginWorker ring r o i p →
      (r.1 o.root).mode = .CWAIT →
      ((r.1 i).tok = .CR1 →
        bankComparatorPrefixMatched ring r o (r.1 i).pack.val) ∧
      ((r.1 i).tok = .CR0 →
        ¬ bankComparatorPrefixMatched ring r o (r.1 i).pack.val) ∧
      ((r.1 i).tok = .CL1 →
        bankComparatorPrefixMatched ring r o
          (compileAdvice (ceilLogTwo n)).b) ∧
      ((r.1 i).tok = .CL0 →
        ¬ bankComparatorPrefixMatched ring r o
          (compileAdvice (ceilLogTwo n)).b)) ∧
  (BankWindowScope ring r root →
    BankWindowInheritedController r root →
    ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ¬ BankWindowTainted r (Counter.site ring root (j.val + 1))) ∧
  (BankWindowScope ring r root →
    (r.1 root).mode = .RWAIT →
    (r.2.sites root).controller = .waiting [] →
    ∃ (j : Fin (compileAdvice (ceilLogTwo n)).b)
      (rho : RenewalBankReceipt n),
      (r.2.sites (Counter.site ring root (j.val + 1))).worker =
        .pending rho ∧
      ((r.1 (Counter.site ring root (j.val + 1))).tok = .RR ∨
       (r.1 (Counter.site ring root (j.val + 1))).tok = .RL) ∧
      bankWindowZeroPrefix ring r root (j.val + 1) ∧
      (∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
        k.val < j.val →
        (r.1 (Counter.site ring root (k.val + 1))).tok = .E) ∧
      ((r.1 (Counter.site ring root (j.val + 1))).tok = .RL →
        bankWindowOnlyToken ring r root
          (Counter.site ring root (j.val + 1)) ∧
        bankWindowZeroPrefix ring r root
          (compileAdvice (ceilLogTwo n)).b)) ∧
  (∀ (o : RenewalBankOrigin n) (p : RenewalBankPayload n),
    BankWindowScope ring r root →
    ((r.1 root).mode = .ARMED ∨ (r.1 root).mode = .CSTART) →
    (r.2.sites root).controller = .active p →
    p.origin = some o →
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      (r.1 (Counter.site ring root (j.val + 1))).tok = .E) ∧
    p.heads = bankOriginBinaryValue ring r.1 o ∧
    ((r.1 root).mode = .ARMED →
      bankOriginBinaryValue ring r.1 o <
        (compileAdvice (ceilLogTwo n)).K) ∧
    ((r.1 root).mode = .CSTART →
      bankOriginBinaryValue ring r.1 o ≤
        (compileAdvice (ceilLogTwo n)).K)) ∧
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    BankWindowScope ring r root →
    (r.1 root).mode = .IWAIT →
    (r.2.sites root).controller = .waiting [] →
    (r.2.sites i).worker = .payload p →
    p.origin = some o → o.root = root →
    bankWindowOnlyToken ring r root i ∧
    (((r.1 i).tok = .IR ∧
        bankWindowZeroPrefix ring r root (r.1 i).pack.val ∧
        p.heads = bankOriginBinaryValue ring r.1 o +
          2 ^ (r.1 i).pack.val ∧
        bankOriginBinaryValue ring r.1 o +
          2 ^ (r.1 i).pack.val ≤
            (compileAdvice (ceilLogTwo n)).K) ∨
     ((r.1 i).tok = .AL ∧
        p.heads = bankOriginBinaryValue ring r.1 o ∧
        bankOriginBinaryValue ring r.1 o ≤
          (compileAdvice (ceilLogTwo n)).K))) ∧
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    o.root = root →
    (r.2.sites i).worker = .payload p →
    p.origin = some o →
    (r.1 o.root).mode = .CWAIT →
    (r.2.sites o.root).controller = .waiting [] →
    bankWindowOnlyToken ring r o.root i ∧
    BankTrialLiveComparisonToken (r.1 i).tok ∧
    p.heads = bankOriginBinaryValue ring r.1 o ∧
    bankOriginBinaryValue ring r.1 o ≤
      (compileAdvice (ceilLogTwo n)).K) ∧
  (BankWindowScope ring r root →
    (r.1 root).mode = .IWAIT →
    (r.2.sites root).controller = .waiting [] →
    ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowTainted r (Counter.site ring root (j.val + 1)) →
      ∃ (o : RenewalBankOrigin n) (p : RenewalBankPayload n),
        (r.2.sites (Counter.site ring root (j.val + 1))).worker =
          .payload p ∧ p.origin = some o ∧
        o.root = root ∧
        bankWindowOnlyToken ring r root
          (Counter.site ring root (j.val + 1))) ∧
  (BankWindowScope ring r root →
    (r.1 root).mode = .CWAIT →
    (r.2.sites root).controller = .waiting [] →
    ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowTainted r (Counter.site ring root (j.val + 1)) →
      ∃ (o : RenewalBankOrigin n) (p : RenewalBankPayload n),
        (r.2.sites (Counter.site ring root (j.val + 1))).worker =
          .payload p ∧ p.origin = some o ∧
        o.root = root ∧
        BankTrialLiveComparisonToken
          (r.1 (Counter.site ring root (j.val + 1))).tok ∧
        bankWindowOnlyToken ring r root
          (Counter.site ring root (j.val + 1))) ∧
  (∀ limit : Nat, BankWindowProtoRun ring r root limit →
    BankWindowRootForeignProtoField ring r root limit) ∧
  (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
    BankWindowOrphanOwner ring r root j →
    BankWindowTainted r (Counter.site ring root (j.val + 1)) →
    (r.1 root).mode = .RESET ∨
      ((r.1 root).mode = .RWAIT ∧
        (r.2.sites root).controller = .waiting []))

/-- BankWindowExact is exactly its three global clauses plus the
root-indexed clauses at every root. This reduces bankWindowExactStep
to bankWindowOverlapRootJointFields (global part) and one
BankWindowRootFieldsAt proof per root geometry class.
Consumer: bankWindowExactStep. -/
theorem bankWindowExactOfRootFields {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (hframe : BankInFlightAligned ring r)
    (hshape : ∀ (i : Fin n) (p : RenewalBankPayload n),
      p ∈ rbSiteLivePayloads (r.2.sites i) →
      p.origin = none → p.atoms ≠ [] ∧ p.heads = 0)
    (hempty : ∀ (i : Fin n) (p : RenewalBankPayload n)
      (o : RenewalBankOrigin n),
      p ∈ rbSiteLivePayloads (r.2.sites i) →
      p.origin = some o → p.atoms = [])
    (hroots : ∀ root : Fin n, BankWindowRootFieldsAt ring r root) :
    BankWindowExact ring r := by
  refine {
    frame := hframe, payloadShape := hshape,
    genuinePayloadEmpty := hempty,
    phaseExcludes := ?_, phaseComplete := ?_, phaseUnique := ?_,
    phaseFlags := ?_, inheritedClean := ?_, resetWait := ?_,
    armedExact := ?_, incrementExact := ?_, compareExact := ?_,
    iwaitTaintedUnique := ?_, cwaitTaintedUnique := ?_,
    proto := ?_, orphan := ?_ }
  · intro o i p hw
    exact (hroots o.root).1 o i p rfl hw
  · intro o i p hw hm
    exact (hroots o.root).2.1 o i p rfl hw hm
  · intro o i p hw hm j ht
    exact (hroots o.root).2.2.1 o i p rfl hw hm j ht
  · intro o i p hw hm
    exact (hroots o.root).2.2.2.1 o i p rfl hw hm
  · intro root hs hi j
    exact (hroots root).2.2.2.2.1 hs hi j
  · intro root hs hm hc
    exact (hroots root).2.2.2.2.2.1 hs hm hc
  · intro root o p hs hm hc ho
    exact (hroots root).2.2.2.2.2.2.1 o p hs hm hc ho
  · intro root o i p hs hm hc hw ho hr
    exact (hroots root).2.2.2.2.2.2.2.1 o i p hs hm hc hw ho hr
  · intro o i p hw ho hm hc
    exact (hroots o.root).2.2.2.2.2.2.2.2.1 o i p rfl hw ho hm hc
  · intro root hs hm hc j ht
    exact (hroots root).2.2.2.2.2.2.2.2.2.1 hs hm hc j ht
  · intro root hs hm hc j ht
    exact (hroots root).2.2.2.2.2.2.2.2.2.2.1 hs hm hc j ht
  · intro root limit hrun
    exact (hroots root).2.2.2.2.2.2.2.2.2.2.2.1 limit hrun
  · intro root j ho ht
    exact (hroots root).2.2.2.2.2.2.2.2.2.2.2.2 j ho ht

/-- compareExact for an origin whose whole BANK window avoids the
selected edge, from a bare genuine POST worker (no live comparison
token assumed). The worker is off the pair by the real-run in-band
theorem; then worker, token, root mode and controller, and every
origin digit token and bit are framed, and OLD J.compareExact
transports through the compareExact read set.
Consumer: bankWindowOverlapOutsideRootFieldsAt. -/
theorem bankWindowOverlapOutsideCompareExactField {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n)
    (houtside : Counter.OutsideSites (q := ceilLogTwo n) ring o.root e)
    (hworker :
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites
        i).worker = .payload p)
    (horigin : p.origin = some o)
    (hmode :
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1
        o.root).mode = .CWAIT)
    (hcontroller :
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites
        o.root).controller = .waiting []) :
    bankWindowOnlyToken ring
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
      o.root i ∧
    BankTrialLiveComparisonToken
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1
        i).tok ∧
    p.heads = bankOriginBinaryValue ring
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 o ∧
    bankOriginBinaryValue ring
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 o ≤
      (compileAdvice (ceilLogTwo n)).K := by
  have hfree := bankWindowOverlapOutsideGenuineWorkerOffPair
    ring hn hbank seed pre e i p o houtside hworker horigin
  have hfreeReads := bankWindowExactOffPairAtomicReads ring
    (rbRun ring (renewalBankStart ring seed) pre) e i
    hfree.1 hfree.2
  have hrootOutside := houtside 0 (by omega)
  have hrootReads := bankWindowExactOffPairAtomicReads ring
    (rbRun ring (renewalBankStart ring seed) pre) e o.root
    (by simpa only [Counter.site] using hrootOutside.1.symm)
    (by simpa only [Counter.site] using hrootOutside.2.symm)
  have hwindow := bankWindowExactOffWindowFrame ring
    (rbRun ring (renewalBankStart ring seed) pre) o.root e houtside
  have htoks : bankWindowReadDigitTokens ring
      (rbRun ring (renewalBankStart ring seed) pre)
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
      o.root := by
    intro j
    have hj : j.val + 1 ≤ (compileAdvice (ceilLogTwo n)).b := by
      have hb := j.isLt
      omega
    exact congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
      (hwindow (j.val + 1) hj).1
  have hbits : bankWindowReadDigitBits ring
      (rbRun ring (renewalBankStart ring seed) pre)
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
      o.root := by
    intro j
    have hj : j.val + 1 ≤ (compileAdvice (ceilLogTwo n)).b := by
      have hb := j.isLt
      omega
    exact congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.bit)
      (hwindow (j.val + 1) hj).1
  exact bankWindowCompareExactReadTransport ring
    (rbRun ring (renewalBankStart ring seed) pre)
    (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
    o i p hJ
    ⟨hrootReads.2.1, hrootReads.2.2.2.2.2.2,
      hfreeReads.2.2.2.2.2.1, hfreeReads.2.2.1, htoks, hbits⟩
    hworker horigin hmode hcontroller

/-- Geometry class OUT, every selected edge: a root whose whole PACK
window avoids both selected endpoints satisfies every root-indexed POST
clause. Uniform over all BANK rows (root source, repair, stable
interior, top, incoming of another root).
Consumer: bankWindowExactStep, OUT branch of the per-root split. -/
theorem bankWindowOverlapOutsideRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (root : Fin n)
    (houtside : Counter.OutsideSites (q := ceilLogTwo n) ring root e) :
    BankWindowRootFieldsAt ring
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
      root := by
  obtain ⟨hic, hiw, hcw, hrw, hor⟩ :=
    bankWindowOverlapOutsideTaintedOwnerFields ring seed pre e root
      hJ houtside
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o i p ho hw
    subst ho
    exact (bankWindowOverlapOutsideOriginPhasePackage ring hn hbank
      seed pre e hJ o i p houtside hw).1
  · intro o i p ho hw hm
    subst ho
    exact ((bankWindowOverlapOutsideOriginPhasePackage ring hn hbank
      seed pre e hJ o i p houtside hw).2 hm).1
  · intro o i p ho hw hm
    subst ho
    exact ((bankWindowOverlapOutsideOriginPhasePackage ring hn hbank
      seed pre e hJ o i p houtside hw).2 hm).2.1
  · intro o i p ho hw hm
    subst ho
    exact ((bankWindowOverlapOutsideOriginPhasePackage ring hn hbank
      seed pre e hJ o i p houtside hw).2 hm).2.2
  · intro hs hi j
    exact hic j hs hi
  · exact hrw
  · intro o p hs hm hc ho
    exact bankWindowOverlapOutsideArmedExactField ring hn hbank seed pre
      e root hJ houtside o p hs hm hc ho
  · intro o i p hs hm hc hw ho hr
    exact bankWindowOverlapOutsideIncrementExactField ring hn hbank seed
      pre e root hJ houtside o i p hs hm hc hw ho hr
  · intro o i p ho hw horig hm hc
    subst ho
    exact bankWindowOverlapOutsideCompareExactField ring hn hbank seed
      pre e hJ o i p houtside hw horig hm hc
  · intro hs hm hc j ht
    exact hiw j hs hm hc ht
  · intro hs hm hc j ht
    exact hcw j hs hm hc ht
  · intro limit hrun
    exact bankWindowOverlapOutsideProtoField ring seed pre e root hJ
      houtside limit hrun
  · exact hor

/-- On a PACK-zero root-source edge, a root other than both endpoints
whose window meets the edge has the source as one of its digits
D_root(k), 1 <= k <= b. The source keeps PACK zero, so the POST window
is not complete and every Scope-guarded clause at that root is vacuous.
Consumer: bankWindowOverlapRootSourceForeignRootFieldsAt. -/
theorem bankWindowOverlapRootSourceForeignNoScope {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hx : (r.1 e).pack.val = 0)
    (root : Fin n)
    (hforeign : root ≠ e ∧ root ≠ ring.rightNeighbor e)
    (hmeets : ¬ Counter.OutsideSites (q := ceilLogTwo n) ring root e) :
    ¬ BankWindowScope ring (renewalBankNext ring r e) root := by
  intro hs
  have hsrc := (bankWindowRootSourceRoles ring hn r e hx).1
  rcases bankWindowGuardedGeometricIncidence ring hbank root e with
    hy | he | ⟨k, hk1, hkb, hek⟩ | htop | hout
  · exact hforeign.2 hy.symm
  · exact hforeign.1 he.symm
  · have hc := hs.1 k (by omega)
    rw [← hek] at hc
    omega
  · have hc := hs.1 (compileAdvice (ceilLogTwo n)).b (Nat.le_refl _)
    rw [← htop] at hc
    have hb0 : (compileAdvice (ceilLogTwo n)).b = 0 := by omega
    rw [hb0] at htop
    exact hforeign.1 (by simpa only [Counter.site] using htop.symm)
  · exact hmeets hout

/-- Root-source edge (OLD source PACK zero), every root other than
both endpoints: all root-indexed POST clauses. Window-disjoint roots use
the OUT bundle; the others have no POST scope, their comparator clauses
come from the root-source foreign comparator theorems, and proto/orphan
from bankWindowOverlapRootJointFields.
Consumer: bankWindowExactStep, root-source edge, foreign roots. -/
theorem bankWindowOverlapRootSourceForeignRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hx : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val = 0)
    (root : Fin n)
    (hforeign : root ≠ e ∧ root ≠ ring.rightNeighbor e) :
    BankWindowRootFieldsAt ring
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
      root := by
  by_cases hout : Counter.OutsideSites (q := ceilLogTwo n) ring root e
  · exact bankWindowOverlapOutsideRootFieldsAt ring hn hbank seed pre e
      hJ root hout
  have hnoscope := bankWindowOverlapRootSourceForeignNoScope ring hn hbank
    (rbRun ring (renewalBankStart ring seed) pre) e hx root hforeign hout
  have hjoint := bankWindowOverlapRootJointFields ring hn hbank seed pre e hJ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o i p ho hw
    subst ho
    exact bankWindowRootForeignPhaseExcludesOnSource ring hn hbank seed pre
      e hJ hx o i p hforeign hw
  · intro o i p ho hw hm
    subst ho
    exact (bankWindowRootForeignComparatorStep ring hn hbank seed pre
      e hJ hx o i p hforeign hw hm).1
  · intro o i p ho hw hm
    subst ho
    exact (bankWindowRootForeignComparatorStep ring hn hbank seed pre
      e hJ hx o i p hforeign hw hm).2.1
  · intro o i p ho hw hm
    subst ho
    exact (bankWindowRootForeignComparatorStep ring hn hbank seed pre
      e hJ hx o i p hforeign hw hm).2.2
  · intro hs
    exact absurd hs hnoscope
  · intro hs
    exact absurd hs hnoscope
  · intro o p hs
    exact absurd hs hnoscope
  · intro o i p hs
    exact absurd hs hnoscope
  · intro o i p ho hw horig hm hc
    subst ho
    exact bankWindowRootForeignCompareExactOnSource ring hn hbank seed pre
      e hJ hx o i p hforeign hw horig hm hc
  · intro hs
    exact absurd hs hnoscope
  · intro hs
    exact absurd hs hnoscope
  · intro limit hrun
    exact hjoint.2.2.2.1 root limit hforeign hrun
  · intro j
    exact hjoint.2.2.2.2 root j hforeign

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open L3.BankComparatorExclusive
open L3.BankHeadThreshold
open L3.BankCounterRows
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- A root whose physical mode is RESET and whose controller is not
inherited satisfies every root-indexed clause once its proto and orphan
clauses are known: every other clause is guarded by a non-RESET mode,
by CWAIT, or by an inherited controller.
Consumer: bankWindowOverlapChangedResponderRootFieldsAt and
bankWindowOverlapIncomingGrantOrArmedRootFieldsAt. -/
theorem bankWindowRootFieldsAtOfReset {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n) (root : Fin n)
    (hmode : (r.1 root).mode = .RESET)
    (hinherited : ¬ BankWindowInheritedController r root)
    (hproto : ∀ limit : Nat, BankWindowProtoRun ring r root limit →
      BankWindowRootForeignProtoField ring r root limit)
    (horphan : ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowOrphanOwner ring r root j →
      BankWindowTainted r (Counter.site ring root (j.val + 1)) →
      (r.1 root).mode = .RESET ∨
        ((r.1 root).mode = .RWAIT ∧
          (r.2.sites root).controller = .waiting [])) :
    BankWindowRootFieldsAt ring r root := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hproto, horphan⟩
  · intro o i p ho _
    subst ho
    rw [hmode]
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;> cases h
  · intro o i p ho _ hm
    subst ho
    rw [hmode] at hm
    cases hm
  · intro o i p ho _ hm
    subst ho
    rw [hmode] at hm
    cases hm
  · intro o i p ho _ hm
    subst ho
    rw [hmode] at hm
    cases hm
  · intro _ hi
    exact absurd hi hinherited
  · intro _ hm
    rw [hmode] at hm
    cases hm
  · intro o p _ hm
    rw [hmode] at hm
    rcases hm with h | h <;> cases h
  · intro o i p _ hm
    rw [hmode] at hm
    cases hm
  · intro o i p ho _ _ hm
    subst ho
    rw [hmode] at hm
    cases hm
  · intro _ hm
    rw [hmode] at hm
    cases hm
  · intro _ hm
    rw [hmode] at hm
    cases hm

/-- Changed-PACK responder (any selected edge whose responder PACK is
rewritten, root source or repair): the responder is RESET with a clean
controller, so every root-indexed POST clause holds at it.
Consumer: bankWindowExactStep, responder of a PACK-changing edge. -/
theorem bankWindowOverlapChangedResponderRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hchanged :
      packNext
        ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val
        ((rbRun ring (renewalBankStart ring seed) pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      ((rbRun ring (renewalBankStart ring seed) pre).1
        (ring.rightNeighbor e)).pack.val) :
    BankWindowRootFieldsAt ring
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
      (ring.rightNeighbor e) := by
  obtain ⟨hmode, hproto, horphan, _⟩ :=
    bankWindowOverlapChangedResponderOwnerFields ring hn hbank seed pre e
      hJ hchanged
  have hclean := bankWindowClosureChangedDigitClean ring hn hbank
    (rbRun ring (renewalBankStart ring seed) pre) e hchanged
  exact bankWindowRootFieldsAtOfReset ring
    (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
    (ring.rightNeighbor e) hmode hclean.2.2.2.2 hproto horphan

/-- Incoming PACK-zero root with an OLD grant or OLD ARMED mode: the
real row resets it with an empty controller, so every root-indexed POST
clause holds at it (including PACK-changing exits).
Consumer: bankWindowExactStep, IN class, grant/ARMED rows. -/
theorem bankWindowOverlapIncomingGrantOrArmedRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hy : ((rbRun ring (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)).pack.val = 0)
    (hgate : ((rbRun ring (renewalBankStart ring seed) pre).1
        (ring.rightNeighbor e)).grant = true ∨
      ((rbRun ring (renewalBankStart ring seed) pre).1
        (ring.rightNeighbor e)).mode = .ARMED) :
    BankWindowRootFieldsAt ring
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
      (ring.rightNeighbor e) := by
  obtain ⟨hmode, hcontroller, hproto, horphan⟩ :=
    bankWindowOverlapIncomingGrantOrArmedOwnerFields ring hn hbank seed pre
      e hJ hy hgate
  have hinherited : ¬ BankWindowInheritedController
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
      (ring.rightNeighbor e) := by
    intro hi
    rcases hi with ⟨atoms, hc, _⟩ | ⟨p, hc, _⟩
    · rw [hcontroller] at hc
      cases hc
    · rw [hcontroller] at hc
      cases hc
  exact bankWindowRootFieldsAtOfReset ring
    (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
    (ring.rightNeighbor e) hmode hinherited hproto horphan

/-- Repair edge (nonzero source PACK, changed responder PACK), a root
other than both endpoints whose POST window is incomplete: no POST scope,
so only the proto, orphan and comparator clauses are live, and the
repair bundle supplies each of them.
Consumer: bankWindowExactStep, repair edge, incomplete foreign roots. -/
theorem bankWindowOverlapRepairIncompleteForeignRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hnonroot :
      ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ≠ 0)
    (hchanged :
      packNext
        ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val
        ((rbRun ring (renewalBankStart ring seed) pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      ((rbRun ring (renewalBankStart ring seed) pre).1
        (ring.rightNeighbor e)).pack.val)
    (hforeign : root ≠ e ∧ root ≠ ring.rightNeighbor e)
    (hincomplete : ¬ Counter.Complete ring
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1
      root) :
    BankWindowRootFieldsAt ring
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
      root := by
  obtain ⟨hproto, horphan, hexcl, hcomp, hcompare⟩ :=
    bankWindowOverlapRepairIncompleteForeignFieldBundle ring hn hbank seed
      pre e root hJ hnonroot hchanged hforeign hincomplete
  have hnoscope : ¬ BankWindowScope ring
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
      root := fun hs => hincomplete hs.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hproto, horphan⟩
  · intro o i p ho hw
    have h := hexcl o i p ho hw
    subst ho
    exact h
  · intro o i p ho hw hm
    have hm' := hm
    rw [ho] at hm'
    exact absurd (hcomp o i p ho hw hm') id
  · intro o i p ho hw hm
    have hm' := hm
    rw [ho] at hm'
    exact absurd (hcomp o i p ho hw hm') id
  · intro o i p ho hw hm
    have hm' := hm
    rw [ho] at hm'
    exact absurd (hcomp o i p ho hw hm') id
  · intro hs
    exact absurd hs hnoscope
  · intro hs
    exact absurd hs hnoscope
  · intro o p hs
    exact absurd hs hnoscope
  · intro o i p hs
    exact absurd hs hnoscope
  · intro o i p ho hw horig hm hc
    have hm' := hm
    have hc' := hc
    rw [ho] at hm' hc'
    exact absurd (hcompare o i p ho hw horig hm' hc') id
  · intro hs
    exact absurd hs hnoscope
  · intro hs
    exact absurd hs hnoscope

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- An empty controller is not inherited.
Consumer: the RESET-exit root bundles below. -/
theorem bankWindowEmptyControllerNotInherited {n : Nat}
    (r : RenewalBankReference n) (root : Fin n)
    (hcontroller : (r.2.sites root).controller = .empty) :
    ¬ BankWindowInheritedController r root := by
  intro hi
  rcases hi with ⟨atoms, hc, _⟩ | ⟨p, hc, _⟩
  · rw [hcontroller] at hc
    cases hc
  · rw [hcontroller] at hc
    cases hc

/-- Selected source root with an OLD grant: the real row resets it with
an empty controller, so every root-indexed POST clause holds at it.
Consumer: bankWindowExactStep, own source root, grant row. -/
theorem bankWindowOverlapRootGrantRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (root : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hroot : ((rbRun ring (renewalBankStart ring seed) pre).1 root).pack.val = 0)
    (hgrant : ((rbRun ring (renewalBankStart ring seed) pre).1 root).grant = true) :
    BankWindowRootFieldsAt ring
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) root)
      root := by
  obtain ⟨hmode, hcontroller, hproto, horphan⟩ :=
    bankWindowOverlapRootGrantPrefixOrphan ring hn hbank seed pre root hJ
      hroot hgrant
  exact bankWindowRootFieldsAtOfReset ring
    (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) root)
    root hmode
    (bankWindowEmptyControllerNotInherited _ root hcontroller)
    hproto horphan

/-- Selected source root whose first responder PACK changes, in RESET,
ARMED, CSTART, or an expiring RWAIT/IWAIT/CWAIT row: the real row resets
it with an empty controller, so every root-indexed POST clause holds.
Consumer: bankWindowExactStep, own source root, changed-exit rows. -/
theorem bankWindowOverlapChangedSourceExitRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (root : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hroot : ((rbRun ring (renewalBankStart ring seed) pre).1 root).pack.val = 0)
    (hchanged :
      packNext
        ((rbRun ring (renewalBankStart ring seed) pre).1 root).pack.val
        ((rbRun ring (renewalBankStart ring seed) pre).1
          (ring.rightNeighbor root)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      ((rbRun ring (renewalBankStart ring seed) pre).1
        (ring.rightNeighbor root)).pack.val)
    (hphase :
      ((rbRun ring (renewalBankStart ring seed) pre).1 root).mode = .RESET ∨
      ((rbRun ring (renewalBankStart ring seed) pre).1 root).mode = .ARMED ∨
      ((rbRun ring (renewalBankStart ring seed) pre).1 root).mode = .CSTART ∨
      (((rbRun ring (renewalBankStart ring seed) pre).1 root).mode = .RWAIT ∨
        ((rbRun ring (renewalBankStart ring seed) pre).1 root).mode = .IWAIT ∨
        ((rbRun ring (renewalBankStart ring seed) pre).1 root).mode = .CWAIT) ∧
        ((rbRun ring (renewalBankStart ring seed) pre).1 root).lease.val ≤ 1) :
    BankWindowRootFieldsAt ring
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) root)
      root := by
  obtain ⟨hmode, hcontroller, hproto, horphan⟩ :=
    bankWindowOverlapChangedSourceExitPrefixOrphan ring hn hbank seed pre
      root hJ hroot hchanged hphase
  exact bankWindowRootFieldsAtOfReset ring
    (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) root)
    root hmode
    (bankWindowEmptyControllerNotInherited _ root hcontroller)
    hproto horphan

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open L3.BankComparatorExclusive
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The clockwise successor is injective (local copy; the BankRepairDigit
version is not in this import closure).
Consumer: bankWindowOverlapRepairCompletedForeignRootFieldsAt. -/
theorem bankWindowJointSuccessorInjective {n : Nat}
    (ring : DirectedRing n) (a b : Fin n)
    (h : ring.rightNeighbor a = ring.rightNeighbor b) : a = b := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  change (a.val + 1) % n = (b.val + 1) % n at hv
  have ha := a.isLt
  have hb := b.isLt
  have hA : (a.val + 1) % n = (if a.val + 1 < n then a.val + 1 else 0) := by
    by_cases h1 : a.val + 1 < n
    · rw [if_pos h1, Nat.mod_eq_of_lt h1]
    · rw [if_neg h1, show a.val + 1 = n by omega, Nat.mod_self]
  have hB : (b.val + 1) % n = (if b.val + 1 < n then b.val + 1 else 0) := by
    by_cases h1 : b.val + 1 < n
    · rw [if_pos h1, Nat.mod_eq_of_lt h1]
    · rw [if_neg h1, show b.val + 1 = n by omega, Nat.mod_self]
  rw [hA, hB] at hv
  split at hv <;> split at hv <;> omega

/-- M4. Repair edge (nonzero source PACK, changed responder PACK), a
root other than both endpoints whose window is incomplete before and
complete after the step. The repaired responder is the old first
mismatch D_root(t), the source is D_root(t-1), and OLD J.proto at limit
t-1 and OLD J.orphan beyond t give: inheritedClean (an inherited
controller is neither RESET, whose controller is empty by the in-flight
frame, nor RWAIT with an empty waiting list), the resetWait front (the
OLD pending RR front lies in the aligned prefix; before the source it is
framed, at the source bankWindowOverlapRepairPendingRrKeeps keeps it),
and both waiting-mode taint clauses (no POST taint at all in a non-RESET,
non-RWAIT root, bankWindowClosureRepairNonresetPhaseDigitsClean). All
other clauses are vacuous or come from the repair-completion theorems.
Consumer: bankWindowExactStep, repair edge, newly completed foreign
roots (ledger row M4). -/
theorem bankWindowOverlapRepairCompletedForeignRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hnonroot :
      ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ≠ 0)
    (hchanged :
      packNext
        ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val
        ((rbRun ring (renewalBankStart ring seed) pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      ((rbRun ring (renewalBankStart ring seed) pre).1
        (ring.rightNeighbor e)).pack.val)
    (hforeign : root ≠ e ∧ root ≠ ring.rightNeighbor e)
    (hcomplete : Counter.Complete ring
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1
      root)
    (hnot : ¬ Counter.Complete ring
      (rbRun ring (renewalBankStart ring seed) pre).1 root) :
    BankWindowRootFieldsAt ring
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
      root := by
  obtain ⟨hnoproto, hnoorphan, hnoactive, _⟩ :=
    bankWindowOverlapRepairCompletedForeignFields ring hn hbank seed pre
      e root hJ hforeign hchanged hcomplete hnot
  have hframeRoot := bankWindowExactOffPairFrame ring
    (rbRun ring (renewalBankStart ring seed) pre) e root
    hforeign.1 hforeign.2
  have hctrl :
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites
        root).controller =
      ((rbRun ring (renewalBankStart ring seed) pre).2.sites root).controller :=
    congrArg (fun a : RenewalBankSite n => a.controller) hframeRoot.2
  have hmodeEq :
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1
        root).mode =
      ((rbRun ring (renewalBankStart ring seed) pre).1 root).mode :=
    congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.mode)
      hframeRoot.1
  obtain ⟨t, htb, hsite, hwrong, hother⟩ :=
    bankWindowClosureRepairFirstMismatchAtResponder ring (by omega : 2 ≤ n)
      (rbRun ring (renewalBankStart ring seed) pre) e root hcomplete hnot
  have ht1 : 1 ≤ t := by
    by_cases hzero : t = 0
    · rw [hzero] at hsite
      exact False.elim (hforeign.2 hsite)
    · omega
  let j0 : Fin (compileAdvice (ceilLogTwo n)).b :=
    ⟨t - 1, (show t - 1 < (compileAdvice (ceilLogTwo n)).b by omega)⟩
  have htarget :
      ring.rightNeighbor e = Counter.site ring root (j0.val + 1) := by
    change ring.rightNeighbor e = Counter.site ring root (t - 1 + 1)
    rw [show t - 1 + 1 = t by omega]
    exact hsite.symm
  have hsrc : e = Counter.site ring root (t - 1) := by
    apply bankWindowJointSuccessorInjective ring
    have hstep : Counter.site ring root (t - 1 + 1) =
        ring.rightNeighbor (Counter.site ring root (t - 1)) := rfl
    rw [← hstep, show t - 1 + 1 = t by omega]
    exact hsite.symm
  have hprotoOld := bankWindowClosureRepairOldProtoAtDigit ring hn
    (rbRun ring (renewalBankStart ring seed) pre) e root j0
    hchanged htarget hcomplete
  have hP := hJ.proto root j0.val hprotoOld
  have hclean := bankWindowClosureChangedDigitClean ring hn hbank
    (rbRun ring (renewalBankStart ring seed) pre) e hchanged
  have htaintOld := bankWindowClosureChangedTaintOld ring hn hbank
    (rbRun ring (renewalBankStart ring seed) pre) e hchanged
  have hrootPack :
      ((rbRun ring (renewalBankStart ring seed) pre).1 root).pack.val = 0 :=
    hother 0 (Nat.zero_le _) (fun h => hforeign.2 h)
  have hEarly : ∀ m : Nat, m < t - 1 →
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1
          (Counter.site ring root m) =
        (rbRun ring (renewalBankStart ring seed) pre).1
          (Counter.site ring root m) ∧
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites
          (Counter.site ring root m) =
        (rbRun ring (renewalBankStart ring seed) pre).2.sites
          (Counter.site ring root m) := by
    intro m hm
    exact bankWindowOverlapRepairEarlierSiteFrame ring hbank
      (rbRun ring (renewalBankStart ring seed) pre) e root (t - 1) m
      hsrc (by omega) hm
  -- No POST taint at all when the (framed) mode is neither RESET nor RWAIT.
  have hnotaint : ((rbRun ring (renewalBankStart ring seed) pre).1 root).mode ≠
        .RESET →
      ((rbRun ring (renewalBankStart ring seed) pre).1 root).mode ≠ .RWAIT →
      ∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
        ¬ BankWindowTainted
          (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
          (Counter.site ring root (k.val + 1)) := fun hr hw =>
    bankWindowClosureRepairNonresetPhaseDigitsClean ring hn hbank
      (rbRun ring (renewalBankStart ring seed) pre) e root hJ j0
      hchanged htarget hcomplete hr hw
  -- A comparator or genuine worker of this root in a non-RESET,
  -- non-RWAIT mode is impossible.
  have hnoworker : ∀ (i : Fin n) (p : RenewalBankPayload n)
      (o : RenewalBankOrigin n),
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1
        root).mode ≠ .RESET →
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1
        root).mode ≠ .RWAIT →
      o.root = root →
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites
        i).worker = .payload p →
      p.origin = some o → False := by
    intro i p o hr hw horoot hwk ho
    exact bankWindowOverlapRepairCompletedForeignNoOriginWorker ring hn hbank
      seed pre e root hJ hforeign hchanged hcomplete hnot hr hw
      i p o horoot hwk ho
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- phaseExcludes
    intro o i p ho hw
    have h := bankWindowOverlapRepairForeignPhaseExcludes ring hn hbank seed
      pre e hJ hchanged hnonroot o i p (by rw [ho]; exact hforeign) hw
    exact h
  · -- phaseComplete
    intro o i p ho _ _
    rw [ho]
    exact hcomplete
  · -- phaseUnique
    intro o i p ho hw hm
    rw [ho] at hm
    exact False.elim (hnoworker i p o (by rw [hm]; intro h; cases h)
      (by rw [hm]; intro h; cases h) ho hw.1 hw.2.1)
  · -- phaseFlags
    intro o i p ho hw hm
    rw [ho] at hm
    exact False.elim (hnoworker i p o (by rw [hm]; intro h; cases h)
      (by rw [hm]; intro h; cases h) ho hw.1 hw.2.1)
  · -- inheritedClean
    intro _ hi j ht
    have hiOld : BankWindowInheritedController
        (rbRun ring (renewalBankStart ring seed) pre) root := by
      unfold BankWindowInheritedController at hi ⊢
      rw [hctrl] at hi
      exact hi
    have htOld := htaintOld _ ht
    by_cases hlt : j.val + 1 ≤ j0.val
    · exact hP.2.1 hiOld j hlt htOld
    by_cases heq : j.val + 1 = t
    · apply hclean.2.2.2.1
      rw [← hsite, ← heq]
      exact ht
    · have hj0 : j0.val = t - 1 := rfl
      have hjb := j.isLt
      have hne : Counter.site ring root (j.val + 1) ≠ ring.rightNeighbor e := by
        intro hs'
        have h1 := hcomplete (j.val + 1) (by omega)
        have h2 := hcomplete t htb
        rw [hs'] at h1
        rw [hsite] at h2
        omega
      have hown : BankWindowOrphanOwner ring
          (rbRun ring (renewalBankStart ring seed) pre) root j :=
        ⟨hrootPack, hother (j.val + 1) (by omega) hne,
          fun hall => hwrong (hall t (by omega))⟩
      rcases hJ.orphan root j hown htOld with hreset | ⟨_, hwaitc⟩
      · have hf := (hJ.frame root).1
        unfold bankInFlightControllerShape at hf
        rw [if_pos hrootPack, hreset] at hf
        have hce : ((rbRun ring (renewalBankStart ring seed) pre).2.sites
            root).controller = .empty := hf
        rcases hiOld with ⟨atoms, hc, _⟩ | ⟨p, hc, _⟩
        · rw [hce] at hc
          cases hc
        · rw [hce] at hc
          cases hc
      · rcases hiOld with ⟨atoms, hc, hnil⟩ | ⟨p, hc, _⟩
        · rw [hwaitc] at hc
          injection hc with hatoms
          exact hnil hatoms.symm
        · rw [hwaitc] at hc
          cases hc
  · -- resetWait
    intro _ hm hc
    have hmOld := hmodeEq.symm.trans hm
    have hcOld := hctrl.symm.trans hc
    obtain ⟨j, hjle, rho, hw, htok, hzero, hearly⟩ := hP.2.2.1 ⟨hmOld, hcOld⟩
    have hj0 : j0.val = t - 1 := rfl
    rw [hj0] at hjle
    have hearlyNew : ∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
        k.val < j.val →
        ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1
          (Counter.site ring root (k.val + 1))).tok = .E := by
      intro k hk
      rw [congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
        (hEarly (k.val + 1) (by omega)).1]
      exact hearly k hk
    by_cases hA : j.val + 1 < t - 1
    · have hfr := hEarly (j.val + 1) hA
      refine ⟨j, rho, ?_, Or.inl ?_, ?_, hearlyNew, ?_⟩
      · rw [congrArg (fun a : RenewalBankSite n => a.worker) hfr.2]
        exact hw
      · rw [congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
          hfr.1]
        exact htok
      · intro k hk
        rw [congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.bit)
          (hEarly (k.val + 1) (by omega)).1]
        exact hzero k hk
      · intro hRL
        rw [congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
          hfr.1, htok] at hRL
        cases hRL
    · have hB : j.val + 1 = t - 1 := by omega
      have hsj : Counter.site ring root (j.val + 1) = e := by
        rw [hB]
        exact hsrc.symm
      rw [hsj] at hw htok
      have hkeep := bankWindowOverlapRepairPendingRrKeeps ring hn hbank seed
        pre e rho hchanged htok hw
      refine ⟨j, rho, ?_, Or.inl ?_, ?_, hearlyNew, ?_⟩
      · rw [hsj]
        exact hkeep.2.2.1
      · rw [hsj]
        exact hkeep.1
      · intro k hk
        by_cases hkA : k.val + 1 < t - 1
        · rw [congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.bit)
            (hEarly (k.val + 1) hkA).1]
          exact hzero k hk
        · have hsk : Counter.site ring root (k.val + 1) = e := by
            rw [show k.val + 1 = t - 1 by omega]
            exact hsrc.symm
          have hold := hzero k hk
          rw [hsk] at hold ⊢
          rw [hkeep.2.1]
          exact hold
      · intro hRL
        rw [hsj, hkeep.1] at hRL
        cases hRL
  · -- armedExact
    intro o p _ _ hact horig
    exact False.elim (hnoactive p o hact horig)
  · -- incrementExact
    intro o i p _ hm _ hw horig horoot
    exact False.elim (hnoworker i p o (by rw [hm]; intro h; cases h)
      (by rw [hm]; intro h; cases h) horoot hw horig)
  · -- compareExact
    intro o i p ho hw horig hm _
    rw [ho] at hm
    exact False.elim (hnoworker i p o (by rw [hm]; intro h; cases h)
      (by rw [hm]; intro h; cases h) ho hw horig)
  · -- iwaitTaintedUnique
    intro _ hm _ j ht
    have hmOld := hmodeEq.symm.trans hm
    exact False.elim (hnotaint (by rw [hmOld]; intro h; cases h)
      (by rw [hmOld]; intro h; cases h) j ht)
  · -- cwaitTaintedUnique
    intro _ hm _ j ht
    have hmOld := hmodeEq.symm.trans hm
    exact False.elim (hnotaint (by rw [hmOld]; intro h; cases h)
      (by rw [hmOld]; intro h; cases h) j ht)
  · intro limit hrun
    exact False.elim (hnoproto limit hrun)
  · intro j hown
    exact False.elim (hnoorphan j hown)

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Projection of a pure Id pair (definitional; a simp normal form for
the unfolded do-block of Base.bankPair).
Consumer: bankWindowJointPairNonrootModes. -/
theorem bankWindowJointIdPureFst {α β : Type} (a : α × β) :
    (pure a : Id (α × β)).1 = a.1 := rfl

/-- Second projection of a pure Id pair.
Consumer: bankWindowJointPairNonrootModes. -/
theorem bankWindowJointIdPureSnd {α β : Type} (a : α × β) :
    (pure a : Id (α × β)).2 = a.2 := rfl

/-- Symbolic BANK pair: an endpoint whose (post) role is nonzero leaves
the pair in physical mode RESET (Base.bankPair resets the mode of every
nonroot endpoint before any branch, and no later branch of a nonroot
endpoint writes its mode).
Consumer: bankWindowJointEndpointNonrootReset. -/
theorem bankWindowJointPairNonrootModes
    (x y : BankCell) (postY b : Nat) (theta : Nat → Bool) :
    (x.role ≠ 0 → (bankPair x y postY b theta).1.mode = .RESET) ∧
    (postY ≠ 0 → (bankPair x y postY b theta).2.mode = .RESET) := by
  constructor
  · intro hx
    exact (bankPair_nonroot_fst_mode x y postY b theta hx).1
  · intro hy
    exact (bankPair_snd_reset x y postY b theta hy).1

/-- On the actual selected BANK edge, the source with nonzero PACK and
the responder with nonzero POST PACK are both in physical mode RESET
after the step.
Consumer: bankWindowOverlapSourceNonrootRootFieldsAt and
bankWindowOverlapResponderNonrootRootFieldsAt. -/
theorem bankWindowJointEndpointNonrootReset {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n) :
    ((r.1 e).pack.val ≠ 0 →
      ((renewalBankNext ring r e).1 e).mode = .RESET) ∧
    (((renewalBankNext ring r e).1 (ring.rightNeighbor e)).pack.val ≠ 0 →
      ((renewalBankNext ring r e).1 (ring.rightNeighbor e)).mode = .RESET) := by
  have htrip := bankWindowClosureSelectedBankTrip ring hn hbank r e
  have hsym := bankWindowJointPairNonrootModes
    (bankCell (r.1 e) (r.1 e).pack.val)
    (bankCell (r.1 (ring.rightNeighbor e))
      (r.1 (ring.rightNeighbor e)).pack.val)
    (packNext (r.1 e).pack.val (r.1 (ring.rightNeighbor e)).pack.val
      (compileAdvice (ceilLogTwo n)).b)
    (compileAdvice (ceilLogTwo n)).b
    (compileAdvice (ceilLogTwo n)).theta
  have hresp := bankWindowExactResponderPack ring r e
    (clockNeighborDifferent ring (by omega : 2 ≤ n) e)
  constructor
  · intro hx
    have hmode := congrArg (fun t : Mode × Bool × BTok => t.1) htrip.1
    change ((renewalBankNext ring r e).1 e).mode =
      (Counter.resetBankOld (r.1 e) (r.1 (ring.rightNeighbor e))).1.mode
      at hmode
    unfold Counter.resetBankOld at hmode
    exact hmode.trans (hsym.1 (by change (r.1 e).pack.val ≠ 0; exact hx))
  · intro hy
    have hmode := congrArg (fun t : Mode × Bool × BTok => t.1) htrip.2
    change ((renewalBankNext ring r e).1 (ring.rightNeighbor e)).mode =
      (Counter.resetBankOld (r.1 e) (r.1 (ring.rightNeighbor e))).2.mode
      at hmode
    unfold Counter.resetBankOld at hmode
    exact hmode.trans (hsym.2 (by rw [← hresp]; exact hy))

/-- A site with nonzero PACK and physical mode RESET, in a state with
the in-flight frame, satisfies every root-indexed clause: the frame
empties its controller, proto-runs and orphan owners need PACK zero at
the root, and every comparator/active clause is mode-guarded.
Consumer: the two nonroot-endpoint bundles below (ledger row M1). -/
theorem bankWindowRootFieldsAtOfNonroot {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n) (z : Fin n)
    (hframe : BankInFlightAligned ring r)
    (hpack : (r.1 z).pack.val ≠ 0)
    (hmode : (r.1 z).mode = .RESET) :
    BankWindowRootFieldsAt ring r z := by
  have hf := (hframe z).1
  unfold bankInFlightControllerShape at hf
  rw [if_neg hpack] at hf
  apply bankWindowRootFieldsAtOfReset ring r z hmode
    (bankWindowEmptyControllerNotInherited r z hf)
  · intro limit hrun
    exact absurd (hrun.2.1 0 (Nat.zero_le _)) hpack
  · intro j hown
    exact absurd hown.1 hpack

/-- M1, source endpoint: on every selected edge whose source has nonzero
PACK, every root-indexed POST clause holds at the source, in particular
all comparator and compareExact clauses for origins rooted there
(whether or not such origins exist in reached states).
Consumer: bankWindowExactStep, root = e with nonzero source PACK. -/
theorem bankWindowOverlapSourceNonrootRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hnonroot :
      ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ≠ 0) :
    BankWindowRootFieldsAt ring
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
      e := by
  have hpack := (rbBankReferencePairPack ring (by omega : 2 ≤ n)
    (rbRun ring (renewalBankStart ring seed) pre) e).1
  change ((renewalBankNext ring
    (rbRun ring (renewalBankStart ring seed) pre) e).1 e).pack.val =
    ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val at hpack
  exact bankWindowRootFieldsAtOfNonroot ring _ e
    (bankWindowOverlapRootJointFields ring hn hbank seed pre e hJ).1
    (by rw [hpack]; exact hnonroot)
    ((bankWindowJointEndpointNonrootReset ring hn hbank
      (rbRun ring (renewalBankStart ring seed) pre) e).1 hnonroot)

/-- M1, responder endpoint: on every selected edge whose responder has
nonzero POST PACK (root-source edges, repairs, stable interior and top
edges), every root-indexed POST clause holds at the responder.
Consumer: bankWindowExactStep, root = e+ with nonzero POST PACK. -/
theorem bankWindowOverlapResponderNonrootRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hpost :
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1
        (ring.rightNeighbor e)).pack.val ≠ 0) :
    BankWindowRootFieldsAt ring
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
      (ring.rightNeighbor e) :=
  bankWindowRootFieldsAtOfNonroot ring _ (ring.rightNeighbor e)
    (bankWindowOverlapRootJointFields ring hn hbank seed pre e hJ).1
    hpost
    ((bankWindowJointEndpointNonrootReset ring hn hbank
      (rbRun ring (renewalBankStart ring seed) pre) e).2 hpost)

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open L3.BankComparatorExclusive
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Symbolic BANK pair, nonroot source and PACK-zero responder that stays
PACK zero: the responder either keeps its mode or is RESET (grant, ARMED
and lease expiry reset it; every other branch leaves its mode alone).
Consumer: bankWindowJointIncomingModeKeepOrReset. -/
theorem bankWindowJointIncomingZeroModeKeepOrResetCell
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : x.role ≠ 0) (hy : y.role = 0) :
    (bankPair x y 0 b theta).2.mode = y.mode ∨
    (bankPair x y 0 b theta).2.mode = .RESET := by
  rw [(bankPair_snd_mode x y 0 b theta).1]
  unfold bankPairModeY
  (repeat' split) <;> simp

/-- On the actual BANK edge into a PACK-zero responder that stays PACK
zero, the responder either keeps its physical mode or is RESET.
Consumer: bankWindowOverlapIncomingStableRootFieldsAt. -/
theorem bankWindowJointIncomingModeKeepOrReset {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 0)
    (hpost : ((renewalBankNext ring r e).1
      (ring.rightNeighbor e)).pack.val = 0) :
    ((renewalBankNext ring r e).1 (ring.rightNeighbor e)).mode =
        (r.1 (ring.rightNeighbor e)).mode ∨
    ((renewalBankNext ring r e).1 (ring.rightNeighbor e)).mode = .RESET := by
  have hx := bankWindowOverlapIncomingSourceNonzero ring hn r e hy hpost
  have hstep := bankWindowExactResponderPack ring r e
    (clockNeighborDifferent ring (by omega : 2 ≤ n) e)
  have hpack :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b = 0 :=
    hstep.symm.trans hpost
  have htriple := (bankWindowClosureSelectedBankTrip ring hn hbank r e).2
  have hmode := congrArg (fun t : Mode × Bool × BTok => t.1) htriple
  change ((renewalBankNext ring r e).1 (ring.rightNeighbor e)).mode =
    (Counter.resetBankOld (r.1 e) (r.1 (ring.rightNeighbor e))).2.mode
    at hmode
  unfold Counter.resetBankOld at hmode
  rw [hpack] at hmode
  rcases bankWindowJointIncomingZeroModeKeepOrResetCell
      (bankCell (r.1 e) (r.1 e).pack.val)
      (bankCell (r.1 (ring.rightNeighbor e))
        (r.1 (ring.rightNeighbor e)).pack.val)
      (compileAdvice (ceilLogTwo n)).b
      (compileAdvice (ceilLogTwo n)).theta
      (by change (r.1 e).pack.val ≠ 0; exact hx)
      (by change (r.1 (ring.rightNeighbor e)).pack.val = 0; exact hy)
    with h | h
  · exact Or.inl (hmode.trans h)
  · exact Or.inr (hmode.trans h)

/-- Frozen-root transport: if the step frames every digit of a root's
window, keeps the root's PACK, mode and controller (and its grant under
POST scope), frames every site carrying a genuine worker of an origin
rooted there, and every POST genuine active controller at the root is
its own origin's, then every root-indexed POST clause follows from OLD J
through the merged read-set transports.
Consumer: bankWindowOverlapIncomingStableRootFieldsAt (ledger row M7). -/
theorem bankWindowRootFieldsAtOfFrozen {n : Nat}
    (ring : DirectedRing n) (r s : RenewalBankReference n) (root : Fin n)
    (hJ : BankWindowExact ring r)
    (hdigits : ∀ k : Nat, 1 ≤ k → k ≤ (compileAdvice (ceilLogTwo n)).b →
      s.1 (Counter.site ring root k) = r.1 (Counter.site ring root k) ∧
      s.2.sites (Counter.site ring root k) =
        r.2.sites (Counter.site ring root k))
    (hpack : (s.1 root).pack.val = (r.1 root).pack.val)
    (hmode : (s.1 root).mode = (r.1 root).mode)
    (hctrl : (s.2.sites root).controller = (r.2.sites root).controller)
    (hgrant : BankWindowScope ring s root →
      (s.1 root).grant = (r.1 root).grant)
    (hworkers : ∀ (i : Fin n) (p : RenewalBankPayload n)
      (o : RenewalBankOrigin n), o.root = root →
      (s.2.sites i).worker = .payload p → p.origin = some o →
      s.1 i = r.1 i ∧ s.2.sites i = r.2.sites i)
    (hactive : ∀ (p : RenewalBankPayload n) (o : RenewalBankOrigin n),
      (s.2.sites root).controller = .active p → p.origin = some o →
      o.root = root) :
    BankWindowRootFieldsAt ring s root := by
  have hP : bankWindowReadPackPrefix ring r s root
      (compileAdvice (ceilLogTwo n)).b := by
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0
      exact hpack
    · exact congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.pack.val)
        (hdigits k (by omega) hk).1
  have hdig : ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      s.1 (Counter.site ring root (j.val + 1)) =
        r.1 (Counter.site ring root (j.val + 1)) ∧
      s.2.sites (Counter.site ring root (j.val + 1)) =
        r.2.sites (Counter.site ring root (j.val + 1)) := by
    intro j
    have hj := j.isLt
    exact hdigits (j.val + 1) (by omega) (by omega)
  have hT : bankWindowReadDigitTokens ring r s root := fun j =>
    congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
      (hdig j).1
  have hB : bankWindowReadDigitBits ring r s root := fun j =>
    congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.bit)
      (hdig j).1
  have hW : ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      bankWindowReadWorker r s (Counter.site ring root (j.val + 1)) := fun j =>
    congrArg (fun a : RenewalBankSite n => a.worker) (hdig j).2
  have hfree : ∀ (o : RenewalBankOrigin n) (i : Fin n)
      (p : RenewalBankPayload n), o.root = root →
      BankComparatorOriginWorker ring s o i p →
      bankWindowPhaseExcludesReadSet r s o i p := by
    intro o i p ho hw
    have hwi := hworkers i p o ho hw.1 hw.2.1
    exact ⟨congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
        hwi.1,
      congrArg (fun a : RenewalBankSite n => a.worker) hwi.2,
      by rw [ho]; exact hmode⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o i p ho hw
    exact bankWindowPhaseExcludesReadTransport ring r s o i p hJ
      (hfree o i p ho hw) hw
  · intro o i p ho hw hm
    exact bankWindowPhaseCompleteReadTransport ring r s o i p hJ
      ⟨hfree o i p ho hw, by rw [ho]; exact hP⟩ hw hm
  · intro o i p ho hw hm j ht
    exact bankWindowPhaseUniqueReadTransport ring r s o i p hJ
      ⟨hfree o i p ho hw, by rw [ho]; exact hT⟩ hw hm j ht
  · intro o i p ho hw hm
    have hwi := hworkers i p o ho hw.1 hw.2.1
    exact bankWindowPhaseFlagsReadTransport ring r s o i p hJ
      ⟨hfree o i p ho hw,
        congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
          a.pack.val) hwi.1,
        by rw [ho]; exact hB⟩ hw hm
  · intro hs hi j ht
    exact bankWindowInheritedCleanReadTransport ring r s root j hJ
      ⟨hP, hgrant hs, hctrl, hW j⟩ hs hi ht
  · intro hs hm hc
    exact bankWindowResetWaitReadTransport ring r s root hJ
      ⟨hP, hgrant hs, hmode, hctrl, hB, hT, hW⟩ hs hm hc
  · intro o p hs hm hc ho
    have hor := hactive p o hc ho
    exact bankWindowArmedExactReadTransport ring r s root o p hJ
      ⟨hP, hgrant hs, hmode, hctrl, hT, by rw [hor]; exact hB⟩
      hs hm hc ho
  · intro o i p hs hm hc hw ho hr
    have hwi := hworkers i p o hr hw ho
    exact bankWindowIncrementExactReadTransport ring r s root o i p hJ
      ⟨hP, hgrant hs, hmode, hctrl,
        congrArg (fun a : RenewalBankSite n => a.worker) hwi.2,
        congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
          a.pack.val) hwi.1,
        congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
          hwi.1,
        hT, hB, by rw [hr]; exact hB⟩
      hs hm hc hw ho hr
  · intro o i p ho hw horig hm hc
    have hwi := hworkers i p o ho hw horig
    exact bankWindowCompareExactReadTransport ring r s o i p hJ
      ⟨by rw [ho]; exact hmode, by rw [ho]; exact hctrl,
        congrArg (fun a : RenewalBankSite n => a.worker) hwi.2,
        congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
          hwi.1,
        by rw [ho]; exact hT, by rw [ho]; exact hB⟩
      hw horig hm hc
  · intro hs hm hc j ht
    exact bankWindowIwaitTaintedUniqueReadTransport ring r s root j hJ
      ⟨hP, hgrant hs, hmode, hctrl, hT, hW j⟩ hs hm hc ht
  · intro hs hm hc j ht
    exact bankWindowCwaitTaintedUniqueReadTransport ring r s root j hJ
      ⟨hP, hgrant hs, hmode, hctrl, hT, hW j⟩ hs hm hc ht
  · intro limit hrun
    have hlim := hrun.1
    exact bankWindowProtoReadTransport ring r s root limit hJ
      ⟨fun k hk => hP k (by omega), hmode, hctrl,
        fun j _ => ⟨hT j, hB j, hW j⟩⟩ hrun
  · intro j hown ht
    have hj := j.isLt
    exact bankWindowOrphanReadTransport ring r s root j hJ
      ⟨fun k hk => hP k (by omega), hmode, hctrl, hW j⟩ hown ht

/-- M7. Incoming PACK-zero root whose PACK stays zero (every OLD mode and
grant): every root-indexed POST clause holds at it. Grant/ARMED rows use
bankWindowOverlapIncomingGrantOrArmedRootFieldsAt; a POST RESET root has
an empty controller by the POST frame and takes its proto/orphan clauses
from the per-mode incoming owner theorems; otherwise the mode is kept
(bankWindowJointIncomingModeKeepOrReset), so the controller is kept
(CSTART: bankWindowOverlapIncomingCstartControllerKeep; RWAIT/IWAIT/CWAIT:
bankWindowOverlapIncomingWaitingKeepsController), the whole digit window
lies off the pair, genuine workers of this root are off the pair
(bankWindowOverlapIncomingGenuineWorkerOffPair), active controllers are
own-rooted by the POST ReceiptInv, and the frozen-root transport applies.
Consumer: bankWindowExactStep, IN class (ledger row M7). -/
theorem bankWindowOverlapIncomingStableRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hy : ((rbRun ring (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)).pack.val = 0)
    (hpost : ((renewalBankNext ring
      (rbRun ring (renewalBankStart ring seed) pre) e).1
        (ring.rightNeighbor e)).pack.val = 0) :
    BankWindowRootFieldsAt ring
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
      (ring.rightNeighbor e) := by
  by_cases hgate :
      ((rbRun ring (renewalBankStart ring seed) pre).1
        (ring.rightNeighbor e)).grant = true ∨
      ((rbRun ring (renewalBankStart ring seed) pre).1
        (ring.rightNeighbor e)).mode = .ARMED
  · exact bankWindowOverlapIncomingGrantOrArmedRootFieldsAt ring hn hbank
      seed pre e hJ hy hgate
  have hg : ((rbRun ring (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)).grant = false := by
    cases h : ((rbRun ring (renewalBankStart ring seed) pre).1
        (ring.rightNeighbor e)).grant with
    | false => rfl
    | true => exact absurd (Or.inl h) hgate
  have harm : ((rbRun ring (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)).mode ≠ .ARMED := fun h => hgate (Or.inr h)
  have hjoint := bankWindowOverlapRootJointFields ring hn hbank seed pre e hJ
  have hOldCtrl : ((rbRun ring (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)).mode = .RESET →
      ((rbRun ring (renewalBankStart ring seed) pre).2.sites
        (ring.rightNeighbor e)).controller = .empty := by
    intro hm
    have hf := (hJ.frame (ring.rightNeighbor e)).1
    unfold bankInFlightControllerShape at hf
    rw [if_pos hy, hm] at hf
    exact hf
  by_cases hres : ((renewalBankNext ring
      (rbRun ring (renewalBankStart ring seed) pre) e).1
        (ring.rightNeighbor e)).mode = .RESET
  · have hce : ((renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e).2.sites
          (ring.rightNeighbor e)).controller = .empty := by
      have hf := (hjoint.1 (ring.rightNeighbor e)).1
      unfold bankInFlightControllerShape at hf
      rw [if_pos hpost, hres] at hf
      exact hf
    have howner :
        (∀ limit : Nat, BankWindowProtoRun ring
          (renewalBankNext ring
            (rbRun ring (renewalBankStart ring seed) pre) e)
          (ring.rightNeighbor e) limit →
          BankWindowRootForeignProtoField ring
            (renewalBankNext ring
              (rbRun ring (renewalBankStart ring seed) pre) e)
            (ring.rightNeighbor e) limit) ∧
        (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          BankWindowOrphanOwner ring
            (renewalBankNext ring
              (rbRun ring (renewalBankStart ring seed) pre) e)
            (ring.rightNeighbor e) j →
          BankWindowTainted
            (renewalBankNext ring
              (rbRun ring (renewalBankStart ring seed) pre) e)
            (Counter.site ring (ring.rightNeighbor e) (j.val + 1)) →
          ((renewalBankNext ring
            (rbRun ring (renewalBankStart ring seed) pre) e).1
              (ring.rightNeighbor e)).mode = .RESET ∨
          (((renewalBankNext ring
            (rbRun ring (renewalBankStart ring seed) pre) e).1
              (ring.rightNeighbor e)).mode = .RWAIT ∧
            ((renewalBankNext ring
              (rbRun ring (renewalBankStart ring seed) pre) e).2.sites
                (ring.rightNeighbor e)).controller = .waiting [])) := by
      cases hmo : ((rbRun ring (renewalBankStart ring seed) pre).1
          (ring.rightNeighbor e)).mode with
      | RESET =>
          exact bankWindowOverlapIncomingStableOwnerFields ring hbank
            (rbRun ring (renewalBankStart ring seed) pre) hJ
            (ring.rightNeighbor e) e rfl hy hpost
            (hres.trans hmo.symm) (hce.trans (hOldCtrl hmo).symm)
      | ARMED => exact absurd hmo harm
      | CSTART =>
          exact bankWindowOverlapIncomingCstartOwnerFields ring hn hbank
            seed pre e hJ hy hg hmo
      | RWAIT =>
          exact bankWindowOverlapIncomingWaitMultiwindowFields ring hn hbank
            seed pre e hJ hy hpost hg (Or.inl hmo)
      | IWAIT =>
          exact bankWindowOverlapIncomingWaitMultiwindowFields ring hn hbank
            seed pre e hJ hy hpost hg (Or.inr (Or.inl hmo))
      | CWAIT =>
          exact bankWindowOverlapIncomingWaitMultiwindowFields ring hn hbank
            seed pre e hJ hy hpost hg (Or.inr (Or.inr hmo))
    exact bankWindowRootFieldsAtOfReset ring _ (ring.rightNeighbor e) hres
      (bankWindowEmptyControllerNotInherited _ _ hce) howner.1 howner.2
  have hkeep : ((renewalBankNext ring
      (rbRun ring (renewalBankStart ring seed) pre) e).1
        (ring.rightNeighbor e)).mode =
      ((rbRun ring (renewalBankStart ring seed) pre).1
        (ring.rightNeighbor e)).mode := by
    rcases bankWindowJointIncomingModeKeepOrReset ring hn hbank
        (rbRun ring (renewalBankStart ring seed) pre) e hy hpost with h | h
    · exact h
    · exact absurd h hres
  have hctrl : ((renewalBankNext ring
      (rbRun ring (renewalBankStart ring seed) pre) e).2.sites
        (ring.rightNeighbor e)).controller =
      ((rbRun ring (renewalBankStart ring seed) pre).2.sites
        (ring.rightNeighbor e)).controller := by
    cases hmo : ((rbRun ring (renewalBankStart ring seed) pre).1
        (ring.rightNeighbor e)).mode with
    | RESET => exact absurd (hkeep.trans hmo) hres
    | ARMED => exact absurd hmo harm
    | CSTART =>
        exact (bankWindowOverlapIncomingCstartControllerKeep ring hn hbank
          seed pre e hJ hy hpost hg hmo).2
    | RWAIT =>
        exact (bankWindowOverlapIncomingWaitingKeepsController ring hn hbank
          seed pre e hJ hy hpost hg (Or.inl hmo) hkeep).2
    | IWAIT =>
        exact (bankWindowOverlapIncomingWaitingKeepsController ring hn hbank
          seed pre e hJ hy hpost hg (Or.inr (Or.inl hmo)) hkeep).2
    | CWAIT =>
        exact (bankWindowOverlapIncomingWaitingKeepsController ring hn hbank
          seed pre e hJ hy hpost hg (Or.inr (Or.inr hmo)) hkeep).2
  have hexcl := bankWindowGuardedGeometricExclusive ring hbank
  apply bankWindowRootFieldsAtOfFrozen ring
    (rbRun ring (renewalBankStart ring seed) pre) _ (ring.rightNeighbor e) hJ
  · intro k hk1 hkb
    exact bankWindowExactOffPairFrame ring
      (rbRun ring (renewalBankStart ring seed) pre) e
      (Counter.site ring (ring.rightNeighbor e) k)
      ((hexcl (ring.rightNeighbor e) e).1 k hkb rfl).symm
      ((hexcl (ring.rightNeighbor e) (ring.rightNeighbor e)).2.1 k hk1 hkb
        rfl).symm
  · exact hpost.trans hy.symm
  · exact hkeep
  · exact hctrl
  · intro hs
    exact hs.2.trans hg.symm
  · intro i p o ho hw horig
    have hoff := bankWindowOverlapIncomingGenuineWorkerOffPair ring hn hbank
      seed pre e hy hpost o i p ho hw horig
    exact bankWindowExactOffPairFrame ring
      (rbRun ring (renewalBankStart ring seed) pre) e i hoff.1
      (by rw [← ho]; exact hoff.2)
  · intro p o hc ho
    exact ((bankWindowOverlapPostReceipt ring hn hbank seed pre e).activeRoot
      (ring.rightNeighbor e) p o hc ho).symm

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open L3.BankComparatorExclusive
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Field-level frozen-root transport: the general form of
bankWindowRootFieldsAtOfFrozen. Only the fields each clause actually
reads must agree: PACK on the whole window, token, bit and worker on the
digits, mode and controller at the root (grant under POST scope), and
token, PACK and worker at every site carrying a genuine worker of an
origin rooted there. Endpoint modes and leases may change freely.
Consumer: bankWindowOverlapStableIdlePairRootFieldsAt and the M6 row
bundles. -/
theorem bankWindowRootFieldsAtOfDigitReads {n : Nat}
    (ring : DirectedRing n) (r s : RenewalBankReference n) (root : Fin n)
    (hJ : BankWindowExact ring r)
    (hP : bankWindowReadPackPrefix ring r s root
      (compileAdvice (ceilLogTwo n)).b)
    (hT : bankWindowReadDigitTokens ring r s root)
    (hB : bankWindowReadDigitBits ring r s root)
    (hW : ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      bankWindowReadWorker r s (Counter.site ring root (j.val + 1)))
    (hmode : bankWindowReadMode r s root)
    (hctrl : bankWindowReadController r s root)
    (hgrant : BankWindowScope ring s root → bankWindowReadGrant r s root)
    (hworkers : ∀ (i : Fin n) (p : RenewalBankPayload n)
      (o : RenewalBankOrigin n), o.root = root →
      (s.2.sites i).worker = .payload p → p.origin = some o →
      bankWindowReadTok r s i ∧ bankWindowReadPack r s i ∧
        bankWindowReadWorker r s i)
    (hactive : ∀ (p : RenewalBankPayload n) (o : RenewalBankOrigin n),
      (s.2.sites root).controller = .active p → p.origin = some o →
      o.root = root) :
    BankWindowRootFieldsAt ring s root := by
  have hfree : ∀ (o : RenewalBankOrigin n) (i : Fin n)
      (p : RenewalBankPayload n), o.root = root →
      BankComparatorOriginWorker ring s o i p →
      bankWindowPhaseExcludesReadSet r s o i p := by
    intro o i p ho hw
    have hwi := hworkers i p o ho hw.1 hw.2.1
    exact ⟨hwi.1, hwi.2.2, by rw [ho]; exact hmode⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o i p ho hw
    exact bankWindowPhaseExcludesReadTransport ring r s o i p hJ
      (hfree o i p ho hw) hw
  · intro o i p ho hw hm
    exact bankWindowPhaseCompleteReadTransport ring r s o i p hJ
      ⟨hfree o i p ho hw, by rw [ho]; exact hP⟩ hw hm
  · intro o i p ho hw hm j ht
    exact bankWindowPhaseUniqueReadTransport ring r s o i p hJ
      ⟨hfree o i p ho hw, by rw [ho]; exact hT⟩ hw hm j ht
  · intro o i p ho hw hm
    have hwi := hworkers i p o ho hw.1 hw.2.1
    exact bankWindowPhaseFlagsReadTransport ring r s o i p hJ
      ⟨hfree o i p ho hw, hwi.2.1, by rw [ho]; exact hB⟩ hw hm
  · intro hs hi j ht
    exact bankWindowInheritedCleanReadTransport ring r s root j hJ
      ⟨hP, hgrant hs, hctrl, hW j⟩ hs hi ht
  · intro hs hm hc
    exact bankWindowResetWaitReadTransport ring r s root hJ
      ⟨hP, hgrant hs, hmode, hctrl, hB, hT, hW⟩ hs hm hc
  · intro o p hs hm hc ho
    have hor := hactive p o hc ho
    exact bankWindowArmedExactReadTransport ring r s root o p hJ
      ⟨hP, hgrant hs, hmode, hctrl, hT, by rw [hor]; exact hB⟩
      hs hm hc ho
  · intro o i p hs hm hc hw ho hr
    have hwi := hworkers i p o hr hw ho
    exact bankWindowIncrementExactReadTransport ring r s root o i p hJ
      ⟨hP, hgrant hs, hmode, hctrl, hwi.2.2, hwi.2.1, hwi.1,
        hT, hB, by rw [hr]; exact hB⟩
      hs hm hc hw ho hr
  · intro o i p ho hw horig hm hc
    have hwi := hworkers i p o ho hw horig
    exact bankWindowCompareExactReadTransport ring r s o i p hJ
      ⟨by rw [ho]; exact hmode, by rw [ho]; exact hctrl,
        hwi.2.2, hwi.1, by rw [ho]; exact hT, by rw [ho]; exact hB⟩
      hw horig hm hc
  · intro hs hm hc j ht
    exact bankWindowIwaitTaintedUniqueReadTransport ring r s root j hJ
      ⟨hP, hgrant hs, hmode, hctrl, hT, hW j⟩ hs hm hc ht
  · intro hs hm hc j ht
    exact bankWindowCwaitTaintedUniqueReadTransport ring r s root j hJ
      ⟨hP, hgrant hs, hmode, hctrl, hT, hW j⟩ hs hm hc ht
  · intro limit hrun
    have hlim := hrun.1
    exact bankWindowProtoReadTransport ring r s root limit hJ
      ⟨fun k hk => hP k (by omega), hmode, hctrl,
        fun j _ => ⟨hT j, hB j, hW j⟩⟩ hrun
  · intro j hown ht
    have hj := j.isLt
    exact bankWindowOrphanReadTransport ring r s root j hJ
      ⟨fun k hk => hP k (by omega), hmode, hctrl, hW j⟩ hown ht

/-- Symbolic BANK pair with an unchanged responder role, a nonroot
source and empty tokens at both endpoints: no row fires, so both bits
and both (empty) tokens are unchanged.
Consumer: bankWindowJointIdlePairPhysical. -/
theorem bankWindowJointIdlePairCell
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : x.role ≠ 0) (hxt : x.tok = .E) (hyt : y.tok = .E) :
    (bankPair x y y.role b theta).1.bit = x.bit ∧
    (bankPair x y y.role b theta).1.tok = .E ∧
    (bankPair x y y.role b theta).2.bit = y.bit ∧
    (bankPair x y y.role b theta).2.tok = .E := by
  rw [bankPair_nonroot x y y.role b theta hx]
  simp [bankPairNR, hxt, hyt, apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd,
    apply_ite BankCell.tok, apply_ite BankCell.bit, ite_self]

/-- On a stable-PACK edge from a nonroot source whose two endpoints carry
the empty token, the step leaves both endpoints' bits and tokens
unchanged and both ghost workers empty.
Consumer: bankWindowOverlapStableIdlePairRootFieldsAt. -/
theorem bankWindowJointIdlePairReads {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hJ : BankWindowExact ring r)
    (hnonroot : (r.1 e).pack.val ≠ 0)
    (hstable : packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      (r.1 (ring.rightNeighbor e)).pack.val)
    (hxt : (r.1 e).tok = .E)
    (hyt : (r.1 (ring.rightNeighbor e)).tok = .E) :
    ∀ z : Fin n, (z = e ∨ z = ring.rightNeighbor e) →
      bankWindowReadTok r (renewalBankNext ring r e) z ∧
      bankWindowReadBit r (renewalBankNext ring r e) z ∧
      bankWindowReadWorker r (renewalBankNext ring r e) z := by
  have htrip := bankWindowClosureSelectedBankTrip ring hn hbank r e
  have hcell := bankWindowJointIdlePairCell
    (bankCell (r.1 e) (r.1 e).pack.val)
    (bankCell (r.1 (ring.rightNeighbor e))
      (r.1 (ring.rightNeighbor e)).pack.val)
    (compileAdvice (ceilLogTwo n)).b
    (compileAdvice (ceilLogTwo n)).theta
    (by change (r.1 e).pack.val ≠ 0; exact hnonroot)
    (by change (r.1 e).tok = .E; exact hxt)
    (by change (r.1 (ring.rightNeighbor e)).tok = .E; exact hyt)
  have hsrcTrip := htrip.1
  have hdstTrip := htrip.2
  change (((renewalBankNext ring r e).1 e).mode,
      ((renewalBankNext ring r e).1 e).bit,
      ((renewalBankNext ring r e).1 e).tok) =
    ((Counter.resetBankOld (r.1 e) (r.1 (ring.rightNeighbor e))).1.mode,
      (Counter.resetBankOld (r.1 e) (r.1 (ring.rightNeighbor e))).1.bit,
      (Counter.resetBankOld (r.1 e) (r.1 (ring.rightNeighbor e))).1.tok)
    at hsrcTrip
  change (((renewalBankNext ring r e).1 (ring.rightNeighbor e)).mode,
      ((renewalBankNext ring r e).1 (ring.rightNeighbor e)).bit,
      ((renewalBankNext ring r e).1 (ring.rightNeighbor e)).tok) =
    ((Counter.resetBankOld (r.1 e) (r.1 (ring.rightNeighbor e))).2.mode,
      (Counter.resetBankOld (r.1 e) (r.1 (ring.rightNeighbor e))).2.bit,
      (Counter.resetBankOld (r.1 e) (r.1 (ring.rightNeighbor e))).2.tok)
    at hdstTrip
  unfold Counter.resetBankOld at hsrcTrip hdstTrip
  rw [hstable] at hsrcTrip hdstTrip
  simp only [Prod.mk.injEq] at hsrcTrip hdstTrip
  -- OLD workers at both endpoints are empty (token E, in-flight frame).
  have hwE : ∀ z : Fin n, (r.1 z).tok = .E → (r.2.sites z).worker = .empty := by
    intro z hz
    have hf := (hJ.frame z).2
    rw [hz] at hf
    exact hf
  have hwx := hwE e hxt
  have hwy := hwE (ring.rightNeighbor e) hyt
  have hframe := rbReferenceSelectedPairFrame ring (by omega : 2 ≤ n) r e
  have hghost : ∀ z : Fin n, (z = e ∨ z = ring.rightNeighbor e) →
      ((renewalBankNext ring r e).2.sites z).worker = .empty := by
    intro z hz
    have hlocal :
        ((renewalBankNext ring r e).2.sites z).worker =
          (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
            r.2 e (ring.rightNeighbor e)
            (r.1 e) (r.1 (ring.rightNeighbor e))).1.worker ∨
        ((renewalBankNext ring r e).2.sites z).worker =
          (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
            r.2 e (ring.rightNeighbor e)
            (r.1 e) (r.1 (ring.rightNeighbor e))).2.worker := by
      rcases hz with hz | hz
      · subst hz
        exact Or.inl (congrArg (fun s : RenewalBankSite n => s.worker)
          hframe.2.2.1)
      · subst hz
        exact Or.inr (congrArg (fun s : RenewalBankSite n => s.worker)
          hframe.2.2.2)
    cases hw : ((renewalBankNext ring r e).2.sites z).worker with
    | empty => rfl
    | pending rho =>
        exfalso
        have hp : (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
            r.2 e (ring.rightNeighbor e)
            (r.1 e) (r.1 (ring.rightNeighbor e))).1.worker = .pending rho ∨
          (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
            r.2 e (ring.rightNeighbor e)
            (r.1 e) (r.1 (ring.rightNeighbor e))).2.worker = .pending rho := by
          rcases hlocal with h | h
          · exact Or.inl (h.symm.trans hw)
          · exact Or.inr (h.symm.trans hw)
        rcases rbGhostNonrootPendingOld (compileAdvice (ceilLogTwo n)) r.2
            e (ring.rightNeighbor e) (r.1 e) (r.1 (ring.rightNeighbor e))
            hnonroot rho hp with h | h
        · rw [hwx] at h
          cases h
        · rw [hwy] at h
          cases h
    | payload p =>
        exfalso
        have hp : (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
            r.2 e (ring.rightNeighbor e)
            (r.1 e) (r.1 (ring.rightNeighbor e))).1.worker = .payload p ∨
          (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
            r.2 e (ring.rightNeighbor e)
            (r.1 e) (r.1 (ring.rightNeighbor e))).2.worker = .payload p := by
          rcases hlocal with h | h
          · exact Or.inl (h.symm.trans hw)
          · exact Or.inr (h.symm.trans hw)
        rcases rbBankNonrootSelectedWorkersInherited
            (compileAdvice (ceilLogTwo n)) r.2
            e (ring.rightNeighbor e) (r.1 e) (r.1 (ring.rightNeighbor e))
            hnonroot p hp with h | h
        · rw [hwx] at h
          cases h
        · rw [hwy] at h
          cases h
  intro z hz
  have hwz : bankWindowReadWorker r (renewalBankNext ring r e) z := by
    unfold bankWindowReadWorker
    rw [hghost z hz]
    rcases hz with hz | hz
    · rw [hz, hwx]
    · rw [hz, hwy]
  rcases hz with hz | hz
  · subst hz
    refine ⟨?_, ?_, hwz⟩
    · exact (hsrcTrip.2.2.trans hcell.2.1).trans hxt.symm
    · exact hsrcTrip.2.1.trans hcell.1
  · subst hz
    refine ⟨?_, ?_, hwz⟩
    · exact (hdstTrip.2.2.trans hcell.2.2.2).trans hyt.symm
    · exact hdstTrip.2.1.trans hcell.2.2.1

/-- M6, idle pair: on a stable-PACK edge from a nonroot source whose two
endpoints carry the empty token, every root other than both endpoints
satisfies every root-indexed POST clause (in particular every foreign
INT/TOP root whose window meets the edge). This covers every complete
ARMED/CSTART window (armedExact makes all its digit tokens empty) and
every edge between two empty digits.
Consumer: bankWindowExactStep, stable nonroot edge, idle-pair branch
(ledger row M6). -/
theorem bankWindowOverlapStableIdlePairRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hnonroot :
      ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ≠ 0)
    (hstable :
      packNext
        ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val
        ((rbRun ring (renewalBankStart ring seed) pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((rbRun ring (renewalBankStart ring seed) pre).1
        (ring.rightNeighbor e)).pack.val)
    (hxt : ((rbRun ring (renewalBankStart ring seed) pre).1 e).tok = .E)
    (hyt : ((rbRun ring (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)).tok = .E)
    (hforeign : root ≠ e ∧ root ≠ ring.rightNeighbor e) :
    BankWindowRootFieldsAt ring
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
      root := by
  have hpair := bankWindowJointIdlePairReads ring hn hbank
    (rbRun ring (renewalBankStart ring seed) pre) e hJ hnonroot hstable
    hxt hyt
  have hpackAll := bankWindowOverlapStablePackFrame ring hn seed pre e hstable
  have hreads : ∀ z : Fin n,
      bankWindowReadTok (rbRun ring (renewalBankStart ring seed) pre)
        (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) z ∧
      bankWindowReadBit (rbRun ring (renewalBankStart ring seed) pre)
        (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) z ∧
      bankWindowReadWorker (rbRun ring (renewalBankStart ring seed) pre)
        (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) z := by
    intro z
    by_cases hz : z = e ∨ z = ring.rightNeighbor e
    · exact hpair z hz
    · have hf := bankWindowExactOffPairAtomicReads ring
        (rbRun ring (renewalBankStart ring seed) pre) e z
        (fun h => hz (Or.inl h)) (fun h => hz (Or.inr h))
      exact ⟨hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.2.1⟩
  have hroot := bankWindowExactOffPairAtomicReads ring
    (rbRun ring (renewalBankStart ring seed) pre) e root
    hforeign.1 hforeign.2
  apply bankWindowRootFieldsAtOfDigitReads ring
    (rbRun ring (renewalBankStart ring seed) pre) _ root hJ
  · intro k _
    exact hpackAll _
  · intro j
    exact (hreads _).1
  · intro j
    exact (hreads _).2.1
  · intro j
    exact (hreads _).2.2
  · exact hroot.2.1
  · exact hroot.2.2.2.2.2.2
  · intro _
    exact hroot.2.2.2.2.1
  · intro i p o _ _ _
    exact ⟨(hreads i).1, hpackAll i, (hreads i).2.2⟩
  · intro p o hc ho
    exact ((bankWindowOverlapPostReceipt ring hn hbank seed pre e).activeRoot
      root p o hc ho).symm

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open L3.BankComparatorExclusive
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- A root in physical mode RESET has an empty controller in any state
with the in-flight frame (at PACK zero by the RESET shape, elsewhere by
the nonroot shape).
Consumer: bankWindowOverlapForeignResetRootFieldsAt. -/
theorem bankWindowResetControllerEmpty {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n) (z : Fin n)
    (hframe : BankInFlightAligned ring r)
    (hmode : (r.1 z).mode = .RESET) :
    (r.2.sites z).controller = .empty := by
  have hf := (hframe z).1
  unfold bankInFlightControllerShape at hf
  by_cases hp : (r.1 z).pack.val = 0
  · rw [if_pos hp, hmode] at hf
    exact hf
  · rw [if_neg hp] at hf
    exact hf

/-- M6 (and every edge class): a root other than both endpoints whose
POST physical mode is RESET satisfies every root-indexed POST clause; its
proto and orphan clauses come from bankWindowOverlapRootJointFields.
Consumer: bankWindowExactStep, foreign RESET roots on every edge. -/
theorem bankWindowOverlapForeignResetRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hforeign : root ≠ e ∧ root ≠ ring.rightNeighbor e)
    (hmode : ((renewalBankNext ring
      (rbRun ring (renewalBankStart ring seed) pre) e).1 root).mode = .RESET) :
    BankWindowRootFieldsAt ring
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
      root := by
  have hjoint := bankWindowOverlapRootJointFields ring hn hbank seed pre e hJ
  exact bankWindowRootFieldsAtOfReset ring _ root hmode
    (bankWindowEmptyControllerNotInherited _ root
      (bankWindowResetControllerEmpty ring _ root hjoint.1 hmode))
    (fun limit hrun => hjoint.2.2.2.1 root limit hforeign hrun)
    (fun j => hjoint.2.2.2.2 root j hforeign)

/-- M6, inherited controller: stable-PACK edge from a nonroot source that
is an interior digit D_root(k), 1 <= k < b, of a foreign root which is in
POST scope with an inherited controller. OLD J.inheritedClean and the
nonroot pair taint preimage keep the whole window untainted; then no
genuine worker of this root exists after the step (real-run in-band and
ReceiptInv.workerSite place it on a digit of the window), every
comparator/compareExact/incrementExact clause is vacuous, and the
waiting-[] and genuine-active clauses are excluded by the inherited
controller.
Consumer: bankWindowExactStep, stable interior edge, inherited-controller
roots (ledger row M6). -/
theorem bankWindowOverlapStableInteriorInheritedRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hnonroot :
      ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ≠ 0)
    (hstable :
      packNext
        ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val
        ((rbRun ring (renewalBankStart ring seed) pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((rbRun ring (renewalBankStart ring seed) pre).1
        (ring.rightNeighbor e)).pack.val)
    (hforeign : root ≠ e ∧ root ≠ ring.rightNeighbor e)
    (k : Nat) (hk1 : 1 ≤ k) (hkb : k < (compileAdvice (ceilLogTwo n)).b)
    (hsite : e = Counter.site ring root k)
    (hscope : BankWindowScope ring
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
      root)
    (hinh : BankWindowInheritedController
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
      root) :
    BankWindowRootFieldsAt ring
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
      root := by
  have hjoint := bankWindowOverlapRootJointFields ring hn hbank seed pre e hJ
  have hroot := bankWindowExactOffPairAtomicReads ring
    (rbRun ring (renewalBankStart ring seed) pre) e root
    hforeign.1 hforeign.2
  have hpackAll := bankWindowOverlapStablePackFrame ring hn seed pre e hstable
  have hscopeOld : BankWindowScope ring
      (rbRun ring (renewalBankStart ring seed) pre) root := by
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [← hpackAll]
      exact hscope.1 j hj
    · have hg := hroot.2.2.2.2.1
      unfold bankWindowReadGrant at hg
      rw [← hg]
      exact hscope.2
  have hinhOld : BankWindowInheritedController
      (rbRun ring (renewalBankStart ring seed) pre) root := by
    have hc := hroot.2.2.2.2.2.2
    unfold bankWindowReadController at hc
    unfold BankWindowInheritedController at hinh ⊢
    rw [hc] at hinh
    exact hinh
  have hnotNil : ((renewalBankNext ring
      (rbRun ring (renewalBankStart ring seed) pre) e).2.sites
        root).controller ≠ .waiting [] := by
    intro hc
    rcases hinh with ⟨atoms, ha, hne⟩ | ⟨p, ha, _⟩
    · rw [hc] at ha
      injection ha with h
      exact hne h.symm
    · rw [hc] at ha
      cases ha
  have hsucc : ring.rightNeighbor e = Counter.site ring root (k + 1) := by
    rw [hsite]
    rfl
  have hclean : ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ¬ BankWindowTainted
        (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
        (Counter.site ring root (j.val + 1)) := by
    intro j ht
    by_cases hz : Counter.site ring root (j.val + 1) = e ∨
        Counter.site ring root (j.val + 1) = ring.rightNeighbor e
    · rcases bankWindowOverlapNonrootPairTaintPreimage ring (by omega : 2 ≤ n)
          (rbRun ring (renewalBankStart ring seed) pre) e
          (Counter.site ring root (j.val + 1)) hnonroot hz ht with h | h
      · let d : Fin (compileAdvice (ceilLogTwo n)).b := ⟨k - 1, by omega⟩
        have hd : Counter.site ring root (d.val + 1) = e := by
          change Counter.site ring root (k - 1 + 1) = e
          rw [show k - 1 + 1 = k by omega]
          exact hsite.symm
        rw [← hd] at h
        exact hJ.inheritedClean root hscopeOld hinhOld d h
      · let d : Fin (compileAdvice (ceilLogTwo n)).b := ⟨k, hkb⟩
        have hd : Counter.site ring root (d.val + 1) = ring.rightNeighbor e :=
          hsucc.symm
        rw [← hd] at h
        exact hJ.inheritedClean root hscopeOld hinhOld d h
    · have hf := bankWindowExactOffPairAtomicReads ring
        (rbRun ring (renewalBankStart ring seed) pre) e
        (Counter.site ring root (j.val + 1))
        (fun h => hz (Or.inl h)) (fun h => hz (Or.inr h))
      have hw := hf.2.2.2.2.2.1
      unfold bankWindowReadWorker at hw
      unfold BankWindowTainted at ht
      rw [hw] at ht
      exact hJ.inheritedClean root hscopeOld hinhOld j ht
  have hphys : rbRun ring (renewalBankStart ring seed) (pre ++ [e]) =
      renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e := by
    rw [rbRunAppend]
    rfl
  have hreceipt := bankWindowOverlapPostReceipt ring hn hbank seed pre e
  have hnogen : ∀ (i : Fin n) (p : RenewalBankPayload n)
      (o : RenewalBankOrigin n), o.root = root →
      ((renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e).2.sites i).worker =
        .payload p → p.origin = some o → False := by
    intro i p o ho hw horig
    have hband := bankWindowOverlapGenuineWorkerInBand ring hn hbank seed
      (pre ++ [e]) i p o (by rw [hphys]; exact hw) horig
    rw [hphys] at hband
    have hsiteI := hreceipt.workerSite i p o hw horig hband.1 hband.2
    let d : Fin (compileAdvice (ceilLogTwo n)).b :=
      ⟨((renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e).1 i).pack.val - 1,
        by omega⟩
    apply hclean d
    have hd : Counter.site ring root (d.val + 1) = i := by
      change Counter.site ring root
        (((renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e).1 i).pack.val - 1 + 1)
        = i
      rw [show ((renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e).1 i).pack.val - 1 + 1 =
          ((renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e).1 i).pack.val by omega,
        ← ho]
      exact hsiteI.symm
    rw [hd]
    exact Or.inr ⟨p, o, hw, horig⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o i p ho hw
    exact False.elim (hnogen i p o ho hw.1 hw.2.1)
  · intro o i p ho hw _
    exact False.elim (hnogen i p o ho hw.1 hw.2.1)
  · intro o i p ho hw _
    exact False.elim (hnogen i p o ho hw.1 hw.2.1)
  · intro o i p ho hw _
    exact False.elim (hnogen i p o ho hw.1 hw.2.1)
  · intro _ _ j
    exact hclean j
  · intro _ _ hc
    exact absurd hc hnotNil
  · intro o p _ _ hc ho
    rcases hinh with ⟨atoms, ha, _⟩ | ⟨q, ha, hq⟩
    · rw [hc] at ha
      cases ha
    · rw [hc] at ha
      injection ha with hpq
      rw [hpq, hq] at ho
      cases ho
  · intro o i p _ _ _ hw ho hr
    exact False.elim (hnogen i p o hr hw ho)
  · intro o i p ho hw horig _ _
    exact False.elim (hnogen i p o ho hw horig)
  · intro _ _ hc
    exact absurd hc hnotNil
  · intro _ _ hc
    exact absurd hc hnotNil
  · intro limit hrun
    exact hjoint.2.2.2.1 root limit hforeign hrun
  · intro j
    exact hjoint.2.2.2.2 root j hforeign

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open L3.BankComparatorExclusive
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- M6, untainted window: stable-PACK edge from a nonroot source that is
an interior digit D_root(k), 1 <= k < b, of a foreign root whose OLD
digits carry no pending receipt and no genuine worker. The nonroot pair
taint preimage keeps the POST window untainted, so no genuine worker of
this root exists after the step (in-band plus ReceiptInv.workerSite),
every comparator, compareExact, incrementExact and taint-uniqueness
clause is vacuous, an RWAIT/waiting-[] scope is impossible (OLD resetWait
would need a pending digit), and a scoped ARMED/CSTART genuine controller
makes OLD armedExact empty both endpoint tokens, so the idle-pair bundle
applies. This includes every root in POST scope with an inherited
controller (OLD J.inheritedClean).
Consumer: bankWindowExactStep, stable interior edge, untainted foreign
windows (ledger row M6). -/
theorem bankWindowOverlapStableInteriorUntaintedRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hnonroot :
      ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ≠ 0)
    (hstable :
      packNext
        ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val
        ((rbRun ring (renewalBankStart ring seed) pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((rbRun ring (renewalBankStart ring seed) pre).1
        (ring.rightNeighbor e)).pack.val)
    (hforeign : root ≠ e ∧ root ≠ ring.rightNeighbor e)
    (k : Nat) (hk1 : 1 ≤ k) (hkb : k < (compileAdvice (ceilLogTwo n)).b)
    (hsite : e = Counter.site ring root k)
    (huntainted : ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ¬ BankWindowTainted (rbRun ring (renewalBankStart ring seed) pre)
        (Counter.site ring root (j.val + 1))) :
    BankWindowRootFieldsAt ring
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
      root := by
  have hjoint := bankWindowOverlapRootJointFields ring hn hbank seed pre e hJ
  have hroot := bankWindowExactOffPairAtomicReads ring
    (rbRun ring (renewalBankStart ring seed) pre) e root
    hforeign.1 hforeign.2
  have hpackAll := bankWindowOverlapStablePackFrame ring hn seed pre e hstable
  have hmodeR := hroot.2.1
  have hctrlR := hroot.2.2.2.2.2.2
  have hgrantR := hroot.2.2.2.2.1
  unfold bankWindowReadMode at hmodeR
  unfold bankWindowReadController at hctrlR
  unfold bankWindowReadGrant at hgrantR
  have hscopeOld : BankWindowScope ring
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
      root →
      BankWindowScope ring (rbRun ring (renewalBankStart ring seed) pre) root := by
    intro hscope
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [← hpackAll]
      exact hscope.1 j hj
    · rw [← hgrantR]
      exact hscope.2
  have hsucc : ring.rightNeighbor e = Counter.site ring root (k + 1) := by
    rw [hsite]
    rfl
  let dk : Fin (compileAdvice (ceilLogTwo n)).b := ⟨k - 1, by omega⟩
  have hdk : Counter.site ring root (dk.val + 1) = e := by
    change Counter.site ring root (k - 1 + 1) = e
    rw [show k - 1 + 1 = k by omega]
    exact hsite.symm
  let dk' : Fin (compileAdvice (ceilLogTwo n)).b := ⟨k, hkb⟩
  have hdk' : Counter.site ring root (dk'.val + 1) = ring.rightNeighbor e :=
    hsucc.symm
  have hclean : ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ¬ BankWindowTainted
        (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
        (Counter.site ring root (j.val + 1)) := by
    intro j ht
    by_cases hz : Counter.site ring root (j.val + 1) = e ∨
        Counter.site ring root (j.val + 1) = ring.rightNeighbor e
    · rcases bankWindowOverlapNonrootPairTaintPreimage ring (by omega : 2 ≤ n)
          (rbRun ring (renewalBankStart ring seed) pre) e
          (Counter.site ring root (j.val + 1)) hnonroot hz ht with h | h
      · rw [← hdk] at h
        exact huntainted dk h
      · rw [← hdk'] at h
        exact huntainted dk' h
    · have hf := bankWindowExactOffPairAtomicReads ring
        (rbRun ring (renewalBankStart ring seed) pre) e
        (Counter.site ring root (j.val + 1))
        (fun h => hz (Or.inl h)) (fun h => hz (Or.inr h))
      have hw := hf.2.2.2.2.2.1
      unfold bankWindowReadWorker at hw
      unfold BankWindowTainted at ht
      rw [hw] at ht
      exact huntainted j ht
  have hphys : rbRun ring (renewalBankStart ring seed) (pre ++ [e]) =
      renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e := by
    rw [rbRunAppend]
    rfl
  have hreceipt := bankWindowOverlapPostReceipt ring hn hbank seed pre e
  have hnogen : ∀ (i : Fin n) (p : RenewalBankPayload n)
      (o : RenewalBankOrigin n), o.root = root →
      ((renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e).2.sites i).worker =
        .payload p → p.origin = some o → False := by
    intro i p o ho hw horig
    have hband := bankWindowOverlapGenuineWorkerInBand ring hn hbank seed
      (pre ++ [e]) i p o (by rw [hphys]; exact hw) horig
    rw [hphys] at hband
    have hsiteI := hreceipt.workerSite i p o hw horig hband.1 hband.2
    let d : Fin (compileAdvice (ceilLogTwo n)).b :=
      ⟨((renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e).1 i).pack.val - 1,
        by omega⟩
    apply hclean d
    have hd : Counter.site ring root (d.val + 1) = i := by
      change Counter.site ring root
        (((renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e).1 i).pack.val - 1 + 1)
        = i
      rw [show ((renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e).1 i).pack.val - 1 + 1 =
          ((renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e).1 i).pack.val by omega,
        ← ho]
      exact hsiteI.symm
    rw [hd]
    exact Or.inr ⟨p, o, hw, horig⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o i p ho hw
    exact False.elim (hnogen i p o ho hw.1 hw.2.1)
  · intro o i p ho hw _
    exact False.elim (hnogen i p o ho hw.1 hw.2.1)
  · intro o i p ho hw _
    exact False.elim (hnogen i p o ho hw.1 hw.2.1)
  · intro o i p ho hw _
    exact False.elim (hnogen i p o ho hw.1 hw.2.1)
  · intro _ _ j
    exact hclean j
  · intro hs hm hc
    obtain ⟨j, rho, hw, _⟩ := hJ.resetWait root (hscopeOld hs)
      (hmodeR.symm.trans hm) (hctrlR.symm.trans hc)
    exact False.elim (huntainted j (Or.inl ⟨rho, hw⟩))
  · intro o p hs hm hc ho
    have hmOld : ((rbRun ring (renewalBankStart ring seed) pre).1 root).mode =
          .ARMED ∨
        ((rbRun ring (renewalBankStart ring seed) pre).1 root).mode = .CSTART := by
      rw [← hmodeR]
      exact hm
    have hE := (hJ.armedExact root o p (hscopeOld hs) hmOld
      (hctrlR.symm.trans hc) ho).1
    have hxt : ((rbRun ring (renewalBankStart ring seed) pre).1 e).tok = .E := by
      have h := hE dk
      rw [hdk] at h
      exact h
    have hyt : ((rbRun ring (renewalBankStart ring seed) pre).1
        (ring.rightNeighbor e)).tok = .E := by
      have h := hE dk'
      rw [hdk'] at h
      exact h
    exact (bankWindowOverlapStableIdlePairRootFieldsAt ring hn hbank seed pre
      e root hJ hnonroot hstable hxt hyt hforeign).2.2.2.2.2.2.1 o p hs hm hc ho
  · intro o i p _ _ _ hw ho hr
    exact False.elim (hnogen i p o hr hw ho)
  · intro o i p ho hw horig _ _
    exact False.elim (hnogen i p o ho hw horig)
  · intro _ _ _ j ht
    exact False.elim (hclean j ht)
  · intro _ _ _ j ht
    exact False.elim (hclean j ht)
  · intro limit hrun
    exact hjoint.2.2.2.1 root limit hforeign hrun
  · intro j
    exact hjoint.2.2.2.2 root j hforeign

end L3.BankWindow


namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open L3.BankComparatorExclusive
open L3.BankHeadThreshold
open L3.BankCounterRows
open Classical

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- M5 in RootFieldsAt form: a root incident to the stepped edge whose
repair is complete before and after the step satisfies every
root-indexed clause after the step. Definitional repackaging of
bankWindowOverlapRepairCompleteIncidentRootClauses (BankWindowOverlapRoot).
Consumer: the final bankWindowExactStep case split (ledger row M5). -/
theorem bankWindowOverlapRepairCompleteRootFieldsAt
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hcompleteOld : Counter.Complete ring
      (rbRun ring (renewalBankStart ring seed) pre).1 root)
    (hcompletePost : Counter.Complete ring
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1
      root)
    (hchanged :
      packNext
        ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val
        ((rbRun ring (renewalBankStart ring seed) pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      ((rbRun ring (renewalBankStart ring seed) pre).1
        (ring.rightNeighbor e)).pack.val)
    (hincident : Counter.Support (ceilLogTwo n) ring root e) :
    BankWindowRootFieldsAt ring
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
      root :=
  bankWindowOverlapRepairCompleteIncidentRootClauses ring hn hbank seed pre
    e root hJ hcompleteOld hcompletePost hchanged hincident

/-- M6-P, aligned stable edge (source PACK k, responder PACK k+1,
1 <= k < b): if the POST source cell carries a live comparison token, the
OLD pair was either an empty source facing a CL token (or, at the top
digit, a CR token turning back) or a CL source that moves left past an
empty or top-IR responder. Rows R5/R6/R8 of Base.bankPair.
Consumer: bankWindowJointAlignedWorkers and the M6-P comparator preimage
for foreign roots on a stable nonroot edge. -/
theorem bankWindowJointAlignedSourceLive {c : Compiled} (x y : Agent c) (k : Nat)
    (hk : 1 ≤ k) (hbelow : k < c.b)
    (hx : x.pack.val = k) (hy : y.pack.val = k + 1)
    (hlive : BankTrialLiveComparisonToken (Counter.resetBankOld x y).1.tok) :
    (x.tok = .E ∧ (y.tok = .CL0 ∨ y.tok = .CL1 ∨
      (k + 1 = c.b ∧ (y.tok = .CR0 ∨ y.tok = .CR1)))) ∨
    ((x.tok = .CL0 ∨ x.tok = .CL1) ∧
      (y.tok = .E ∨ (k + 1 = c.b ∧ y.tok = .IR))) := by
  have hle : k ≤ c.b := by omega
  have hnz : k ≠ 0 := by omega
  have hbz : c.b ≠ 0 := by omega
  have hne : k ≠ c.b := by omega
  have hnextPos : 1 ≤ k + 1 := by omega
  have hnextNz : k + 1 ≠ 0 := by omega
  have hnl : ¬ c.b < k + 1 := by omega
  have hrole : packNext k (k + 1) c.b = k + 1 := by
    simp [packNext, hbelow]
  unfold BankTrialLiveComparisonToken at hlive
  rw [Counter.resetBankOld, bankPair_nonroot _ _ _ _ _ (by simp [bankCell, hx, hnz])] at hlive
  by_cases htop : k + 1 = c.b
  · have hpTop : packNext k c.b c.b = c.b := by
      have h := hrole
      rw [htop] at h
      exact h
    simp [Counter.resetBankOld, bankPairNR, bankCell, hx, hy, hk, hbelow, hle, hnz, hbz, hne,
      hnextPos, hnextNz, hnl, hrole, hpTop, htop, Id.run_pure, Id.run_bind, apply_ite Id.run,
      apply_ite Prod.fst, apply_ite Prod.snd, apply_ite BankCell.tok,
      apply_ite BankCell.role, apply_ite BankCell.mode, ite_self] at hlive ⊢
    all_goals (cases hxt : x.tok <;> cases hyt : y.tok <;>
      simp [Counter.resetBankOld, bankPairNR, bankCell, hx, hy, hk, hbelow, hle, hnz, hbz, hne,
        hnextPos, hnextNz, hnl, hrole, hpTop, htop, hxt, hyt, Id.run_pure, Id.run_bind,
        apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd, apply_ite BankCell.tok,
        apply_ite BankCell.role, apply_ite BankCell.mode, ite_self] at hlive ⊢)
  · simp [Counter.resetBankOld, bankPairNR, bankCell, hx, hy, hk, hbelow, hle, hnz, hbz, hne,
      hnextPos, hnextNz, hnl, hrole, htop, Id.run_pure, Id.run_bind, apply_ite Id.run,
      apply_ite Prod.fst, apply_ite Prod.snd, apply_ite BankCell.tok,
      apply_ite BankCell.role, apply_ite BankCell.mode, ite_self] at hlive ⊢
    all_goals (cases hxt : x.tok <;> cases hyt : y.tok <;>
      simp [Counter.resetBankOld, bankPairNR, bankCell, hx, hy, hk, hbelow, hle, hnz, hbz, hne,
        hnextPos, hnextNz, hnl, hrole, htop, hxt, hyt, Id.run_pure, Id.run_bind,
        apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd, apply_ite BankCell.tok,
        apply_ite BankCell.role, apply_ite BankCell.mode, ite_self] at hlive ⊢)

/-- M6-P, aligned stable edge: a live comparison token in the POST
responder cell comes from a CR source carried right into an empty (or
top-IR) responder, or from a non-top CR responder kept in place.
Consumer: bankWindowJointAlignedWorkers and the M6-P comparator preimage. -/
theorem bankWindowJointAlignedResponderLive {c : Compiled} (x y : Agent c) (k : Nat)
    (hk : 1 ≤ k) (hbelow : k < c.b)
    (hx : x.pack.val = k) (hy : y.pack.val = k + 1)
    (hlive : BankTrialLiveComparisonToken (Counter.resetBankOld x y).2.tok) :
    ((x.tok = .CR0 ∨ x.tok = .CR1) ∧
      (y.tok = .E ∨ (k + 1 = c.b ∧ y.tok = .IR))) ∨
    (x.tok = .E ∧ (y.tok = .CR0 ∨ y.tok = .CR1) ∧ k + 1 ≠ c.b) := by
  have hle : k ≤ c.b := by omega
  have hnz : k ≠ 0 := by omega
  have hbz : c.b ≠ 0 := by omega
  have hne : k ≠ c.b := by omega
  have hnextPos : 1 ≤ k + 1 := by omega
  have hnextNz : k + 1 ≠ 0 := by omega
  have hnl : ¬ c.b < k + 1 := by omega
  have hrole : packNext k (k + 1) c.b = k + 1 := by
    simp [packNext, hbelow]
  unfold BankTrialLiveComparisonToken at hlive
  rw [Counter.resetBankOld, bankPair_nonroot _ _ _ _ _ (by simp [bankCell, hx, hnz])] at hlive
  by_cases htop : k + 1 = c.b
  · have hpTop : packNext k c.b c.b = c.b := by
      have h := hrole
      rw [htop] at h
      exact h
    simp [Counter.resetBankOld, bankPairNR, bankCell, hx, hy, hk, hbelow, hle, hnz, hbz, hne,
      hnextPos, hnextNz, hnl, hrole, hpTop, htop, Id.run_pure, Id.run_bind, apply_ite Id.run,
      apply_ite Prod.fst, apply_ite Prod.snd, apply_ite BankCell.tok,
      apply_ite BankCell.role, apply_ite BankCell.mode, ite_self] at hlive ⊢
    all_goals (cases hxt : x.tok <;> cases hyt : y.tok <;>
      simp [Counter.resetBankOld, bankPairNR, bankCell, hx, hy, hk, hbelow, hle, hnz, hbz, hne,
        hnextPos, hnextNz, hnl, hrole, hpTop, htop, hxt, hyt, Id.run_pure, Id.run_bind,
        apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd, apply_ite BankCell.tok,
        apply_ite BankCell.role, apply_ite BankCell.mode, ite_self] at hlive ⊢ <;>
      (try (split at hlive <;> simp at hlive)))
  · simp [Counter.resetBankOld, bankPairNR, bankCell, hx, hy, hk, hbelow, hle, hnz, hbz, hne,
      hnextPos, hnextNz, hnl, hrole, htop, Id.run_pure, Id.run_bind, apply_ite Id.run,
      apply_ite Prod.fst, apply_ite Prod.snd, apply_ite BankCell.tok,
      apply_ite BankCell.role, apply_ite BankCell.mode, ite_self] at hlive ⊢
    all_goals (cases hxt : x.tok <;> cases hyt : y.tok <;>
      simp [Counter.resetBankOld, bankPairNR, bankCell, hx, hy, hk, hbelow, hle, hnz, hbz, hne,
        hnextPos, hnextNz, hnl, hrole, htop, hxt, hyt, Id.run_pure, Id.run_bind,
        apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd, apply_ite BankCell.tok,
        apply_ite BankCell.role, apply_ite BankCell.mode, ite_self] at hlive ⊢ <;>
      (try (split at hlive <;> simp at hlive)))

/-- M6-P, aligned stable edge: for each token row of
bankWindowJointAlignedSourceLive / bankWindowJointAlignedResponderLive the
POST pair memory takes its worker from the OLD site the token came from.
Consumer: the M6-P comparator preimage (worker of a NEW live comparator
cell is the OLD worker of a cell in {e, e+1}). -/
theorem bankWindowJointAlignedWorkers {n : Nat} {c : Compiled} (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (k : Nat)
    (hk : 1 ≤ k) (hbelow : k < c.b)
    (hx : x.pack.val = k) (hy : y.pack.val = k + 1) :
    ((x.tok = .E ∧ (y.tok = .CL0 ∨ y.tok = .CL1 ∨
      (k + 1 = c.b ∧ (y.tok = .CR0 ∨ y.tok = .CR1)))) →
      (renewalBankPairMemory c m e dest x y).1.worker = (m.sites dest).worker) ∧
    (((x.tok = .CL0 ∨ x.tok = .CL1) ∧
      (y.tok = .E ∨ (k + 1 = c.b ∧ y.tok = .IR))) →
      (renewalBankPairMemory c m e dest x y).1.worker = (m.sites e).worker) ∧
    (((x.tok = .CR0 ∨ x.tok = .CR1) ∧
      (y.tok = .E ∨ (k + 1 = c.b ∧ y.tok = .IR))) →
      (renewalBankPairMemory c m e dest x y).2.worker = (m.sites e).worker) ∧
    ((x.tok = .E ∧ (y.tok = .CR0 ∨ y.tok = .CR1) ∧ k + 1 ≠ c.b) →
      (renewalBankPairMemory c m e dest x y).2.worker = (m.sites dest).worker) := by
  have hle : k ≤ c.b := by omega
  have hnz : k ≠ 0 := by omega
  have hbz : c.b ≠ 0 := by omega
  have hne : k ≠ c.b := by omega
  have hnextPos : 1 ≤ k + 1 := by omega
  have hnextNz : k + 1 ≠ 0 := by omega
  have hnl : ¬ c.b < k + 1 := by omega
  have hrole : packNext k (k + 1) c.b = k + 1 := by
    simp [packNext, hbelow]
  rw [renewalBankPairMemory_nonroot c m e dest x y (by omega)]
  by_cases htop : k + 1 = c.b
  · have hpTop : packNext k c.b c.b = c.b := by
      have h := hrole
      rw [htop] at h
      exact h
    simp [bankMemoryNRW, bankCell, hx, hy, hk, hbelow, hle, hnz, hbz, hne, hnextPos, hnextNz,
      hnl, hrole, hpTop, htop, Id.run_pure, Id.run_bind]
    all_goals (cases hxt : x.tok <;> cases hyt : y.tok <;>
      simp [bankMemoryNRW, bankCell, hx, hy, hk, hbelow, hle, hnz, hbz, hne, hnextPos, hnextNz,
        hnl, hrole, hpTop, htop, hxt, hyt, Id.run_pure, Id.run_bind])
  · simp [bankMemoryNRW, bankCell, hx, hy, hk, hbelow, hle, hnz, hbz, hne, hnextPos, hnextNz,
      hnl, hrole, htop, Id.run_pure, Id.run_bind]
    all_goals (cases hxt : x.tok <;> cases hyt : y.tok <;>
      simp [bankMemoryNRW, bankCell, hx, hy, hk, hbelow, hle, hnz, hbz, hne, hnextPos, hnextNz,
        hnl, hrole, htop, hxt, hyt, Id.run_pure, Id.run_bind])

/-- M6-P, top stable edge (source PACK b, responder PACK 0 or b+1): a
live POST source token was already live in the OLD source and keeps the
OLD source worker; the POST responder carries no live comparison token.
Consumer: the M6-P comparator preimage, top-digit case. -/
theorem bankWindowJointTopEdgeTokens {n : Nat} {c : Compiled} (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = c.b) (hbz : c.b ≠ 0)
    (hy : y.pack.val = 0 ∨ y.pack.val = c.b + 1) :
    (BankTrialLiveComparisonToken (Counter.resetBankOld x y).1.tok →
      BankTrialLiveComparisonToken x.tok ∧
      (renewalBankPairMemory c m e dest x y).1.worker = (m.sites e).worker) ∧
    ¬ BankTrialLiveComparisonToken (Counter.resetBankOld x y).2.tok := by
  have hp0 : packNext c.b 0 c.b = 0 := by simp [packNext]
  have hpb : packNext c.b (c.b + 1) c.b = c.b + 1 := by simp [packNext]
  unfold BankTrialLiveComparisonToken
  rw [Counter.resetBankOld, bankPair_nonroot _ _ _ _ _ (by simp [bankCell, hx, hbz])]
  rw [renewalBankPairMemory_nonroot c m e dest x y (by omega)]
  rcases hy with hy | hy
  · simp [Counter.resetBankOld, bankMemoryNRW, bankPairNR, bankCell, hx, hy, hbz, hp0,
      Id.run_pure, Id.run_bind, apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd,
      apply_ite BankCell.tok, apply_ite BankCell.role, ite_self]
    all_goals (cases hxt : x.tok <;> cases hyt : y.tok <;>
      simp [Counter.resetBankOld, bankMemoryNRW, bankPairNR, bankCell, hx, hy, hbz, hp0, hxt, hyt,
        Id.run_pure, Id.run_bind, apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd,
        apply_ite BankCell.tok, apply_ite BankCell.role, ite_self])
  · simp [Counter.resetBankOld, bankMemoryNRW, bankPairNR, bankCell, hx, hy, hbz, hpb,
      Id.run_pure, Id.run_bind]
    all_goals (cases hxt : x.tok <;> cases hyt : y.tok <;>
      simp [Counter.resetBankOld, bankMemoryNRW, bankPairNR, bankCell, hx, hy, hbz, hpb, hxt, hyt,
        Id.run_pure, Id.run_bind])

/-- M6-P, spacer stable edge (source PACK > b, responder PACK 0): no
POST pair cell carries a live comparison token.
Consumer: the M6-P comparator preimage, spacer case. -/
theorem bankWindowJointSpacerEdgeTokens {c : Compiled} (x y : Agent c)
    (hx : c.b < x.pack.val) (hy : y.pack.val = 0) :
    ¬ BankTrialLiveComparisonToken (Counter.resetBankOld x y).1.tok ∧
    ¬ BankTrialLiveComparisonToken (Counter.resetBankOld x y).2.tok := by
  have hp : packNext x.pack.val 0 c.b = 0 := by
    simp [packNext]
    omega
  have hxz : x.pack.val ≠ 0 := by omega
  have hxb : ¬ x.pack.val ≤ c.b := by omega
  have hxb' : ¬ x.pack.val < c.b := by omega
  have hxb'' : x.pack.val ≠ c.b := by omega
  unfold BankTrialLiveComparisonToken
  rw [Counter.resetBankOld, bankPair_nonroot _ _ _ _ _ (by simp [bankCell, hxz])]
  simp [Counter.resetBankOld, bankPairNR, bankCell, hy, hp, hxz, hxb, hxb', hxb'', Id.run_pure,
    Id.run_bind, apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd,
    apply_ite BankCell.tok, apply_ite BankCell.role, ite_self]
  all_goals (cases hxt : x.tok <;> cases hyt : y.tok <;>
    simp [Counter.resetBankOld, bankPairNR, bankCell, hy, hp, hxz, hxb, hxb', hxb'', hxt, hyt,
      Id.run_pure, Id.run_bind, apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd,
      apply_ite BankCell.tok, apply_ite BankCell.role, ite_self])

/-- M6-P, edge classification: a stable edge from a nonroot source is
aligned (source PACK k < b, responder k+1), top (source PACK b, responder
0 or b+1) or spacer (source PACK > b, responder 0); read off packNext.
Consumer: bankWindowJointStableEdgeComparatorPreimage. -/
theorem bankWindowJointStableEdgeShape (a c b : Nat)
    (hstable : packNext a c b = c) :
    (a < b ∧ c = a + 1) ∨ (a = b ∧ (c = 0 ∨ c = b + 1)) ∨
      (b < a ∧ c = 0) := by
  unfold packNext at hstable
  by_cases h1 : a < b
  · rw [if_pos h1] at hstable
    exact Or.inl ⟨h1, hstable.symm⟩
  · rw [if_neg h1] at hstable
    by_cases h2 : a = b
    · rw [if_pos h2] at hstable
      refine Or.inr (Or.inl ⟨h2, ?_⟩)
      by_cases h3 : c = 0
      · exact Or.inl h3
      · rw [if_neg h3] at hstable
        exact Or.inr hstable.symm
    · rw [if_neg h2] at hstable
      exact Or.inr (Or.inr ⟨by omega, hstable.symm⟩)

/-- M6-P, comparator preimage on a stable nonroot edge: a POST genuine
comparator (live comparison token, payload worker with origin o) at one
of the two pair sites was already a comparator with the same payload at
one of the two pair sites before the step. Token from
bankWindowClosureSelectedBankTrip, worker from
rbReferenceSelectedPairFrame, row facts from the aligned/top/spacer
lemmas above.
Consumer: M6-P phaseExcludes/phaseComplete and M6-Q CWAIT clauses for
foreign roots on a stable nonroot edge. -/
theorem bankWindowJointStableEdgeComparatorPreimage {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hnonroot : (r.1 e).pack.val ≠ 0)
    (hstable :
      packNext (r.1 e).pack.val (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      (r.1 (ring.rightNeighbor e)).pack.val)
    (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n)
    (hi : i = e ∨ i = ring.rightNeighbor e)
    (hw : BankComparatorOriginWorker ring (renewalBankNext ring r e) o i p) :
    ∃ j : Fin n, (j = e ∨ j = ring.rightNeighbor e) ∧
      BankComparatorOriginWorker ring r o j p := by
  have ht := bankWindowClosureSelectedBankTrip ring hn hbank r e
  simp only [Counter.resetAgentBankTrip, Counter.resetCellBankTrip,
    Prod.mk.injEq] at ht
  have hf := rbReferenceSelectedPairFrame ring (by omega : 2 ≤ n) r e
  have hmS :
      ((renewalBankNext ring r e).2.sites e) =
        (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
          r.2 e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).1 := hf.2.2.1
  have hmD :
      ((renewalBankNext ring r e).2.sites (ring.rightNeighbor e)) =
        (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
          r.2 e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).2 := hf.2.2.2
  obtain ⟨hwk, horig, hlive⟩ := hw
  rcases bankWindowJointStableEdgeShape _ _ _ hstable with
    ⟨hlt, hy⟩ | ⟨hx, hy⟩ | ⟨hgt, hy⟩
  · have hk : 1 ≤ (r.1 e).pack.val := by omega
    have hm := bankWindowJointAlignedWorkers r.2 e (ring.rightNeighbor e)
      (r.1 e) (r.1 (ring.rightNeighbor e)) _ hk hlt rfl hy
    rcases hi with hi | hi <;> rw [hi] at hlive hwk
    · rw [ht.1.2.2] at hlive
      rw [hmS] at hwk
      rcases bankWindowJointAlignedSourceLive (r.1 e)
          (r.1 (ring.rightNeighbor e)) _ hk hlt rfl hy hlive with hA | hB
      · refine ⟨ring.rightNeighbor e, Or.inr rfl, ?_, horig, ?_⟩
        · rw [← hm.1 hA]
          exact hwk
        · rcases hA with ⟨_, hy' | hy' | ⟨_, hy' | hy'⟩⟩ <;>
            simp [BankTrialLiveComparisonToken, hy']
      · refine ⟨e, Or.inl rfl, ?_, horig, ?_⟩
        · rw [← hm.2.1 hB]
          exact hwk
        · rcases hB with ⟨hx' | hx', _⟩ <;>
            simp [BankTrialLiveComparisonToken, hx']
    · rw [ht.2.2.2] at hlive
      rw [hmD] at hwk
      rcases bankWindowJointAlignedResponderLive (r.1 e)
          (r.1 (ring.rightNeighbor e)) _ hk hlt rfl hy hlive with hA | hB
      · refine ⟨e, Or.inl rfl, ?_, horig, ?_⟩
        · rw [← hm.2.2.1 hA]
          exact hwk
        · rcases hA with ⟨hx' | hx', _⟩ <;>
            simp [BankTrialLiveComparisonToken, hx']
      · refine ⟨ring.rightNeighbor e, Or.inr rfl, ?_, horig, ?_⟩
        · rw [← hm.2.2.2 hB]
          exact hwk
        · rcases hB with ⟨_, hy' | hy', _⟩ <;>
            simp [BankTrialLiveComparisonToken, hy']
  · have hbz : (compileAdvice (ceilLogTwo n)).b ≠ 0 := by omega
    have hT := bankWindowJointTopEdgeTokens r.2 e (ring.rightNeighbor e)
      (r.1 e) (r.1 (ring.rightNeighbor e)) hx hbz hy
    rcases hi with hi | hi <;> rw [hi] at hlive hwk
    · rw [ht.1.2.2] at hlive
      rw [hmS] at hwk
      obtain ⟨hold, hwork⟩ := hT.1 hlive
      refine ⟨e, Or.inl rfl, ?_, horig, hold⟩
      rw [← hwork]
      exact hwk
    · rw [ht.2.2.2] at hlive
      exact (hT.2 hlive).elim
  · have hS := bankWindowJointSpacerEdgeTokens
      (r.1 e) (r.1 (ring.rightNeighbor e)) hgt hy
    rcases hi with hi | hi <;> rw [hi] at hlive hwk
    · rw [ht.1.2.2] at hlive
      exact (hS.1 hlive).elim
    · rw [ht.2.2.2] at hlive
      exact (hS.2 hlive).elim

/-- M6-P, phaseExcludes and phaseComplete at a foreign root on a stable
edge from a nonroot source: every POST comparator rooted at root has an
OLD comparator with the same payload (on the pair by
bankWindowJointStableEdgeComparatorPreimage, off the pair framed), the
root mode is framed, and Complete transfers along the stable PACK frame.
No scope, mode or taint hypothesis is needed.
Consumer: the M6 assembly of BankWindowRootFieldsAt for foreign roots on
a stable nonroot edge (ledger row M6-P; also the first two clauses of
M6-Q and M6-S). -/
theorem bankWindowOverlapStableNonrootPhaseFields {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hnonroot :
      ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ≠ 0)
    (hstable :
      packNext
        ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val
        ((rbRun ring (renewalBankStart ring seed) pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((rbRun ring (renewalBankStart ring seed) pre).1
        (ring.rightNeighbor e)).pack.val)
    (hforeign : root ≠ e ∧ root ≠ ring.rightNeighbor e) :
    (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
      o.root = root →
      BankComparatorOriginWorker ring
        (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
        o i p →
      ((renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e).1 o.root).mode ≠
          .ARMED ∧
      ((renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e).1 o.root).mode ≠
          .CSTART ∧
      ((renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e).1 o.root).mode ≠
          .IWAIT) ∧
    (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
      o.root = root →
      BankComparatorOriginWorker ring
        (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
        o i p →
      ((renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e).1 o.root).mode =
          .CWAIT →
      Counter.Complete ring
        (renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e).1 o.root) := by
  have hpackAll := bankWindowOverlapStablePackFrame ring hn seed pre e hstable
  have hpre : ∀ (o : RenewalBankOrigin n) (i : Fin n)
      (p : RenewalBankPayload n),
      BankComparatorOriginWorker ring
        (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
        o i p →
      ∃ j : Fin n, BankComparatorOriginWorker ring
        (rbRun ring (renewalBankStart ring seed) pre) o j p := by
    intro o i p hw
    by_cases hi : i = e ∨ i = ring.rightNeighbor e
    · obtain ⟨j, _, hj⟩ := bankWindowJointStableEdgeComparatorPreimage ring
        hn hbank (rbRun ring (renewalBankStart ring seed) pre) e hnonroot
        hstable o i p hi hw
      exact ⟨j, hj⟩
    · have hf := bankWindowExactOffPairFrame ring
        (rbRun ring (renewalBankStart ring seed) pre) e i
        (fun h => hi (Or.inl h)) (fun h => hi (Or.inr h))
      obtain ⟨hwk, horig, hlive⟩ := hw
      refine ⟨i, ?_, horig, ?_⟩
      · rw [← hf.2]
        exact hwk
      · rw [← hf.1]
        exact hlive
  have hframeRoot := bankWindowExactOffPairFrame ring
    (rbRun ring (renewalBankStart ring seed) pre) e root
    hforeign.1 hforeign.2
  have hmode :
      ((renewalBankNext ring
          (rbRun ring (renewalBankStart ring seed) pre) e).1 root).mode =
        ((rbRun ring (renewalBankStart ring seed) pre).1 root).mode := by
    rw [hframeRoot.1]
  constructor
  · intro o i p ho hw
    obtain ⟨j, hj⟩ := hpre o i p hw
    have hold := hJ.phaseExcludes o j p hj
    rw [ho] at hold ⊢
    rw [hmode]
    exact hold
  · intro o i p ho hw hc
    obtain ⟨j, hj⟩ := hpre o i p hw
    rw [ho] at hc ⊢
    rw [hmode] at hc
    have hold := hJ.phaseComplete o j p hj (by rw [ho]; exact hc)
    rw [ho] at hold
    intro jj hjj
    rw [hpackAll]
    exact hold jj hjj

/-- M6, frozen pair: on a stable-PACK edge whose two endpoints keep their
token, bit and worker (idle pairs, and the quiet rows where a CL source
or a non-top CR responder waits for another edge), every root other than
both endpoints satisfies every root-indexed POST clause, by the
field-level transport bankWindowRootFieldsAtOfDigitReads.
Consumer: bankWindowOverlapStableCwaitRootFieldsAt (quiet rows of M6-Q). -/
theorem bankWindowOverlapStableFrozenPairRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hstable :
      packNext ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val)
    (hpair : ∀ z : Fin n, (z = e ∨ z = ring.rightNeighbor e) →
      bankWindowReadTok (rbRun ring (renewalBankStart ring seed) pre) (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) z ∧ bankWindowReadBit (rbRun ring (renewalBankStart ring seed) pre) (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) z ∧
      bankWindowReadWorker (rbRun ring (renewalBankStart ring seed) pre) (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) z)
    (hforeign : root ≠ e ∧ root ≠ ring.rightNeighbor e) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) root := by
  have hpackAll := bankWindowOverlapStablePackFrame ring hn seed pre e hstable
  have hreads : ∀ z : Fin n,
      bankWindowReadTok (rbRun ring (renewalBankStart ring seed) pre) (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) z ∧ bankWindowReadBit (rbRun ring (renewalBankStart ring seed) pre) (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) z ∧
      bankWindowReadWorker (rbRun ring (renewalBankStart ring seed) pre) (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) z := by
    intro z
    by_cases hz : z = e ∨ z = ring.rightNeighbor e
    · exact hpair z hz
    · have hf := bankWindowExactOffPairAtomicReads ring (rbRun ring (renewalBankStart ring seed) pre) e z
        (fun h => hz (Or.inl h)) (fun h => hz (Or.inr h))
      exact ⟨hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.2.1⟩
  have hroot := bankWindowExactOffPairAtomicReads ring (rbRun ring (renewalBankStart ring seed) pre) e root
    hforeign.1 hforeign.2
  apply bankWindowRootFieldsAtOfDigitReads ring (rbRun ring (renewalBankStart ring seed) pre) _ root hJ
  · intro k _
    exact hpackAll _
  · intro j
    exact (hreads _).1
  · intro j
    exact (hreads _).2.1
  · intro j
    exact (hreads _).2.2
  · exact hroot.2.1
  · exact hroot.2.2.2.2.2.2
  · intro _
    exact hroot.2.2.2.2.1
  · intro i p o _ _ _
    exact ⟨(hreads i).1, hpackAll i, (hreads i).2.2⟩
  · intro p o hc ho
    exact ((bankWindowOverlapPostReceipt ring hn hbank seed pre e).activeRoot
      root p o hc ho).symm

/-- M6-Q quiet rows, cell level: on an aligned stable edge a CL source
facing an empty responder, or an empty source facing a non-top CR
responder, leaves both tokens, both bits and both workers unchanged.
Consumer: bankWindowOverlapStableQuietPairReads. -/
theorem bankWindowJointAlignedQuietCells {n : Nat} {c : Compiled}
    (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (k : Nat)
    (hk : 1 ≤ k) (hbelow : k < c.b)
    (hx : x.pack.val = k) (hy : y.pack.val = k + 1)
    (hq : ((x.tok = .CL0 ∨ x.tok = .CL1) ∧ y.tok = .E) ∨
      (x.tok = .E ∧ (y.tok = .CR0 ∨ y.tok = .CR1) ∧ k + 1 ≠ c.b)) :
    (Counter.resetBankOld x y).1.tok = x.tok ∧
    (Counter.resetBankOld x y).1.bit = x.bit ∧
    (Counter.resetBankOld x y).2.tok = y.tok ∧
    (Counter.resetBankOld x y).2.bit = y.bit ∧
    (renewalBankPairMemory c m e dest x y).1.worker = (m.sites e).worker ∧
    (renewalBankPairMemory c m e dest x y).2.worker =
      (m.sites dest).worker := by
  have hle : k ≤ c.b := by omega
  have hnz : k ≠ 0 := by omega
  have hbz : c.b ≠ 0 := by omega
  have hne : k ≠ c.b := by omega
  have hnextPos : 1 ≤ k + 1 := by omega
  have hnextNz : k + 1 ≠ 0 := by omega
  have hnl : ¬ c.b < k + 1 := by omega
  have hrole : packNext k (k + 1) c.b = k + 1 := by
    simp [packNext, hbelow]
  rcases hq with ⟨hxt, hyt⟩ | ⟨hxt, hyt | hyt, htop⟩
  · by_cases htop : k + 1 = c.b
    · have hpTop : packNext k c.b c.b = c.b := by
        have h := hrole
        rw [htop] at h
        exact h
      rcases hxt with hxt | hxt <;>
        simp [Counter.resetBankOld, renewalBankPairMemory, bankPair, bankCell,
          hx, hy, hk, hbelow, hle, hnz, hbz, hne, hnextPos, hnextNz, hnl,
          hrole, hpTop, htop, hxt, hyt, Id.run_pure, Id.run_bind]
    · rcases hxt with hxt | hxt <;>
        simp [Counter.resetBankOld, renewalBankPairMemory, bankPair, bankCell,
          hx, hy, hk, hbelow, hle, hnz, hbz, hne, hnextPos, hnextNz, hnl,
          hrole, htop, hxt, hyt, Id.run_pure, Id.run_bind]
  · simp [Counter.resetBankOld, renewalBankPairMemory, bankPair, bankCell,
      hx, hy, hk, hbelow, hle, hnz, hbz, hne, hnextPos, hnextNz, hnl, hrole,
      hxt, hyt, htop, Id.run_pure, Id.run_bind]
  · simp [Counter.resetBankOld, renewalBankPairMemory, bankPair, bankCell,
      hx, hy, hk, hbelow, hle, hnz, hbz, hne, hnextPos, hnextNz, hnl, hrole,
      hxt, hyt, htop, Id.run_pure, Id.run_bind]

/-- M6-Q quiet rows, reference level: the quiet cell rows give unchanged
token, bit and worker reads at both pair sites.
Consumer: bankWindowOverlapStableFrozenPairRootFieldsAt in
bankWindowOverlapStableCwaitRootFieldsAt. -/
theorem bankWindowOverlapStableQuietPairReads {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n) (k : Nat)
    (hk : 1 ≤ k) (hbelow : k < (compileAdvice (ceilLogTwo n)).b)
    (hx : (r.1 e).pack.val = k)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = k + 1)
    (hq : (((r.1 e).tok = .CL0 ∨ (r.1 e).tok = .CL1) ∧
        (r.1 (ring.rightNeighbor e)).tok = .E) ∨
      ((r.1 e).tok = .E ∧
        ((r.1 (ring.rightNeighbor e)).tok = .CR0 ∨
          (r.1 (ring.rightNeighbor e)).tok = .CR1) ∧
        k + 1 ≠ (compileAdvice (ceilLogTwo n)).b)) :
    ∀ z : Fin n, (z = e ∨ z = ring.rightNeighbor e) →
      bankWindowReadTok r (renewalBankNext ring r e) z ∧
      bankWindowReadBit r (renewalBankNext ring r e) z ∧
      bankWindowReadWorker r (renewalBankNext ring r e) z := by
  have hcells := bankWindowJointAlignedQuietCells r.2 e (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e)) k hk hbelow hx hy hq
  have htrip := bankWindowClosureSelectedBankTrip ring hn hbank r e
  simp only [Counter.resetAgentBankTrip, Counter.resetCellBankTrip,
    Prod.mk.injEq] at htrip
  have hf := rbReferenceSelectedPairFrame ring (by omega : 2 ≤ n) r e
  have hwS := congrArg (fun s : RenewalBankSite n => s.worker) hf.2.2.1
  have hwD := congrArg (fun s : RenewalBankSite n => s.worker) hf.2.2.2
  intro z hz
  unfold bankWindowReadTok bankWindowReadBit bankWindowReadWorker
  rcases hz with hz | hz <;> rw [hz]
  · exact ⟨htrip.1.2.2.trans hcells.1, htrip.1.2.1.trans hcells.2.1,
      hwS.trans hcells.2.2.2.2.1⟩
  · exact ⟨htrip.2.2.2.trans hcells.2.2.1, htrip.2.2.1.trans hcells.2.2.2.1,
      hwD.trans hcells.2.2.2.2.2⟩

/-- M6-Q, D7 top comparison turn, physical and ghost rows: on the aligned
top edge (source PACK k, responder PACK k+1 = b) an empty source facing
CR0/CR1 receives CL0/CL1 (CL1 exactly for CR1), the responder token is
erased, both bits are fixed, the source takes the responder's worker and
the responder worker is erased.
Consumer: bankWindowOverlapTopComparisonTurnCurrentFields. -/
theorem bankWindowJointTopTurnCells {n : Nat} {c : Compiled}
    (m : RenewalBankMemory n) (e dest : Fin n) (x y : Agent c) (k : Nat)
    (hk : 1 ≤ k) (htop : k + 1 = c.b)
    (hx : x.pack.val = k) (hy : y.pack.val = k + 1)
    (hempty : x.tok = .E)
    (hcr : y.tok = .CR0 ∨ y.tok = .CR1) :
    (Counter.resetBankOld x y).1.tok =
      (if y.tok = .CR1 then .CL1 else .CL0) ∧
    (Counter.resetBankOld x y).2.tok = .E ∧
    (Counter.resetBankOld x y).1.bit = x.bit ∧
    (Counter.resetBankOld x y).2.bit = y.bit ∧
    (renewalBankPairMemory c m e dest x y).1.worker =
      (m.sites dest).worker ∧
    (renewalBankPairMemory c m e dest x y).2.worker = .empty := by
  have hbelow : k < c.b := by omega
  have hle : k ≤ c.b := by omega
  have hnz : k ≠ 0 := by omega
  have hbz : c.b ≠ 0 := by omega
  have hne : k ≠ c.b := by omega
  have hnextPos : 1 ≤ k + 1 := by omega
  have hnextNz : k + 1 ≠ 0 := by omega
  have hnl : ¬ c.b < k + 1 := by omega
  have hrole : packNext k (k + 1) c.b = k + 1 := by
    simp [packNext, hbelow]
  have hpTop : packNext k c.b c.b = c.b := by
    have h := hrole
    rw [htop] at h
    exact h
  rcases hcr with hz | ho
  · simp [Counter.resetBankOld, renewalBankPairMemory, bankPair, bankCell,
      hx, hy, hk, hbelow, hle, hnz, hbz, hne, hnextPos, hnextNz, hnl, hrole,
      hpTop, htop, hempty, hz, Id.run_pure, Id.run_bind]
  · simp [Counter.resetBankOld, renewalBankPairMemory, bankPair, bankCell,
      hx, hy, hk, hbelow, hle, hnz, hbz, hne, hnextPos, hnextNz, hnl, hrole,
      hpTop, htop, hempty, ho, Id.run_pure, Id.run_bind]

/-- M6-Q, D7 top comparison turn, full current-origin package: the old
genuine CR comparator p at the top digit D(b) = e+ of a CWAIT root with
controller waiting [] becomes a CL comparator at D(b-1) = e with the same
payload; the origin root stays CWAIT and complete, the CL flag records
exactly the old CR flag (prefix matched through b), the live token and
OnlyToken move to e, and the head count is unchanged. Mirror of
bankWindowOverlapInteriorComparisonReturnCurrentFields; no POST-J
assumption.
Consumer: bankWindowOverlapStableCwaitMovedRootFieldsAt, D7 row of M6-Q. -/
theorem bankWindowOverlapTopComparisonTurnCurrentFields {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n) (k : Nat)
    (hk : 1 ≤ k)
    (htop : k + 1 = (compileAdvice (ceilLogTwo n)).b)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hx : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val = k)
    (hy : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val = k + 1)
    (hempty : ((rbRun ring (renewalBankStart ring seed) pre).1 e).tok = .E)
    (hcr : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .CR0 ∨
      ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .CR1)
    (o : RenewalBankOrigin n) (p : RenewalBankPayload n)
    (hworker : ((rbRun ring (renewalBankStart ring seed) pre).2.sites (ring.rightNeighbor e)).worker = .payload p)
    (horigin : p.origin = some o)
    (hmode : ((rbRun ring (renewalBankStart ring seed) pre).1 o.root).mode = .CWAIT)
    (hcontroller : ((rbRun ring (renewalBankStart ring seed) pre).2.sites o.root).controller = .waiting []) :
    BankComparatorCurrentWorker ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) o e p ∧
    Counter.Complete ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 o.root ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankTrialLiveComparisonToken
        ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 (Counter.site ring o.root (j.val + 1))).tok →
      Counter.site ring o.root (j.val + 1) = e) ∧
    (((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).tok = .CR1 →
      bankComparatorPrefixMatched ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) o ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).pack.val) ∧
    (((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).tok = .CR0 →
      ¬ bankComparatorPrefixMatched ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) o ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).pack.val) ∧
    (((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).tok = .CL1 →
      bankComparatorPrefixMatched ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) o
        (compileAdvice (ceilLogTwo n)).b) ∧
    (((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).tok = .CL0 →
      ¬ bankComparatorPrefixMatched ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) o
        (compileAdvice (ceilLogTwo n)).b) ∧
    (bankWindowOnlyToken ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) o.root e ∧
      p.heads = bankOriginBinaryValue ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 o ∧
      bankOriginBinaryValue ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 o ≤
        (compileAdvice (ceilLogTwo n)).K) := by
  have hcells := bankWindowJointTopTurnCells (rbRun ring (renewalBankStart ring seed) pre).2 e (ring.rightNeighbor e)
    ((rbRun ring (renewalBankStart ring seed) pre).1 e) ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)) k hk htop hx hy hempty hcr
  have htrip := bankWindowClosureSelectedBankTrip ring hn hbank (rbRun ring (renewalBankStart ring seed) pre) e
  simp only [Counter.resetAgentBankTrip, Counter.resetCellBankTrip,
    Prod.mk.injEq] at htrip
  have hf := rbReferenceSelectedPairFrame ring (by omega : 2 ≤ n) (rbRun ring (renewalBankStart ring seed) pre) e
  have hwS : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites e).worker = .payload p := by
    have h := congrArg (fun s : RenewalBankSite n => s.worker) hf.2.2.1
    exact (h.trans hcells.2.2.2.2.1).trans hworker
  have hwD : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites (ring.rightNeighbor e)).worker = .empty := by
    have h := congrArg (fun s : RenewalBankSite n => s.worker) hf.2.2.2
    exact h.trans hcells.2.2.2.2.2
  have htokS : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).tok =
      (if ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .CR1 then .CL1 else .CL0) :=
    htrip.1.2.2.trans hcells.1
  have htokD : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 (ring.rightNeighbor e)).tok = .E :=
    htrip.2.2.2.trans hcells.2.1
  have hbitS : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).bit = ((rbRun ring (renewalBankStart ring seed) pre).1 e).bit :=
    htrip.1.2.1.trans hcells.2.2.1
  have hbitD : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 (ring.rightNeighbor e)).bit =
      ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).bit :=
    htrip.2.2.1.trans hcells.2.2.2.1
  have hliveS : BankTrialLiveComparisonToken ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).tok := by
    rw [htokS]
    split <;> simp [BankTrialLiveComparisonToken]
  have htokenOld :
      BankTrialLiveComparisonToken ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok := by
    rcases hcr with hz | ho
    · simp [BankTrialLiveComparisonToken, hz]
    · simp [BankTrialLiveComparisonToken, ho]
  have hcompOld : BankComparatorOriginWorker ring (rbRun ring (renewalBankStart ring seed) pre)
      o (ring.rightNeighbor e) p := ⟨hworker, horigin, htokenOld⟩
  have holdCompare := hJ.compareExact o
    (ring.rightNeighbor e) p hworker horigin hmode hcontroller
  have honly := bankWindowOverlapOnlyTokenBackward ring (rbRun ring (renewalBankStart ring seed) pre)
    e o.root holdCompare.1 htokD
  have hbitsGlobal := bankWindowOverlapSelectedBitFrame ring (rbRun ring (renewalBankStart ring seed) pre) e
    hbitS hbitD
  have hbits : bankWindowReadDigitBits ring (rbRun ring (renewalBankStart ring seed) pre) (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) o.root := by
    intro j
    exact hbitsGlobal (Counter.site ring o.root (j.val + 1))
  have hvalue := bankWindowOverlapComparatorBinaryBitTransport
    ring (rbRun ring (renewalBankStart ring seed) pre) (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) o hbits
  have hmatch := bankWindowOverlapComparatorPrefixBitTransport
    ring (rbRun ring (renewalBankStart ring seed) pre) (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) o (compileAdvice (ceilLogTwo n)).b hbits
  have hflags := hJ.phaseFlags o (ring.rightNeighbor e) p hcompOld hmode
  have hcompleteOld := hJ.phaseComplete o (ring.rightNeighbor e) p
    hcompOld hmode
  have hzero : ((rbRun ring (renewalBankStart ring seed) pre).1 o.root).pack.val = 0 := by
    have hz := hcompleteOld 0 (by omega)
    change ((rbRun ring (renewalBankStart ring seed) pre).1 o.root).pack.val = 0 at hz
    exact hz
  have hforeign : o.root ≠ e ∧ o.root ≠ ring.rightNeighbor e := by
    constructor
    · intro hroot
      rw [hroot, hx] at hzero
      omega
    · intro hroot
      rw [hroot, hy] at hzero
      omega
  have hrootFrame := bankWindowExactOffPairFrame ring (rbRun ring (renewalBankStart ring seed) pre) e o.root
    hforeign.1 hforeign.2
  have hmodePost : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 o.root).mode = .CWAIT :=
    (congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.mode)
      hrootFrame.1).trans hmode
  have hstable :
      packNext ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val := by
    rw [hx, hy]
    simp [packNext, show k < (compileAdvice (ceilLogTwo n)).b by omega]
  have hcompletePost : Counter.Complete ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 o.root := by
    intro t ht
    exact (bankWindowOverlapStablePackFrame ring hn seed pre e hstable
      (Counter.site ring o.root t)).trans (hcompleteOld t ht)
  have hunique :
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        BankTrialLiveComparisonToken
          ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 (Counter.site ring o.root (j.val + 1))).tok →
        Counter.site ring o.root (j.val + 1) = e := by
    intro j ht
    apply honly j
    intro hE
    rw [hE] at ht
    simp [BankTrialLiveComparisonToken] at ht
  have hpackTop : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val =
      (compileAdvice (ceilLogTwo n)).b := by omega
  refine ⟨⟨⟨hwS, horigin, hliveS⟩, hmodePost⟩, hcompletePost, hunique,
    ?_, ?_, ?_, ?_, honly, holdCompare.2.2.1.trans hvalue.symm,
    by rw [hvalue]; exact holdCompare.2.2.2⟩
  · intro hpost
    rw [htokS] at hpost
    split at hpost <;> cases hpost
  · intro hpost
    rw [htokS] at hpost
    split at hpost <;> cases hpost
  · intro hpost
    rw [htokS] at hpost
    by_cases h1 : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .CR1
    · have hm := hflags.1 h1
      rw [hpackTop] at hm
      exact hmatch.mpr hm
    · rw [if_neg h1] at hpost
      cases hpost
  · intro hpost hmatched
    rw [htokS] at hpost
    by_cases h1 : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .CR1
    · rw [if_pos h1] at hpost
      cases hpost
    · have h0 : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .CR0 := by
        rcases hcr with hz | ho
        · exact hz
        · exact absurd ho h1
      have hm := hflags.2.1 h0
      rw [hpackTop] at hm
      exact hm (hmatch.mp hmatched)

/-- M6-Q CWAIT, moving-comparator assembly: a foreign CWAIT root with
controller waiting [] on a stable nonroot edge whose old window carries
its unique live token at a pair site c (digit jc), and whose genuine
comparator p (origin o rooted there) is, after the step, the current
comparator at the pair site s with the other pair site t worker-empty.
Given the moved package (current worker, complete window, unique live
token, the four flags, OnlyToken, heads and cap at s), every
root-indexed POST clause holds. Off-pair genuine workers or taint would
need a second old window token (old compareExact / cwaitTaintedUnique
OnlyToken against the live token at c).
Consumer: bankWindowOverlapStableCwaitRootFieldsAt (rows D6, D7, D8). -/
theorem bankWindowOverlapStableCwaitMovedRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hnonroot : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ≠ 0)
    (hstable :
      packNext ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val)
    (hforeign : root ≠ e ∧ root ≠ ring.rightNeighbor e)
    (hmodeOld : ((rbRun ring (renewalBankStart ring seed) pre).1 root).mode = .CWAIT)
    (hctrlOld : ((rbRun ring (renewalBankStart ring seed) pre).2.sites root).controller = .waiting [])
    (c : Fin n) (hcpair : c = e ∨ c = ring.rightNeighbor e)
    (jc : Fin (compileAdvice (ceilLogTwo n)).b)
    (hjc : Counter.site ring root (jc.val + 1) = c)
    (hliveOld : BankTrialLiveComparisonToken ((rbRun ring (renewalBankStart ring seed) pre).1 c).tok)
    (s t : Fin n)
    (hst : (s = e ∧ t = ring.rightNeighbor e) ∨
      (s = ring.rightNeighbor e ∧ t = e))
    (o : RenewalBankOrigin n) (p : RenewalBankPayload n)
    (ho : o.root = root) (horig : p.origin = some o)
    (hwt : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites t).worker = .empty)
    (hpkg :
      BankComparatorCurrentWorker ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) o s p ∧
      Counter.Complete ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 o.root ∧
      (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        BankTrialLiveComparisonToken
          ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 (Counter.site ring o.root (j.val + 1))).tok →
        Counter.site ring o.root (j.val + 1) = s) ∧
      (((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 s).tok = .CR1 →
        bankComparatorPrefixMatched ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) o ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 s).pack.val) ∧
      (((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 s).tok = .CR0 →
        ¬ bankComparatorPrefixMatched ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) o ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 s).pack.val) ∧
      (((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 s).tok = .CL1 →
        bankComparatorPrefixMatched ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) o
          (compileAdvice (ceilLogTwo n)).b) ∧
      (((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 s).tok = .CL0 →
        ¬ bankComparatorPrefixMatched ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) o
          (compileAdvice (ceilLogTwo n)).b) ∧
      (bankWindowOnlyToken ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) o.root s ∧
        p.heads = bankOriginBinaryValue ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 o ∧
        bankOriginBinaryValue ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 o ≤
          (compileAdvice (ceilLogTwo n)).K)) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) root := by
  obtain ⟨hcur, _hcomp, huniq, hf1, hf2, hf3, hf4, honly, hheads, hK⟩ := hpkg
  have hws : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites s).worker = .payload p := hcur.1.1
  have hphase := bankWindowOverlapStableNonrootPhaseFields ring hn hbank
    seed pre e root hJ hnonroot hstable hforeign
  have hjoint := bankWindowOverlapRootJointFields ring hn hbank seed pre e hJ
  have hpackAll := bankWindowOverlapStablePackFrame ring hn seed pre e hstable
  have hroot := bankWindowExactOffPairAtomicReads ring (rbRun ring (renewalBankStart ring seed) pre) e root
    hforeign.1 hforeign.2
  have hmodeR := hroot.2.1
  have hctrlR := hroot.2.2.2.2.2.2
  have hgrantR := hroot.2.2.2.2.1
  unfold bankWindowReadMode at hmodeR
  unfold bankWindowReadController at hctrlR
  unfold bankWindowReadGrant at hgrantR
  have hmodeN : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 root).mode = .CWAIT := hmodeR.trans hmodeOld
  have hctrlN : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites root).controller = .waiting [] :=
    hctrlR.trans hctrlOld
  have hcne : ((rbRun ring (renewalBankStart ring seed) pre).1 c).tok ≠ .E := by
    intro h
    rw [h] at hliveOld
    simp [BankTrialLiveComparisonToken] at hliveOld
  have hsplit : ∀ z : Fin n, (z = e ∨ z = ring.rightNeighbor e) →
      z = s ∨ z = t := by
    intro z hz
    rcases hst with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hz with h | h
    · exact Or.inl (h.trans h1.symm)
    · exact Or.inr (h.trans h2.symm)
    · exact Or.inr (h.trans h2.symm)
    · exact Or.inl (h.trans h1.symm)
  have hoffOnly : ∀ z : Fin n, ¬ (z = e ∨ z = ring.rightNeighbor e) →
      bankWindowOnlyToken ring (rbRun ring (renewalBankStart ring seed) pre) root z → False := by
    intro z hz honlyz
    have h := honlyz jc (by rw [hjc]; exact hcne)
    rw [hjc] at h
    rw [h] at hcpair
    exact hz hcpair
  have hgen : ∀ (i : Fin n) (p' : RenewalBankPayload n)
      (o' : RenewalBankOrigin n), o'.root = root →
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites i).worker = .payload p' → p'.origin = some o' →
      i = s ∧ p' = p := by
    intro i p' o' ho' hw' horig'
    by_cases hi : i = e ∨ i = ring.rightNeighbor e
    · rcases hsplit i hi with his | hit
      · rw [his, hws] at hw'
        injection hw' with h
        exact ⟨his, h.symm⟩
      · rw [hit, hwt] at hw'
        cases hw'
    · have hf := bankWindowExactOffPairFrame ring (rbRun ring (renewalBankStart ring seed) pre) e i
        (fun h => hi (Or.inl h)) (fun h => hi (Or.inr h))
      have hwOld : ((rbRun ring (renewalBankStart ring seed) pre).2.sites i).worker = .payload p' := by
        rw [← hf.2]
        exact hw'
      have hm' : ((rbRun ring (renewalBankStart ring seed) pre).1 o'.root).mode = .CWAIT := by
        rw [ho']
        exact hmodeOld
      have hc' : ((rbRun ring (renewalBankStart ring seed) pre).2.sites o'.root).controller = .waiting [] := by
        rw [ho']
        exact hctrlOld
      have hce := (hJ.compareExact o' i p' hwOld horig' hm' hc').1
      rw [ho'] at hce
      exact (hoffOnly i hi hce).elim
  have horigEq : ∀ o' : RenewalBankOrigin n, p.origin = some o' → o' = o := by
    intro o' h
    rw [horig] at h
    injection h with h
    exact h.symm
  refine ⟨hphase.1, hphase.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o' i p' ho' hw' _ j ht
    obtain ⟨hi, _⟩ := hgen i p' o' ho' hw'.1 hw'.2.1
    rw [hi]
    rw [ho', ← ho] at ht ⊢
    exact huniq j ht
  · intro o' i p' ho' hw' _
    obtain ⟨hi, hp⟩ := hgen i p' o' ho' hw'.1 hw'.2.1
    have hoo : o' = o := by
      have h := hw'.2.1
      rw [hp] at h
      exact horigEq o' h
    rw [hoo, hi]
    exact ⟨hf1, hf2, hf3, hf4⟩
  · intro _ hinh _ _
    rcases hinh with ⟨atoms, hc, hne⟩ | ⟨_, hc, _⟩
    · rw [hctrlN] at hc
      injection hc with h
      exact hne h.symm
    · rw [hctrlN] at hc
      cases hc
  · intro _ hm
    rw [hmodeN] at hm
    cases hm
  · intro _ _ _ hm
    rw [hmodeN] at hm
    rcases hm with h | h <;> cases h
  · intro _ _ _ _ hm
    rw [hmodeN] at hm
    cases hm
  · intro o' i p' ho' hw' horig' _ _
    obtain ⟨hi, hp⟩ := hgen i p' o' ho' hw' horig'
    have hoo : o' = o := by
      rw [hp] at horig'
      exact horigEq o' horig'
    rw [hoo, hi, hp]
    exact ⟨honly, hcur.1.2.2, hheads, hK⟩
  · intro _ hm
    rw [hmodeN] at hm
    cases hm
  · intro hs _ _ j ht
    by_cases hd : Counter.site ring root (j.val + 1) = e ∨
        Counter.site ring root (j.val + 1) = ring.rightNeighbor e
    · rcases hsplit _ hd with hds | hdt
      · refine ⟨o, p, by rw [hds]; exact hws, horig, ho, ?_, ?_⟩
        · rw [hds]
          exact hcur.1.2.2
        · rw [hds, ← ho]
          exact honly
      · rw [hdt] at ht
        unfold BankWindowTainted at ht
        rw [hwt] at ht
        rcases ht with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
    · have hf := bankWindowExactOffPairAtomicReads ring (rbRun ring (renewalBankStart ring seed) pre) e
        (Counter.site ring root (j.val + 1))
        (fun h => hd (Or.inl h)) (fun h => hd (Or.inr h))
      have hw := hf.2.2.2.2.2.1
      unfold bankWindowReadWorker at hw
      have htOld : BankWindowTainted (rbRun ring (renewalBankStart ring seed) pre) (Counter.site ring root (j.val + 1)) := by
        unfold BankWindowTainted at ht ⊢
        rw [hw] at ht
        exact ht
      have hscopeOld : BankWindowScope ring (rbRun ring (renewalBankStart ring seed) pre) root := by
        refine ⟨fun jj hjj => ?_, ?_⟩
        · rw [← hpackAll]
          exact hs.1 jj hjj
        · rw [← hgrantR]
          exact hs.2
      obtain ⟨_, _, _, _, _, _, honlyOld⟩ := hJ.cwaitTaintedUnique root
        hscopeOld hmodeOld hctrlOld j htOld
      exact (hoffOnly _ hd honlyOld).elim
  · intro limit hrun
    exact hjoint.2.2.2.1 root limit hforeign hrun
  · intro j
    exact hjoint.2.2.2.2 root j hforeign

/-- M6-Q CWAIT, no genuine worker: a foreign CWAIT root with controller
waiting [] whose old state has no genuine worker of any origin rooted
there, on a stable nonroot edge from its interior digit D(k), 1 <= k < b.
No genuine worker rooted there exists after the step (pair workers are
inherited, off-pair ones framed), so every comparator and compareExact
clause is vacuous; a POST tainted digit would give an old tainted digit
(pair taint preimage or frame), hence by old cwaitTaintedUnique an old
genuine worker rooted there.
Consumer: bankWindowOverlapStableCwaitRootFieldsAt. -/
theorem bankWindowOverlapStableCwaitNoGenuineRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hnonroot : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ≠ 0)
    (hstable :
      packNext ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val)
    (hforeign : root ≠ e ∧ root ≠ ring.rightNeighbor e)
    (k : Nat) (hk1 : 1 ≤ k) (hkb : k < (compileAdvice (ceilLogTwo n)).b)
    (hsite : e = Counter.site ring root k)
    (hmodeOld : ((rbRun ring (renewalBankStart ring seed) pre).1 root).mode = .CWAIT)
    (hctrlOld : ((rbRun ring (renewalBankStart ring seed) pre).2.sites root).controller = .waiting [])
    (hnone : ∀ (i : Fin n) (p : RenewalBankPayload n)
      (o : RenewalBankOrigin n), o.root = root →
      ((rbRun ring (renewalBankStart ring seed) pre).2.sites i).worker = .payload p → p.origin = some o → False) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) root := by
  have hjoint := bankWindowOverlapRootJointFields ring hn hbank seed pre e hJ
  have hpackAll := bankWindowOverlapStablePackFrame ring hn seed pre e hstable
  have hroot := bankWindowExactOffPairAtomicReads ring (rbRun ring (renewalBankStart ring seed) pre) e root
    hforeign.1 hforeign.2
  have hmodeR := hroot.2.1
  have hctrlR := hroot.2.2.2.2.2.2
  have hgrantR := hroot.2.2.2.2.1
  unfold bankWindowReadMode at hmodeR
  unfold bankWindowReadController at hctrlR
  unfold bankWindowReadGrant at hgrantR
  have hmodeN : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 root).mode = .CWAIT := hmodeR.trans hmodeOld
  have hctrlN : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites root).controller = .waiting [] :=
    hctrlR.trans hctrlOld
  have hf := rbReferenceSelectedPairFrame ring (by omega : 2 ≤ n) (rbRun ring (renewalBankStart ring seed) pre) e
  have hnogen : ∀ (i : Fin n) (p : RenewalBankPayload n)
      (o : RenewalBankOrigin n), o.root = root →
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites i).worker = .payload p → p.origin = some o → False := by
    intro i p o ho hw horig
    by_cases hi : i = e ∨ i = ring.rightNeighbor e
    · have hp : (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
            (rbRun ring (renewalBankStart ring seed) pre).2 e (ring.rightNeighbor e)
            ((rbRun ring (renewalBankStart ring seed) pre).1 e) ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e))).1.worker = .payload p ∨
          (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
            (rbRun ring (renewalBankStart ring seed) pre).2 e (ring.rightNeighbor e)
            ((rbRun ring (renewalBankStart ring seed) pre).1 e) ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e))).2.worker = .payload p := by
        rcases hi with hi | hi
        · rw [hi] at hw
          have h := congrArg (fun s : RenewalBankSite n => s.worker) hf.2.2.1
          exact Or.inl (h.symm.trans hw)
        · rw [hi] at hw
          have h := congrArg (fun s : RenewalBankSite n => s.worker) hf.2.2.2
          exact Or.inr (h.symm.trans hw)
      rcases rbBankNonrootSelectedWorkersInherited
          (compileAdvice (ceilLogTwo n)) (rbRun ring (renewalBankStart ring seed) pre).2 e (ring.rightNeighbor e)
          ((rbRun ring (renewalBankStart ring seed) pre).1 e) ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)) hnonroot p hp with h | h
      · exact hnone e p o ho h horig
      · exact hnone (ring.rightNeighbor e) p o ho h horig
    · have hfi := bankWindowExactOffPairFrame ring (rbRun ring (renewalBankStart ring seed) pre) e i
        (fun h => hi (Or.inl h)) (fun h => hi (Or.inr h))
      apply hnone i p o ho _ horig
      rw [← hfi.2]
      exact hw
  have hdk : Counter.site ring root ((⟨k - 1, by omega⟩ :
      Fin (compileAdvice (ceilLogTwo n)).b).val + 1) = e := by
    change Counter.site ring root (k - 1 + 1) = e
    rw [show k - 1 + 1 = k by omega]
    exact hsite.symm
  have hdk' : Counter.site ring root ((⟨k, hkb⟩ :
      Fin (compileAdvice (ceilLogTwo n)).b).val + 1) =
      ring.rightNeighbor e := by
    change Counter.site ring root (k + 1) = ring.rightNeighbor e
    rw [hsite]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o i p ho hw
    exact False.elim (hnogen i p o ho hw.1 hw.2.1)
  · intro o i p ho hw _
    exact False.elim (hnogen i p o ho hw.1 hw.2.1)
  · intro o i p ho hw _
    exact False.elim (hnogen i p o ho hw.1 hw.2.1)
  · intro o i p ho hw _
    exact False.elim (hnogen i p o ho hw.1 hw.2.1)
  · intro _ hinh _ _
    rcases hinh with ⟨atoms, hc, hne⟩ | ⟨_, hc, _⟩
    · rw [hctrlN] at hc
      injection hc with h
      exact hne h.symm
    · rw [hctrlN] at hc
      cases hc
  · intro _ hm
    rw [hmodeN] at hm
    cases hm
  · intro _ _ _ hm
    rw [hmodeN] at hm
    rcases hm with h | h <;> cases h
  · intro _ _ _ _ hm
    rw [hmodeN] at hm
    cases hm
  · intro o i p ho hw horig _ _
    exact False.elim (hnogen i p o ho hw horig)
  · intro _ hm
    rw [hmodeN] at hm
    cases hm
  · intro hs _ _ j ht
    have hscopeOld : BankWindowScope ring (rbRun ring (renewalBankStart ring seed) pre) root := by
      refine ⟨fun jj hjj => ?_, ?_⟩
      · rw [← hpackAll]
        exact hs.1 jj hjj
      · rw [← hgrantR]
        exact hs.2
    have hold : ∃ jj : Fin (compileAdvice (ceilLogTwo n)).b,
        BankWindowTainted (rbRun ring (renewalBankStart ring seed) pre) (Counter.site ring root (jj.val + 1)) := by
      by_cases hd : Counter.site ring root (j.val + 1) = e ∨
          Counter.site ring root (j.val + 1) = ring.rightNeighbor e
      · rcases bankWindowOverlapNonrootPairTaintPreimage ring
            (by omega : 2 ≤ n) (rbRun ring (renewalBankStart ring seed) pre) e (Counter.site ring root (j.val + 1))
            hnonroot hd ht with h | h
        · exact ⟨⟨k - 1, by omega⟩, by rw [hdk]; exact h⟩
        · exact ⟨⟨k, hkb⟩, by rw [hdk']; exact h⟩
      · have hfd := bankWindowExactOffPairAtomicReads ring (rbRun ring (renewalBankStart ring seed) pre) e
          (Counter.site ring root (j.val + 1))
          (fun h => hd (Or.inl h)) (fun h => hd (Or.inr h))
        have hw := hfd.2.2.2.2.2.1
        unfold bankWindowReadWorker at hw
        refine ⟨j, ?_⟩
        unfold BankWindowTainted at ht ⊢
        rw [hw] at ht
        exact ht
    obtain ⟨jj, hjj⟩ := hold
    obtain ⟨o, p, hw, horig, ho, _⟩ := hJ.cwaitTaintedUnique root
      hscopeOld hmodeOld hctrlOld jj hjj
    exact False.elim (hnone _ p o ho hw horig)
  · intro limit hrun
    exact hjoint.2.2.2.1 root limit hforeign hrun
  · intro j
    exact hjoint.2.2.2.2 root j hforeign

/-- M6-Q CWAIT: a foreign root in CWAIT with controller waiting [] on a
stable nonroot edge from its interior digit D(k), 1 <= k < b, satisfies
every root-indexed POST clause. Case split on the old window: no genuine
worker rooted there (bankWindowOverlapStableCwaitNoGenuineRootFieldsAt);
otherwise old compareExact gives the unique live token at the genuine
comparator site c and old phaseComplete aligns the pair PACK. c off the
pair: idle pair. c = e: CR advance (D6) or quiet CL. c = e+: CL return
(D8), top CR turn (D7, k+1 = b) or quiet non-top CR.
Consumer: the final bankWindowExactStep case split, stable interior edge,
CWAIT foreign roots (ledger row M6-Q, CWAIT part). -/
theorem bankWindowOverlapStableCwaitRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hnonroot : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ≠ 0)
    (hstable :
      packNext ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val)
    (hforeign : root ≠ e ∧ root ≠ ring.rightNeighbor e)
    (k : Nat) (hk1 : 1 ≤ k) (hkb : k < (compileAdvice (ceilLogTwo n)).b)
    (hsite : e = Counter.site ring root k)
    (hmodeOld : ((rbRun ring (renewalBankStart ring seed) pre).1 root).mode = .CWAIT)
    (hctrlOld : ((rbRun ring (renewalBankStart ring seed) pre).2.sites root).controller = .waiting []) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) root := by
  by_cases hex : ∃ (c : Fin n) (p : RenewalBankPayload n)
      (o : RenewalBankOrigin n), o.root = root ∧
      ((rbRun ring (renewalBankStart ring seed) pre).2.sites c).worker = .payload p ∧ p.origin = some o
  · obtain ⟨c, p, o, ho, hw, horig⟩ := hex
    have hm' : ((rbRun ring (renewalBankStart ring seed) pre).1 o.root).mode = .CWAIT := by
      rw [ho]
      exact hmodeOld
    have hc' : ((rbRun ring (renewalBankStart ring seed) pre).2.sites o.root).controller = .waiting [] := by
      rw [ho]
      exact hctrlOld
    obtain ⟨honlyC, hliveC, _, _⟩ := hJ.compareExact o c p hw horig hm' hc'
    rw [ho] at honlyC
    have hcomp := hJ.phaseComplete o c p ⟨hw, horig, hliveC⟩ hm'
    rw [ho] at hcomp
    have hx : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val = k := by
      rw [hsite]
      exact hcomp k (by omega)
    have hy : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val = k + 1 := by
      rw [hsite]
      exact hcomp (k + 1) (by omega)
    have hne : e ≠ ring.rightNeighbor e := by
      intro h
      have h2 := hy
      rw [← h, hx] at h2
      omega
    let jk : Fin (compileAdvice (ceilLogTwo n)).b := ⟨k - 1, by omega⟩
    have hdk : Counter.site ring root (jk.val + 1) = e := by
      change Counter.site ring root (k - 1 + 1) = e
      rw [show k - 1 + 1 = k by omega]
      exact hsite.symm
    let jk' : Fin (compileAdvice (ceilLogTwo n)).b := ⟨k, hkb⟩
    have hdk' : Counter.site ring root (jk'.val + 1) = ring.rightNeighbor e := by
      change Counter.site ring root (k + 1) = ring.rightNeighbor e
      rw [hsite]
      rfl
    have hf := rbReferenceSelectedPairFrame ring (by omega : 2 ≤ n) (rbRun ring (renewalBankStart ring seed) pre) e
    by_cases hcp : c = e ∨ c = ring.rightNeighbor e
    · rcases hcp with hce | hce
      · have hyE : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .E := by
          apply Classical.byContradiction
          intro h
          have h2 := honlyC jk' (by rw [hdk']; exact h)
          rw [hdk'] at h2
          exact hne (hce.symm.trans h2.symm)
        rw [hce] at hw hliveC
        by_cases hcr : ((rbRun ring (renewalBankStart ring seed) pre).1 e).tok = .CR0 ∨ ((rbRun ring (renewalBankStart ring seed) pre).1 e).tok = .CR1
        · have hpkg := bankWindowOverlapInteriorComparisonAdvanceCurrentFields
            ring hn hbank seed pre e k hk1 hkb hJ hx hy hcr hyE o p hw horig
            hm' hc'
          have hwt := (bankWindowOverlapInteriorComparisonAdvanceWorkers
            ring hn seed pre e k hk1 hkb hx hy hcr hyE).1
          exact bankWindowOverlapStableCwaitMovedRootFieldsAt ring hn hbank
            seed pre e root hJ hnonroot hstable hforeign hmodeOld hctrlOld
            e (Or.inl rfl) jk hdk hliveC (ring.rightNeighbor e) e
            (Or.inr ⟨rfl, rfl⟩) o p ho horig hwt hpkg
        · have hcl : ((rbRun ring (renewalBankStart ring seed) pre).1 e).tok = .CL0 ∨ ((rbRun ring (renewalBankStart ring seed) pre).1 e).tok = .CL1 := by
            have hl := hliveC
            unfold BankTrialLiveComparisonToken at hl
            rcases hl with h | h | h | h
            · exact absurd (Or.inl h) hcr
            · exact absurd (Or.inr h) hcr
            · exact Or.inl h
            · exact Or.inr h
          exact bankWindowOverlapStableFrozenPairRootFieldsAt ring hn hbank
            seed pre e root hJ hstable
            (bankWindowOverlapStableQuietPairReads ring hn hbank (rbRun ring (renewalBankStart ring seed) pre) e k hk1
              hkb hx hy (Or.inl ⟨hcl, hyE⟩)) hforeign
      · have hxE : ((rbRun ring (renewalBankStart ring seed) pre).1 e).tok = .E := by
          apply Classical.byContradiction
          intro h
          have h2 := honlyC jk (by rw [hdk]; exact h)
          rw [hdk] at h2
          exact hne (h2.trans hce)
        rw [hce] at hw hliveC
        by_cases hcr : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .CR0 ∨
            ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .CR1
        · by_cases htop : k + 1 = (compileAdvice (ceilLogTwo n)).b
          · have hpkg := bankWindowOverlapTopComparisonTurnCurrentFields
              ring hn hbank seed pre e k hk1 htop hJ hx hy hxE hcr o p hw
              horig hm' hc'
            have hcells := bankWindowJointTopTurnCells (rbRun ring (renewalBankStart ring seed) pre).2 e
              (ring.rightNeighbor e) ((rbRun ring (renewalBankStart ring seed) pre).1 e) ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e))
              k hk1 htop hx hy hxE hcr
            have hwt : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites (ring.rightNeighbor e)).worker = .empty :=
              (congrArg (fun s : RenewalBankSite n => s.worker) hf.2.2.2).trans
                hcells.2.2.2.2.2
            exact bankWindowOverlapStableCwaitMovedRootFieldsAt ring hn hbank
              seed pre e root hJ hnonroot hstable hforeign hmodeOld hctrlOld
              (ring.rightNeighbor e) (Or.inr rfl) jk' hdk' hliveC e
              (ring.rightNeighbor e) (Or.inl ⟨rfl, rfl⟩) o p ho horig hwt hpkg
          · exact bankWindowOverlapStableFrozenPairRootFieldsAt ring hn hbank
              seed pre e root hJ hstable
              (bankWindowOverlapStableQuietPairReads ring hn hbank (rbRun ring (renewalBankStart ring seed) pre) e k hk1
                hkb hx hy (Or.inr ⟨hxE, hcr, htop⟩)) hforeign
        · have hcl : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .CL0 ∨
              ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .CL1 := by
            have hl := hliveC
            unfold BankTrialLiveComparisonToken at hl
            rcases hl with h | h | h | h
            · exact absurd (Or.inl h) hcr
            · exact absurd (Or.inr h) hcr
            · exact Or.inl h
            · exact Or.inr h
          have hpkg := bankWindowOverlapInteriorComparisonReturnCurrentFields
            ring hn hbank seed pre e k hk1 hkb hJ hx hy hxE hcl o p hw horig
            hm' hc'
          have hwt := (bankWindowOverlapInteriorComparisonReturnWorkers
            ring hn seed pre e k hk1 hkb hx hy hxE hcl).2
          exact bankWindowOverlapStableCwaitMovedRootFieldsAt ring hn hbank
            seed pre e root hJ hnonroot hstable hforeign hmodeOld hctrlOld
            (ring.rightNeighbor e) (Or.inr rfl) jk' hdk' hliveC e
            (ring.rightNeighbor e) (Or.inl ⟨rfl, rfl⟩) o p ho horig hwt hpkg
    · have hxE : ((rbRun ring (renewalBankStart ring seed) pre).1 e).tok = .E := by
        apply Classical.byContradiction
        intro h
        have h2 := honlyC jk (by rw [hdk]; exact h)
        rw [hdk] at h2
        exact hcp (Or.inl h2.symm)
      have hyE : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .E := by
        apply Classical.byContradiction
        intro h
        have h2 := honlyC jk' (by rw [hdk']; exact h)
        rw [hdk'] at h2
        exact hcp (Or.inr h2.symm)
      exact bankWindowOverlapStableIdlePairRootFieldsAt ring hn hbank seed pre
        e root hJ hnonroot hstable hxE hyE hforeign
  · exact bankWindowOverlapStableCwaitNoGenuineRootFieldsAt ring hn hbank
      seed pre e root hJ hnonroot hstable hforeign k hk1 hkb hsite
      hmodeOld hctrlOld
      (fun i p o ho hw horig => hex ⟨i, p, o, ho, hw, horig⟩)


/-- M6-P closure: a foreign root out of POST scope whose mode is not
CWAIT, on a stable edge from a nonroot source, satisfies every
root-indexed POST clause: phaseExcludes and phaseComplete by
bankWindowOverlapStableNonrootPhaseFields, the CWAIT-guarded comparator
and compareExact clauses and every scope-guarded clause are vacuous,
proto and orphan come from bankWindowOverlapRootJointFields. Together
with bankWindowOverlapStableCwaitRootFieldsAt (CWAIT, waiting [], any
scope) this leaves only M6-S (CWAIT, nonempty waiting list) among
out-of-scope INT roots.
Consumer: the final bankWindowExactStep case split, stable nonroot edge,
foreign roots out of scope (ledger row M6-P). -/
theorem bankWindowOverlapStableNonrootOutOfScopeRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hnonroot : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ≠ 0)
    (hstable :
      packNext ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val)
    (hforeign : root ≠ e ∧ root ≠ ring.rightNeighbor e)
    (hnscope : ¬ BankWindowScope ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) root)
    (hncwait : ((rbRun ring (renewalBankStart ring seed) pre).1 root).mode ≠ .CWAIT) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) root := by
  have hphase := bankWindowOverlapStableNonrootPhaseFields ring hn hbank
    seed pre e root hJ hnonroot hstable hforeign
  have hjoint := bankWindowOverlapRootJointFields ring hn hbank seed pre e hJ
  have hroot := bankWindowExactOffPairAtomicReads ring (rbRun ring (renewalBankStart ring seed) pre) e root
    hforeign.1 hforeign.2
  have hmodeR := hroot.2.1
  unfold bankWindowReadMode at hmodeR
  have hmN : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 root).mode ≠ .CWAIT := by
    rw [hmodeR]
    exact hncwait
  refine ⟨hphase.1, hphase.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o _ _ ho _ hm
    rw [ho] at hm
    exact (hmN hm).elim
  · intro o _ _ ho _ hm
    rw [ho] at hm
    exact (hmN hm).elim
  · intro hs
    exact (hnscope hs).elim
  · intro hs
    exact (hnscope hs).elim
  · intro _ _ hs
    exact (hnscope hs).elim
  · intro _ _ _ hs
    exact (hnscope hs).elim
  · intro o _ _ ho _ _ hm
    rw [ho] at hm
    exact (hmN hm).elim
  · intro hs
    exact (hnscope hs).elim
  · intro hs
    exact (hnscope hs).elim
  · intro limit hrun
    exact hjoint.2.2.2.1 root limit hforeign hrun
  · intro j
    exact hjoint.2.2.2.2 root j hforeign


/-- M6-T in RootFieldsAt form: a root whose window has the stepped edge's
source as its top digit D(b), complete before the step, on a stable-PACK
edge, satisfies every root-indexed POST clause. Definitional repackaging
of bankWindowOverlapTopGhostStableRootClauses (BankWindowOverlapRoot).
Consumer: the final bankWindowExactStep case split, TOP class (ledger
row M6-T). -/
theorem bankWindowOverlapTopGhostStableRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hcompleteOld : Counter.Complete ring (rbRun ring (renewalBankStart ring seed) pre).1 root)
    (htop : e = Counter.site ring root (compileAdvice (ceilLogTwo n)).b)
    (hstable :
      packNext ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) root :=
  bankWindowOverlapTopGhostStableRootClauses ring hn hbank seed pre e root
    hJ hcompleteOld htop hstable

/-- M6-S, controller shape at a waiting site: in a state with the
in-flight frame, a site whose controller is a waiting list has PACK zero
and mode RWAIT, IWAIT or CWAIT.
Consumer: bankWindowJointCwaitWaitingStepBack. -/
theorem bankWindowJointWaitingControllerShape {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n) (z : Fin n)
    (atoms : List (RenewalBankAtom n))
    (hframe : BankInFlightAligned ring r)
    (hc : (r.2.sites z).controller = .waiting atoms) :
    (r.1 z).pack.val = 0 ∧
    ((r.1 z).mode = .RWAIT ∨ (r.1 z).mode = .IWAIT ∨
      (r.1 z).mode = .CWAIT) := by
  have hfr := (hframe z).1
  unfold bankInFlightControllerShape at hfr
  by_cases hp0 : (r.1 z).pack.val = 0
  · rw [if_pos hp0] at hfr
    refine ⟨hp0, ?_⟩
    cases hm : (r.1 z).mode with
    | RESET =>
        rw [hm, hc] at hfr
        cases hfr
    | ARMED =>
        rw [hm, hc] at hfr
        obtain ⟨_, h⟩ := hfr
        cases h
    | CSTART =>
        rw [hm, hc] at hfr
        obtain ⟨_, h⟩ := hfr
        cases h
    | RWAIT => exact Or.inl rfl
    | IWAIT => exact Or.inr (Or.inl rfl)
    | CWAIT => exact Or.inr (Or.inr rfl)
  · rw [if_neg hp0, hc] at hfr
    cases hfr

/-- M6-S cells: a PACK-zero RWAIT source on a first-digit edge does not end in CWAIT.
Consumer: bankWindowJointSourceRootWaitNotCwait. -/
theorem bankWindowJointSourceRootRwaitAlignedNotCwait {c : Compiled} (x y : Agent c)
    (hx : x.pack.val = 0) (hm : x.mode = .RWAIT) (hy1 : y.pack.val = 1) :
    (Counter.resetBankOld x y).1.mode ≠ .CWAIT := by
  have hb : 0 < c.b := by
    change 0 < c.s + 11
    omega
  have hbz : c.b ≠ 0 := by omega
  have hwide : c.b ≠ 1 := by
    change c.s + 11 ≠ 1
    omega
  have hp : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  cases hg : x.grant <;> cases ht : y.tok <;>
    by_cases hl : 1 < x.lease.val <;>
    simp [Counter.resetBankOld, bankPair, bankCell, hx, hy1, hp, hb, hbz, hwide,
      hg, hm, ht, hl, isWaitMode, isRetTok, Id.run_pure, Id.run_bind]

/-- M6-S cells: a PACK-zero RWAIT source whose responder changes PACK does not end in CWAIT.
Consumer: bankWindowJointSourceRootWaitNotCwait. -/
theorem bankWindowJointSourceRootRwaitChangedNotCwait {c : Compiled} (x y : Agent c)
    (hx : x.pack.val = 0) (hm : x.mode = .RWAIT) (hy1 : y.pack.val ≠ 1) :
    (Counter.resetBankOld x y).1.mode ≠ .CWAIT := by
  have hb : 0 < c.b := by
    change 0 < c.s + 11
    omega
  have hbz : c.b ≠ 0 := by omega
  have hwide : c.b ≠ 1 := by
    change c.s + 11 ≠ 1
    omega
  have hp : packNext 0 y.pack.val c.b = 1 := by
    simp [packNext, hb]
  cases hg : x.grant <;> cases ht : y.tok <;>
    by_cases hl : 1 < x.lease.val <;>
    simp [Counter.resetBankOld, bankPair, bankCell, hx, hp, hb, hbz, hwide,
      hy1, hg, hm, ht, hl, isWaitMode, isRetTok, Id.run_pure, Id.run_bind,
      apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd, apply_ite BankCell.tok,
      apply_ite BankCell.role, apply_ite BankCell.mode, ite_self] <;>
    (repeat' split) <;> simp_all

/-- M6-S cells: a PACK-zero IWAIT source on a first-digit edge does not end in CWAIT.
Consumer: bankWindowJointSourceRootWaitNotCwait. -/
theorem bankWindowJointSourceRootIwaitAlignedNotCwait {c : Compiled} (x y : Agent c)
    (hx : x.pack.val = 0) (hm : x.mode = .IWAIT) (hy1 : y.pack.val = 1) :
    (Counter.resetBankOld x y).1.mode ≠ .CWAIT := by
  have hb : 0 < c.b := by
    change 0 < c.s + 11
    omega
  have hbz : c.b ≠ 0 := by omega
  have hwide : c.b ≠ 1 := by
    change c.s + 11 ≠ 1
    omega
  have hp : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  cases hg : x.grant <;> cases ht : y.tok <;>
    by_cases hl : 1 < x.lease.val <;>
    simp [Counter.resetBankOld, bankPair, bankCell, hx, hy1, hp, hb, hbz, hwide,
      hg, hm, ht, hl, isWaitMode, isRetTok, Id.run_pure, Id.run_bind]

/-- M6-S cells: a PACK-zero IWAIT source whose responder changes PACK does not end in CWAIT.
Consumer: bankWindowJointSourceRootWaitNotCwait. -/
theorem bankWindowJointSourceRootIwaitChangedNotCwait {c : Compiled} (x y : Agent c)
    (hx : x.pack.val = 0) (hm : x.mode = .IWAIT) (hy1 : y.pack.val ≠ 1) :
    (Counter.resetBankOld x y).1.mode ≠ .CWAIT := by
  have hb : 0 < c.b := by
    change 0 < c.s + 11
    omega
  have hbz : c.b ≠ 0 := by omega
  have hwide : c.b ≠ 1 := by
    change c.s + 11 ≠ 1
    omega
  have hp : packNext 0 y.pack.val c.b = 1 := by
    simp [packNext, hb]
  cases hg : x.grant <;> cases ht : y.tok <;>
    by_cases hl : 1 < x.lease.val <;>
    simp [Counter.resetBankOld, bankPair, bankCell, hx, hp, hb, hbz, hwide,
      hy1, hg, hm, ht, hl, isWaitMode, isRetTok, Id.run_pure, Id.run_bind,
      apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd, apply_ite BankCell.tok,
      apply_ite BankCell.role, apply_ite BankCell.mode, ite_self] <;>
    (repeat' split) <;> simp_all

/-- M6-S cells, source root: an RWAIT or IWAIT source at PACK zero never
leaves the BANK pair in CWAIT (only the CSTART issue row enters CWAIT).
Consumer: bankWindowJointCwaitWaitingStepBack. -/
theorem bankWindowJointSourceRootWaitNotCwait {c : Compiled} (x y : Agent c)
    (hx : x.pack.val = 0) (hm : x.mode = .RWAIT ∨ x.mode = .IWAIT) :
    (Counter.resetBankOld x y).1.mode ≠ .CWAIT := by
  by_cases hy1 : y.pack.val = 1
  · rcases hm with hm | hm
    · exact bankWindowJointSourceRootRwaitAlignedNotCwait x y hx hm hy1
    · exact bankWindowJointSourceRootIwaitAlignedNotCwait x y hx hm hy1
  · rcases hm with hm | hm
    · exact bankWindowJointSourceRootRwaitChangedNotCwait x y hx hm hy1
    · exact bankWindowJointSourceRootIwaitChangedNotCwait x y hx hm hy1

/-- M6-S cells, responder ghost: if the responder PACK changes, its
controller is erased.
Consumer: bankWindowJointCwaitWaitingStepBack. -/
theorem bankWindowJointResponderChangedControllerEmpty {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hchanged : packNext x.pack.val y.pack.val c.b ≠ y.pack.val) :
    (renewalBankPairMemory c m e dest x y).2.controller = .empty := by
  have hb : 0 < c.b := by
    change 0 < c.s + 11
    omega
  by_cases hx : x.pack.val = 0
  · have hp : packNext 0 y.pack.val c.b = 1 := by
      simp [packNext, hb]
    have hpost : packNext x.pack.val y.pack.val c.b = 1 := by
      rw [hx]
      exact hp
    have hneq : y.pack.val ≠ 1 := by
      intro he
      exact hchanged (hpost.trans he.symm)
    cases hg : x.grant <;> cases hm : x.mode <;>
      by_cases hl : 1 < x.lease.val <;>
      simp [renewalBankPairMemory, bankCell, hx,
        hp, hpost, hneq, Ne.symm hneq, hg, hm, hl,
        renewalBankWaitSlot, isWaitMode] <;>
        (repeat' split) <;> rfl
  · cases ht : x.tok <;>
      simp [renewalBankPairMemory, bankCell,
        hchanged, hx, ht] <;>
        (repeat' split) <;> rfl

/-- M6-S cells, responder ghost at PACK zero behind a nonroot source:
the responder controller is erased or passes through the wait slot.
Consumer: bankWindowJointCwaitWaitingStepBack. -/
theorem bankWindowJointResponderZeroControllerSlot {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hx0 : x.pack.val ≠ 0) (hy : y.pack.val = 0)
    (hpost : packNext x.pack.val y.pack.val c.b = 0) :
    (renewalBankPairMemory c m e dest x y).2.controller = .empty ∨
    (renewalBankPairMemory c m e dest x y).2.controller =
      renewalBankWaitSlot y.mode y.lease.val (m.sites dest).controller := by
  rw [renewalBankPairMemory_nonroot c m e dest x y hx0]
  unfold bankMemoryCtlY
  (repeat' split) <;> simp [bankCell]

/-- M6-S cells, source root ghost: a PACK-zero source whose controller
after the step is a nonempty waiting list kept its old controller (the
root-row classification writes only empty, active, waiting [] or the
wait slot).
Consumer: bankWindowJointCwaitWaitingStepBack. -/
theorem bankWindowJointSourceRootWaitingKept {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (hx : x.pack.val = 0)
    (atoms : List (RenewalBankAtom n)) (hne : atoms ≠ [])
    (h : (renewalBankPairMemory c m e dest x y).1.controller = .waiting atoms) :
    (m.sites e).controller = .waiting atoms := by
  rcases rbRootRowClassification c m e dest x y hx with
    hpass | hlaunch | hreturn | haccept | hset | hissue | hcompare
  · rcases hpass with ⟨controller, worker, hp, hc, _⟩
    rw [hp] at h
    change controller = .waiting atoms at h
    rcases hc with hc | hc
    · rw [hc] at h
      cases h
    · rw [hc] at h
      unfold renewalBankWaitSlot at h
      split at h
      · split at h
        · exact h
        · cases h
      · exact h
  · rw [hlaunch] at h
    change RenewalBankController.waiting [] = .waiting atoms at h
    injection h with h
    exact absurd h.symm hne
  · rw [hreturn] at h
    cases h
  · rcases haccept with ⟨rho, _, _, hp⟩
    rw [hp] at h
    cases h
  · rw [hset] at h
    cases h
  · rw [hissue] at h
    change RenewalBankController.waiting [] = .waiting atoms at h
    injection h with h
    exact absurd h.symm hne
  · rw [hcompare] at h
    change RenewalBankController.waiting [] = .waiting atoms at h
    injection h with h
    exact absurd h.symm hne

/-- M6-S reference step: a POST root z in physical mode CWAIT whose
controller is a nonempty waiting list had the same mode and the same
controller before the step (write-site census in R11-step-missing.md).
Consumer: bankWindowJointCwaitWaitingNoBirth. -/
theorem bankWindowJointCwaitWaitingStepBack {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e z : Fin n)
    (atoms : List (RenewalBankAtom n))
    (hframe : BankInFlightAligned ring r)
    (hframeN : BankInFlightAligned ring (renewalBankNext ring r e))
    (hm : ((renewalBankNext ring r e).1 z).mode = .CWAIT)
    (hc : ((renewalBankNext ring r e).2.sites z).controller = .waiting atoms)
    (hne : atoms ≠ []) :
    (r.1 z).mode = .CWAIT ∧ (r.2.sites z).controller = .waiting atoms := by
  have hf := rbReferenceSelectedPairFrame ring (by omega : 2 ≤ n) r e
  have ht := bankWindowClosureSelectedBankTrip ring hn hbank r e
  simp only [Counter.resetAgentBankTrip, Counter.resetCellBankTrip,
    Prod.mk.injEq] at ht
  have hdiff : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) e
  have hshapeN := bankWindowJointWaitingControllerShape ring _ z atoms
    hframeN hc
  by_cases hze : z = e
  · rw [hze] at hm hc hshapeN ⊢
    have hpOld : (r.1 e).pack.val = 0 := by
      rw [← bankWindowClosureRepairNonresponderPackFixed ring
        (by omega : 2 ≤ n) r e e (Ne.symm hdiff)]
      exact hshapeN.1
    have hcOld : (r.2.sites e).controller = .waiting atoms := by
      have h := congrArg (fun s : RenewalBankSite n => s.controller) hf.2.2.1
      exact bankWindowJointSourceRootWaitingKept _ r.2 e
        (ring.rightNeighbor e) _ _ hpOld atoms hne (h.symm.trans hc)
    refine ⟨?_, hcOld⟩
    rcases (bankWindowJointWaitingControllerShape ring r e atoms hframe
      hcOld).2 with h | h | h
    · exact absurd (ht.1.1.symm.trans hm)
        (bankWindowJointSourceRootWaitNotCwait _ _ hpOld (Or.inl h))
    · exact absurd (ht.1.1.symm.trans hm)
        (bankWindowJointSourceRootWaitNotCwait _ _ hpOld (Or.inr h))
    · exact h
  · by_cases hzd : z = ring.rightNeighbor e
    · rw [hzd] at hm hc hshapeN ⊢
      have hresp := bankWindowExactResponderPack ring r e hdiff
      have hcPair : (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
          r.2 e (ring.rightNeighbor e) (r.1 e)
          (r.1 (ring.rightNeighbor e))).2.controller = .waiting atoms := by
        have h := congrArg (fun s : RenewalBankSite n => s.controller)
          hf.2.2.2
        exact h.symm.trans hc
      have hstab : packNext (r.1 e).pack.val
          (r.1 (ring.rightNeighbor e)).pack.val
          (compileAdvice (ceilLogTwo n)).b =
          (r.1 (ring.rightNeighbor e)).pack.val := by
        apply Classical.byContradiction
        intro hch
        rw [bankWindowJointResponderChangedControllerEmpty _ r.2 e
          (ring.rightNeighbor e) _ _ hch] at hcPair
        cases hcPair
      have hy0 : (r.1 (ring.rightNeighbor e)).pack.val = 0 := by
        rw [← hstab, ← hresp]
        exact hshapeN.1
      have hx0 := bankWindowOverlapIncomingSourceNonzero ring hn r e hy0
        hshapeN.1
      have hpost : packNext (r.1 e).pack.val
          (r.1 (ring.rightNeighbor e)).pack.val
          (compileAdvice (ceilLogTwo n)).b = 0 := by
        rw [hstab]
        exact hy0
      have hcOld : (r.2.sites (ring.rightNeighbor e)).controller =
          .waiting atoms := by
        rcases bankWindowJointResponderZeroControllerSlot _ r.2 e
            (ring.rightNeighbor e) _ _ hx0 hy0 hpost with h | h
        · rw [h] at hcPair
          cases hcPair
        · rw [h] at hcPair
          unfold renewalBankWaitSlot at hcPair
          split at hcPair
          · split at hcPair
            · exact hcPair
            · cases hcPair
          · exact hcPair
      refine ⟨?_, hcOld⟩
      rcases bankWindowJointIncomingModeKeepOrReset ring hn hbank r e hy0
          hshapeN.1 with h | h
      · exact h.symm.trans hm
      · rw [h] at hm
        cases hm
    · have hfo := bankWindowExactOffPairFrame ring r e z hze hzd
      rw [hfo.1] at hm
      rw [hfo.2] at hc
      exact ⟨hm, hc⟩

/-- The reset-return row fires only from a source in RWAIT. -/
private theorem bankWindowJointResetReturnMode (x y : BankCell) (p b : Nat)
    (h : Counter.resetRootRow x y p b = .resetReturn) : x.mode = .RWAIT := by
  by_cases hm : x.mode = .RWAIT
  · exact hm
  · exfalso
    revert h
    simp [Counter.resetRootRow, hm, apply_ite (fun r : Counter.ResetRootRow => r = .resetReturn)]

/-- A BANK birth at e is rooted at e and needs e in RWAIT (the reset
return row Counter.resetRootRow = .resetReturn only fires from RWAIT).
Consumer: bankWindowJointCwaitWaitingNoBirth. -/
theorem bankWindowJointBirthRootRwait {n : Nat} (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (m : RenewalBankMemory n) (e : Fin n)
    (o : RenewalBankOrigin n)
    (h : renewalBankBirth ring C m e = some o) :
    o.root = e ∧ (C e).mode = .RWAIT := by
  unfold renewalBankBirth at h
  split at h
  · rename_i hrow
    constructor
    · split at h
      · cases h
        rfl
      · cases h
    · simpa [bankCell] using bankWindowJointResetReturnMode _ _ _ _ hrow
  · cases h

/-- M6-S run invariant: along the actual BANK run, a root in CWAIT with
a nonempty waiting list is the root of no born origin. Induction on the
word: by bankWindowJointCwaitWaitingStepBack the state held one step
earlier, and a birth at the root needs that root in RWAIT
(bankWindowJointBirthRootRwait).
Consumer: bankWindowJointCwaitWaitingNoOrigin. -/
theorem bankWindowJointCwaitWaitingNoBirth {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) :
    ∀ (pre : List (Fin n)) (z : Fin n) (atoms : List (RenewalBankAtom n)),
      ((rbRun ring (renewalBankStart ring seed) pre).1 z).mode = .CWAIT →
      ((rbRun ring (renewalBankStart ring seed) pre).2.sites z).controller =
        .waiting atoms →
      atoms ≠ [] →
      ∀ o ∈ rbBirths ring (renewalBankStart ring seed) pre, o.root ≠ z := by
  have key : ∀ (l : List (Fin n)) (z : Fin n)
      (atoms : List (RenewalBankAtom n)),
      ((rbRun ring (renewalBankStart ring seed) l.reverse).1 z).mode =
        .CWAIT →
      ((rbRun ring (renewalBankStart ring seed) l.reverse).2.sites
        z).controller = .waiting atoms →
      atoms ≠ [] →
      ∀ o ∈ rbBirths ring (renewalBankStart ring seed) l.reverse,
        o.root ≠ z := by
    intro l
    induction l with
    | nil =>
        intro z atoms _ _ _ o ho
        simp [rbBirths] at ho
    | cons e l ih =>
        intro z atoms hm hc hne o ho
        rw [List.reverse_cons] at hm hc ho
        have hstep : rbRun ring (renewalBankStart ring seed)
            (l.reverse ++ [e]) =
            renewalBankNext ring
              (rbRun ring (renewalBankStart ring seed) l.reverse) e := by
          rw [rbRunAppend]
          rfl
        rw [hstep] at hm hc
        have hframeN : BankInFlightAligned ring (renewalBankNext ring
            (rbRun ring (renewalBankStart ring seed) l.reverse) e) := by
          rw [← hstep]
          exact bankInFlightAlignedWord ring hn seed hbank (l.reverse ++ [e])
        obtain ⟨hmO, hcO⟩ := bankWindowJointCwaitWaitingStepBack ring hn hbank
          _ e z atoms (bankInFlightAlignedWord ring hn seed hbank l.reverse)
          hframeN hm hc hne
        rw [rbBirthsSnoc] at ho
        rcases List.mem_append.mp ho with h | h
        · exact ih z atoms hmO hcO hne o h
        · intro hroot
          cases hb : renewalBankBirth ring
              (rbRun ring (renewalBankStart ring seed) l.reverse).1
              (rbRun ring (renewalBankStart ring seed) l.reverse).2 e with
          | none =>
              rw [hb] at h
              simp at h
          | some o' =>
              rw [hb] at h
              simp at h
              have hB := bankWindowJointBirthRootRwait ring _ _ e o' hb
              rw [h, hB.1] at hroot
              rw [← hroot, hB.2] at hmO
              cases hmO
  intro pre
  have h := key pre.reverse
  rw [List.reverse_reverse] at h
  exact h

/-- M6-S: in the actual run, no genuine payload (worker with an origin)
has its origin rooted at a root in CWAIT with a nonempty waiting list.
ReceiptInv.payload provenance puts every origin in rbBirths, and
bankWindowJointCwaitWaitingNoBirth excludes that root.
Consumer: bankWindowOverlapStableCwaitWaitingRootFieldsAt. -/
theorem bankWindowJointCwaitWaitingNoOrigin {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n)) (z : Fin n)
    (atoms : List (RenewalBankAtom n))
    (hm : ((rbRun ring (renewalBankStart ring seed) pre).1 z).mode = .CWAIT)
    (hc : ((rbRun ring (renewalBankStart ring seed) pre).2.sites
      z).controller = .waiting atoms)
    (hne : atoms ≠ [])
    (i : Fin n) (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hw : ((rbRun ring (renewalBankStart ring seed) pre).2.sites i).worker =
      .payload p)
    (horig : p.origin = some o) :
    o.root ≠ z := by
  have hR := rbReceiptInvBankWordOfInv ring (by omega : 2 ≤ n) seed hbank pre
  have hlive : p ∈ rbLivePayloads
      (rbRun ring (renewalBankStart ring seed) pre).2 := by
    unfold rbLivePayloads
    refine List.mem_flatMap.mpr ⟨i, List.mem_finRange i, ?_⟩
    unfold rbSiteLivePayloads
    rw [hw]
    simp
  have hprov := (hR.payload p hlive).2 o horig
  exact bankWindowJointCwaitWaitingNoBirth ring hn hbank seed pre z atoms
    hm hc hne o hprov.1

/-- M6-S: a foreign root out of POST scope in CWAIT with a nonempty
waiting list, on a stable edge from a nonroot source, satisfies every
root-indexed POST clause. phaseExcludes/phaseComplete come from
bankWindowOverlapStableNonrootPhaseFields; phaseUnique and phaseFlags
are vacuous because no genuine payload is rooted there
(bankWindowJointCwaitWaitingNoOrigin); compareExact needs waiting [];
every scope-guarded clause is vacuous; proto and orphan come from
bankWindowOverlapRootJointFields.
Consumer: the final bankWindowExactStep case split, stable nonroot edge,
out-of-scope CWAIT roots (ledger row M6-S). -/
theorem bankWindowOverlapStableCwaitWaitingRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hnonroot : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ≠ 0)
    (hstable :
      packNext ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val)
    (hforeign : root ≠ e ∧ root ≠ ring.rightNeighbor e)
    (hnscope : ¬ BankWindowScope ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) root)
    (hmodeOld : ((rbRun ring (renewalBankStart ring seed) pre).1 root).mode = .CWAIT)
    (atoms : List (RenewalBankAtom n))
    (hctrlOld : ((rbRun ring (renewalBankStart ring seed) pre).2.sites root).controller = .waiting atoms)
    (hne : atoms ≠ []) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) root := by
  have hphase := bankWindowOverlapStableNonrootPhaseFields ring hn hbank
    seed pre e root hJ hnonroot hstable hforeign
  have hjoint := bankWindowOverlapRootJointFields ring hn hbank seed pre e hJ
  have hfr := bankWindowExactOffPairFrame ring (rbRun ring (renewalBankStart ring seed) pre) e root
    hforeign.1 hforeign.2
  have hmN : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 root).mode = .CWAIT := by
    rw [hfr.1]
    exact hmodeOld
  have hcN : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites root).controller = .waiting atoms := by
    rw [hfr.2]
    exact hctrlOld
  have hphys : rbRun ring (renewalBankStart ring seed) (pre ++ [e]) = (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) := by
    rw [rbRunAppend]
    rfl
  have hno : ∀ (i : Fin n) (p : RenewalBankPayload n)
      (o : RenewalBankOrigin n), ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites i).worker = .payload p →
      p.origin = some o → o.root ≠ root := by
    intro i p o hw horig
    exact bankWindowJointCwaitWaitingNoOrigin ring hn hbank seed (pre ++ [e])
      root atoms (by rw [hphys]; exact hmN) (by rw [hphys]; exact hcN) hne
      i p o (by rw [hphys]; exact hw) horig
  refine ⟨hphase.1, hphase.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o i p ho hw _
    exact (hno i p o hw.1 hw.2.1 ho).elim
  · intro o i p ho hw _
    exact (hno i p o hw.1 hw.2.1 ho).elim
  · intro hs
    exact (hnscope hs).elim
  · intro hs
    exact (hnscope hs).elim
  · intro _ _ hs
    exact (hnscope hs).elim
  · intro _ _ _ hs
    exact (hnscope hs).elim
  · intro o i p ho hw horig _ _
    exact (hno i p o hw horig ho).elim
  · intro hs
    exact (hnscope hs).elim
  · intro hs
    exact (hnscope hs).elim
  · intro limit hrun
    exact hjoint.2.2.2.1 root limit hforeign hrun
  · intro j
    exact hjoint.2.2.2.2 root j hforeign

/-- The resetWait front of a root at digit D(j+1): a pending receipt
worker carrying RR or RL there, a zero bit prefix through D(j+1), empty
tokens before it, and, for RL, the only window token and an all-zero
window. This is the body of the resetWait clause of BankWindowExact.
Consumer: bankWindowOverlapStableRwaitAssembly and the M6-Q RWAIT rows. -/
def bankWindowJointResetFront {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (rho : RenewalBankReceipt n) : Prop :=
  (r.2.sites (Counter.site ring root (j.val + 1))).worker = .pending rho ∧
  ((r.1 (Counter.site ring root (j.val + 1))).tok = .RR ∨
   (r.1 (Counter.site ring root (j.val + 1))).tok = .RL) ∧
  bankWindowZeroPrefix ring r root (j.val + 1) ∧
  (∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
    k.val < j.val →
    (r.1 (Counter.site ring root (k.val + 1))).tok = .E) ∧
  ((r.1 (Counter.site ring root (j.val + 1))).tok = .RL →
    bankWindowOnlyToken ring r root (Counter.site ring root (j.val + 1)) ∧
    bankWindowZeroPrefix ring r root (compileAdvice (ceilLogTwo n)).b)

/-- M6-Q RWAIT, assembly: a foreign root in RWAIT with controller
waiting [] on a stable nonroot edge, given a POST resetWait front,
satisfies every root-indexed POST clause; all comparator, ARMED/CSTART
and IWAIT clauses are vacuous by the framed mode.
Consumer: bankWindowOverlapStableRwaitRootFieldsAt. -/
theorem bankWindowOverlapStableRwaitAssembly {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hnonroot : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ≠ 0)
    (hstable :
      packNext ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val)
    (hforeign : root ≠ e ∧ root ≠ ring.rightNeighbor e)
    (hmodeOld : ((rbRun ring (renewalBankStart ring seed) pre).1 root).mode = .RWAIT)
    (hctrlOld : ((rbRun ring (renewalBankStart ring seed) pre).2.sites root).controller = .waiting [])
    (hfront : ∃ (j : Fin (compileAdvice (ceilLogTwo n)).b)
      (rho : RenewalBankReceipt n), bankWindowJointResetFront ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) root j rho) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) root := by
  have hphase := bankWindowOverlapStableNonrootPhaseFields ring hn hbank
    seed pre e root hJ hnonroot hstable hforeign
  have hjoint := bankWindowOverlapRootJointFields ring hn hbank seed pre e hJ
  have hfr := bankWindowExactOffPairFrame ring (rbRun ring (renewalBankStart ring seed) pre) e root
    hforeign.1 hforeign.2
  have hmN : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 root).mode = .RWAIT := by
    rw [hfr.1]
    exact hmodeOld
  have hcN : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites root).controller = .waiting [] := by
    rw [hfr.2]
    exact hctrlOld
  refine ⟨hphase.1, hphase.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o _ _ ho _ hm
    rw [ho, hmN] at hm
    cases hm
  · intro o _ _ ho _ hm
    rw [ho, hmN] at hm
    cases hm
  · intro _ hinh _ _
    rcases hinh with ⟨atoms, hc, hne⟩ | ⟨_, hc, _⟩
    · rw [hcN] at hc
      injection hc with h
      exact hne h.symm
    · rw [hcN] at hc
      cases hc
  · intro _ _ _
    obtain ⟨j, rho, h⟩ := hfront
    exact ⟨j, rho, h⟩
  · intro _ _ _ hm
    rw [hmN] at hm
    rcases hm with h | h <;> cases h
  · intro _ _ _ _ hm
    rw [hmN] at hm
    cases hm
  · intro o _ _ ho _ _ hm
    rw [ho, hmN] at hm
    cases hm
  · intro _ hm
    rw [hmN] at hm
    cases hm
  · intro _ hm
    rw [hmN] at hm
    cases hm
  · intro limit hrun
    exact hjoint.2.2.2.1 root limit hforeign hrun
  · intro j
    exact hjoint.2.2.2.2 root j hforeign

/-- M6-Q quiet RWAIT/IWAIT rows, cell level: on an aligned stable edge an
RL or AL source facing an empty responder, or an empty source facing a
non-top RR or IR responder, leaves tokens, bits and workers unchanged.
Consumer: bankWindowOverlapStableCellsUnchangedReads in the M6-Q rows. -/
theorem bankWindowJointAlignedQuietWaitCells {n : Nat} {c : Compiled}
    (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (k : Nat)
    (hk : 1 ≤ k) (hbelow : k < c.b)
    (hx : x.pack.val = k) (hy : y.pack.val = k + 1)
    (hq : ((x.tok = .RL ∨ x.tok = .AL) ∧ y.tok = .E) ∨
      (x.tok = .E ∧ (y.tok = .RR ∨ y.tok = .IR) ∧ k + 1 ≠ c.b)) :
    (Counter.resetBankOld x y).1.tok = x.tok ∧
    (Counter.resetBankOld x y).1.bit = x.bit ∧
    (Counter.resetBankOld x y).2.tok = y.tok ∧
    (Counter.resetBankOld x y).2.bit = y.bit ∧
    (renewalBankPairMemory c m e dest x y).1.worker = (m.sites e).worker ∧
    (renewalBankPairMemory c m e dest x y).2.worker =
      (m.sites dest).worker := by
  have hle : k ≤ c.b := by omega
  have hnz : k ≠ 0 := by omega
  have hbz : c.b ≠ 0 := by omega
  have hne : k ≠ c.b := by omega
  have hnextPos : 1 ≤ k + 1 := by omega
  have hnextNz : k + 1 ≠ 0 := by omega
  have hnl : ¬ c.b < k + 1 := by omega
  have hrole : packNext k (k + 1) c.b = k + 1 := by
    simp [packNext, hbelow]
  rcases hq with ⟨hxt, hyt⟩ | ⟨hxt, hyt, htop⟩
  · by_cases htop : k + 1 = c.b
    · have hpTop : packNext k c.b c.b = c.b := by
        have h := hrole
        rw [htop] at h
        exact h
      rcases hxt with hxt | hxt <;>
        simp [Counter.resetBankOld, renewalBankPairMemory, bankPair, bankCell,
          hx, hy, hk, hbelow, hle, hnz, hbz, hne, hnextPos, hnextNz, hnl,
          hrole, hpTop, htop, hxt, hyt, Id.run_pure, Id.run_bind]
    · rcases hxt with hxt | hxt <;>
        simp [Counter.resetBankOld, renewalBankPairMemory, bankPair, bankCell,
          hx, hy, hk, hbelow, hle, hnz, hbz, hne, hnextPos, hnextNz, hnl,
          hrole, htop, hxt, hyt, Id.run_pure, Id.run_bind]
  · rcases hyt with hyt | hyt <;>
      simp [Counter.resetBankOld, renewalBankPairMemory, bankPair, bankCell,
        hx, hy, hk, hbelow, hle, hnz, hbz, hne, hnextPos, hnextNz, hnl,
        hrole, htop, hxt, hyt, Id.run_pure, Id.run_bind]

/-- Reference-level reads from unchanged cells: if the selected pair's
token, bit and worker outputs equal the old ones at both endpoints, the
two pair sites keep their token, bit and worker reads.
Consumer: bankWindowOverlapStableFrozenPairRootFieldsAt in the M6-Q
RWAIT/IWAIT quiet rows. -/
theorem bankWindowOverlapStableCellsUnchangedReads {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hcells :
      (Counter.resetBankOld (r.1 e) (r.1 (ring.rightNeighbor e))).1.tok =
        (r.1 e).tok ∧
      (Counter.resetBankOld (r.1 e) (r.1 (ring.rightNeighbor e))).1.bit =
        (r.1 e).bit ∧
      (Counter.resetBankOld (r.1 e) (r.1 (ring.rightNeighbor e))).2.tok =
        (r.1 (ring.rightNeighbor e)).tok ∧
      (Counter.resetBankOld (r.1 e) (r.1 (ring.rightNeighbor e))).2.bit =
        (r.1 (ring.rightNeighbor e)).bit ∧
      (renewalBankPairMemory (compileAdvice (ceilLogTwo n)) r.2 e
        (ring.rightNeighbor e) (r.1 e) (r.1 (ring.rightNeighbor e))).1.worker =
        (r.2.sites e).worker ∧
      (renewalBankPairMemory (compileAdvice (ceilLogTwo n)) r.2 e
        (ring.rightNeighbor e) (r.1 e) (r.1 (ring.rightNeighbor e))).2.worker =
        (r.2.sites (ring.rightNeighbor e)).worker) :
    ∀ z : Fin n, (z = e ∨ z = ring.rightNeighbor e) →
      bankWindowReadTok r (renewalBankNext ring r e) z ∧
      bankWindowReadBit r (renewalBankNext ring r e) z ∧
      bankWindowReadWorker r (renewalBankNext ring r e) z := by
  have htrip := bankWindowClosureSelectedBankTrip ring hn hbank r e
  simp only [Counter.resetAgentBankTrip, Counter.resetCellBankTrip,
    Prod.mk.injEq] at htrip
  have hf := rbReferenceSelectedPairFrame ring (by omega : 2 ≤ n) r e
  have hwS := congrArg (fun s : RenewalBankSite n => s.worker) hf.2.2.1
  have hwD := congrArg (fun s : RenewalBankSite n => s.worker) hf.2.2.2
  intro z hz
  unfold bankWindowReadTok bankWindowReadBit bankWindowReadWorker
  rcases hz with hz | hz <;> rw [hz]
  · exact ⟨htrip.1.2.2.trans hcells.1, htrip.1.2.1.trans hcells.2.1,
      hwS.trans hcells.2.2.2.2.1⟩
  · exact ⟨htrip.2.2.2.trans hcells.2.2.1, htrip.2.2.1.trans hcells.2.2.2.1,
      hwD.trans hcells.2.2.2.2.2⟩

/-- M6-Q RWAIT, D0 RR forward, cell level: an RR source on an aligned
stable edge sends RR to the responder with bit zero, empties its own
token, keeps its bit, and the responder takes the source worker.
Consumer: bankWindowOverlapStableRwaitRootFieldsAt. -/
theorem bankWindowJointAlignedRrForwardCells {n : Nat} {c : Compiled}
    (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (k : Nat)
    (hk : 1 ≤ k) (hbelow : k < c.b)
    (hx : x.pack.val = k) (hy : y.pack.val = k + 1)
    (hrr : x.tok = .RR) :
    (Counter.resetBankOld x y).1.tok = .E ∧
    (Counter.resetBankOld x y).1.bit = x.bit ∧
    (Counter.resetBankOld x y).2.tok = .RR ∧
    (Counter.resetBankOld x y).2.bit = false ∧
    (renewalBankPairMemory c m e dest x y).2.worker = (m.sites e).worker := by
  have hle : k ≤ c.b := by omega
  have hnz : k ≠ 0 := by omega
  have hbz : c.b ≠ 0 := by omega
  have hne : k ≠ c.b := by omega
  have hnextPos : 1 ≤ k + 1 := by omega
  have hnextNz : k + 1 ≠ 0 := by omega
  have hnl : ¬ c.b < k + 1 := by omega
  have hrole : packNext k (k + 1) c.b = k + 1 := by
    simp [packNext, hbelow]
  by_cases htop : k + 1 = c.b
  · have hpTop : packNext k c.b c.b = c.b := by
      have h := hrole
      rw [htop] at h
      exact h
    cases hyt : y.tok <;>
      simp [Counter.resetBankOld, renewalBankPairMemory, bankPair, bankCell,
        hx, hy, hk, hbelow, hle, hnz, hbz, hne, hnextPos, hnextNz, hnl,
        hrole, hpTop, htop, hrr, hyt, Id.run_pure, Id.run_bind]
  · cases hyt : y.tok <;>
      simp [Counter.resetBankOld, renewalBankPairMemory, bankPair, bankCell,
        hx, hy, hk, hbelow, hle, hnz, hbz, hne, hnextPos, hnextNz, hnl,
        hrole, htop, hrr, hyt, Id.run_pure, Id.run_bind]

/-- M6-Q RWAIT, D1 top RR turn and D2 RL retreat, cell level: an empty
source facing RL, or facing RR at the top digit, receives RL with bit
zero, the responder token is erased with its bit kept, and the source
takes the responder worker.
Consumer: bankWindowOverlapStableRwaitRootFieldsAt. -/
theorem bankWindowJointAlignedRlBackCells {n : Nat} {c : Compiled}
    (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (k : Nat)
    (hk : 1 ≤ k) (hbelow : k < c.b)
    (hx : x.pack.val = k) (hy : y.pack.val = k + 1)
    (hxe : x.tok = .E)
    (hq : y.tok = .RL ∨ (y.tok = .RR ∧ k + 1 = c.b)) :
    (Counter.resetBankOld x y).1.tok = .RL ∧
    (Counter.resetBankOld x y).1.bit = false ∧
    (Counter.resetBankOld x y).2.tok = .E ∧
    (Counter.resetBankOld x y).2.bit = y.bit ∧
    (renewalBankPairMemory c m e dest x y).1.worker = (m.sites dest).worker := by
  have hle : k ≤ c.b := by omega
  have hnz : k ≠ 0 := by omega
  have hbz : c.b ≠ 0 := by omega
  have hne : k ≠ c.b := by omega
  have hnextPos : 1 ≤ k + 1 := by omega
  have hnextNz : k + 1 ≠ 0 := by omega
  have hnl : ¬ c.b < k + 1 := by omega
  have hrole : packNext k (k + 1) c.b = k + 1 := by
    simp [packNext, hbelow]
  by_cases htop : k + 1 = c.b
  · have hpTop : packNext k c.b c.b = c.b := by
      have h := hrole
      rw [htop] at h
      exact h
    rcases hq with hyt | ⟨hyt, _⟩ <;>
      simp [Counter.resetBankOld, renewalBankPairMemory, bankPair, bankCell,
        hx, hy, hk, hbelow, hle, hnz, hbz, hne, hnextPos, hnextNz, hnl,
        hrole, hpTop, htop, hxe, hyt, Id.run_pure, Id.run_bind]
  · rcases hq with hyt | ⟨_, h⟩
    · simp [Counter.resetBankOld, renewalBankPairMemory, bankPair, bankCell,
        hx, hy, hk, hbelow, hle, hnz, hbz, hne, hnextPos, hnextNz, hnl,
        hrole, htop, hxe, hyt, Id.run_pure, Id.run_bind]
    · exact absurd h htop

/-- M6-Q RWAIT: a foreign root in RWAIT with controller waiting [] on a
stable nonroot edge from its interior digit D(k), 1 <= k < b, satisfies
every root-indexed POST clause. Out of POST scope this is
bankWindowOverlapStableNonrootOutOfScopeRootFieldsAt. In scope the old
resetWait front D(j+1) is compared with the pair (D(k), D(k+1)): front
before the pair (RR: the front reads are framed; RL: OnlyToken makes the
pair idle), front at e (RR forward D0; RL quiet), front at e+ (RL retreat
D2; RR top turn D1; non-top RR quiet), front after the pair (idle pair).
Digits are told apart by their complete old PACK values.
Consumer: the final bankWindowExactStep case split, stable interior edge,
RWAIT foreign roots (ledger row M6-Q, RWAIT part). -/
theorem bankWindowOverlapStableRwaitRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hnonroot : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ≠ 0)
    (hstable :
      packNext ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val)
    (hforeign : root ≠ e ∧ root ≠ ring.rightNeighbor e)
    (k : Nat) (hk1 : 1 ≤ k) (hkb : k < (compileAdvice (ceilLogTwo n)).b)
    (hsite : e = Counter.site ring root k)
    (hmodeOld : ((rbRun ring (renewalBankStart ring seed) pre).1 root).mode = .RWAIT)
    (hctrlOld : ((rbRun ring (renewalBankStart ring seed) pre).2.sites root).controller = .waiting []) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) root := by
  by_cases hs : BankWindowScope ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) root
  case neg =>
    exact bankWindowOverlapStableNonrootOutOfScopeRootFieldsAt ring hn hbank
      seed pre e root hJ hnonroot hstable hforeign hs
      (by rw [hmodeOld]; intro h; cases h)
  have hpackAll := bankWindowOverlapStablePackFrame ring hn seed pre e hstable
  have hroot := bankWindowExactOffPairAtomicReads ring (rbRun ring (renewalBankStart ring seed) pre) e root
    hforeign.1 hforeign.2
  have hgrantR := hroot.2.2.2.2.1
  unfold bankWindowReadGrant at hgrantR
  have hscopeOld : BankWindowScope ring (rbRun ring (renewalBankStart ring seed) pre) root := by
    refine ⟨fun jj hjj => ?_, ?_⟩
    · rw [← hpackAll]
      exact hs.1 jj hjj
    · rw [← hgrantR]
      exact hs.2
  have hcomp := hscopeOld.1
  obtain ⟨j, rho, hw, htok, hzero, hbefore, hrl⟩ :=
    hJ.resetWait root hscopeOld hmodeOld hctrlOld
  have hx : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val = k := by
    rw [hsite]
    exact hcomp k (by omega)
  have hsucc : ring.rightNeighbor e = Counter.site ring root (k + 1) := by
    rw [hsite]
    rfl
  have hy : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val = k + 1 := by
    rw [hsucc]
    exact hcomp (k + 1) (by omega)
  have hpk : ∀ a : Nat, a ≤ (compileAdvice (ceilLogTwo n)).b →
      ((rbRun ring (renewalBankStart ring seed) pre).1 (Counter.site ring root a)).pack.val = a := hcomp
  have hsiteE : ∀ a : Nat, a = k → Counter.site ring root a = e := by
    intro a ha
    rw [ha]
    exact hsite.symm
  have hsiteD : ∀ a : Nat, a = k + 1 →
      Counter.site ring root a = ring.rightNeighbor e := by
    intro a ha
    rw [ha]
    exact hsucc.symm
  let jk : Fin (compileAdvice (ceilLogTwo n)).b := ⟨k - 1, by omega⟩
  have hdk : Counter.site ring root (jk.val + 1) = e := by
    change Counter.site ring root (k - 1 + 1) = e
    rw [show k - 1 + 1 = k by omega]
    exact hsite.symm
  let jk' : Fin (compileAdvice (ceilLogTwo n)).b := ⟨k, hkb⟩
  have hdk' : Counter.site ring root (jk'.val + 1) = ring.rightNeighbor e :=
    hsucc.symm
  have hoff : ∀ a : Nat, a ≤ (compileAdvice (ceilLogTwo n)).b → a ≠ k →
      a ≠ k + 1 →
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 (Counter.site ring root a) = (rbRun ring (renewalBankStart ring seed) pre).1 (Counter.site ring root a) ∧
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites (Counter.site ring root a) =
        (rbRun ring (renewalBankStart ring seed) pre).2.sites (Counter.site ring root a) := by
    intro a ha h1 h2
    have hp := hpk a ha
    apply bankWindowExactOffPairFrame
    · intro h
      rw [h, hx] at hp
      omega
    · intro h
      rw [h, hy] at hp
      omega
  have htrip := bankWindowClosureSelectedBankTrip ring hn hbank (rbRun ring (renewalBankStart ring seed) pre) e
  simp only [Counter.resetAgentBankTrip, Counter.resetCellBankTrip,
    Prod.mk.injEq] at htrip
  have hf := rbReferenceSelectedPairFrame ring (by omega : 2 ≤ n) (rbRun ring (renewalBankStart ring seed) pre) e
  have hwS := congrArg (fun s : RenewalBankSite n => s.worker) hf.2.2.1
  have hwD := congrArg (fun s : RenewalBankSite n => s.worker) hf.2.2.2
  have _hjb := j.isLt
  have hidle : ((rbRun ring (renewalBankStart ring seed) pre).1 e).tok = .E → ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .E →
      BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) root := fun hxe hye =>
    bankWindowOverlapStableIdlePairRootFieldsAt ring hn hbank seed pre e root
      hJ hnonroot hstable hxe hye hforeign
  have hfrozen : (∀ z : Fin n, (z = e ∨ z = ring.rightNeighbor e) →
      bankWindowReadTok (rbRun ring (renewalBankStart ring seed) pre) (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) z ∧ bankWindowReadBit (rbRun ring (renewalBankStart ring seed) pre) (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) z ∧
      bankWindowReadWorker (rbRun ring (renewalBankStart ring seed) pre) (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) z) → BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) root :=
    fun hpair => bankWindowOverlapStableFrozenPairRootFieldsAt ring hn hbank
      seed pre e root hJ hstable hpair hforeign
  have hasm : (∃ (j' : Fin (compileAdvice (ceilLogTwo n)).b)
      (rho' : RenewalBankReceipt n), bankWindowJointResetFront ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) root
        j' rho') → BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) root :=
    bankWindowOverlapStableRwaitAssembly ring hn hbank seed pre e root hJ
      hnonroot hstable hforeign hmodeOld hctrlOld
  have hEbefore : ∀ a : Nat, 1 ≤ a → a ≤ j.val →
      ((rbRun ring (renewalBankStart ring seed) pre).1 (Counter.site ring root a)).tok = .E := by
    intro a ha1 ha
    have h : ((rbRun ring (renewalBankStart ring seed) pre).1 (Counter.site ring root (a - 1 + 1))).tok = .E :=
      hbefore ⟨a - 1, by omega⟩ (by show a - 1 < j.val; omega)
    rw [show a - 1 + 1 = a by omega] at h
    exact h
  have hZero : ∀ a : Nat, 1 ≤ a → a ≤ j.val + 1 →
      ((rbRun ring (renewalBankStart ring seed) pre).1 (Counter.site ring root a)).bit = false := by
    intro a ha1 ha
    have h : ((rbRun ring (renewalBankStart ring seed) pre).1 (Counter.site ring root (a - 1 + 1))).bit = false :=
      hzero ⟨a - 1, by omega⟩ (by show a - 1 + 1 ≤ j.val + 1; omega)
    rw [show a - 1 + 1 = a by omega] at h
    exact h
  rcases Nat.lt_or_ge (j.val + 1) k with hlt | hge
  · -- front before the pair
    by_cases hRL : ((rbRun ring (renewalBankStart ring seed) pre).1 (Counter.site ring root (j.val + 1))).tok = .RL
    · have honly := (hrl hRL).1
      apply hidle
      · apply Classical.byContradiction
        intro h
        have h2 := honly jk (by rw [hdk]; exact h)
        rw [hdk] at h2
        have hp := hpk (j.val + 1) (by omega)
        rw [← h2, hx] at hp
        omega
      · apply Classical.byContradiction
        intro h
        have h2 := honly jk' (by rw [hdk']; exact h)
        rw [hdk'] at h2
        have hp := hpk (j.val + 1) (by omega)
        rw [← h2, hy] at hp
        omega
    · have hRR : ((rbRun ring (renewalBankStart ring seed) pre).1 (Counter.site ring root (j.val + 1))).tok = .RR := by
        rcases htok with h | h
        · exact h
        · exact absurd h hRL
      have hfr := hoff (j.val + 1) (by omega) (by omega) (by omega)
      apply hasm
      refine ⟨j, rho, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hfr.2]
        exact hw
      · rw [hfr.1]
        exact Or.inl hRR
      · intro jj hjj
        have _hjjb := jj.isLt
        change jj.val + 1 ≤ j.val + 1 at hjj
        rw [(hoff (jj.val + 1) (by omega) (by omega) (by omega)).1]
        exact hzero jj hjj
      · intro kk hkk
        have _hkkb := kk.isLt
        change kk.val < j.val at hkk
        rw [(hoff (kk.val + 1) (by omega) (by omega) (by omega)).1]
        exact hbefore kk hkk
      · intro h
        rw [hfr.1, hRR] at h
        cases h
  by_cases hle2 : j.val + 1 ≤ k
  case pos =>
    -- front at e
    have hjk : j.val + 1 = k := by omega
    have hfe := hsiteE (j.val + 1) hjk
    rw [hfe] at hw htok hrl
    by_cases hRL : ((rbRun ring (renewalBankStart ring seed) pre).1 e).tok = .RL
    · have honly := (hrl hRL).1
      have hye : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .E := by
        apply Classical.byContradiction
        intro h
        have h2 := honly jk' (by rw [hdk']; exact h)
        rw [hdk'] at h2
        have hp := hy
        rw [h2, hx] at hp
        omega
      apply hfrozen
      exact bankWindowOverlapStableCellsUnchangedReads ring hn hbank (rbRun ring (renewalBankStart ring seed) pre) e
        (bankWindowJointAlignedQuietWaitCells (rbRun ring (renewalBankStart ring seed) pre).2 e (ring.rightNeighbor e)
          ((rbRun ring (renewalBankStart ring seed) pre).1 e) ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)) k hk1 hkb hx hy
          (Or.inl ⟨Or.inl hRL, hye⟩))
    · have hRR : ((rbRun ring (renewalBankStart ring seed) pre).1 e).tok = .RR := by
        rcases htok with h | h
        · exact h
        · exact absurd h hRL
      have hcells := bankWindowJointAlignedRrForwardCells (rbRun ring (renewalBankStart ring seed) pre).2 e
        (ring.rightNeighbor e) ((rbRun ring (renewalBankStart ring seed) pre).1 e) ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)) k hk1
        hkb hx hy hRR
      apply hasm
      refine ⟨jk', rho, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hdk']
        exact (hwD.trans hcells.2.2.2.2).trans hw
      · rw [hdk']
        exact Or.inl (htrip.2.2.2.trans hcells.2.2.1)
      · intro jj hjj
        have _hjjb := jj.isLt
        change jj.val + 1 ≤ k + 1 at hjj
        by_cases h1 : jj.val + 1 = k + 1
        · rw [hsiteD (jj.val + 1) h1]
          exact htrip.2.2.1.trans hcells.2.2.2.1
        · by_cases h2 : jj.val + 1 = k
          · rw [hsiteE (jj.val + 1) h2]
            rw [htrip.1.2.1.trans hcells.2.1]
            have h := hZero k hk1 (by omega)
            rw [hsiteE k rfl] at h
            exact h
          · rw [(hoff (jj.val + 1) (by omega) h2 h1).1]
            exact hZero (jj.val + 1) (by omega) (by omega)
      · intro kk hkk
        have _hkkb := kk.isLt
        change kk.val < k at hkk
        by_cases h2 : kk.val + 1 = k
        · rw [hsiteE (kk.val + 1) h2]
          exact htrip.1.2.2.trans hcells.1
        · rw [(hoff (kk.val + 1) (by omega) h2 (by omega)).1]
          exact hEbefore (kk.val + 1) (by omega) (by omega)
      · intro h
        rw [hdk', htrip.2.2.2.trans hcells.2.2.1] at h
        cases h
  rcases Nat.lt_or_ge (k + 1) (j.val + 1) with hlt3 | hle3
  · -- front after the pair
    apply hidle
    · have h := hEbefore k hk1 (by omega)
      rw [hsiteE k rfl] at h
      exact h
    · have h := hEbefore (k + 1) (by omega) (by omega)
      rw [hsiteD (k + 1) rfl] at h
      exact h
  -- front at e+
  have hjk : j.val + 1 = k + 1 := by omega
  have hfd := hsiteD (j.val + 1) hjk
  rw [hfd] at hw htok hrl
  have hxe : ((rbRun ring (renewalBankStart ring seed) pre).1 e).tok = .E := by
    have h := hEbefore k hk1 (by omega)
    rw [hsiteE k rfl] at h
    exact h
  have hzk : ∀ a : Nat, 1 ≤ a → a < k →
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 (Counter.site ring root a)).bit = false := by
    intro a ha1 ha
    rw [(hoff a (by omega) (by omega) (by omega)).1]
    exact hZero a ha1 (by omega)
  have hEk : ∀ a : Nat, 1 ≤ a → a < k →
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 (Counter.site ring root a)).tok = .E := by
    intro a ha1 ha
    rw [(hoff a (by omega) (by omega) (by omega)).1]
    exact hEbefore a ha1 (by omega)
  have hback : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .RL ∨
      (((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .RR ∧
        k + 1 = (compileAdvice (ceilLogTwo n)).b) →
      BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) root := by
    intro hq
    have hcells := bankWindowJointAlignedRlBackCells (rbRun ring (renewalBankStart ring seed) pre).2 e
      (ring.rightNeighbor e) ((rbRun ring (renewalBankStart ring seed) pre).1 e) ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)) k hk1
      hkb hx hy hxe hq
    have hNe : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).tok = .RL := htrip.1.2.2.trans hcells.1
    have hNeb : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).bit = false := htrip.1.2.1.trans hcells.2.1
    have hNd : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 (ring.rightNeighbor e)).tok = .E :=
      htrip.2.2.2.trans hcells.2.2.1
    have hNdb : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 (ring.rightNeighbor e)).bit =
        ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).bit := htrip.2.2.1.trans hcells.2.2.2.1
    have hzeroB : bankWindowZeroPrefix ring (rbRun ring (renewalBankStart ring seed) pre) root
        (compileAdvice (ceilLogTwo n)).b := by
      rcases hq with h | ⟨_, htop⟩
      · exact (hrl h).2
      · intro jj hjj
        exact hzero jj (by omega)
    apply hasm
    refine ⟨jk, rho, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hdk]
      exact (hwS.trans hcells.2.2.2.2).trans hw
    · rw [hdk]
      exact Or.inr hNe
    · intro jj hjj
      have _hjjb := jj.isLt
      change jj.val + 1 ≤ k - 1 + 1 at hjj
      by_cases h2 : jj.val + 1 = k
      · rw [hsiteE (jj.val + 1) h2]
        exact hNeb
      · exact hzk (jj.val + 1) (by omega) (by omega)
    · intro kk hkk
      have _hkkb := kk.isLt
      change kk.val < k - 1 at hkk
      exact hEk (kk.val + 1) (by omega) (by omega)
    · intro _
      rw [hdk]
      constructor
      · intro jj hjj
        by_cases h2 : jj.val + 1 = k
        · exact hsiteE (jj.val + 1) h2
        · by_cases h1 : jj.val + 1 = k + 1
          · rw [hsiteD (jj.val + 1) h1, hNd] at hjj
            exact absurd rfl hjj
          · exfalso
            have _hjjb := jj.isLt
            rw [(hoff (jj.val + 1) (by omega) h2 h1).1] at hjj
            rcases hq with h | ⟨hrr, htop⟩
            · have h3 := (hrl h).1 jj hjj
              have hp := hpk (jj.val + 1) (by omega)
              rw [h3, hy] at hp
              omega
            · exact hjj (hEbefore (jj.val + 1) (by omega) (by omega))
      · intro jj hjj
        by_cases h2 : jj.val + 1 = k
        · rw [hsiteE (jj.val + 1) h2]
          exact hNeb
        · by_cases h1 : jj.val + 1 = k + 1
          · rw [hsiteD (jj.val + 1) h1, hNdb]
            have h := hzeroB jj hjj
            rw [hsiteD (jj.val + 1) h1] at h
            exact h
          · have _hjjb := jj.isLt
            rw [(hoff (jj.val + 1) (by omega) h2 h1).1]
            exact hzeroB jj hjj
  by_cases hRL : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .RL
  · exact hback (Or.inl hRL)
  · have hRR : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .RR := by
      rcases htok with h | h
      · exact h
      · exact absurd h hRL
    by_cases htop : k + 1 = (compileAdvice (ceilLogTwo n)).b
    · exact hback (Or.inr ⟨hRR, htop⟩)
    · apply hfrozen
      exact bankWindowOverlapStableCellsUnchangedReads ring hn hbank (rbRun ring (renewalBankStart ring seed) pre) e
        (bankWindowJointAlignedQuietWaitCells (rbRun ring (renewalBankStart ring seed) pre).2 e (ring.rightNeighbor e)
          ((rbRun ring (renewalBankStart ring seed) pre).1 e) ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)) k hk1 hkb hx hy
          (Or.inr ⟨hxe, Or.inl hRR, htop⟩))


/-- A list sum over Fin m changes by d when exactly one entry grows by d.
Consumer: bankWindowJointBinaryValueBitSet. -/
theorem bankWindowJointOfFnSumUpdate :
    ∀ (m : Nat) (f g : Fin m → Nat) (i : Fin m) (d : Nat),
      g i = f i + d → (∀ j : Fin m, j ≠ i → g j = f j) →
      (List.ofFn g).sum = (List.ofFn f).sum + d := by
  intro m
  induction m with
  | zero =>
      intro f g i
      exact i.elim0
  | succ m ih =>
      intro f g i d hi hrest
      simp only [List.ofFn_succ, List.sum_cons]
      induction i using Fin.cases with
      | zero =>
          have htail : (List.ofFn fun j : Fin m => g j.succ) =
              List.ofFn fun j : Fin m => f j.succ := by
            congr 1
            funext j
            exact hrest j.succ (Fin.succ_ne_zero j)
          rw [htail, hi]
          omega
      | succ i' =>
          have h0 : g 0 = f 0 := hrest 0 (Fin.succ_ne_zero i').symm
          have htail := ih (fun j : Fin m => f j.succ) (fun j : Fin m => g j.succ)
            i' d hi (fun j hj => hrest j.succ
              (fun h => hj (Fin.ext (by
                have h2 := congrArg Fin.val h
                simp only [Fin.val_succ] at h2
                omega))))
          rw [h0, htail]
          omega

/-- Setting one window bit (digit k+1, weight 2^k) of an origin while
keeping every other window bit adds 2^k to its binary value.
Consumer: bankWindowOverlapStableIwaitRootFieldsAt (IR toggle row). -/
theorem bankWindowJointBinaryValueBitSet {n : Nat} (ring : DirectedRing n)
    (C D : HeadlineConfiguration n) (o : RenewalBankOrigin n)
    (i : Fin (compileAdvice (ceilLogTwo n)).b)
    (hC : (C (Counter.site ring o.root (i.val + 1))).bit = false)
    (hD : (D (Counter.site ring o.root (i.val + 1))).bit = true)
    (hrest : ∀ j : Fin (compileAdvice (ceilLogTwo n)).b, j ≠ i →
      (D (Counter.site ring o.root (j.val + 1))).bit =
        (C (Counter.site ring o.root (j.val + 1))).bit) :
    bankOriginBinaryValue ring D o = bankOriginBinaryValue ring C o + 2 ^ i.val := by
  unfold bankOriginBinaryValue
  apply bankWindowJointOfFnSumUpdate _ _ _ i
  · simp [hC, hD]
  · intro j hj
    simp only [hrest j hj]

/-- `m ≤ 2 ^ ceilLogTwo m`.
Consumer: bankWindowJointKBelowWidth. -/
theorem bankWindowJointLeTwoPowCeilLog (m : Nat) : m ≤ 2 ^ ceilLogTwo m := by
  unfold ceilLogTwo
  split
  · simp
    omega
  · have h := Nat.lt_log2_self (n := m - 1)
    omega

/-- `x ≤ 2^t` gives `ceilLogTwo x ≤ t`.
Consumer: bankWindowJointKBelowWidth. -/
theorem bankWindowJointCeilLogLe (x t : Nat) (h : x ≤ 2 ^ t) : ceilLogTwo x ≤ t := by
  unfold ceilLogTwo
  split
  · omega
  · have hne : x - 1 ≠ 0 := by omega
    have := (Nat.log2_lt hne).mpr (show x - 1 < 2 ^ t by omega)
    omega

/-- `s + 1 ≤ 2^s`.
Consumer: bankWindowJointKBelowWidth. -/
theorem bankWindowJointSuccLeTwoPow : ∀ s : Nat, s + 1 ≤ 2 ^ s := by
  intro s
  induction s with
  | zero => simp
  | succ s ih =>
      rw [Nat.pow_succ]
      omega

/-- The production comparator threshold is below the BANK width:
K < 2^b for every advice q.
Consumer: the M6-Q IWAIT top-IR row (an IR at the top digit would need
V + 2^b ≤ K). -/
theorem bankWindowJointKBelowWidth (q : Nat) :
    (compileAdvice q).K < 2 ^ (compileAdvice q).b := by
  change 2 * q + productionKappa q < 2 ^ (paddedS (sourceTOfQ q) + 11)
  have hs2 : 2 ≤ paddedS (sourceTOfQ q) := Nat.le_max_left 2 _
  have hsq : ceilLogTwo q ≤ paddedS (sourceTOfQ q) := Nat.le_max_right 2 _
  have hA1 : q ≤ 2 ^ paddedS (sourceTOfQ q) :=
    Nat.le_trans (bankWindowJointLeTwoPowCeilLog q)
      (Nat.pow_le_pow_right (by omega) hsq)
  have hA2 := bankWindowJointSuccLeTwoPow (paddedS (sourceTOfQ q))
  have hA4 : 4 ≤ 2 ^ paddedS (sourceTOfQ q) := by
    have := Nat.pow_le_pow_right (show 0 < 2 by omega) hs2
    simpa using this
  have hkappa : productionKappa q ≤ paddedS (sourceTOfQ q) + 29 := by
    unfold productionKappa
    split
    · unfold finiteKappa
      repeat' split
      all_goals omega
    · unfold kappaDot
      repeat' split
      all_goals try omega
      have hbig : 557 * paddedS (sourceTOfQ q) + 119981 + 1 ≤
          2 ^ (paddedS (sourceTOfQ q) + 17) := by
        rw [Nat.pow_add, show (2 : Nat) ^ 17 = 131072 by rfl]
        have := hA2
        omega
      have := bankWindowJointCeilLogLe _ _ hbig
      omega
  rw [Nat.pow_add, show (2 : Nat) ^ 11 = 2048 by rfl]
  omega

/-- M6-Q IWAIT, IR toggle, cell level: an IR source facing an empty
responder on an aligned stable edge empties its own token (bit kept) and
toggles the responder bit; the responder takes IR when its old bit was 1
(carry) and AL when it was 0; the source worker moves to the responder.
Consumer: bankWindowOverlapStableIwaitRootFieldsAt. -/
theorem bankWindowJointAlignedIrToggleCells {n : Nat} {c : Compiled} (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (k : Nat)
    (hk : 1 ≤ k) (hbelow : k < c.b)
    (hx : x.pack.val = k) (hy : y.pack.val = k + 1)
    (hir : x.tok = .IR) (hye : y.tok = .E) :
    (Counter.resetBankOld x y).1.tok = .E ∧
    (Counter.resetBankOld x y).1.bit = x.bit ∧
    (Counter.resetBankOld x y).2.tok = (if y.bit then .IR else .AL) ∧
    (Counter.resetBankOld x y).2.bit = !y.bit ∧
    (renewalBankPairMemory c m e dest x y).1.worker = .empty ∧
    (renewalBankPairMemory c m e dest x y).2.worker = (m.sites e).worker := by
  have hle : k ≤ c.b := by omega
  have hnz : k ≠ 0 := by omega
  have hbz : c.b ≠ 0 := by omega
  have hne : k ≠ c.b := by omega
  have hnextPos : 1 ≤ k + 1 := by omega
  have hnextNz : k + 1 ≠ 0 := by omega
  have hnl : ¬ c.b < k + 1 := by omega
  have hrole : packNext k (k + 1) c.b = k + 1 := by
    simp [packNext, hbelow]
  by_cases htop : k + 1 = c.b
  · have hpTop : packNext k c.b c.b = c.b := by
      have h := hrole
      rw [htop] at h
      exact h
    cases hb : y.bit <;>
      simp [Counter.resetBankOld, renewalBankPairMemory, bankPair, bankCell,
        hx, hy, hk, hbelow, hle, hnz, hbz, hne, hnextPos, hnextNz, hnl,
        hrole, hpTop, htop, hir, hye, hb, Id.run_pure, Id.run_bind]
  · cases hb : y.bit <;>
      simp [Counter.resetBankOld, renewalBankPairMemory, bankPair, bankCell,
        hx, hy, hk, hbelow, hle, hnz, hbz, hne, hnextPos, hnextNz, hnl,
        hrole, htop, hir, hye, hb, Id.run_pure, Id.run_bind]

/-- M6-Q IWAIT, AL back step, cell level: an empty source facing an AL
responder on an aligned stable edge receives AL (bits kept on both
sides), the responder token is erased and the responder worker moves to
the source.
Consumer: bankWindowOverlapStableIwaitRootFieldsAt. -/
theorem bankWindowJointAlignedAlBackCells {n : Nat} {c : Compiled} (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (k : Nat)
    (hk : 1 ≤ k) (hbelow : k < c.b)
    (hx : x.pack.val = k) (hy : y.pack.val = k + 1)
    (hxe : x.tok = .E) (hal : y.tok = .AL) :
    (Counter.resetBankOld x y).1.tok = .AL ∧
    (Counter.resetBankOld x y).1.bit = x.bit ∧
    (Counter.resetBankOld x y).2.tok = .E ∧
    (Counter.resetBankOld x y).2.bit = y.bit ∧
    (renewalBankPairMemory c m e dest x y).1.worker = (m.sites dest).worker ∧
    (renewalBankPairMemory c m e dest x y).2.worker = .empty := by
  have hle : k ≤ c.b := by omega
  have hnz : k ≠ 0 := by omega
  have hbz : c.b ≠ 0 := by omega
  have hne : k ≠ c.b := by omega
  have hnextPos : 1 ≤ k + 1 := by omega
  have hnextNz : k + 1 ≠ 0 := by omega
  have hnl : ¬ c.b < k + 1 := by omega
  have hrole : packNext k (k + 1) c.b = k + 1 := by
    simp [packNext, hbelow]
  by_cases htop : k + 1 = c.b
  · have hpTop : packNext k c.b c.b = c.b := by
      have h := hrole
      rw [htop] at h
      exact h
    simp [Counter.resetBankOld, renewalBankPairMemory, bankPair, bankCell,
      hx, hy, hk, hbelow, hle, hnz, hbz, hne, hnextPos, hnextNz, hnl,
      hrole, hpTop, htop, hxe, hal, Id.run_pure, Id.run_bind]
  · simp [Counter.resetBankOld, renewalBankPairMemory, bankPair, bankCell,
      hx, hy, hk, hbelow, hle, hnz, hbz, hne, hnextPos, hnextNz, hnl,
      hrole, htop, hxe, hal, Id.run_pure, Id.run_bind]

/-- The incrementExact package of a genuine increment worker p (origin
o) at site i of a root: the only window token is at i, and it is either
IR with a zero bit prefix and heads V + 2^PACK, or AL with heads V; the
head count stays at most K. This is the body of the incrementExact
clause of BankWindowExact.
Consumer: bankWindowOverlapStableIwaitMovedRootFieldsAt and the M6-Q
IWAIT rows. -/
def bankWindowJointIncrementAt {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root i : Fin n)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n) : Prop :=
  bankWindowOnlyToken ring r root i ∧
  (((r.1 i).tok = .IR ∧
      bankWindowZeroPrefix ring r root (r.1 i).pack.val ∧
      p.heads = bankOriginBinaryValue ring r.1 o + 2 ^ (r.1 i).pack.val ∧
      bankOriginBinaryValue ring r.1 o + 2 ^ (r.1 i).pack.val ≤
        (compileAdvice (ceilLogTwo n)).K) ∨
   ((r.1 i).tok = .AL ∧
      p.heads = bankOriginBinaryValue ring r.1 o ∧
      bankOriginBinaryValue ring r.1 o ≤ (compileAdvice (ceilLogTwo n)).K))

/-- M6-Q IWAIT, moving-worker assembly: a foreign IWAIT root with
controller waiting [] on a stable nonroot edge whose old window carries
its only token at a pair site c (digit jc), and whose genuine increment
worker p (origin o rooted there) sits after the step at the pair site s
with the other pair site t worker-empty and the POST increment package
at s. Then every root-indexed POST clause holds; off-pair genuine
workers or taint would need a second old window token (old
incrementExact / iwaitTaintedUnique OnlyToken against the token at c).
Consumer: bankWindowOverlapStableIwaitRootFieldsAt (rows D3, D5). -/
theorem bankWindowOverlapStableIwaitMovedRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hnonroot : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ≠ 0)
    (hstable :
      packNext ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val)
    (hforeign : root ≠ e ∧ root ≠ ring.rightNeighbor e)
    (hmodeOld : ((rbRun ring (renewalBankStart ring seed) pre).1 root).mode = .IWAIT)
    (hctrlOld : ((rbRun ring (renewalBankStart ring seed) pre).2.sites root).controller = .waiting [])
    (c : Fin n) (hcpair : c = e ∨ c = ring.rightNeighbor e)
    (jc : Fin (compileAdvice (ceilLogTwo n)).b)
    (hjc : Counter.site ring root (jc.val + 1) = c)
    (hcne : ((rbRun ring (renewalBankStart ring seed) pre).1 c).tok ≠ .E)
    (s t : Fin n)
    (hst : (s = e ∧ t = ring.rightNeighbor e) ∨
      (s = ring.rightNeighbor e ∧ t = e))
    (o : RenewalBankOrigin n) (p : RenewalBankPayload n)
    (ho : o.root = root) (horig : p.origin = some o)
    (hws : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites s).worker = .payload p)
    (hwt : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites t).worker = .empty)
    (hpkg : bankWindowJointIncrementAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) root s p o) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) root := by
  have hphase := bankWindowOverlapStableNonrootPhaseFields ring hn hbank
    seed pre e root hJ hnonroot hstable hforeign
  have hjoint := bankWindowOverlapRootJointFields ring hn hbank seed pre e hJ
  have hpackAll := bankWindowOverlapStablePackFrame ring hn seed pre e hstable
  have hroot := bankWindowExactOffPairAtomicReads ring (rbRun ring (renewalBankStart ring seed) pre) e root
    hforeign.1 hforeign.2
  have hmodeR := hroot.2.1
  have hctrlR := hroot.2.2.2.2.2.2
  have hgrantR := hroot.2.2.2.2.1
  unfold bankWindowReadMode at hmodeR
  unfold bankWindowReadController at hctrlR
  unfold bankWindowReadGrant at hgrantR
  have hmodeN : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 root).mode = .IWAIT := hmodeR.trans hmodeOld
  have hctrlN : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites root).controller = .waiting [] :=
    hctrlR.trans hctrlOld
  have hsplit : ∀ z : Fin n, (z = e ∨ z = ring.rightNeighbor e) →
      z = s ∨ z = t := by
    intro z hz
    rcases hst with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hz with h | h
    · exact Or.inl (h.trans h1.symm)
    · exact Or.inr (h.trans h2.symm)
    · exact Or.inr (h.trans h2.symm)
    · exact Or.inl (h.trans h1.symm)
  have hoffOnly : ∀ z : Fin n, ¬ (z = e ∨ z = ring.rightNeighbor e) →
      bankWindowOnlyToken ring (rbRun ring (renewalBankStart ring seed) pre) root z → False := by
    intro z hz honlyz
    have h := honlyz jc (by rw [hjc]; exact hcne)
    rw [hjc] at h
    rw [h] at hcpair
    exact hz hcpair
  have hscopeBack : BankWindowScope ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) root →
      BankWindowScope ring (rbRun ring (renewalBankStart ring seed) pre) root := by
    intro hs
    refine ⟨fun jj hjj => ?_, ?_⟩
    · rw [← hpackAll]
      exact hs.1 jj hjj
    · rw [← hgrantR]
      exact hs.2
  have hgen : BankWindowScope ring (rbRun ring (renewalBankStart ring seed) pre) root →
      ∀ (i : Fin n) (p' : RenewalBankPayload n)
      (o' : RenewalBankOrigin n), o'.root = root →
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites i).worker = .payload p' → p'.origin = some o' →
      i = s ∧ p' = p := by
    intro hsO i p' o' ho' hw' horig'
    by_cases hi : i = e ∨ i = ring.rightNeighbor e
    · rcases hsplit i hi with his | hit
      · rw [his, hws] at hw'
        injection hw' with h
        exact ⟨his, h.symm⟩
      · rw [hit, hwt] at hw'
        cases hw'
    · have hf := bankWindowExactOffPairFrame ring (rbRun ring (renewalBankStart ring seed) pre) e i
        (fun h => hi (Or.inl h)) (fun h => hi (Or.inr h))
      have hwOld : ((rbRun ring (renewalBankStart ring seed) pre).2.sites i).worker = .payload p' := by
        rw [← hf.2]
        exact hw'
      have hie := (hJ.incrementExact root o' i p' hsO hmodeOld hctrlOld hwOld
        horig' ho').1
      exact (hoffOnly i hi hie).elim
  have horigEq : ∀ o' : RenewalBankOrigin n, p.origin = some o' → o' = o := by
    intro o' h
    rw [horig] at h
    injection h with h
    exact h.symm
  refine ⟨hphase.1, hphase.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o' _ _ ho' _ hm
    rw [ho', hmodeN] at hm
    cases hm
  · intro o' _ _ ho' _ hm
    rw [ho', hmodeN] at hm
    cases hm
  · intro _ hinh _ _
    rcases hinh with ⟨atoms, hc, hne⟩ | ⟨_, hc, _⟩
    · rw [hctrlN] at hc
      injection hc with h
      exact hne h.symm
    · rw [hctrlN] at hc
      cases hc
  · intro _ hm
    rw [hmodeN] at hm
    cases hm
  · intro _ _ _ hm
    rw [hmodeN] at hm
    rcases hm with h | h <;> cases h
  · intro o' i p' hs _ _ hw' horig' ho'
    obtain ⟨hi, hp⟩ := hgen (hscopeBack hs) i p' o' ho' hw' horig'
    have hoo : o' = o := by
      rw [hp] at horig'
      exact horigEq o' horig'
    rw [hoo, hi, hp]
    exact hpkg
  · intro o' _ _ ho' _ _ hm
    rw [ho', hmodeN] at hm
    cases hm
  · intro hs _ _ j ht
    by_cases hd : Counter.site ring root (j.val + 1) = e ∨
        Counter.site ring root (j.val + 1) = ring.rightNeighbor e
    · rcases hsplit _ hd with hds | hdt
      · refine ⟨o, p, by rw [hds]; exact hws, horig, ho, ?_⟩
        rw [hds]
        exact hpkg.1
      · rw [hdt] at ht
        unfold BankWindowTainted at ht
        rw [hwt] at ht
        rcases ht with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
    · have hf := bankWindowExactOffPairAtomicReads ring (rbRun ring (renewalBankStart ring seed) pre) e
        (Counter.site ring root (j.val + 1))
        (fun h => hd (Or.inl h)) (fun h => hd (Or.inr h))
      have hw := hf.2.2.2.2.2.1
      unfold bankWindowReadWorker at hw
      have htOld : BankWindowTainted (rbRun ring (renewalBankStart ring seed) pre) (Counter.site ring root (j.val + 1)) := by
        unfold BankWindowTainted at ht ⊢
        rw [hw] at ht
        exact ht
      obtain ⟨_, _, _, _, _, honlyOld⟩ := hJ.iwaitTaintedUnique root
        (hscopeBack hs) hmodeOld hctrlOld j htOld
      exact (hoffOnly _ hd honlyOld).elim
  · intro _ hm
    rw [hmodeN] at hm
    cases hm
  · intro limit hrun
    exact hjoint.2.2.2.1 root limit hforeign hrun
  · intro j
    exact hjoint.2.2.2.2 root j hforeign

/-- Equal window bits give equal binary values.
Consumer: bankWindowOverlapStableIwaitRootFieldsAt (AL back row). -/
theorem bankWindowJointBinaryValueCongr {n : Nat} (ring : DirectedRing n)
    (C D : HeadlineConfiguration n) (o : RenewalBankOrigin n)
    (h : ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      (D (Counter.site ring o.root (j.val + 1))).bit =
        (C (Counter.site ring o.root (j.val + 1))).bit) :
    bankOriginBinaryValue ring D o = bankOriginBinaryValue ring C o := by
  unfold bankOriginBinaryValue
  simp only [h]

/-- M6-Q IWAIT, no genuine worker: a foreign IWAIT root with controller
waiting [] whose old state has no genuine worker rooted there, on a
stable nonroot edge from its interior digit D(k), 1 <= k < b. No genuine
worker rooted there exists after the step, so the comparator and
incrementExact clauses are vacuous; a POST tainted digit would give an
old tainted digit, hence by old iwaitTaintedUnique an old genuine worker.
Consumer: bankWindowOverlapStableIwaitRootFieldsAt. -/
theorem bankWindowOverlapStableIwaitNoGenuineRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hnonroot : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ≠ 0)
    (hstable :
      packNext ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val)
    (hforeign : root ≠ e ∧ root ≠ ring.rightNeighbor e)
    (k : Nat) (hk1 : 1 ≤ k) (hkb : k < (compileAdvice (ceilLogTwo n)).b)
    (hsite : e = Counter.site ring root k)
    (hmodeOld : ((rbRun ring (renewalBankStart ring seed) pre).1 root).mode = .IWAIT)
    (hctrlOld : ((rbRun ring (renewalBankStart ring seed) pre).2.sites root).controller = .waiting [])
    (hnone : ∀ (i : Fin n) (p : RenewalBankPayload n)
      (o : RenewalBankOrigin n), o.root = root →
      ((rbRun ring (renewalBankStart ring seed) pre).2.sites i).worker = .payload p → p.origin = some o → False) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) root := by
  have hjoint := bankWindowOverlapRootJointFields ring hn hbank seed pre e hJ
  have hpackAll := bankWindowOverlapStablePackFrame ring hn seed pre e hstable
  have hroot := bankWindowExactOffPairAtomicReads ring (rbRun ring (renewalBankStart ring seed) pre) e root
    hforeign.1 hforeign.2
  have hmodeR := hroot.2.1
  have hctrlR := hroot.2.2.2.2.2.2
  have hgrantR := hroot.2.2.2.2.1
  unfold bankWindowReadMode at hmodeR
  unfold bankWindowReadController at hctrlR
  unfold bankWindowReadGrant at hgrantR
  have hmodeN : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 root).mode = .IWAIT := hmodeR.trans hmodeOld
  have hctrlN : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites root).controller = .waiting [] :=
    hctrlR.trans hctrlOld
  have hf := rbReferenceSelectedPairFrame ring (by omega : 2 ≤ n) (rbRun ring (renewalBankStart ring seed) pre) e
  have hnogen : ∀ (i : Fin n) (p : RenewalBankPayload n)
      (o : RenewalBankOrigin n), o.root = root →
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites i).worker = .payload p → p.origin = some o → False := by
    intro i p o ho hw horig
    by_cases hi : i = e ∨ i = ring.rightNeighbor e
    · have hp : (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
            (rbRun ring (renewalBankStart ring seed) pre).2 e (ring.rightNeighbor e)
            ((rbRun ring (renewalBankStart ring seed) pre).1 e) ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e))).1.worker = .payload p ∨
          (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
            (rbRun ring (renewalBankStart ring seed) pre).2 e (ring.rightNeighbor e)
            ((rbRun ring (renewalBankStart ring seed) pre).1 e) ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e))).2.worker = .payload p := by
        rcases hi with hi | hi
        · rw [hi] at hw
          have h := congrArg (fun s : RenewalBankSite n => s.worker) hf.2.2.1
          exact Or.inl (h.symm.trans hw)
        · rw [hi] at hw
          have h := congrArg (fun s : RenewalBankSite n => s.worker) hf.2.2.2
          exact Or.inr (h.symm.trans hw)
      rcases rbBankNonrootSelectedWorkersInherited
          (compileAdvice (ceilLogTwo n)) (rbRun ring (renewalBankStart ring seed) pre).2 e (ring.rightNeighbor e)
          ((rbRun ring (renewalBankStart ring seed) pre).1 e) ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)) hnonroot p hp with h | h
      · exact hnone e p o ho h horig
      · exact hnone (ring.rightNeighbor e) p o ho h horig
    · have hfi := bankWindowExactOffPairFrame ring (rbRun ring (renewalBankStart ring seed) pre) e i
        (fun h => hi (Or.inl h)) (fun h => hi (Or.inr h))
      apply hnone i p o ho _ horig
      rw [← hfi.2]
      exact hw
  have hdk : Counter.site ring root ((⟨k - 1, by omega⟩ :
      Fin (compileAdvice (ceilLogTwo n)).b).val + 1) = e := by
    change Counter.site ring root (k - 1 + 1) = e
    rw [show k - 1 + 1 = k by omega]
    exact hsite.symm
  have hdk' : Counter.site ring root ((⟨k, hkb⟩ :
      Fin (compileAdvice (ceilLogTwo n)).b).val + 1) =
      ring.rightNeighbor e := by
    change Counter.site ring root (k + 1) = ring.rightNeighbor e
    rw [hsite]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o i p ho hw
    exact False.elim (hnogen i p o ho hw.1 hw.2.1)
  · intro o i p ho hw _
    exact False.elim (hnogen i p o ho hw.1 hw.2.1)
  · intro o i p ho hw _
    exact False.elim (hnogen i p o ho hw.1 hw.2.1)
  · intro o i p ho hw _
    exact False.elim (hnogen i p o ho hw.1 hw.2.1)
  · intro _ hinh _ _
    rcases hinh with ⟨atoms, hc, hne⟩ | ⟨_, hc, _⟩
    · rw [hctrlN] at hc
      injection hc with h
      exact hne h.symm
    · rw [hctrlN] at hc
      cases hc
  · intro _ hm
    rw [hmodeN] at hm
    cases hm
  · intro _ _ _ hm
    rw [hmodeN] at hm
    rcases hm with h | h <;> cases h
  · intro o i p _ _ _ hw horig ho
    exact False.elim (hnogen i p o ho hw horig)
  · intro o _ _ ho _ _ hm
    rw [ho, hmodeN] at hm
    cases hm
  · intro hs _ _ j ht
    have hscopeOld : BankWindowScope ring (rbRun ring (renewalBankStart ring seed) pre) root := by
      refine ⟨fun jj hjj => ?_, ?_⟩
      · rw [← hpackAll]
        exact hs.1 jj hjj
      · rw [← hgrantR]
        exact hs.2
    have hold : ∃ jj : Fin (compileAdvice (ceilLogTwo n)).b,
        BankWindowTainted (rbRun ring (renewalBankStart ring seed) pre) (Counter.site ring root (jj.val + 1)) := by
      by_cases hd : Counter.site ring root (j.val + 1) = e ∨
          Counter.site ring root (j.val + 1) = ring.rightNeighbor e
      · rcases bankWindowOverlapNonrootPairTaintPreimage ring
            (by omega : 2 ≤ n) (rbRun ring (renewalBankStart ring seed) pre) e (Counter.site ring root (j.val + 1))
            hnonroot hd ht with h | h
        · exact ⟨⟨k - 1, by omega⟩, by rw [hdk]; exact h⟩
        · exact ⟨⟨k, hkb⟩, by rw [hdk']; exact h⟩
      · have hfd := bankWindowExactOffPairAtomicReads ring (rbRun ring (renewalBankStart ring seed) pre) e
          (Counter.site ring root (j.val + 1))
          (fun h => hd (Or.inl h)) (fun h => hd (Or.inr h))
        have hw := hfd.2.2.2.2.2.1
        unfold bankWindowReadWorker at hw
        refine ⟨j, ?_⟩
        unfold BankWindowTainted at ht ⊢
        rw [hw] at ht
        exact ht
    obtain ⟨jj, hjj⟩ := hold
    obtain ⟨o, p, hw, horig, ho, _⟩ := hJ.iwaitTaintedUnique root
      hscopeOld hmodeOld hctrlOld jj hjj
    exact False.elim (hnone _ p o ho hw horig)
  · intro _ hm
    rw [hmodeN] at hm
    cases hm
  · intro limit hrun
    exact hjoint.2.2.2.1 root limit hforeign hrun
  · intro j
    exact hjoint.2.2.2.2 root j hforeign

/-- M6-Q IWAIT: a foreign root in IWAIT with controller waiting [] on a
stable nonroot edge from its interior digit D(k), 1 <= k < b, satisfies
every root-indexed POST clause. Out of POST scope this is
bankWindowOverlapStableNonrootOutOfScopeRootFieldsAt; with no genuine
worker it is bankWindowOverlapStableIwaitNoGenuineRootFieldsAt.
Otherwise old incrementExact puts the only window token at the genuine
worker site c. c off the pair: idle pair. c = e: IR toggles digit k+1
(bit 0: AL with value V + 2^k; bit 1: IR one digit higher with value
V - 2^k, same heads), AL is quiet. c = e+: AL steps back to e with the
value unchanged, non-top IR is quiet, and an IR at the top digit is
impossible because V + 2^b <= K < 2^b (bankWindowJointKBelowWidth).
Consumer: the final bankWindowExactStep case split, stable interior edge,
IWAIT foreign roots (ledger row M6-Q, IWAIT part). -/
theorem bankWindowOverlapStableIwaitRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hnonroot : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ≠ 0)
    (hstable :
      packNext ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val)
    (hforeign : root ≠ e ∧ root ≠ ring.rightNeighbor e)
    (k : Nat) (hk1 : 1 ≤ k) (hkb : k < (compileAdvice (ceilLogTwo n)).b)
    (hsite : e = Counter.site ring root k)
    (hmodeOld : ((rbRun ring (renewalBankStart ring seed) pre).1 root).mode = .IWAIT)
    (hctrlOld : ((rbRun ring (renewalBankStart ring seed) pre).2.sites root).controller = .waiting []) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) root := by
  by_cases hs : BankWindowScope ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) root
  case neg =>
    exact bankWindowOverlapStableNonrootOutOfScopeRootFieldsAt ring hn hbank
      seed pre e root hJ hnonroot hstable hforeign hs
      (by rw [hmodeOld]; intro h; cases h)
  by_cases hex : ∃ (c : Fin n) (p : RenewalBankPayload n)
      (o : RenewalBankOrigin n), o.root = root ∧
      ((rbRun ring (renewalBankStart ring seed) pre).2.sites c).worker = .payload p ∧ p.origin = some o
  case neg =>
    exact bankWindowOverlapStableIwaitNoGenuineRootFieldsAt ring hn hbank
      seed pre e root hJ hnonroot hstable hforeign k hk1 hkb hsite
      hmodeOld hctrlOld
      (fun i p o ho hw horig => hex ⟨i, p, o, ho, hw, horig⟩)
  obtain ⟨c, p, o, ho, hw, horig⟩ := hex
  have hpackAll := bankWindowOverlapStablePackFrame ring hn seed pre e hstable
  have hroot := bankWindowExactOffPairAtomicReads ring (rbRun ring (renewalBankStart ring seed) pre) e root
    hforeign.1 hforeign.2
  have hgrantR := hroot.2.2.2.2.1
  unfold bankWindowReadGrant at hgrantR
  have hscopeOld : BankWindowScope ring (rbRun ring (renewalBankStart ring seed) pre) root := by
    refine ⟨fun jj hjj => ?_, ?_⟩
    · rw [← hpackAll]
      exact hs.1 jj hjj
    · rw [← hgrantR]
      exact hs.2
  have hcomp := hscopeOld.1
  obtain ⟨honlyC, hpkC⟩ := hJ.incrementExact root o c p hscopeOld hmodeOld
    hctrlOld hw horig ho
  have hcne : ((rbRun ring (renewalBankStart ring seed) pre).1 c).tok ≠ .E := by
    rcases hpkC with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> intro h' <;> cases h'
  have hx : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val = k := by
    rw [hsite]
    exact hcomp k (by omega)
  have hsucc : ring.rightNeighbor e = Counter.site ring root (k + 1) := by
    rw [hsite]
    rfl
  have hy : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val = k + 1 := by
    rw [hsucc]
    exact hcomp (k + 1) (by omega)
  have hpk : ∀ a : Nat, a ≤ (compileAdvice (ceilLogTwo n)).b →
      ((rbRun ring (renewalBankStart ring seed) pre).1 (Counter.site ring root a)).pack.val = a := hcomp
  have hsiteE : ∀ a : Nat, a = k → Counter.site ring root a = e := by
    intro a ha
    rw [ha]
    exact hsite.symm
  have hsiteD : ∀ a : Nat, a = k + 1 →
      Counter.site ring root a = ring.rightNeighbor e := by
    intro a ha
    rw [ha]
    exact hsucc.symm
  have hne : e ≠ ring.rightNeighbor e := by
    intro h
    have h2 := hy
    rw [← h, hx] at h2
    omega
  let jk : Fin (compileAdvice (ceilLogTwo n)).b := ⟨k - 1, by omega⟩
  have hdk : Counter.site ring root (jk.val + 1) = e := by
    change Counter.site ring root (k - 1 + 1) = e
    rw [show k - 1 + 1 = k by omega]
    exact hsite.symm
  let jk' : Fin (compileAdvice (ceilLogTwo n)).b := ⟨k, hkb⟩
  have hdk' : Counter.site ring root (jk'.val + 1) = ring.rightNeighbor e :=
    hsucc.symm
  have hoff : ∀ a : Nat, a ≤ (compileAdvice (ceilLogTwo n)).b → a ≠ k →
      a ≠ k + 1 →
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 (Counter.site ring root a) = (rbRun ring (renewalBankStart ring seed) pre).1 (Counter.site ring root a) ∧
      (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites (Counter.site ring root a) =
        (rbRun ring (renewalBankStart ring seed) pre).2.sites (Counter.site ring root a) := by
    intro a ha h1 h2
    have hp := hpk a ha
    apply bankWindowExactOffPairFrame
    · intro h
      rw [h, hx] at hp
      omega
    · intro h
      rw [h, hy] at hp
      omega
  have htrip := bankWindowClosureSelectedBankTrip ring hn hbank (rbRun ring (renewalBankStart ring seed) pre) e
  simp only [Counter.resetAgentBankTrip, Counter.resetCellBankTrip,
    Prod.mk.injEq] at htrip
  have hf := rbReferenceSelectedPairFrame ring (by omega : 2 ≤ n) (rbRun ring (renewalBankStart ring seed) pre) e
  have hwS := congrArg (fun s : RenewalBankSite n => s.worker) hf.2.2.1
  have hwD := congrArg (fun s : RenewalBankSite n => s.worker) hf.2.2.2
  have hyN : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 (ring.rightNeighbor e)).pack.val = k + 1 := by
    rw [hpackAll]
    exact hy
  have hoD : Counter.site ring o.root (jk'.val + 1) = ring.rightNeighbor e := by
    rw [ho]
    exact hdk'
  have hfrozen : (∀ z : Fin n, (z = e ∨ z = ring.rightNeighbor e) →
      bankWindowReadTok (rbRun ring (renewalBankStart ring seed) pre) (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) z ∧ bankWindowReadBit (rbRun ring (renewalBankStart ring seed) pre) (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) z ∧
      bankWindowReadWorker (rbRun ring (renewalBankStart ring seed) pre) (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) z) → BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) root :=
    fun hpair => bankWindowOverlapStableFrozenPairRootFieldsAt ring hn hbank
      seed pre e root hJ hstable hpair hforeign
  by_cases hcp : c = e ∨ c = ring.rightNeighbor e
  case neg =>
    have hxE : ((rbRun ring (renewalBankStart ring seed) pre).1 e).tok = .E := by
      apply Classical.byContradiction
      intro h
      have h2 := honlyC jk (by rw [hdk]; exact h)
      rw [hdk] at h2
      exact hcp (Or.inl h2.symm)
    have hyE : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .E := by
      apply Classical.byContradiction
      intro h
      have h2 := honlyC jk' (by rw [hdk']; exact h)
      rw [hdk'] at h2
      exact hcp (Or.inr h2.symm)
    exact bankWindowOverlapStableIdlePairRootFieldsAt ring hn hbank seed pre
      e root hJ hnonroot hstable hxE hyE hforeign
  rcases hcp with hce | hce
  · -- genuine worker at e
    have hyE : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .E := by
      apply Classical.byContradiction
      intro h
      have h2 := honlyC jk' (by rw [hdk']; exact h)
      rw [hdk'] at h2
      exact hne (hce.symm.trans h2.symm)
    rw [hce] at hw hpkC hcne
    by_cases hAL : ((rbRun ring (renewalBankStart ring seed) pre).1 e).tok = .AL
    · apply hfrozen
      exact bankWindowOverlapStableCellsUnchangedReads ring hn hbank (rbRun ring (renewalBankStart ring seed) pre) e
        (bankWindowJointAlignedQuietWaitCells (rbRun ring (renewalBankStart ring seed) pre).2 e (ring.rightNeighbor e)
          ((rbRun ring (renewalBankStart ring seed) pre).1 e) ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)) k hk1 hkb hx hy
          (Or.inl ⟨Or.inr hAL, hyE⟩))
    obtain ⟨hIR, hzp, hheads, hK⟩ := hpkC.resolve_right (fun h => hAL h.1)
    have hcells := bankWindowJointAlignedIrToggleCells (rbRun ring (renewalBankStart ring seed) pre).2 e
      (ring.rightNeighbor e) ((rbRun ring (renewalBankStart ring seed) pre).1 e) ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)) k hk1
      hkb hx hy hIR hyE
    have hNe : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).tok = .E := htrip.1.2.2.trans hcells.1
    have hNeb : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).bit = ((rbRun ring (renewalBankStart ring seed) pre).1 e).bit := htrip.1.2.1.trans hcells.2.1
    have hNd : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 (ring.rightNeighbor e)).tok =
        (if ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).bit then .IR else .AL) :=
      htrip.2.2.2.trans hcells.2.2.1
    have hNdb : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 (ring.rightNeighbor e)).bit =
        !((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).bit :=
      htrip.2.2.1.trans hcells.2.2.2.1
    have hwNe : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites e).worker = .empty :=
      hwS.trans hcells.2.2.2.2.1
    have hwNd : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites (ring.rightNeighbor e)).worker = .payload p :=
      (hwD.trans hcells.2.2.2.2.2).trans hw
    have honlyN : bankWindowOnlyToken ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) root (ring.rightNeighbor e) := by
      intro jj hjj
      have _hjjb := jj.isLt
      by_cases h1 : jj.val + 1 = k + 1
      · exact hsiteD (jj.val + 1) h1
      · by_cases h2 : jj.val + 1 = k
        · rw [hsiteE (jj.val + 1) h2, hNe] at hjj
          exact absurd rfl hjj
        · rw [(hoff (jj.val + 1) (by omega) h2 h1).1] at hjj
          have h3 := honlyC jj hjj
          have hp := hpk (jj.val + 1) (by omega)
          rw [h3, hce, hx] at hp
          omega
    have hrest : ∀ jj : Fin (compileAdvice (ceilLogTwo n)).b, jj ≠ jk' →
        ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 (Counter.site ring o.root (jj.val + 1))).bit =
          ((rbRun ring (renewalBankStart ring seed) pre).1 (Counter.site ring o.root (jj.val + 1))).bit := by
      intro jj hjj
      have _hjjb := jj.isLt
      have h1 : jj.val + 1 ≠ k + 1 := by
        intro h
        apply hjj
        apply Fin.ext
        change jj.val = k
        omega
      rw [ho]
      by_cases h2 : jj.val + 1 = k
      · rw [hsiteE (jj.val + 1) h2]
        exact hNeb
      · rw [(hoff (jj.val + 1) (by omega) h2 h1).1]
    have hzeroE : ((rbRun ring (renewalBankStart ring seed) pre).1 e).bit = false := by
      have h := hzp jk (by rw [hx]; show k - 1 + 1 ≤ k; omega)
      rw [hdk] at h
      exact h
    rw [hx] at hheads hK
    apply bankWindowOverlapStableIwaitMovedRootFieldsAt ring hn hbank seed pre
      e root hJ hnonroot hstable hforeign hmodeOld hctrlOld e (Or.inl rfl)
      jk hdk hcne (ring.rightNeighbor e) e (Or.inr ⟨rfl, rfl⟩) o p ho horig
      hwNd hwNe
    refine ⟨honlyN, ?_⟩
    cases hb : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).bit
    · rw [hb] at hNd hNdb
      have hval := bankWindowJointBinaryValueBitSet ring (rbRun ring (renewalBankStart ring seed) pre).1 (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 o jk'
        (by rw [hoD]; exact hb) (by rw [hoD]; exact hNdb) hrest
      change bankOriginBinaryValue ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 o =
        bankOriginBinaryValue ring (rbRun ring (renewalBankStart ring seed) pre).1 o + 2 ^ k at hval
      refine Or.inr ⟨?_, ?_, ?_⟩
      · rw [hNd]
        rfl
      · rw [hheads, hval]
      · rw [hval]
        exact hK
    · rw [hb] at hNd hNdb
      have hval := bankWindowJointBinaryValueBitSet ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 (rbRun ring (renewalBankStart ring seed) pre).1 o jk'
        (by rw [hoD]; exact hNdb) (by rw [hoD]; exact hb)
        (fun jj hjj => (hrest jj hjj).symm)
      change bankOriginBinaryValue ring (rbRun ring (renewalBankStart ring seed) pre).1 o =
        bankOriginBinaryValue ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 o + 2 ^ k at hval
      refine Or.inl ⟨?_, ?_, ?_, ?_⟩
      · rw [hNd]
        rfl
      · rw [hyN]
        intro jj hjj
        have _hjjb := jj.isLt
        by_cases h1 : jj.val + 1 = k + 1
        · rw [hsiteD (jj.val + 1) h1]
          exact hNdb
        · by_cases h2 : jj.val + 1 = k
          · rw [hsiteE (jj.val + 1) h2, hNeb]
            exact hzeroE
          · rw [(hoff (jj.val + 1) (by omega) h2 h1).1]
            exact hzp jj (by rw [hx]; omega)
      · rw [hyN, hheads, hval, Nat.pow_succ]
        omega
      · rw [hyN, Nat.pow_succ]
        rw [hval] at hK
        omega
  · -- genuine worker at e+
    have hxE : ((rbRun ring (renewalBankStart ring seed) pre).1 e).tok = .E := by
      apply Classical.byContradiction
      intro h
      have h2 := honlyC jk (by rw [hdk]; exact h)
      rw [hdk] at h2
      exact hne (h2.trans hce)
    rw [hce] at hw hpkC hcne
    rcases hpkC with ⟨hIR, _, _, hK⟩ | ⟨hAL, hheads, hK⟩
    · by_cases htop : k + 1 = (compileAdvice (ceilLogTwo n)).b
      · exfalso
        have hKb := bankWindowJointKBelowWidth (ceilLogTwo n)
        rw [hy, htop] at hK
        omega
      · apply hfrozen
        exact bankWindowOverlapStableCellsUnchangedReads ring hn hbank (rbRun ring (renewalBankStart ring seed) pre) e
          (bankWindowJointAlignedQuietWaitCells (rbRun ring (renewalBankStart ring seed) pre).2 e (ring.rightNeighbor e)
            ((rbRun ring (renewalBankStart ring seed) pre).1 e) ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)) k hk1 hkb hx hy
            (Or.inr ⟨hxE, Or.inr hIR, htop⟩))
    have hcells := bankWindowJointAlignedAlBackCells (rbRun ring (renewalBankStart ring seed) pre).2 e
      (ring.rightNeighbor e) ((rbRun ring (renewalBankStart ring seed) pre).1 e) ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)) k hk1
      hkb hx hy hxE hAL
    have hNe : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).tok = .AL := htrip.1.2.2.trans hcells.1
    have hNeb : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).bit = ((rbRun ring (renewalBankStart ring seed) pre).1 e).bit := htrip.1.2.1.trans hcells.2.1
    have hNd : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 (ring.rightNeighbor e)).tok = .E :=
      htrip.2.2.2.trans hcells.2.2.1
    have hNdb : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 (ring.rightNeighbor e)).bit =
        ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).bit :=
      htrip.2.2.1.trans hcells.2.2.2.1
    have hwNe : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites e).worker = .payload p :=
      (hwS.trans hcells.2.2.2.2.1).trans hw
    have hwNd : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites (ring.rightNeighbor e)).worker = .empty :=
      hwD.trans hcells.2.2.2.2.2
    have honlyN : bankWindowOnlyToken ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) root e := by
      intro jj hjj
      have _hjjb := jj.isLt
      by_cases h2 : jj.val + 1 = k
      · exact hsiteE (jj.val + 1) h2
      · by_cases h1 : jj.val + 1 = k + 1
        · rw [hsiteD (jj.val + 1) h1, hNd] at hjj
          exact absurd rfl hjj
        · rw [(hoff (jj.val + 1) (by omega) h2 h1).1] at hjj
          have h3 := honlyC jj hjj
          have hp := hpk (jj.val + 1) (by omega)
          rw [h3, hce, hy] at hp
          omega
    have hval : bankOriginBinaryValue ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 o =
        bankOriginBinaryValue ring (rbRun ring (renewalBankStart ring seed) pre).1 o := by
      apply bankWindowJointBinaryValueCongr
      intro jj
      have _hjjb := jj.isLt
      rw [ho]
      by_cases h2 : jj.val + 1 = k
      · rw [hsiteE (jj.val + 1) h2]
        exact hNeb
      · by_cases h1 : jj.val + 1 = k + 1
        · rw [hsiteD (jj.val + 1) h1]
          exact hNdb
        · rw [(hoff (jj.val + 1) (by omega) h2 h1).1]
    apply bankWindowOverlapStableIwaitMovedRootFieldsAt ring hn hbank seed pre
      e root hJ hnonroot hstable hforeign hmodeOld hctrlOld
      (ring.rightNeighbor e) (Or.inr rfl) jk' hdk' hcne e
      (ring.rightNeighbor e) (Or.inl ⟨rfl, rfl⟩) o p ho horig hwNe hwNd
    refine ⟨honlyN, Or.inr ⟨hNe, ?_, ?_⟩⟩
    · rw [hval]
      exact hheads
    · rw [hval]
      exact hK

/-- Any reference whose root satisfies the eleven source-owned clauses
of bankWindowOverlapSourceOwnClauses (textually clauses 1-11 of
BankWindowRootFieldsAt; bankWindowOverlapSourceActiveOwnerFields and
bankWindowOverlapSourceCountingOwnFields have the same body) together with
the proto and orphan clauses satisfies BankWindowRootFieldsAt.
Consumer: the M2 SRC wrappers below. -/
theorem bankWindowRootFieldsAtOfSourceOwnClauses {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n) (root : Fin n)
    (hown : bankWindowOverlapSourceOwnClauses ring r root)
    (hproto : ∀ limit : Nat, BankWindowProtoRun ring r root limit →
      BankWindowRootForeignProtoField ring r root limit)
    (horphan : ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowOrphanOwner ring r root j →
      BankWindowTainted r (Counter.site ring root (j.val + 1)) →
      (r.1 root).mode = .RESET ∨
        ((r.1 root).mode = .RWAIT ∧
          (r.2.sites root).controller = .waiting [])) :
    BankWindowRootFieldsAt ring r root := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hown
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hproto, horphan⟩

/-- M2 SRC, complete OLD window: the selected PACK-zero source root e with
a complete OLD window has no POST proto run and no POST orphan
(bankWindowOverlapSelectedCompleteSourceNoPrefixOrphan), so the eleven
source-owned clauses give every root-indexed POST clause.
Consumer: the M2 SRC wrappers below. -/
theorem bankWindowOverlapSourceCompleteRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n)) (e : Fin n)
    (hcomplete : Counter.Complete ring (rbRun ring (renewalBankStart ring seed) pre).1 e)
    (hown : bankWindowOverlapSourceOwnClauses ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  have hno := bankWindowOverlapSelectedCompleteSourceNoPrefixOrphan ring hn
    seed pre e hcomplete
  exact bankWindowRootFieldsAtOfSourceOwnClauses ring _ e hown
    (fun limit hrun => absurd hrun (hno.1 limit))
    (fun j howner _ => absurd howner (hno.2 j))

/-- M2 SRC, RESET launch: every root-indexed POST clause at the selected
PACK-zero source root e. The eleven non-proto/non-orphan clauses are the
Root row bankWindowOverlapSourceOwnResetLaunch; the OLD window is complete (scope), so bankWindowOverlapSelectedCompleteSourceNoPrefixOrphan rules out every POST proto run and orphan.
Consumer: the final bankWindowExactStep case split, SRC own root (ledger
row M2). -/
theorem bankWindowOverlapSourceResetLaunchRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hscope : BankWindowScope ring (rbRun ring (renewalBankStart ring seed) pre) e)
    (hreset : ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .RESET) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  exact bankWindowOverlapSourceCompleteRootFieldsAt ring hn seed pre e
    hscope.1
    (bankWindowOverlapSourceOwnResetLaunch ring hn hbank seed pre e hJ hscope hreset)

/-- M2 SRC, RWAIT non-return expiry: every root-indexed POST clause at the selected
PACK-zero source root e. The eleven non-proto/non-orphan clauses are the
Root row bankWindowOverlapSourceOwnRwaitNonreturnExpiry; the OLD window is complete (scope), so bankWindowOverlapSelectedCompleteSourceNoPrefixOrphan rules out every POST proto run and orphan.
Consumer: the final bankWindowExactStep case split, SRC own root (ledger
row M2). -/
theorem bankWindowOverlapSourceRwaitNonreturnExpiryRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hscope : BankWindowScope ring (rbRun ring (renewalBankStart ring seed) pre) e)
    (hmode : ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .RWAIT)
    (htok : ((rbRun ring (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)).tok = .E)
    (hlease : ((rbRun ring (renewalBankStart ring seed) pre).1 e).lease.val ≤ 1) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  exact bankWindowOverlapSourceCompleteRootFieldsAt ring hn seed pre e
    hscope.1
    (bankWindowOverlapSourceOwnRwaitNonreturnExpiry ring hn hbank seed pre e hJ hscope hmode htok hlease)

/-- M2 SRC, ARMED A0: every root-indexed POST clause at the selected
PACK-zero source root e. The eleven non-proto/non-orphan clauses are the
Root row bankWindowOverlapSourceActiveArmedSetFields; the OLD window is complete (scope), so bankWindowOverlapSelectedCompleteSourceNoPrefixOrphan rules out every POST proto run and orphan.
Consumer: the final bankWindowExactStep case split, SRC own root (ledger
row M2). -/
theorem bankWindowOverlapSourceArmedSetRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (rbRun ring (renewalBankStart ring seed) pre))
    (hscope : BankWindowScope ring
      (rbRun ring (renewalBankStart ring seed) pre) e)
    (hm :
      ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .ARMED)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hactive :
      ((rbRun ring (renewalBankStart ring seed) pre).2.sites e).controller =
        .active p)
    (horigin : p.origin = some o)
    (hbit :
      ((rbRun ring (renewalBankStart ring seed) pre).1
        (ring.rightNeighbor e)).bit = false) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  exact bankWindowOverlapSourceCompleteRootFieldsAt ring hn seed pre e
    hscope.1
    (bankWindowOverlapSourceActiveArmedSetFields ring hn hbank seed pre e hJ hscope hm p o hactive horigin hbit)

/-- M2 SRC, ARMED A0, genuine controller: every root-indexed POST clause at the selected
PACK-zero source root e. The eleven non-proto/non-orphan clauses are the
Root row bankWindowOverlapSourceActiveArmedSetGenuineFields; OLD J.proto forces the OLD window complete (bankWindowOverlapSourceActiveGenuineComplete), so no POST proto run or orphan exists.
Consumer: the final bankWindowExactStep case split, SRC own root (ledger
row M2). -/
theorem bankWindowOverlapSourceArmedSetGenuineRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (rbRun ring (renewalBankStart ring seed) pre))
    (hx : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val = 0)
    (hg : ((rbRun ring (renewalBankStart ring seed) pre).1 e).grant = false)
    (hm : ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .ARMED)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hactive :
      ((rbRun ring (renewalBankStart ring seed) pre).2.sites e).controller =
        .active p)
    (horigin : p.origin = some o)
    (hbit :
      ((rbRun ring (renewalBankStart ring seed) pre).1
        (ring.rightNeighbor e)).bit = false) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  exact bankWindowOverlapSourceCompleteRootFieldsAt ring hn seed pre e
    (bankWindowOverlapSourceActiveGenuineComplete ring (rbRun ring (renewalBankStart ring seed) pre) e hJ hx p o
      hactive horigin)
    (bankWindowOverlapSourceActiveArmedSetGenuineFields ring hn hbank seed pre e hJ hx hg hm p o hactive horigin hbit)

/-- M2 SRC, ARMED A1: every root-indexed POST clause at the selected
PACK-zero source root e. The eleven non-proto/non-orphan clauses are the
Root row bankWindowOverlapSourceActiveArmedIssueFields; the OLD window is complete (scope), so bankWindowOverlapSelectedCompleteSourceNoPrefixOrphan rules out every POST proto run and orphan.
Consumer: the final bankWindowExactStep case split, SRC own root (ledger
row M2). -/
theorem bankWindowOverlapSourceArmedIssueRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (rbRun ring (renewalBankStart ring seed) pre))
    (hscope : BankWindowScope ring
      (rbRun ring (renewalBankStart ring seed) pre) e)
    (hm :
      ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .ARMED)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hactive :
      ((rbRun ring (renewalBankStart ring seed) pre).2.sites e).controller =
        .active p)
    (horigin : p.origin = some o)
    (hbit :
      ((rbRun ring (renewalBankStart ring seed) pre).1
        (ring.rightNeighbor e)).bit = true) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  exact bankWindowOverlapSourceCompleteRootFieldsAt ring hn seed pre e
    hscope.1
    (bankWindowOverlapSourceActiveArmedIssueFields ring hn hbank seed pre e hJ hscope hm p o hactive horigin hbit)

/-- M2 SRC, ARMED A1, genuine controller: every root-indexed POST clause at the selected
PACK-zero source root e. The eleven non-proto/non-orphan clauses are the
Root row bankWindowOverlapSourceActiveArmedIssueGenuineFields; OLD J.proto forces the OLD window complete (bankWindowOverlapSourceActiveGenuineComplete), so no POST proto run or orphan exists.
Consumer: the final bankWindowExactStep case split, SRC own root (ledger
row M2). -/
theorem bankWindowOverlapSourceArmedIssueGenuineRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (rbRun ring (renewalBankStart ring seed) pre))
    (hx : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val = 0)
    (hg : ((rbRun ring (renewalBankStart ring seed) pre).1 e).grant = false)
    (hm : ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .ARMED)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hactive :
      ((rbRun ring (renewalBankStart ring seed) pre).2.sites e).controller =
        .active p)
    (horigin : p.origin = some o)
    (hbit :
      ((rbRun ring (renewalBankStart ring seed) pre).1
        (ring.rightNeighbor e)).bit = true) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  exact bankWindowOverlapSourceCompleteRootFieldsAt ring hn seed pre e
    (bankWindowOverlapSourceActiveGenuineComplete ring (rbRun ring (renewalBankStart ring seed) pre) e hJ hx p o
      hactive horigin)
    (bankWindowOverlapSourceActiveArmedIssueGenuineFields ring hn hbank seed pre e hJ hx hg hm p o hactive horigin hbit)

/-- M2 SRC, CSTART issue: every root-indexed POST clause at the selected
PACK-zero source root e. The eleven non-proto/non-orphan clauses are the
Root row bankWindowOverlapSourceActiveCstartIssueFields; the OLD window is complete (scope), so bankWindowOverlapSelectedCompleteSourceNoPrefixOrphan rules out every POST proto run and orphan.
Consumer: the final bankWindowExactStep case split, SRC own root (ledger
row M2). -/
theorem bankWindowOverlapSourceCstartIssueRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (rbRun ring (renewalBankStart ring seed) pre))
    (hscope : BankWindowScope ring
      (rbRun ring (renewalBankStart ring seed) pre) e)
    (hmode :
      ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .CSTART)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hactive :
      ((rbRun ring (renewalBankStart ring seed) pre).2.sites e).controller =
        .active p)
    (horigin : p.origin = some o) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  exact bankWindowOverlapSourceCompleteRootFieldsAt ring hn seed pre e
    hscope.1
    (bankWindowOverlapSourceActiveCstartIssueFields ring hn hbank seed pre e hJ hscope hmode p o hactive horigin)

/-- M2 SRC, CSTART S1: every root-indexed POST clause at the selected
PACK-zero source root e. The eleven non-proto/non-orphan clauses are the
Root row bankWindowOverlapSourceActiveCstartMatchFields; the OLD window is complete (scope), so bankWindowOverlapSelectedCompleteSourceNoPrefixOrphan rules out every POST proto run and orphan.
Consumer: the final bankWindowExactStep case split, SRC own root (ledger
row M2). -/
theorem bankWindowOverlapSourceCstartMatchRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (rbRun ring (renewalBankStart ring seed) pre))
    (hscope : BankWindowScope ring
      (rbRun ring (renewalBankStart ring seed) pre) e)
    (hmode :
      ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .CSTART)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hactive :
      ((rbRun ring (renewalBankStart ring seed) pre).2.sites e).controller =
        .active p)
    (horigin : p.origin = some o)
    (hbit :
      ((rbRun ring (renewalBankStart ring seed) pre).1
        (ring.rightNeighbor e)).bit =
        (compileAdvice (ceilLogTwo n)).theta 0) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  exact bankWindowOverlapSourceCompleteRootFieldsAt ring hn seed pre e
    hscope.1
    ((bankWindowOverlapSourceActiveCstartMatchFields ring hn hbank seed pre e hJ hscope hmode p o hactive horigin hbit).1)

/-- M2 SRC, CSTART S1, genuine controller: every root-indexed POST clause at the selected
PACK-zero source root e. The eleven non-proto/non-orphan clauses are the
Root row bankWindowOverlapSourceActiveCstartMatchGenuineFields; OLD J.proto forces the OLD window complete (bankWindowOverlapSourceActiveGenuineComplete), so no POST proto run or orphan exists.
Consumer: the final bankWindowExactStep case split, SRC own root (ledger
row M2). -/
theorem bankWindowOverlapSourceCstartMatchGenuineRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (rbRun ring (renewalBankStart ring seed) pre))
    (hx : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val = 0)
    (hg : ((rbRun ring (renewalBankStart ring seed) pre).1 e).grant = false)
    (hm : ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .CSTART)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hactive :
      ((rbRun ring (renewalBankStart ring seed) pre).2.sites e).controller =
        .active p)
    (horigin : p.origin = some o)
    (hbit :
      ((rbRun ring (renewalBankStart ring seed) pre).1
        (ring.rightNeighbor e)).bit =
          (compileAdvice (ceilLogTwo n)).theta 0) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  exact bankWindowOverlapSourceCompleteRootFieldsAt ring hn seed pre e
    (bankWindowOverlapSourceActiveGenuineComplete ring (rbRun ring (renewalBankStart ring seed) pre) e hJ hx p o
      hactive horigin)
    ((bankWindowOverlapSourceActiveCstartMatchGenuineFields ring hn hbank seed pre e hJ hx hg hm p o hactive horigin hbit).1)

/-- M2 SRC, CSTART S0: every root-indexed POST clause at the selected
PACK-zero source root e. The eleven non-proto/non-orphan clauses are the
Root row bankWindowOverlapSourceActiveCstartMismatchFields; the OLD window is complete (scope), so bankWindowOverlapSelectedCompleteSourceNoPrefixOrphan rules out every POST proto run and orphan.
Consumer: the final bankWindowExactStep case split, SRC own root (ledger
row M2). -/
theorem bankWindowOverlapSourceCstartMismatchRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (rbRun ring (renewalBankStart ring seed) pre))
    (hscope : BankWindowScope ring
      (rbRun ring (renewalBankStart ring seed) pre) e)
    (hmode :
      ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .CSTART)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hactive :
      ((rbRun ring (renewalBankStart ring seed) pre).2.sites e).controller =
        .active p)
    (horigin : p.origin = some o)
    (hbit :
      ((rbRun ring (renewalBankStart ring seed) pre).1
        (ring.rightNeighbor e)).bit ≠
        (compileAdvice (ceilLogTwo n)).theta 0) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  exact bankWindowOverlapSourceCompleteRootFieldsAt ring hn seed pre e
    hscope.1
    ((bankWindowOverlapSourceActiveCstartMismatchFields ring hn hbank seed pre e hJ hscope hmode p o hactive horigin hbit).1)

/-- M2 SRC, CSTART S0, genuine controller: every root-indexed POST clause at the selected
PACK-zero source root e. The eleven non-proto/non-orphan clauses are the
Root row bankWindowOverlapSourceActiveCstartMismatchGenuineFields; OLD J.proto forces the OLD window complete (bankWindowOverlapSourceActiveGenuineComplete), so no POST proto run or orphan exists.
Consumer: the final bankWindowExactStep case split, SRC own root (ledger
row M2). -/
theorem bankWindowOverlapSourceCstartMismatchGenuineRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (rbRun ring (renewalBankStart ring seed) pre))
    (hx : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val = 0)
    (hg : ((rbRun ring (renewalBankStart ring seed) pre).1 e).grant = false)
    (hm : ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .CSTART)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hactive :
      ((rbRun ring (renewalBankStart ring seed) pre).2.sites e).controller =
        .active p)
    (horigin : p.origin = some o)
    (hbit :
      ((rbRun ring (renewalBankStart ring seed) pre).1
        (ring.rightNeighbor e)).bit ≠
          (compileAdvice (ceilLogTwo n)).theta 0) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  exact bankWindowOverlapSourceCompleteRootFieldsAt ring hn seed pre e
    (bankWindowOverlapSourceActiveGenuineComplete ring (rbRun ring (renewalBankStart ring seed) pre) e hJ hx p o
      hactive horigin)
    ((bankWindowOverlapSourceActiveCstartMismatchGenuineFields ring hn hbank seed pre e hJ hx hg hm p o hactive horigin hbit).1)

/-- M2 SRC, IWAIT I0 (matched AL return): every root-indexed POST clause at the selected
PACK-zero source root e. The eleven non-proto/non-orphan clauses are the
Root row bankWindowOverlapSourceCountingIwaitAlOwnFields; the OLD window is complete (scope), so bankWindowOverlapSelectedCompleteSourceNoPrefixOrphan rules out every POST proto run and orphan.
Consumer: the final bankWindowExactStep case split, SRC own root (ledger
row M2). -/
theorem bankWindowOverlapSourceIwaitAlRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (rbRun ring (renewalBankStart ring seed) pre))
    (hscope : BankWindowScope ring
      (rbRun ring (renewalBankStart ring seed) pre) e)
    (hm : ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .IWAIT)
    (hwait :
      ((rbRun ring (renewalBankStart ring seed) pre).2.sites e).controller =
        .waiting [])
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hw : ((rbRun ring (renewalBankStart ring seed) pre).2.sites
      (ring.rightNeighbor e)).worker = .payload p)
    (ho : p.origin = some o)
    (hroot : o.root = e)
    (ht : ((rbRun ring (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)).tok = .AL) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  exact bankWindowOverlapSourceCompleteRootFieldsAt ring hn seed pre e
    hscope.1
    (bankWindowOverlapSourceCountingIwaitAlOwnFields ring hn hbank seed pre e hJ hscope hm hwait p o hw ho hroot ht)

/-- M2 SRC, IWAIT I1 timeout: every root-indexed POST clause at the selected
PACK-zero source root e. The eleven non-proto/non-orphan clauses are the
Root row bankWindowOverlapSourceCountingIwaitExpiredOwnFields; the OLD window is complete (scope), so bankWindowOverlapSelectedCompleteSourceNoPrefixOrphan rules out every POST proto run and orphan.
Consumer: the final bankWindowExactStep case split, SRC own root (ledger
row M2). -/
theorem bankWindowOverlapSourceIwaitExpiredRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (rbRun ring (renewalBankStart ring seed) pre))
    (hscope : BankWindowScope ring
      (rbRun ring (renewalBankStart ring seed) pre) e)
    (hm : ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .IWAIT)
    (ht : ((rbRun ring (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)).tok = .E)
    (hl : ((rbRun ring (renewalBankStart ring seed) pre).1 e).lease.val ≤ 1) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  exact bankWindowOverlapSourceCompleteRootFieldsAt ring hn seed pre e
    hscope.1
    (bankWindowOverlapSourceCountingIwaitExpiredOwnFields ring hn hbank seed pre e hJ hscope hm ht hl)

/-- M2 SRC, CWAIT CL1: every root-indexed POST clause at the selected
PACK-zero source root e. The eleven non-proto/non-orphan clauses are the
Root row bankWindowOverlapSourceCountingCwaitClOneOwnFields; the OLD window is complete (scope), so bankWindowOverlapSelectedCompleteSourceNoPrefixOrphan rules out every POST proto run and orphan.
Consumer: the final bankWindowExactStep case split, SRC own root (ledger
row M2). -/
theorem bankWindowOverlapSourceCwaitClOneRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (rbRun ring (renewalBankStart ring seed) pre))
    (hscope : BankWindowScope ring
      (rbRun ring (renewalBankStart ring seed) pre) e)
    (hm : ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .CWAIT)
    (ht : ((rbRun ring (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)).tok = .CL1) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  exact bankWindowOverlapSourceCompleteRootFieldsAt ring hn seed pre e
    hscope.1
    (bankWindowOverlapSourceCountingCwaitClOneOwnFields ring hn hbank seed pre e hJ hscope hm ht)

/-- M2 SRC, CWAIT timeout: every root-indexed POST clause at the selected
PACK-zero source root e. The eleven non-proto/non-orphan clauses are the
Root row bankWindowOverlapSourceCountingCwaitExpiredOwnFields; the OLD window is complete (scope), so bankWindowOverlapSelectedCompleteSourceNoPrefixOrphan rules out every POST proto run and orphan.
Consumer: the final bankWindowExactStep case split, SRC own root (ledger
row M2). -/
theorem bankWindowOverlapSourceCwaitExpiredRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (rbRun ring (renewalBankStart ring seed) pre))
    (hscope : BankWindowScope ring
      (rbRun ring (renewalBankStart ring seed) pre) e)
    (hm : ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .CWAIT)
    (ht : ((rbRun ring (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)).tok = .E)
    (hl : ((rbRun ring (renewalBankStart ring seed) pre).1 e).lease.val ≤ 1) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  exact bankWindowOverlapSourceCompleteRootFieldsAt ring hn seed pre e
    hscope.1
    (bankWindowOverlapSourceCountingCwaitExpiredOwnFields ring hn hbank seed pre e hJ hscope hm ht hl)

/-- M2 SRC, IWAIT/CWAIT timeout: every root-indexed POST clause at the selected
PACK-zero source root e. The eleven non-proto/non-orphan clauses are the
Root row bankWindowOverlapSourceCountingTimedOutOwnFields; the OLD window is complete (scope), so bankWindowOverlapSelectedCompleteSourceNoPrefixOrphan rules out every POST proto run and orphan.
Consumer: the final bankWindowExactStep case split, SRC own root (ledger
row M2). -/
theorem bankWindowOverlapSourceWaitTimedOutRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (rbRun ring (renewalBankStart ring seed) pre))
    (hscope : BankWindowScope ring
      (rbRun ring (renewalBankStart ring seed) pre) e)
    (hm :
      ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .IWAIT ∨
      ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .CWAIT)
    (ht :
      ((rbRun ring (renewalBankStart ring seed) pre).1
        (ring.rightNeighbor e)).tok = .E)
    (hl : ((rbRun ring (renewalBankStart ring seed) pre).1 e).lease.val ≤ 1) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  exact bankWindowOverlapSourceCompleteRootFieldsAt ring hn seed pre e
    hscope.1
    (bankWindowOverlapSourceCountingTimedOutOwnFields ring hn hbank seed pre e hJ hscope hm ht hl)

/-- M2 SRC, ARMED/CSTART collision: every root-indexed POST clause at the selected
PACK-zero source root e. The eleven non-proto/non-orphan clauses are the
Root row bankWindowOverlapSourceActiveCollisionFields; proto and orphan come from the M3 row bankWindowOverlapActiveCollisionPrefixOrphan on the same hypotheses.
Consumer: the final bankWindowExactStep case split, SRC own root (ledger
row M2). -/
theorem bankWindowOverlapSourceActiveCollisionRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (rbRun ring (renewalBankStart ring seed) pre))
    (hx : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val = 0)
    (hy : ((rbRun ring (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)).pack.val = 1)
    (hg : ((rbRun ring (renewalBankStart ring seed) pre).1 e).grant = false)
    (hphase :
      ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .ARMED ∨
      ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .CSTART)
    (hret : isRetTok ((rbRun ring (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)).tok = false)
    (htok : ((rbRun ring (renewalBankStart ring seed) pre).1
      (ring.rightNeighbor e)).tok ≠ .E) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  obtain ⟨hproto, horphan⟩ := bankWindowOverlapActiveCollisionPrefixOrphan ring
    hn hbank seed pre e hJ hx hy hg hphase hret htok
  exact bankWindowRootFieldsAtOfSourceOwnClauses ring _ e
    (bankWindowOverlapSourceActiveCollisionFields ring hn hbank seed pre e hJ hx hy hg hphase hret htok) hproto horphan

/-- M2 SRC, inherited active row, OLD window complete: every root-indexed POST clause at the selected
PACK-zero source root e. The eleven non-proto/non-orphan clauses are the
Root row bankWindowOverlapSourceActiveCleanOwnerFields; with the OLD window complete there is no POST proto run or orphan.
Consumer: the final bankWindowExactStep case split, SRC own root (ledger
row M2). -/
theorem bankWindowOverlapSourceCleanCompleteRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hphase :
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).mode = .CSTART ∨
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).mode = .IWAIT ∨
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).mode = .CWAIT)
    (hclean :
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        ¬ BankWindowTainted
          (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
          (Counter.site ring e (j.val + 1)))
    (hnoActive :
      ∀ (q : RenewalBankPayload n) (o : RenewalBankOrigin n),
        ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites e).controller =
          .active q → q.origin = some o → False)
    (hcomplete : Counter.Complete ring (rbRun ring (renewalBankStart ring seed) pre).1 e) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  exact bankWindowOverlapSourceCompleteRootFieldsAt ring hn seed pre e
    hcomplete (bankWindowOverlapSourceActiveCleanOwnerFields ring hn hbank seed pre e hphase hclean hnoActive)

/-- M2 SRC, inherited active row, OLD window incomplete, ARMED/CSTART facing E: every root-indexed POST clause at the selected
PACK-zero source root e. The eleven non-proto/non-orphan clauses are the
Root row bankWindowOverlapSourceActiveCleanOwnerFields; proto and orphan come from the M3 row bankWindowOverlapSourceActiveEmptyPrefixOrphan (OLD incomplete, ARMED/CSTART, responder token E); InheritedArmedMemory is the cell lemma behind the inherited ARMED case of the clean hypotheses.
Consumer: the final bankWindowExactStep case split, SRC own root (ledger
row M2). -/
theorem bankWindowOverlapSourceCleanEmptyRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hphase :
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).mode = .CSTART ∨
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).mode = .IWAIT ∨
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).mode = .CWAIT)
    (hclean :
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        ¬ BankWindowTainted
          (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
          (Counter.site ring e (j.val + 1)))
    (hnoActive :
      ∀ (q : RenewalBankPayload n) (o : RenewalBankOrigin n),
        ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites e).controller =
          .active q → q.origin = some o → False)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hnot : ¬ Counter.Complete ring (rbRun ring (renewalBankStart ring seed) pre).1 e)
    (hx : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val = 0)
    (hy : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val = 1)
    (hg : ((rbRun ring (renewalBankStart ring seed) pre).1 e).grant = false)
    (hphaseOld : ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .ARMED ∨
      ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .CSTART)
    (ht : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .E) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  obtain ⟨hproto, horphan⟩ := bankWindowOverlapSourceActiveEmptyPrefixOrphan ring
    hn hbank seed pre e hJ hnot hx hy hg hphaseOld ht
  exact bankWindowRootFieldsAtOfSourceOwnClauses ring _ e
    (bankWindowOverlapSourceActiveCleanOwnerFields ring hn hbank seed pre e hphase hclean hnoActive) hproto horphan

/-- A foreign root whose window does not have both stepped endpoints
outside it is incident to the step: the source is some site of the
window (Counter.Support).
Consumer: bankWindowExactStepOfSourceRoot (repair edges, M5). -/
theorem bankWindowJointSupportOfNotOutside {n : Nat} (ring : DirectedRing n)
    (root e : Fin n)
    (hout : ¬ Counter.OutsideSites (ceilLogTwo n) ring root e) :
    Counter.Support (ceilLogTwo n) ring root e := by
  unfold Counter.OutsideSites at hout
  unfold Counter.Support
  apply Classical.byContradiction
  intro hno
  apply hout
  intro j hj
  constructor
  · intro he
    exact hno (Or.inr ⟨j, hj, he⟩)
  · intro he
    cases j with
    | zero => exact hno (Or.inl he)
    | succ j =>
        exact hno (Or.inr ⟨j, by omega,
          bankWindowJointSuccessorInjective ring e (Counter.site ring root j) he⟩)

/-- A foreign root (distinct from both stepped endpoints) whose window does
not have both endpoints outside it has the source at one of its digits:
e = D(k) with 1 <= k <= b.
Consumer: bankWindowOverlapStableForeignRootFieldsAt. -/
theorem bankWindowJointDigitOfNotOutside {n : Nat} (ring : DirectedRing n)
    (root e : Fin n)
    (hforeign : root ≠ e ∧ root ≠ ring.rightNeighbor e)
    (hout : ¬ Counter.OutsideSites (ceilLogTwo n) ring root e) :
    ∃ k : Nat, 1 ≤ k ∧ k ≤ (compileAdvice (ceilLogTwo n)).b ∧
      e = Counter.site ring root k := by
  unfold Counter.OutsideSites at hout
  apply Classical.byContradiction
  intro hno
  apply hout
  intro j hj
  constructor
  · intro he
    cases j with
    | zero => exact hforeign.1 he.symm
    | succ j => exact hno ⟨j + 1, by omega, hj, he⟩
  · intro he
    cases j with
    | zero => exact hforeign.2 he.symm
    | succ j =>
        have he' : e = Counter.site ring root j :=
          bankWindowJointSuccessorInjective ring e (Counter.site ring root j) he
        cases j with
        | zero => exact hforeign.1 he'.symm
        | succ j => exact hno ⟨j + 1, by omega, by omega, he'⟩

/-- M6, POST-incomplete CWAIT root: a foreign CWAIT root (any
controller) on a stable nonroot edge whose POST window is incomplete
satisfies every root-indexed POST clause. The comparator clauses are
vacuous because a POST comparator worker in CWAIT would make the window
complete (bankWindowOverlapStableNonrootPhaseFields); compareExact is
vacuous because a genuine worker under waiting [] comes (pair inheritance
or frame) from an (rbRun ring (renewalBankStart ring seed) pre) genuine worker, which (rbRun ring (renewalBankStart ring seed) pre) compareExact makes a
comparator and (rbRun ring (renewalBankStart ring seed) pre) phaseComplete then makes the (rbRun ring (renewalBankStart ring seed) pre) window complete,
hence the POST window too (PACK frame); scope-guarded clauses are vacuous.
Consumer: bankWindowOverlapStableForeignRootFieldsAt (incomplete INT/TOP
CWAIT roots). -/
theorem bankWindowOverlapStableIncompleteCwaitRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hnonroot : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ≠ 0)
    (hstable :
      packNext ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val)
    (hforeign : root ≠ e ∧ root ≠ ring.rightNeighbor e)
    (hnot : ¬ Counter.Complete ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 root)
    (hmodeOld : ((rbRun ring (renewalBankStart ring seed) pre).1 root).mode = .CWAIT) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) root := by
  have hphase := bankWindowOverlapStableNonrootPhaseFields ring hn hbank
    seed pre e root hJ hnonroot hstable hforeign
  have hjoint := bankWindowOverlapRootJointFields ring hn hbank seed pre e hJ
  have hpackAll := bankWindowOverlapStablePackFrame ring hn seed pre e hstable
  have hroot := bankWindowExactOffPairAtomicReads ring (rbRun ring (renewalBankStart ring seed) pre) e root
    hforeign.1 hforeign.2
  have hctrlR := hroot.2.2.2.2.2.2
  unfold bankWindowReadController at hctrlR
  have hf := rbReferenceSelectedPairFrame ring (by omega : 2 ≤ n) (rbRun ring (renewalBankStart ring seed) pre) e
  have hnoComp : ∀ (o : RenewalBankOrigin n) (i : Fin n)
      (p : RenewalBankPayload n), o.root = root →
      BankComparatorOriginWorker ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) o i p →
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 o.root).mode = .CWAIT → False := by
    intro o i p ho hw hm
    apply hnot
    have h := hphase.2 o i p ho hw hm
    rw [ho] at h
    exact h
  have hnoScope : BankWindowScope ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) root → False := fun hs => hnot hs.1
  have hnoGen : ∀ (o : RenewalBankOrigin n) (i : Fin n)
      (p : RenewalBankPayload n), o.root = root →
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites i).worker = .payload p → p.origin = some o →
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites o.root).controller = .waiting [] → False := by
    intro o i p ho hw horig hc
    have hold : ∃ i' : Fin n, ((rbRun ring (renewalBankStart ring seed) pre).2.sites i').worker = .payload p := by
      by_cases hi : i = e ∨ i = ring.rightNeighbor e
      · have hp : (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
              (rbRun ring (renewalBankStart ring seed) pre).2 e (ring.rightNeighbor e)
              ((rbRun ring (renewalBankStart ring seed) pre).1 e) ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e))).1.worker = .payload p ∨
            (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
              (rbRun ring (renewalBankStart ring seed) pre).2 e (ring.rightNeighbor e)
              ((rbRun ring (renewalBankStart ring seed) pre).1 e) ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e))).2.worker = .payload p := by
          rcases hi with hi | hi
          · rw [hi] at hw
            have h := congrArg (fun s : RenewalBankSite n => s.worker) hf.2.2.1
            exact Or.inl (h.symm.trans hw)
          · rw [hi] at hw
            have h := congrArg (fun s : RenewalBankSite n => s.worker) hf.2.2.2
            exact Or.inr (h.symm.trans hw)
        rcases rbBankNonrootSelectedWorkersInherited
            (compileAdvice (ceilLogTwo n)) (rbRun ring (renewalBankStart ring seed) pre).2 e (ring.rightNeighbor e)
            ((rbRun ring (renewalBankStart ring seed) pre).1 e) ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)) hnonroot p hp with h | h
        · exact ⟨e, h⟩
        · exact ⟨ring.rightNeighbor e, h⟩
      · have hfi := bankWindowExactOffPairFrame ring (rbRun ring (renewalBankStart ring seed) pre) e i
          (fun h => hi (Or.inl h)) (fun h => hi (Or.inr h))
        refine ⟨i, ?_⟩
        rw [← hfi.2]
        exact hw
    obtain ⟨i', hw'⟩ := hold
    have hm' : ((rbRun ring (renewalBankStart ring seed) pre).1 o.root).mode = .CWAIT := by
      rw [ho]
      exact hmodeOld
    have hc' : ((rbRun ring (renewalBankStart ring seed) pre).2.sites o.root).controller = .waiting [] := by
      rw [ho] at hc ⊢
      exact hctrlR.symm.trans hc
    obtain ⟨_, hlive, _, _⟩ := hJ.compareExact o i' p hw' horig hm' hc'
    have hcO := hJ.phaseComplete o i' p ⟨hw', horig, hlive⟩ hm'
    rw [ho] at hcO
    apply hnot
    intro j hj
    rw [hpackAll]
    exact hcO j hj
  refine ⟨hphase.1, hphase.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o i p ho hw hm
    exact (hnoComp o i p ho hw hm).elim
  · intro o i p ho hw hm
    exact (hnoComp o i p ho hw hm).elim
  · intro hs
    exact (hnoScope hs).elim
  · intro hs
    exact (hnoScope hs).elim
  · intro _ _ hs
    exact (hnoScope hs).elim
  · intro _ _ _ hs
    exact (hnoScope hs).elim
  · intro o i p ho hw horig _ hc
    exact (hnoGen o i p ho hw horig hc).elim
  · intro hs
    exact (hnoScope hs).elim
  · intro hs
    exact (hnoScope hs).elim
  · intro limit hrun
    exact hjoint.2.2.2.1 root limit hforeign hrun
  · intro j
    exact hjoint.2.2.2.2 root j hforeign

/-- M6 dispatcher: every foreign root on a stable edge from a nonroot
source. Outside the window: bankWindowOverlapOutsideRootFieldsAt. POST
window incomplete: out of scope (M6-P) or incomplete CWAIT. Complete
window with the source at the top digit: M6-T. Interior digit D(k),
1 <= k < b: POST RESET (foreign reset row); out of POST scope (M6-P, or
CWAIT with waiting [] / nonempty waiting list: M6-Q CWAIT / M6-S); in
scope with an inherited controller (interior inherited row); a genuine
ARMED/CSTART root has an all-E window ((rbRun ring (renewalBankStart ring seed) pre) armedExact), hence untainted
(interior untainted row); RWAIT/IWAIT/CWAIT with waiting [] (M6-Q).
Consumer: bankWindowExactStepOfSourceRoot (foreign roots, stable edge,
nonroot source). -/
theorem bankWindowOverlapStableForeignRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hnonroot : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ≠ 0)
    (hstable :
      packNext ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val)
    (hforeign : root ≠ e ∧ root ≠ ring.rightNeighbor e) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) root := by
  have hpackAll := bankWindowOverlapStablePackFrame ring hn seed pre e hstable
  by_cases hout : Counter.OutsideSites (ceilLogTwo n) ring root e
  · exact bankWindowOverlapOutsideRootFieldsAt ring hn hbank seed pre e hJ
      root hout
  by_cases hcN : Counter.Complete ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 root
  case neg =>
    by_cases hmc : ((rbRun ring (renewalBankStart ring seed) pre).1 root).mode = .CWAIT
    · exact bankWindowOverlapStableIncompleteCwaitRootFieldsAt ring hn hbank
        seed pre e root hJ hnonroot hstable hforeign hcN hmc
    · exact bankWindowOverlapStableNonrootOutOfScopeRootFieldsAt ring hn
        hbank seed pre e root hJ hnonroot hstable hforeign
        (fun hs => hcN hs.1) hmc
  have hcO : Counter.Complete ring (rbRun ring (renewalBankStart ring seed) pre).1 root := by
    intro j hj
    rw [← hpackAll]
    exact hcN j hj
  obtain ⟨k, hk1, hkb, hsite⟩ :=
    bankWindowJointDigitOfNotOutside ring root e hforeign hout
  by_cases htop : k = (compileAdvice (ceilLogTwo n)).b
  · exact bankWindowOverlapTopGhostStableRootFieldsAt ring hn hbank seed pre
      e root hJ hcO (by rw [hsite, htop]) hstable
  have hkb' : k < (compileAdvice (ceilLogTwo n)).b := by omega
  have hroot := bankWindowExactOffPairAtomicReads ring (rbRun ring (renewalBankStart ring seed) pre) e root
    hforeign.1 hforeign.2
  have hmodeR := hroot.2.1
  have hctrlR := hroot.2.2.2.2.2.2
  have hgrantR := hroot.2.2.2.2.1
  unfold bankWindowReadMode at hmodeR
  unfold bankWindowReadController at hctrlR
  unfold bankWindowReadGrant at hgrantR
  by_cases hreset : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 root).mode = .RESET
  · exact bankWindowOverlapForeignResetRootFieldsAt ring hn hbank seed pre
      e root hJ hforeign hreset
  have hshape := (hJ.frame root).1
  unfold bankInFlightControllerShape at hshape
  rw [if_pos (show ((rbRun ring (renewalBankStart ring seed) pre).1 root).pack.val = 0 from
    hcO 0 (by omega))] at hshape
  by_cases hs : BankWindowScope ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) root
  case neg =>
    by_cases hmc : ((rbRun ring (renewalBankStart ring seed) pre).1 root).mode = .CWAIT
    · rw [hmc] at hshape
      obtain ⟨atoms, hatoms⟩ := hshape
      cases atoms with
      | nil =>
          exact bankWindowOverlapStableCwaitRootFieldsAt ring hn hbank seed
            pre e root hJ hnonroot hstable hforeign k hk1 hkb' hsite hmc hatoms
      | cons a as =>
          exact bankWindowOverlapStableCwaitWaitingRootFieldsAt ring hn hbank
            seed pre e root hJ hnonroot hstable hforeign hs hmc (a :: as) hatoms
            (List.cons_ne_nil a as)
    · exact bankWindowOverlapStableNonrootOutOfScopeRootFieldsAt ring hn
        hbank seed pre e root hJ hnonroot hstable hforeign hs hmc
  by_cases hinh : BankWindowInheritedController (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) root
  · exact bankWindowOverlapStableInteriorInheritedRootFieldsAt ring hn hbank
      seed pre e root hJ hnonroot hstable hforeign k hk1 hkb' hsite hs hinh
  have hscopeOld : BankWindowScope ring (rbRun ring (renewalBankStart ring seed) pre) root := by
    refine ⟨hcO, ?_⟩
    rw [← hgrantR]
    exact hs.2
  have hwaitNil : ∀ atoms : List (RenewalBankAtom n),
      ((rbRun ring (renewalBankStart ring seed) pre).2.sites root).controller = .waiting atoms → atoms = [] := by
    intro atoms hc
    cases atoms with
    | nil => rfl
    | cons a as =>
        exact (hinh (Or.inl ⟨a :: as, hctrlR.trans hc,
          List.cons_ne_nil a as⟩)).elim
  have hactiveCase : (((rbRun ring (renewalBankStart ring seed) pre).1 root).mode = .ARMED ∨
      ((rbRun ring (renewalBankStart ring seed) pre).1 root).mode = .CSTART) →
      (∃ p : RenewalBankPayload n, ((rbRun ring (renewalBankStart ring seed) pre).2.sites root).controller = .active p) →
      BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) root := by
    intro hm hex
    obtain ⟨p, hp⟩ := hex
    cases horig : p.origin with
    | none =>
        exact (hinh (Or.inr ⟨p, hctrlR.trans hp, horig⟩)).elim
    | some o =>
        have htok := (hJ.armedExact root o p hscopeOld hm hp horig).1
        apply bankWindowOverlapStableInteriorUntaintedRootFieldsAt ring hn
          hbank seed pre e root hJ hnonroot hstable hforeign k hk1 hkb' hsite
        intro j ht
        have hw := (hJ.frame (Counter.site ring root (j.val + 1))).2
        rw [htok j] at hw
        simp only [bankInFlightWorkerShape] at hw
        unfold BankWindowTainted at ht
        rcases ht with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> rw [hw] at h <;> cases h
  cases hmo : ((rbRun ring (renewalBankStart ring seed) pre).1 root).mode with
  | RESET => exact (hreset (hmodeR.trans hmo)).elim
  | ARMED =>
      rw [hmo] at hshape
      exact hactiveCase (Or.inl hmo) hshape
  | CSTART =>
      rw [hmo] at hshape
      exact hactiveCase (Or.inr hmo) hshape
  | RWAIT =>
      rw [hmo] at hshape
      obtain ⟨atoms, hc⟩ := hshape
      rw [hwaitNil atoms hc] at hc
      exact bankWindowOverlapStableRwaitRootFieldsAt ring hn hbank seed pre
        e root hJ hnonroot hstable hforeign k hk1 hkb' hsite hmo hc
  | IWAIT =>
      rw [hmo] at hshape
      obtain ⟨atoms, hc⟩ := hshape
      rw [hwaitNil atoms hc] at hc
      exact bankWindowOverlapStableIwaitRootFieldsAt ring hn hbank seed pre
        e root hJ hnonroot hstable hforeign k hk1 hkb' hsite hmo hc
  | CWAIT =>
      rw [hmo] at hshape
      obtain ⟨atoms, hc⟩ := hshape
      rw [hwaitNil atoms hc] at hc
      exact bankWindowOverlapStableCwaitRootFieldsAt ring hn hbank seed pre
        e root hJ hnonroot hstable hforeign k hk1 hkb' hsite hmo hc

/-- R11 reduction: one BANK step preserves BankWindowExact as soon as the
selected PACK-zero source root has its POST root fields (class SRC,
ledger row M2). Every other root is dispatched here: a nonroot source
(M1), the responder (changed: changed-responder row; stable PACK zero:
M7 incoming row; stable nonzero: M1), foreign roots with a PACK-zero
source (root-source foreign row), outside windows, repair edges (M4,
M5, incomplete repair row) and stable nonroot edges
(bankWindowOverlapStableForeignRootFieldsAt, M6).
Consumer: bankWindowExactStep, once the M2 SRC dispatch is complete. -/
theorem bankWindowExactStepOfSourceRoot {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hsrc : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val = 0 → BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e) :
    BankWindowExact ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) := by
  have hjoint := bankWindowOverlapRootJointFields ring hn hbank seed pre e hJ
  apply bankWindowExactOfRootFields ring _ hjoint.1 hjoint.2.1 hjoint.2.2.1
  intro root
  have hresp := bankWindowExactResponderPack ring (rbRun ring (renewalBankStart ring seed) pre) e
    (clockNeighborDifferent ring (by omega : 2 ≤ n) e)
  by_cases h1 : root = e
  · rw [h1]
    by_cases hx : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val = 0
    · exact hsrc hx
    · exact bankWindowOverlapSourceNonrootRootFieldsAt ring hn hbank seed pre
        e hJ hx
  by_cases h2 : root = ring.rightNeighbor e
  · rw [h2]
    by_cases hch : packNext ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val
        ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
        ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val
    · exact bankWindowOverlapChangedResponderRootFieldsAt ring hn hbank seed
        pre e hJ hch
    have hst : packNext ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val
        ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
        ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val :=
      Classical.byContradiction hch
    by_cases hy : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val = 0
    · exact bankWindowOverlapIncomingStableRootFieldsAt ring hn hbank seed
        pre e hJ hy (by rw [hresp, hst, hy])
    · exact bankWindowOverlapResponderNonrootRootFieldsAt ring hn hbank seed
        pre e hJ (by rw [hresp, hst]; exact hy)
  have hforeign : root ≠ e ∧ root ≠ ring.rightNeighbor e := ⟨h1, h2⟩
  by_cases hx : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val = 0
  · exact bankWindowOverlapRootSourceForeignRootFieldsAt ring hn hbank seed
      pre e hJ hx root hforeign
  by_cases hch : packNext ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val
      ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val
      (compileAdvice (ceilLogTwo n)).b ≠
      ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val
  · by_cases hcN : Counter.Complete ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 root
    · by_cases hcO : Counter.Complete ring (rbRun ring (renewalBankStart ring seed) pre).1 root
      · by_cases hout : Counter.OutsideSites (ceilLogTwo n) ring root e
        · exact bankWindowOverlapOutsideRootFieldsAt ring hn hbank seed pre e
            hJ root hout
        · exact bankWindowOverlapRepairCompleteRootFieldsAt ring hn hbank seed
            pre e root hJ hcO hcN hch
            (bankWindowJointSupportOfNotOutside ring root e hout)
      · exact bankWindowOverlapRepairCompletedForeignRootFieldsAt ring hn
          hbank seed pre e root hJ hx hch hforeign hcN hcO
    · exact bankWindowOverlapRepairIncompleteForeignRootFieldsAt ring hn hbank
        seed pre e root hJ hx hch hforeign hcN
  · exact bankWindowOverlapStableForeignRootFieldsAt ring hn hbank seed pre
      e root hJ hx (Classical.byContradiction hch) hforeign

/-- M2 SRC, RESET launch with an incomplete (rbRun ring (renewalBankStart ring seed) pre) window: the real row puts
the source in RWAIT with controller waiting [] (M3 row
bankWindowOverlapRootLaunchPrefixOrphan, which also gives proto and
orphan). The edge is stable (PACK 0 -> 1), so every PACK is kept and the
POST window is incomplete too; the RWAIT-mode clauses then hold with the
scope-guarded resetWait clause vacuous.
Consumer: the M2 SRC dispatch (RESET launch, incomplete window). -/
theorem bankWindowOverlapSourceResetLaunchIncompleteRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hnot : ¬ Counter.Complete ring (rbRun ring (renewalBankStart ring seed) pre).1 e)
    (hx : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val = 0)
    (hy : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val = 1)
    (hg : ((rbRun ring (renewalBankStart ring seed) pre).1 e).grant = false)
    (hm : ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .RESET) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  obtain ⟨hmode, hctrl, hproto, horphan⟩ :=
    bankWindowOverlapRootLaunchPrefixOrphan ring hn hbank seed pre e hx hy hg hm
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hstable :
      packNext ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val := by
    rw [hx, hy]
    simp [packNext, hb]
  have hpackAll := bankWindowOverlapStablePackFrame ring hn seed pre e hstable
  apply bankWindowRootFieldsAtOfSourceOwnClauses ring _ e _ hproto horphan
  apply bankWindowOverlapSourceOwnRwaitModeClauses ring _ e hmode hctrl
  intro hs _ _
  exfalso
  apply hnot
  intro j hj
  rw [← hpackAll]
  exact hs.1 j hj

/-- Cell-level memory row: on an aligned PACK 0 -> 1 source edge without
grant, a source that leaves its waiting phase into RESET (CWAIT meeting
CL1; or a waiting phase with lease <= 1 meeting a non-return token or a
non-matching return token) gets the empty controller.
Consumer: bankWindowOverlapSourceResetExitRootFieldsAt and the M2 SRC rows
M2-e, M2-f (lease <= 1), M2-i. -/
theorem bankWindowJointSourceResetExitController {n : Nat} {c : Compiled}
    (m : RenewalBankMemory n) (e dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1) (hg : x.grant = false)
    (hrow : (x.mode = .CWAIT ∧ y.tok = .CL1) ∨
      ((x.mode = .RWAIT ∨ x.mode = .IWAIT ∨ x.mode = .CWAIT) ∧
        x.lease.val ≤ 1 ∧
        (isRetTok y.tok = false ∨
          (x.mode = .RWAIT ∧ (y.tok = .AL ∨ y.tok = .CL0 ∨ y.tok = .CL1)) ∨
          (x.mode = .IWAIT ∧ (y.tok = .RL ∨ y.tok = .CL0 ∨ y.tok = .CL1)) ∨
          (x.mode = .CWAIT ∧ (y.tok = .RL ∨ y.tok = .AL))))) :
    (renewalBankPairMemory c m e dest x y).1.controller = .empty := by
  have hb : 0 < c.b := by
    change 0 < c.s + 11
    omega
  have hbz : c.b ≠ 0 := by omega
  have hwide : c.b ≠ 1 := by
    change c.s + 11 ≠ 1
    omega
  have hp : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  rcases hrow with ⟨hm, ht⟩ | ⟨hm, hl, hcase⟩
  · simp [renewalBankPairMemory, renewalBankWaitSlot, bankCell, hx, hy, hg,
      hm, ht, hb, hbz, hp, hwide, isRetTok, isWaitMode, Id.run_pure,
      Id.run_bind]
  · have hno : ¬ 1 < x.lease.val := by omega
    rcases hm with hm | hm | hm <;> cases ht : y.tok <;>
      rw [hm, ht] at hcase <;> simp [isRetTok] at hcase <;>
      simp [renewalBankPairMemory, renewalBankWaitSlot, bankCell, hx, hy, hg,
        hm, ht, hb, hbz, hp, hwide, hno, isRetTok, isWaitMode, Id.run_pure,
        Id.run_bind]

/-- M2 SRC, reset exit at the selected PACK-zero source: if the literal
pair row sets the source mode to RESET and its controller to empty, and
the M3 proto/orphan clauses hold, every root-indexed POST clause holds at
e (bankWindowRootFieldsAtOfReset; an empty controller is not inherited).
Consumer: the M2 SRC rows M2-e, M2-f (lease <= 1), M2-i. -/
theorem bankWindowOverlapSourceResetExitRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hcellMode : (Counter.resetBankOld ((rbRun ring (renewalBankStart ring seed) pre).1 e)
      ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e))).1.mode = .RESET)
    (hcellCtrl : (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
      (rbRun ring (renewalBankStart ring seed) pre).2 e (ring.rightNeighbor e) ((rbRun ring (renewalBankStart ring seed) pre).1 e)
      ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e))).1.controller = .empty)
    (hproto : ∀ limit : Nat, BankWindowProtoRun ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e limit →
      BankWindowRootForeignProtoField ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e limit)
    (horphan : ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowOrphanOwner ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e j →
      BankWindowTainted (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) (Counter.site ring e (j.val + 1)) →
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).mode = .RESET ∨
        (((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).mode = .RWAIT ∧ ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites e).controller = .waiting [])) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  have htrip := (bankWindowClosureSelectedBankTrip ring hn hbank (rbRun ring (renewalBankStart ring seed) pre) e).1
  have hmode := congrArg (fun t : Mode × Bool × BTok => t.1) htrip
  change ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).mode = (Counter.resetBankOld ((rbRun ring (renewalBankStart ring seed) pre).1 e)
    ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e))).1.mode at hmode
  have hframe := (rbReferenceSelectedPairFrame ring (by omega : 2 ≤ n)
    (rbRun ring (renewalBankStart ring seed) pre) e).2.2.1
  have hctl := congrArg (fun q : RenewalBankSite n => q.controller) hframe
  change ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites e).controller =
    (renewalBankPairMemory (compileAdvice (ceilLogTwo n)) (rbRun ring (renewalBankStart ring seed) pre).2 e
      (ring.rightNeighbor e) ((rbRun ring (renewalBankStart ring seed) pre).1 e)
      ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e))).1.controller at hctl
  exact bankWindowRootFieldsAtOfReset ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e (hmode.trans hcellMode)
    (bankWindowEmptyControllerNotInherited _ e (hctl.trans hcellCtrl))
    hproto horphan

/-- M2-e: CWAIT source meeting CL1 at an aligned first digit, any (rbRun ring (renewalBankStart ring seed) pre)
window: RESET with empty controller; proto/orphan from M3
bankWindowOverlapSourceClOnePrefixOrphan.
Consumer: the M2 SRC dispatch. -/
theorem bankWindowOverlapSourceClOneRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hx : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val = 0)
    (hy : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val = 1)
    (hg : ((rbRun ring (renewalBankStart ring seed) pre).1 e).grant = false)
    (hm : ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .CWAIT)
    (ht : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .CL1) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  obtain ⟨hproto, horphan⟩ := bankWindowOverlapSourceClOnePrefixOrphan ring hn
    hbank seed pre e hJ hx hy hg hm ht
  exact bankWindowOverlapSourceResetExitRootFieldsAt ring hn hbank seed pre e
    (bankWindowOverlapSourceClOneResetMode _ _ hx hy hg hm ht)
    (bankWindowJointSourceResetExitController _ _ _ _ _ hx hy hg
      (Or.inl ⟨hm, ht⟩))
    hproto horphan

/-- M2-f, lease <= 1: a waiting source meeting a non-matching return token
at an aligned first digit, any (rbRun ring (renewalBankStart ring seed) pre) window: RESET with empty controller;
proto/orphan from M3 bankWindowOverlapSourceMismatchReturnTimeoutPrefixOrphan.
Consumer: the M2 SRC dispatch. -/
theorem bankWindowOverlapSourceMismatchTimeoutRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hx : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val = 0)
    (hy : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val = 1)
    (hg : ((rbRun ring (renewalBankStart ring seed) pre).1 e).grant = false)
    (hcases : ((((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .RWAIT ∧ ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .AL) ∨
       (((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .RWAIT ∧ ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .CL0) ∨
       (((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .RWAIT ∧ ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .CL1) ∨
       (((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .IWAIT ∧ ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .RL) ∨
       (((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .IWAIT ∧ ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .CL0) ∨
       (((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .IWAIT ∧ ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .CL1) ∨
       (((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .CWAIT ∧ ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .RL) ∨
       (((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .CWAIT ∧ ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .AL)))
    (hshort : ((rbRun ring (renewalBankStart ring seed) pre).1 e).lease.val ≤ 1) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  obtain ⟨hproto, horphan⟩ :=
    bankWindowOverlapSourceMismatchReturnTimeoutPrefixOrphan ring hn hbank seed
      pre e hJ hx hy hg hcases hshort
  have hrow : (((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .RWAIT ∨ ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .IWAIT ∨
        ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .CWAIT) ∧
      (isRetTok ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = false ∨
        (((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .RWAIT ∧ (((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .AL ∨
          ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .CL0 ∨
          ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .CL1)) ∨
        (((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .IWAIT ∧ (((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .RL ∨
          ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .CL0 ∨
          ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .CL1)) ∨
        (((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .CWAIT ∧ (((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .RL ∨
          ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .AL))) := by
    rcases hcases with h | h | h | h | h | h | h | h <;> obtain ⟨hm, ht⟩ := h
    · exact ⟨Or.inl hm, Or.inr (Or.inl ⟨hm, Or.inl ht⟩)⟩
    · exact ⟨Or.inl hm, Or.inr (Or.inl ⟨hm, Or.inr (Or.inl ht)⟩)⟩
    · exact ⟨Or.inl hm, Or.inr (Or.inl ⟨hm, Or.inr (Or.inr ht)⟩)⟩
    · exact ⟨Or.inr (Or.inl hm), Or.inr (Or.inr (Or.inl ⟨hm, Or.inl ht⟩))⟩
    · exact ⟨Or.inr (Or.inl hm),
        Or.inr (Or.inr (Or.inl ⟨hm, Or.inr (Or.inl ht)⟩))⟩
    · exact ⟨Or.inr (Or.inl hm),
        Or.inr (Or.inr (Or.inl ⟨hm, Or.inr (Or.inr ht)⟩))⟩
    · exact ⟨Or.inr (Or.inr hm), Or.inr (Or.inr (Or.inr ⟨hm, Or.inl ht⟩))⟩
    · exact ⟨Or.inr (Or.inr hm), Or.inr (Or.inr (Or.inr ⟨hm, Or.inr ht⟩))⟩
  exact bankWindowOverlapSourceResetExitRootFieldsAt ring hn hbank seed pre e
    (bankWindowOverlapSourceMismatchReturnTimeoutMode _ _ hx hy hg hcases hshort)
    (bankWindowJointSourceResetExitController _ _ _ _ _ hx hy hg
      (Or.inr ⟨hrow.1, hshort, hrow.2⟩))
    hproto horphan

/-- M2-i: a waiting source with lease <= 1 meeting a non-return token at
an aligned first digit, any (rbRun ring (renewalBankStart ring seed) pre) window: RESET with empty controller;
proto/orphan from M3 bankWindowOverlapNonreturnShortWaitPrefixOrphan.
Consumer: the M2 SRC dispatch. -/
theorem bankWindowOverlapSourceShortWaitRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hx : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val = 0)
    (hy : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val = 1)
    (hg : ((rbRun ring (renewalBankStart ring seed) pre).1 e).grant = false)
    (hphase : ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .RWAIT ∨ ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .IWAIT ∨
      ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .CWAIT)
    (hshort : ((rbRun ring (renewalBankStart ring seed) pre).1 e).lease.val ≤ 1)
    (hret : isRetTok ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = false) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  obtain ⟨hproto, horphan⟩ := bankWindowOverlapNonreturnShortWaitPrefixOrphan
    ring hn hbank seed pre e hJ hx hy hg hphase hshort hret
  exact bankWindowOverlapSourceResetExitRootFieldsAt ring hn hbank seed pre e
    (bankWindowOverlapNonreturnShortWaitMode _ _ hx hy hg hphase hshort hret)
    (bankWindowJointSourceResetExitController _ _ _ _ _ hx hy hg
      (Or.inr ⟨hphase, hshort, Or.inl hret⟩))
    hproto horphan

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open L3.BankComparatorExclusive
open L3.BankHeadThreshold
open L3.BankCounterRows
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- A POST genuine worker whose origin is rooted at the selected source e
sits at the digit of e's window whose index equals its own PACK
(ReceiptInv.workerSite through bankWindowGenuineWorkerSiteOfRun, band from
bankWindowOverlapGenuineWorkerInBand). So if every POST digit of e whose
PACK equals its index is untainted, no POST genuine worker rooted at e
exists anywhere. Unlike bankWindowOverlapSourceActiveNoOwnGenuineFromClean
this needs no cleanliness of unaligned digits (incomplete windows).
Consumer: bankWindowOverlapSourceAlignedCleanRootFieldsAt. -/
theorem bankWindowJointSourceNoOwnGenuineOfAlignedClean {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n)) (e : Fin n)
    (hclean : ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 (Counter.site ring e (j.val + 1))).pack.val = j.val + 1 →
      ¬ BankWindowTainted (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) (Counter.site ring e (j.val + 1)))
    (o : RenewalBankOrigin n) (i : Fin n) (q : RenewalBankPayload n)
    (hroot : o.root = e)
    (hw : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites i).worker = .payload q)
    (ho : q.origin = some o) : False := by
  have hrun : rbRun ring (renewalBankStart ring seed) (pre ++ [e]) = (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) := by
    rw [rbRunAppend]
    rfl
  rw [← hrun] at hclean hw
  have hband := bankWindowOverlapGenuineWorkerInBand ring hn hbank seed
    (pre ++ [e]) i q o hw ho
  have hsite := bankWindowGenuineWorkerSiteOfRun ring hn hbank seed
    (pre ++ [e]) i q o hw ho
  generalize rbRun ring (renewalBankStart ring seed) (pre ++ [e]) = X
    at hclean hw hband hsite
  rw [hroot] at hsite
  obtain ⟨hlo, hhi⟩ := hband
  -- Term proofs, not omega: omega's auxiliary proof took the kernel 104 s to check here.
  have hk : (X.1 i).pack.val - 1 < (compileAdvice (ceilLogTwo n)).b :=
    Nat.lt_of_lt_of_le (Nat.sub_lt hlo Nat.one_pos) hhi
  have hsucc : (X.1 i).pack.val - 1 + 1 = (X.1 i).pack.val := Nat.sub_add_cancel hlo
  have hc : (X.1 (Counter.site ring e ((X.1 i).pack.val - 1 + 1))).pack.val =
      (X.1 i).pack.val - 1 + 1 →
      ¬ BankWindowTainted X (Counter.site ring e ((X.1 i).pack.val - 1 + 1)) :=
    hclean ⟨(X.1 i).pack.val - 1, hk⟩
  rw [hsucc, ← hsite] at hc
  exact hc rfl (Or.inr ⟨q, o, hw, ho⟩)

/-- Selected PACK-zero source e that is not POST (RWAIT, waiting []),
whose POST controller is not a genuine active one, and whose POST
digits are untainted wherever the digit PACK equals its index: every
root-indexed POST clause holds at e, proto and orphan included. Genuine
workers rooted at e are excluded by
bankWindowJointSourceNoOwnGenuineOfAlignedClean; scope-guarded clauses
read only aligned digits (a complete window is aligned); a proto run and
an orphan owner only name digits whose PACK equals their index.
Consumer: the M2 rows bankWindowOverlapSourceActiveReturnRootFieldsAt (M2-g),
bankWindowOverlapSourceInheritedActiveRootFieldsAt (M2-h),
bankWindowOverlapSourceIwaitReturnRootFieldsAt (M2-c),
bankWindowOverlapSourceMismatchLongRootFieldsAt (M2-f) and
bankWindowOverlapSourceChangedLongWaitRootFieldsAt (M2-a). -/
theorem bankWindowOverlapSourceAlignedCleanRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n)) (e : Fin n)
    (hrw : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).mode = .RWAIT →
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites e).controller = .waiting [] → False)
    (hclean : ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 (Counter.site ring e (j.val + 1))).pack.val = j.val + 1 →
      ¬ BankWindowTainted (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) (Counter.site ring e (j.val + 1)))
    (hnoActive : ∀ (q : RenewalBankPayload n) (o : RenewalBankOrigin n),
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites e).controller = .active q → q.origin = some o → False) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  have hnoWorker : ∀ (o : RenewalBankOrigin n) (i : Fin n)
      (q : RenewalBankPayload n), o.root = e →
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites i).worker = .payload q → q.origin = some o → False :=
    fun o i q hroot hw ho =>
      bankWindowJointSourceNoOwnGenuineOfAlignedClean ring hn hbank seed pre e
        hclean o i q hroot hw ho
  have hcompClean : Counter.Complete ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e →
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        ¬ BankWindowTainted (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) (Counter.site ring e (j.val + 1)) := by
    intro hc j
    have hj := j.isLt
    exact hclean j (hc (j.val + 1) (by omega))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o i q hroot hcomp
    exact False.elim (hnoWorker o i q hroot hcomp.1 hcomp.2.1)
  · intro o i q hroot hcomp _
    exact False.elim (hnoWorker o i q hroot hcomp.1 hcomp.2.1)
  · intro o i q hroot hcomp _ _
    exact False.elim (hnoWorker o i q hroot hcomp.1 hcomp.2.1)
  · intro o i q hroot hcomp _
    exact False.elim (hnoWorker o i q hroot hcomp.1 hcomp.2.1)
  · intro hs _ j
    exact hcompClean hs.1 j
  · intro _ hm hc
    exact False.elim (hrw hm hc)
  · intro o q _ _ hctl ho
    exact False.elim (hnoActive q o hctl ho)
  · intro o i q _ _ _ hw ho hroot
    exact False.elim (hnoWorker o i q hroot hw ho)
  · intro o i q hroot hw ho _ _
    exact False.elim (hnoWorker o i q hroot hw ho)
  · intro hs _ _ j ht
    exact False.elim (hcompClean hs.1 j ht)
  · intro hs _ _ j ht
    exact False.elim (hcompClean hs.1 j ht)
  · intro limit hrun
    refine ⟨fun q o hc ho => hnoActive q o hc ho, ?_, ?_, ?_⟩
    · intro _ j hj
      exact hclean j (hrun.2.1 (j.val + 1) hj)
    · intro hm
      exact False.elim (hrw hm.1 hm.2)
    · intro _ _ j hj
      exact hclean j (hrun.2.1 (j.val + 1) hj)
  · intro j howner ht
    exact False.elim (hclean j howner.2.1 ht)

/-- A site whose POST worker is its OLD worker, empty, or an origin-free
payload is untainted after the step if it was untainted before.
Consumer: bankWindowOverlapSourceActiveReturnRootFieldsAt and
bankWindowOverlapSourceInheritedActiveRootFieldsAt (responder digit). -/
theorem bankWindowJointUntaintedOfWorker {n : Nat}
    (r s : RenewalBankReference n) (i : Fin n)
    (h : (s.2.sites i).worker = (r.2.sites i).worker ∨
      (s.2.sites i).worker = .empty ∨
      ∃ q : RenewalBankPayload n,
        (s.2.sites i).worker = .payload q ∧ q.origin = none)
    (hr : ¬ BankWindowTainted r i) : ¬ BankWindowTainted s i := by
  intro ht
  rcases ht with ⟨rho, hw⟩ | ⟨q, o, hw, ho⟩
  · rcases h with h | h | ⟨q', h, _⟩
    · exact hr (Or.inl ⟨rho, h.symm.trans hw⟩)
    · rw [h] at hw
      cases hw
    · rw [h] at hw
      cases hw
  · rcases h with h | h | ⟨q', h, hq⟩
    · exact hr (Or.inr ⟨q, o, h.symm.trans hw, ho⟩)
    · rw [h] at hw
      cases hw
    · rw [h] at hw
      injection hw with hqq
      subst hqq
      rw [hq] at ho
      cases ho

/-- OLD inherited (origin-free) active controller at a grant-free
PACK-zero ARMED/CSTART source e on a stable PACK 0 -> 1 edge: every POST
digit of e whose PACK equals its index is untainted, provided the POST
responder e+ is. Such a digit is never e (PACK 0); off the pair the
worker is framed and OLD cleanliness is
bankWindowOverlapSourceActiveInheritedOldClean (OLD inheritedClean, OLD
proto, OLD orphan).
Consumer: bankWindowOverlapSourceActiveReturnRootFieldsAt and
bankWindowOverlapSourceInheritedActiveRootFieldsAt. -/
theorem bankWindowJointSourceInheritedAlignedClean {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n)) (e : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hx : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val = 0)
    (hy : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val = 1)
    (hg : ((rbRun ring (renewalBankStart ring seed) pre).1 e).grant = false)
    (hm : ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .ARMED ∨ ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .CSTART)
    (p : RenewalBankPayload n)
    (hactive : ((rbRun ring (renewalBankStart ring seed) pre).2.sites e).controller = .active p)
    (hnone : p.origin = none)
    (hresp : ¬ BankWindowTainted (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) (ring.rightNeighbor e)) :
    ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 (Counter.site ring e (j.val + 1))).pack.val = j.val + 1 →
      ¬ BankWindowTainted (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) (Counter.site ring e (j.val + 1)) := by
  intro j hj
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hstable : packNext ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val (compileAdvice (ceilLogTwo n)).b =
      ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val := by
    rw [hx, hy]
    simp [packNext, hb]
  have hpackAll : ∀ z : Fin n, ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 z).pack.val = ((rbRun ring (renewalBankStart ring seed) pre).1 z).pack.val :=
    bankWindowOverlapStablePackFrame ring hn seed pre e hstable
  have hold : ((rbRun ring (renewalBankStart ring seed) pre).1 (Counter.site ring e (j.val + 1))).pack.val = j.val + 1 := by
    rw [← hpackAll]
    exact hj
  by_cases hze : Counter.site ring e (j.val + 1) = e
  · rw [hze, hx] at hold
    omega
  by_cases hzr : Counter.site ring e (j.val + 1) = (ring.rightNeighbor e)
  · rw [hzr]
    exact hresp
  · have hframe := (bankWindowExactOffPairFrame ring (rbRun ring (renewalBankStart ring seed) pre) e
      (Counter.site ring e (j.val + 1)) hze hzr).2
    exact bankWindowJointUntaintedOfWorker (rbRun ring (renewalBankStart ring seed) pre) (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
      (Counter.site ring e (j.val + 1))
      (Or.inl (by rw [hframe]))
      (bankWindowOverlapSourceActiveInheritedOldClean ring (rbRun ring (renewalBankStart ring seed) pre) e hJ hx hg hm
        p hactive hnone j hold)

/-- Cell row (bankPair return branch): a grant-free ARMED/CSTART PACK-zero
source facing a return token on an aligned PACK-one responder keeps its
mode (the return branch precedes the ARMED/CSTART rows; wait is the
identity off wait modes).
Consumer: bankWindowOverlapSourceActiveReturnRootFieldsAt (M2-g). -/
theorem bankWindowJointSourceActiveReturnMode {c : Compiled} (x y : Agent c)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1) (hg : x.grant = false)
    (hm : x.mode = .ARMED ∨ x.mode = .CSTART)
    (hret : isRetTok y.tok = true) :
    (Counter.resetBankOld x y).1.mode = x.mode := by
  have hb : 0 < c.b := by
    change 0 < c.s + 11
    omega
  have hbz : c.b ≠ 0 := by omega
  have hpost : packNext x.pack.val y.pack.val c.b = 1 := by
    rw [hx, hy]
    simp [packNext, hb]
  unfold Counter.resetBankOld
  rw [hpost]
  rcases hm with hm | hm <;> rw [hm] <;> cases ht : y.tok <;>
    rw [ht] at hret <;> simp [isRetTok] at hret <;>
    simp [bankPair, bankCell, hx, hy, hg, hm, ht, hb, hbz, hpost,
      isRetTok, isWaitMode, Id.run_pure, Id.run_bind]
  all_goals (try simp only [if_neg hbz, if_true, Id.run_pure])
  all_goals (try rfl)

/-- Memory row (renewalBankPairMemory return branch): the same source
keeps its controller (wait slot is the identity off wait modes) and the
responder worker is erased.
Consumer: bankWindowOverlapSourceActiveReturnRootFieldsAt (M2-g). -/
theorem bankWindowJointSourceActiveReturnMemory {n : Nat} {c : Compiled}
    (m : RenewalBankMemory n) (e dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1) (hg : x.grant = false)
    (hm : x.mode = .ARMED ∨ x.mode = .CSTART)
    (hret : isRetTok y.tok = true) :
    (renewalBankPairMemory c m e dest x y).1.controller =
      (m.sites e).controller ∧
    (renewalBankPairMemory c m e dest x y).2.worker = .empty := by
  have hb : 0 < c.b := by
    change 0 < c.s + 11
    omega
  have hbz : c.b ≠ 0 := by omega
  have hwide : c.b ≠ 1 := by
    change c.s + 11 ≠ 1
    omega
  have hp : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  rcases hm with hm | hm <;> cases ht : y.tok <;>
    rw [ht] at hret <;> simp [isRetTok] at hret <;>
    simp [renewalBankPairMemory, renewalBankWaitSlot, bankCell, hx, hy, hg,
      hm, ht, hb, hbz, hp, hwide, isRetTok, isWaitMode, Id.run_pure,
      Id.run_bind]

/-- M2-g exclusion: a genuine active controller at a grant-free PACK-zero
ARMED/CSTART source cannot face a return token. OLD J.proto forces the
window complete (bankWindowOverlapSourceActiveGenuineComplete), and OLD
armedExact then makes every digit token E, digit one being e+.
Consumer: bankWindowOverlapSourceActiveReturnRootFieldsAt (M2-g). -/
theorem bankWindowJointSourceActiveReturnNotGenuine {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n) (e : Fin n)
    (hJ : BankWindowExact ring r)
    (hx : (r.1 e).pack.val = 0) (hg : (r.1 e).grant = false)
    (hm : (r.1 e).mode = .ARMED ∨ (r.1 e).mode = .CSTART)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hactive : (r.2.sites e).controller = .active p)
    (horigin : p.origin = some o)
    (hret : isRetTok (r.1 (ring.rightNeighbor e)).tok = true) : False := by
  have hcomplete := bankWindowOverlapSourceActiveGenuineComplete ring r e hJ
    hx p o hactive horigin
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hE := (hJ.armedExact e o p ⟨hcomplete, hg⟩ hm hactive horigin).1
    ⟨0, hb⟩
  change (r.1 (ring.rightNeighbor e)).tok = .E at hE
  rw [hE] at hret
  simp [isRetTok] at hret

/-- An OLD PACK-zero ARMED/CSTART root carries an active controller
(in-flight controller shape of OLD J.frame).
Consumer: bankWindowOverlapSourceActiveReturnRootFieldsAt and the M2 SRC
dispatch bankWindowOverlapSourceRootFieldsAt. -/
theorem bankWindowJointActiveControllerOfPhase {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n) (e : Fin n)
    (hJ : BankWindowExact ring r)
    (hx : (r.1 e).pack.val = 0)
    (hm : (r.1 e).mode = .ARMED ∨ (r.1 e).mode = .CSTART) :
    ∃ p : RenewalBankPayload n, (r.2.sites e).controller = .active p := by
  have hsh := (hJ.frame e).1
  unfold bankInFlightControllerShape at hsh
  rw [if_pos hx] at hsh
  rcases hm with hm | hm <;> rw [hm] at hsh <;> exact hsh

/-- M2-g: grant-free PACK-zero ARMED/CSTART source facing a return token
on an aligned PACK-one responder. The return branch erases the e+ token
and worker and keeps mode and controller. A genuine controller is
impossible (bankWindowJointSourceActiveReturnNotGenuine); with the
inherited controller every POST digit whose PACK equals its index is
untainted (bankWindowJointSourceInheritedAlignedClean; e+ worker empty),
so bankWindowOverlapSourceAlignedCleanRootFieldsAt gives every
root-indexed POST clause, proto and orphan included, for complete and
incomplete windows.
Consumer: the M2 SRC dispatch bankWindowOverlapSourceRootFieldsAt. -/
theorem bankWindowOverlapSourceActiveReturnRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n)) (e : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hx : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val = 0)
    (hy : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val = 1)
    (hg : ((rbRun ring (renewalBankStart ring seed) pre).1 e).grant = false)
    (hm : ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .ARMED ∨ ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .CSTART)
    (hret : isRetTok ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = true) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  obtain ⟨p, hactive⟩ := bankWindowJointActiveControllerOfPhase ring (rbRun ring (renewalBankStart ring seed) pre) e
    hJ hx hm
  have hnone : p.origin = none := by
    cases ho : p.origin with
    | none => rfl
    | some o =>
        exact False.elim (bankWindowJointSourceActiveReturnNotGenuine ring
          (rbRun ring (renewalBankStart ring seed) pre) e hJ hx hg hm p o hactive ho hret)
  have hcell := bankWindowJointSourceActiveReturnMemory (rbRun ring (renewalBankStart ring seed) pre).2 e (ring.rightNeighbor e)
    ((rbRun ring (renewalBankStart ring seed) pre).1 e) ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)) hx hy hg hm hret
  have hframe := rbReferenceSelectedPairFrame ring (by omega : 2 ≤ n) (rbRun ring (renewalBankStart ring seed) pre) e
  have hctlPost : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites e).controller = .active p := by
    have h := congrArg (fun q : RenewalBankSite n => q.controller) hframe.2.2.1
    change ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites e).controller =
      (renewalBankPairMemory (compileAdvice (ceilLogTwo n)) (rbRun ring (renewalBankStart ring seed) pre).2 e (ring.rightNeighbor e) ((rbRun ring (renewalBankStart ring seed) pre).1 e)
        ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e))).1.controller at h
    rw [h, hcell.1, hactive]
  have hwPost : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites (ring.rightNeighbor e)).worker = .empty := by
    have h := congrArg (fun q : RenewalBankSite n => q.worker) hframe.2.2.2
    change ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites (ring.rightNeighbor e)).worker =
      (renewalBankPairMemory (compileAdvice (ceilLogTwo n)) (rbRun ring (renewalBankStart ring seed) pre).2 e (ring.rightNeighbor e) ((rbRun ring (renewalBankStart ring seed) pre).1 e)
        ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e))).2.worker at h
    rw [h, hcell.2]
  have hmodePost : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).mode = ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode := by
    have htrip := (bankWindowClosureSelectedBankTrip ring hn hbank (rbRun ring (renewalBankStart ring seed) pre) e).1
    have h := congrArg (fun t : Mode × Bool × BTok => t.1) htrip
    change ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).mode =
      (Counter.resetBankOld ((rbRun ring (renewalBankStart ring seed) pre).1 e) ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e))).1.mode at h
    rw [h]
    exact bankWindowJointSourceActiveReturnMode _ _ hx hy hg hm hret
  apply bankWindowOverlapSourceAlignedCleanRootFieldsAt ring hn hbank seed pre e
  · intro hh _
    rw [hmodePost] at hh
    rcases hm with h | h <;> rw [h] at hh <;> cases hh
  · exact bankWindowJointSourceInheritedAlignedClean ring hn seed pre e hJ hx
      hy hg hm p hactive hnone
      (by
          intro ht
          rcases ht with ⟨rho, hw⟩ | ⟨q, o, hw, _⟩
          · rw [hwPost] at hw
            cases hw
          · rw [hwPost] at hw
            cases hw)
  · intro q o hc ho
    rw [hctlPost] at hc
    injection hc with hpq
    subst hpq
    rw [hnone] at ho
    cases ho

/-- M2-h: grant-free PACK-zero ARMED/CSTART source with an inherited
(origin-free) active controller and responder token E on an aligned
PACK-one responder: rows A0 (-> CSTART, controller active head p, e+
worker kept), A1 (-> IWAIT, controller waiting [], e+ worker the
origin-free head payload) and CSTART issue (-> CWAIT, controller
waiting [], e+ worker the origin-free payload p). The OLD e+ worker is
digit one, untainted by bankWindowOverlapSourceActiveInheritedOldClean;
then bankWindowJointSourceInheritedAlignedClean and
bankWindowOverlapSourceAlignedCleanRootFieldsAt give every POST clause,
complete or incomplete OLD window.
Consumer: the M2 SRC dispatch bankWindowOverlapSourceRootFieldsAt. -/
theorem bankWindowOverlapSourceInheritedActiveRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n)) (e : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hx : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val = 0)
    (hy : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val = 1)
    (hg : ((rbRun ring (renewalBankStart ring seed) pre).1 e).grant = false)
    (hm : ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .ARMED ∨ ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .CSTART)
    (ht : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .E)
    (p : RenewalBankPayload n)
    (hactive : ((rbRun ring (renewalBankStart ring seed) pre).2.sites e).controller = .active p)
    (hnone : p.origin = none) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hframe := rbReferenceSelectedPairFrame ring (by omega : 2 ≤ n) (rbRun ring (renewalBankStart ring seed) pre) e
  have hctlEq : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites e).controller =
      (renewalBankPairMemory (compileAdvice (ceilLogTwo n)) (rbRun ring (renewalBankStart ring seed) pre).2 e (ring.rightNeighbor e) ((rbRun ring (renewalBankStart ring seed) pre).1 e)
        ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e))).1.controller := by
    have h := congrArg (fun q : RenewalBankSite n => q.controller) hframe.2.2.1
    exact h
  have hwEq : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites (ring.rightNeighbor e)).worker =
      (renewalBankPairMemory (compileAdvice (ceilLogTwo n)) (rbRun ring (renewalBankStart ring seed) pre).2 e (ring.rightNeighbor e) ((rbRun ring (renewalBankStart ring seed) pre).1 e)
        ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e))).2.worker := by
    have h := congrArg (fun q : RenewalBankSite n => q.worker) hframe.2.2.2
    exact h
  have hrespOld : ¬ BankWindowTainted (rbRun ring (renewalBankStart ring seed) pre) (ring.rightNeighbor e) :=
    bankWindowOverlapSourceActiveInheritedOldClean ring (rbRun ring (renewalBankStart ring seed) pre) e hJ hx hg hm p
      hactive hnone ⟨0, hb⟩ hy
  have hfinish :
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).mode ≠ .RESET → ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).mode ≠ .RWAIT →
      (((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites (ring.rightNeighbor e)).worker = ((rbRun ring (renewalBankStart ring seed) pre).2.sites (ring.rightNeighbor e)).worker ∨
        ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites (ring.rightNeighbor e)).worker = .empty ∨
        ∃ q : RenewalBankPayload n,
          ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites (ring.rightNeighbor e)).worker = .payload q ∧ q.origin = none) →
      (∀ (q : RenewalBankPayload n) (o : RenewalBankOrigin n),
        ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites e).controller = .active q → q.origin = some o →
          False) →
      BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
    intro _ h2 hw hna
    exact bankWindowOverlapSourceAlignedCleanRootFieldsAt ring hn hbank seed
      pre e (fun hh _ => h2 hh)
      (bankWindowJointSourceInheritedAlignedClean ring hn seed pre e hJ hx hy
        hg hm p hactive hnone
        (bankWindowJointUntaintedOfWorker (rbRun ring (renewalBankStart ring seed) pre) (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) (ring.rightNeighbor e) hw hrespOld))
      hna
  rcases hm with hmA | hmC
  · have hmem := bankWindowOverlapSourceActiveInheritedArmedMemory (compileAdvice (ceilLogTwo n)) (rbRun ring (renewalBankStart ring seed) pre).2
      e (ring.rightNeighbor e) ((rbRun ring (renewalBankStart ring seed) pre).1 e) ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)) hb hx hy hg hmA ht p hactive hnone
    have hphys := bankWindowOverlapSourceActiveArmedPhysical ring hn hbank
      (rbRun ring (renewalBankStart ring seed) pre) e hx hy hg hmA ht
    cases hbit : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).bit with
    | false =>
        rw [hbit] at hmem hphys
        have hmode : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).mode = .CSTART := by
          rw [hphys.1]
          rfl
        apply hfinish
        · rw [hmode]
          intro hh
          cases hh
        · rw [hmode]
          intro hh
          cases hh
        · left
          rw [hwEq, hmem.2.1]
          rfl
        · intro q o hc ho
          rw [hctlEq, hmem.1] at hc
          have hc' : RenewalBankController.active (renewalBankHead p) =
              .active q := hc
          injection hc' with hpq
          rw [← hpq, hmem.2.2] at ho
          cases ho
    | true =>
        rw [hbit] at hmem hphys
        have hmode : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).mode = .IWAIT := by
          rw [hphys.1]
          rfl
        apply hfinish
        · rw [hmode]
          intro hh
          cases hh
        · rw [hmode]
          intro hh
          cases hh
        · right
          right
          refine ⟨renewalBankHead p, ?_, hmem.2.2⟩
          rw [hwEq, hmem.2.1]
          rfl
        · intro q o hc ho
          rw [hctlEq, hmem.1] at hc
          have hc' : (RenewalBankController.waiting [] : RenewalBankController n) =
              .active q := hc
          cases hc'
  · have hmem := bankWindowOverlapSourceActiveInheritedCstartMemory (compileAdvice (ceilLogTwo n)) (rbRun ring (renewalBankStart ring seed) pre).2
      e (ring.rightNeighbor e) ((rbRun ring (renewalBankStart ring seed) pre).1 e) ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)) hb hx hy hg hmC ht p hactive hnone
    have hphys := bankWindowOverlapRootCstartComparatorIssuePhysical ring hn
      hbank seed pre e hx hy hg hmC ht
    apply hfinish
    · rw [hphys.1]
      intro hh
      cases hh
    · rw [hphys.1]
      intro hh
      cases hh
    · right
      right
      exact ⟨p, by rw [hwEq, hmem.2.1], hnone⟩
    · intro q o hc ho
      rw [hctlEq, hmem.1] at hc
      cases hc



/-- POST reads of the selected pair: source mode from the literal cell
row, source controller and responder worker from the memory row.
Consumer: the M2 rows bankWindowOverlapSourceIwaitReturnRootFieldsAt,
bankWindowOverlapSourceMismatchLongRootFieldsAt and
bankWindowOverlapSourceChangedLongWaitRootFieldsAt. -/
theorem bankWindowJointSelectedPairReads {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n) :
    ((renewalBankNext ring r e).1 e).mode =
      (Counter.resetBankOld (r.1 e) (r.1 (ring.rightNeighbor e))).1.mode ∧
    ((renewalBankNext ring r e).2.sites e).controller =
      (renewalBankPairMemory (compileAdvice (ceilLogTwo n)) r.2 e (ring.rightNeighbor e) (r.1 e) (r.1 (ring.rightNeighbor e))).1.controller ∧
    ((renewalBankNext ring r e).2.sites (ring.rightNeighbor e)).worker =
      (renewalBankPairMemory (compileAdvice (ceilLogTwo n)) r.2 e (ring.rightNeighbor e) (r.1 e) (r.1 (ring.rightNeighbor e))).2.worker := by
  have htrip := (bankWindowClosureSelectedBankTrip ring hn hbank r e).1
  have hframe := rbReferenceSelectedPairFrame ring (by omega : 2 ≤ n) r e
  exact ⟨congrArg (fun t : Mode × Bool × BTok => t.1) htrip,
    congrArg (fun q : RenewalBankSite n => q.controller) hframe.2.2.1,
    congrArg (fun q : RenewalBankSite n => q.worker) hframe.2.2.2⟩

/-- A site with an empty worker is untainted.
Consumer: the M2 rows M2-c, M2-f, M2-a (responder worker erased). -/
theorem bankWindowJointUntaintedOfEmpty {n : Nat}
    (r : RenewalBankReference n) (i : Fin n)
    (h : (r.2.sites i).worker = .empty) : ¬ BankWindowTainted r i := by
  intro ht
  rcases ht with ⟨rho, hw⟩ | ⟨q, o, hw, _⟩
  · rw [h] at hw
    cases hw
  · rw [h] at hw
    cases hw

/-- An OLD PACK-zero root in a wait mode carries a waiting controller
(in-flight controller shape of OLD J.frame).
Consumer: bankWindowJointWaitSourceOldAlignedClean and the M2 rows M2-c,
M2-f, M2-a. -/
theorem bankWindowJointWaitingControllerOfPhase {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n) (e : Fin n)
    (hJ : BankWindowExact ring r)
    (hx : (r.1 e).pack.val = 0)
    (hm : (r.1 e).mode = .RWAIT ∨ (r.1 e).mode = .IWAIT ∨
      (r.1 e).mode = .CWAIT) :
    ∃ atoms : List (RenewalBankAtom n),
      (r.2.sites e).controller = .waiting atoms := by
  have hsh := (hJ.frame e).1
  unfold bankInFlightControllerShape at hsh
  rw [if_pos hx] at hsh
  rcases hm with hm | hm | hm <;> rw [hm] at hsh <;> exact hsh

/-- POST cleanliness of the POST-aligned digits of a PACK-zero source e
(digits whose POST PACK equals their index) from OLD cleanliness of the
OLD-aligned digits other than e+, on any edge out of e, given that the
POST responder e+ is untainted. The source keeps PACK 0, so no aligned
digit is e; off the pair PACK and worker are framed.
Consumer: the M2 rows bankWindowOverlapSourceIwaitReturnRootFieldsAt (M2-c),
bankWindowOverlapSourceMismatchLongRootFieldsAt (M2-f) and
bankWindowOverlapSourceChangedLongWaitRootFieldsAt (M2-a). -/
theorem bankWindowJointPostAlignedCleanOfOld {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n)) (e : Fin n)
    (hx : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val = 0)
    (hold : ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ((rbRun ring (renewalBankStart ring seed) pre).1 (Counter.site ring e (j.val + 1))).pack.val = j.val + 1 →
      Counter.site ring e (j.val + 1) ≠ (ring.rightNeighbor e) →
      ¬ BankWindowTainted (rbRun ring (renewalBankStart ring seed) pre) (Counter.site ring e (j.val + 1)))
    (hresp : ¬ BankWindowTainted (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) (ring.rightNeighbor e)) :
    ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 (Counter.site ring e (j.val + 1))).pack.val = j.val + 1 →
      ¬ BankWindowTainted (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) (Counter.site ring e (j.val + 1)) := by
  intro j hj
  have hsrc : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).pack.val = ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val :=
    (rbBankReferencePairPack ring (by omega : 2 ≤ n) (rbRun ring (renewalBankStart ring seed) pre) e).1
  by_cases hze : Counter.site ring e (j.val + 1) = e
  · rw [hze, hsrc, hx] at hj
    omega
  by_cases hzr : Counter.site ring e (j.val + 1) = (ring.rightNeighbor e)
  · rw [hzr]
    exact hresp
  have hframe := bankWindowExactOffPairFrame ring (rbRun ring (renewalBankStart ring seed) pre) e
    (Counter.site ring e (j.val + 1)) hze hzr
  have hpk : ((rbRun ring (renewalBankStart ring seed) pre).1 (Counter.site ring e (j.val + 1))).pack.val =
      j.val + 1 := by
    rw [← hframe.1]
    exact hj
  exact bankWindowJointUntaintedOfWorker (rbRun ring (renewalBankStart ring seed) pre) (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e)
    (Counter.site ring e (j.val + 1))
    (Or.inl (by rw [hframe.2]))
    (hold j hpk hzr)

/-- OLD wait-mode PACK-zero grant-free source that is not (RWAIT,
waiting []): every OLD digit whose PACK equals its index, other than e+,
is untainted. Complete window: an inherited list gives inheritedClean;
the empty list in IWAIT/CWAIT gives iwait/cwaitTaintedUnique, whose
only-token clause would put a tainted digit at e+ since e+ carries a
token. Incomplete window: OLD proto up to the first misaligned digit
(inherited controller or a mode other than RESET/RWAIT), OLD orphan
beyond it.
Consumer: the M2 rows M2-c, M2-f, M2-a. -/
theorem bankWindowJointWaitSourceOldAlignedClean {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n) (e : Fin n)
    (hJ : BankWindowExact ring r)
    (hx : (r.1 e).pack.val = 0) (hg : (r.1 e).grant = false)
    (hm : (r.1 e).mode = .RWAIT ∨ (r.1 e).mode = .IWAIT ∨
      (r.1 e).mode = .CWAIT)
    (hrw : (r.1 e).mode = .RWAIT → (r.2.sites e).controller = .waiting [] →
      False)
    (htok : Counter.Complete ring r.1 e → (r.1 (ring.rightNeighbor e)).tok ≠ .E) :
    ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      (r.1 (Counter.site ring e (j.val + 1))).pack.val = j.val + 1 →
      Counter.site ring e (j.val + 1) ≠ (ring.rightNeighbor e) →
      ¬ BankWindowTainted r (Counter.site ring e (j.val + 1)) := by
  intro j haligned hzr ht
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  obtain ⟨atoms, hctl⟩ := bankWindowJointWaitingControllerOfPhase ring r e hJ
    hx hm
  have hnotReset : (r.1 e).mode ≠ .RESET := by
    rcases hm with h | h | h <;> rw [h] <;> intro hh <;> cases hh
  by_cases hc : Counter.Complete ring r.1 e
  · by_cases hne : atoms = []
    · subst hne
      rcases hm with h | h | h
      · exact hrw h hctl
      · obtain ⟨o, p, _, _, _, honly⟩ :=
          hJ.iwaitTaintedUnique e ⟨hc, hg⟩ h hctl j ht
        exact hzr (honly ⟨0, hb⟩ (htok hc)).symm
      · obtain ⟨o, p, _, _, _, _, honly⟩ :=
          hJ.cwaitTaintedUnique e ⟨hc, hg⟩ h hctl j ht
        exact hzr (honly ⟨0, hb⟩ (htok hc)).symm
    · exact hJ.inheritedClean e ⟨hc, hg⟩ (Or.inl ⟨atoms, hctl, hne⟩) j ht
  · obtain ⟨limit, hproto⟩ :=
      bankWindowOverlapSourceActiveIncompleteProto ring r e hx hc
    by_cases hle : j.val + 1 ≤ limit
    · by_cases hrwm : (r.1 e).mode = .RWAIT
      · by_cases hne : atoms = []
        · subst hne
          exact hrw hrwm hctl
        · exact (hJ.proto e limit hproto).2.1 (Or.inl ⟨atoms, hctl, hne⟩) j
            hle ht
      · exact (hJ.proto e limit hproto).2.2.2 hnotReset hrwm j hle ht
    · have howner : BankWindowOrphanOwner ring r e j := by
        refine ⟨hx, haligned, ?_⟩
        intro hall
        exact hproto.2.2 (hall (limit + 1) (by omega))
      rcases hJ.orphan e j howner ht with hreset | ⟨hwait, hc'⟩
      · exact hnotReset hreset
      · exact hrw hwait hc'

/-- OLD (RWAIT, waiting []) at a PACK-zero grant-free root: its first
digit e+ is aligned (PACK 1) and carries RR, RL or E (OLD resetWait for a
complete window, OLD proto clause three otherwise: the pending front is a
digit at most the proto limit and every earlier digit token is E).
Consumer: the M2 rows bankWindowOverlapSourceMismatchLongRootFieldsAt
(M2-f) and bankWindowOverlapSourceChangedLongWaitRootFieldsAt (M2-a). -/
theorem bankWindowJointResetWaitFront {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n) (e : Fin n)
    (hJ : BankWindowExact ring r)
    (hx : (r.1 e).pack.val = 0) (hg : (r.1 e).grant = false)
    (hm : (r.1 e).mode = .RWAIT)
    (hctl : (r.2.sites e).controller = .waiting []) :
    (r.1 (ring.rightNeighbor e)).pack.val = 1 ∧
    ((r.1 (ring.rightNeighbor e)).tok = .RR ∨ (r.1 (ring.rightNeighbor e)).tok = .RL ∨ (r.1 (ring.rightNeighbor e)).tok = .E) := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  by_cases hc : Counter.Complete ring r.1 e
  · obtain ⟨j, rho, _, htk, _, hE, _⟩ := hJ.resetWait e ⟨hc, hg⟩ hm hctl
    refine ⟨hc 1 (by omega), ?_⟩
    by_cases hj : j.val = 0
    · have hs : Counter.site ring e (j.val + 1) = (ring.rightNeighbor e) := by
        rw [hj] <;> rfl
      rw [hs] at htk
      rcases htk with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (hE ⟨0, hb⟩ (by show 0 < j.val; omega)))
  · obtain ⟨limit, hproto⟩ :=
      bankWindowOverlapSourceActiveIncompleteProto ring r e hx hc
    obtain ⟨j, hjle, rho, _, htk, _, hE⟩ :=
      (hJ.proto e limit hproto).2.2.1 ⟨hm, hctl⟩
    refine ⟨hproto.2.1 1 (by omega), ?_⟩
    by_cases hj : j.val = 0
    · have hs : Counter.site ring e (j.val + 1) = (ring.rightNeighbor e) := by
        rw [hj] <;> rfl
      rw [hs] at htk
      exact Or.inl htk
    · exact Or.inr (Or.inr (hE ⟨0, hb⟩ (by show 0 < j.val; omega)))

/-- Cell and memory row M2-c: grant-free PACK-zero IWAIT source meeting AL
on an aligned PACK-one responder: source to CSTART, controller the
returned payload of the OLD responder worker, responder worker erased.
Consumer: bankWindowOverlapSourceIwaitReturnRootFieldsAt (M2-c). -/
theorem bankWindowJointSourceIwaitReturnCell {n : Nat} {c : Compiled}
    (m : RenewalBankMemory n) (e dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1) (hg : x.grant = false)
    (hm : x.mode = .IWAIT) (ht : y.tok = .AL) :
    (Counter.resetBankOld x y).1.mode = .CSTART ∧
    (renewalBankPairMemory c m e dest x y).1.controller =
      .active (renewalBankReturned (m.sites e).controller
        (m.sites dest).worker dest) ∧
    (renewalBankPairMemory c m e dest x y).2.worker = .empty := by
  have hb : 0 < c.b := by
    change 0 < c.s + 11
    omega
  have hbz : c.b ≠ 0 := by omega
  have hwide : c.b ≠ 1 := by
    change c.s + 11 ≠ 1
    omega
  have hp : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  have hpost : packNext x.pack.val y.pack.val c.b = 1 := by
    rw [hx, hy]
    exact hp
  refine ⟨?_, ?_⟩
  · unfold Counter.resetBankOld
    rw [hpost]
    simp [bankPair, bankCell, hx, hy, hg, hm, ht, hb, hbz, hpost,
      isRetTok, isWaitMode, Id.run_pure, Id.run_bind]
    all_goals (try simp only [if_neg hbz, if_true, Id.run_pure])
    all_goals (try rfl)
  · simp [renewalBankPairMemory, renewalBankWaitSlot, bankCell, hx, hy, hg,
      hm, ht, hb, hbz, hp, hwide, isRetTok, isWaitMode, Id.run_pure,
      Id.run_bind]

/-- Cell and memory row M2-f, long lease: a grant-free PACK-zero wait
source meeting a non-matching return token on an aligned PACK-one
responder with lease > 1 keeps its mode and controller (wait decrements
the lease) and the responder worker is erased.
Consumer: bankWindowOverlapSourceMismatchLongRootFieldsAt (M2-f). -/
theorem bankWindowJointSourceMismatchLongCell {n : Nat} {c : Compiled}
    (m : RenewalBankMemory n) (e dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1) (hg : x.grant = false)
    (hcases : ((x.mode = .RWAIT ∧ y.tok = .AL) ∨
       (x.mode = .RWAIT ∧ y.tok = .CL0) ∨
       (x.mode = .RWAIT ∧ y.tok = .CL1) ∨
       (x.mode = .IWAIT ∧ y.tok = .RL) ∨
       (x.mode = .IWAIT ∧ y.tok = .CL0) ∨
       (x.mode = .IWAIT ∧ y.tok = .CL1) ∨
       (x.mode = .CWAIT ∧ y.tok = .RL) ∨
       (x.mode = .CWAIT ∧ y.tok = .AL)))
    (hlong : 1 < x.lease.val) :
    (Counter.resetBankOld x y).1.mode = x.mode ∧
    (renewalBankPairMemory c m e dest x y).1.controller =
      (m.sites e).controller ∧
    (renewalBankPairMemory c m e dest x y).2.worker = .empty := by
  have hb : 0 < c.b := by
    change 0 < c.s + 11
    omega
  have hbz : c.b ≠ 0 := by omega
  have hwide : c.b ≠ 1 := by
    change c.s + 11 ≠ 1
    omega
  have hp : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  have hpost : packNext x.pack.val y.pack.val c.b = 1 := by
    rw [hx, hy]
    exact hp
  rcases hcases with h | h | h | h | h | h | h | h <;>
    rcases h with ⟨hm, ht⟩ <;> refine ⟨?_, ?_⟩ <;>
    first
    | (rw [hm]
       unfold Counter.resetBankOld
       rw [hpost]
       simp [bankPair, bankCell, hx, hy, hg, hm, ht, hb, hbz, hpost, hlong,
         isRetTok, isWaitMode, Id.run_pure, Id.run_bind]
       all_goals (try simp only [if_neg hbz, if_true, Id.run_pure])
       all_goals (try rfl))
    | (simp [renewalBankPairMemory, renewalBankWaitSlot, bankCell, hx, hy, hg,
        hm, ht, hb, hbz, hp, hwide, hlong, isRetTok, isWaitMode, Id.run_pure,
        Id.run_bind])

/-- Cell and memory row M2-a: a grant-free PACK-zero wait source whose
first responder PACK changes (OLD PACK not 1), lease > 1, keeps its mode
and controller (the changed branch applies wait) and the responder site
is cleared.
Consumer: bankWindowOverlapSourceChangedLongWaitRootFieldsAt (M2-a). -/
theorem bankWindowJointSourceChangedLongCell {n : Nat} {c : Compiled}
    (m : RenewalBankMemory n) (e dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = 0) (hy : y.pack.val ≠ 1) (hg : x.grant = false)
    (hm : x.mode = .RWAIT ∨ x.mode = .IWAIT ∨ x.mode = .CWAIT)
    (hlong : 1 < x.lease.val) :
    (Counter.resetBankOld x y).1.mode = x.mode ∧
    (renewalBankPairMemory c m e dest x y).1.controller =
      (m.sites e).controller ∧
    (renewalBankPairMemory c m e dest x y).2.worker = .empty := by
  have hb : 0 < c.b := by
    change 0 < c.s + 11
    omega
  have hbz : c.b ≠ 0 := by omega
  have hpost : packNext x.pack.val y.pack.val c.b = 1 := by
    rw [hx]
    simp [packNext, hb]
  have hy' : (1 : Nat) ≠ y.pack.val := fun h => hy h.symm
  have hp0 : packNext 0 y.pack.val c.b = 1 := by
    simp [packNext, hb]
  rcases hm with hm | hm | hm <;> refine ⟨?_, ?_⟩ <;>
    first
    | (rw [hm]
       unfold Counter.resetBankOld
       rw [hpost]
       simp [bankPair, bankCell, hx, hy, hy', hp0, hg, hm, hb, hbz, hlong,
         isRetTok, isWaitMode, Id.run_pure, Id.run_bind]
       all_goals (try simp only [if_neg hbz, if_true, Id.run_pure])
       all_goals (try rfl))
    | (simp [renewalBankPairMemory, renewalBankWaitSlot, bankCell, hx, hy,
        hy', hp0, hg, hm, hb, hbz, hpost, hlong, isRetTok, isWaitMode,
        Id.run_pure, Id.run_bind])

/-- M2-c: grant-free PACK-zero IWAIT source meeting AL on an aligned
PACK-one responder, any controller, any OLD window. The AL worker is a
payload (in-flight worker shape). A genuine payload has its origin rooted
at e (ReceiptInv.workerSite, e+ = site root 1); it forces the window
complete (OLD proto clause four on digit one) and the controller to be
waiting [] (OLD inheritedClean), which is the proved row
bankWindowOverlapSourceIwaitAlRootFieldsAt. An origin-free payload makes
the POST controller an origin-free active one in CSTART with the e+
worker erased, and the OLD aligned digits off e+ are clean
(bankWindowJointWaitSourceOldAlignedClean), so
bankWindowOverlapSourceAlignedCleanRootFieldsAt applies.
Consumer: the M2 SRC dispatch bankWindowOverlapSourceRootFieldsAt. -/
theorem bankWindowOverlapSourceIwaitReturnRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n)) (e : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hx : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val = 0)
    (hy : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val = 1)
    (hg : ((rbRun ring (renewalBankStart ring seed) pre).1 e).grant = false)
    (hm : ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .IWAIT)
    (ht : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .AL) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  obtain ⟨q, hq⟩ : ∃ q : RenewalBankPayload n,
      ((rbRun ring (renewalBankStart ring seed) pre).2.sites (ring.rightNeighbor e)).worker = .payload q := by
    have h := (hJ.frame (ring.rightNeighbor e)).2
    rw [ht] at h
    exact h
  obtain ⟨atoms, hctl⟩ := bankWindowJointWaitingControllerOfPhase ring (rbRun ring (renewalBankStart ring seed) pre)
    e hJ hx (Or.inr (Or.inl hm))
  cases ho : q.origin with
  | some o =>
      have hsite := bankWindowGenuineWorkerSiteOfRun ring hn hbank seed pre
        (ring.rightNeighbor e) q o hq ho
      rw [hy] at hsite
      have hnb : ring.rightNeighbor o.root = (ring.rightNeighbor e) := hsite.symm
      have hroot : o.root = e := Counter.resetTrialNeighborInjective ring hnb
      have htaint : BankWindowTainted (rbRun ring (renewalBankStart ring seed) pre) (ring.rightNeighbor e) := Or.inr ⟨q, o, hq, ho⟩
      by_cases hc : Counter.Complete ring (rbRun ring (renewalBankStart ring seed) pre).1 e
      · by_cases hne : atoms = []
        · subst hne
          exact bankWindowOverlapSourceIwaitAlRootFieldsAt ring hn hbank seed
            pre e hJ ⟨hc, hg⟩ hm hctl q o hq ho hroot ht
        · exact False.elim (hJ.inheritedClean e ⟨hc, hg⟩
            (Or.inl ⟨atoms, hctl, hne⟩) ⟨0, hb⟩ htaint)
      · obtain ⟨limit, hproto⟩ :=
          bankWindowOverlapSourceActiveIncompleteProto ring (rbRun ring (renewalBankStart ring seed) pre) e hx hc
        have hlim : 0 + 1 ≤ limit := by
          rcases Nat.eq_zero_or_pos limit with h0 | h0
          · exfalso
            apply hproto.2.2
            rw [h0]
            exact hy
          · omega
        exact False.elim ((hJ.proto e limit hproto).2.2.2
          (by rw [hm]; intro hh; cases hh) (by rw [hm]; intro hh; cases hh)
          ⟨0, hb⟩ hlim htaint)
  | none =>
      have hcell := bankWindowJointSourceIwaitReturnCell (rbRun ring (renewalBankStart ring seed) pre).2 e (ring.rightNeighbor e)
        ((rbRun ring (renewalBankStart ring seed) pre).1 e) ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)) hx hy hg hm ht
      have hreads := bankWindowJointSelectedPairReads ring hn hbank (rbRun ring (renewalBankStart ring seed) pre) e
      have hmodeP : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).mode = .CSTART := hreads.1.trans hcell.1
      have hctlP := hreads.2.1.trans hcell.2.1
      have hwP : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites (ring.rightNeighbor e)).worker = .empty :=
        hreads.2.2.trans hcell.2.2
      have horig : (renewalBankReturned ((rbRun ring (renewalBankStart ring seed) pre).2.sites e).controller
          ((rbRun ring (renewalBankStart ring seed) pre).2.sites (ring.rightNeighbor e)).worker (ring.rightNeighbor e)).origin = none := by
        rw [hq]
        simp [renewalBankReturned, renewalBankWorkerPayload, ho]
      apply bankWindowOverlapSourceAlignedCleanRootFieldsAt ring hn hbank seed
        pre e
      · intro h _
        rw [hmodeP] at h
        cases h
      · exact bankWindowJointPostAlignedCleanOfOld ring hn seed pre e hx
          (bankWindowJointWaitSourceOldAlignedClean ring (rbRun ring (renewalBankStart ring seed) pre) e hJ hx hg
            (Or.inr (Or.inl hm))
            (fun h _ => by rw [hm] at h; cases h)
            (fun _ => by rw [ht]; intro h; cases h))
          (bankWindowJointUntaintedOfEmpty (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) (ring.rightNeighbor e) hwP)
      · intro q' o' hc ho'
        rw [hctlP] at hc
        injection hc with hqq
        rw [← hqq, horig] at ho'
        cases ho'

/-- M2-f, lease > 1: grant-free PACK-zero wait source meeting a
non-matching return token on an aligned PACK-one responder, any OLD
window. The source keeps mode and controller, e+ worker is erased. An OLD
(RWAIT, waiting []) source would have RR, RL or E at e+
(bankWindowJointResetWaitFront), not a mismatched return token; so the
OLD aligned digits off e+ are clean
(bankWindowJointWaitSourceOldAlignedClean) and
bankWindowOverlapSourceAlignedCleanRootFieldsAt applies.
Consumer: the M2 SRC dispatch bankWindowOverlapSourceRootFieldsAt. -/
theorem bankWindowOverlapSourceMismatchLongRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n)) (e : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hx : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val = 0)
    (hy : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val = 1)
    (hg : ((rbRun ring (renewalBankStart ring seed) pre).1 e).grant = false)
    (hcases : ((((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .RWAIT ∧ ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .AL) ∨
       (((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .RWAIT ∧ ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .CL0) ∨
       (((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .RWAIT ∧ ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .CL1) ∨
       (((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .IWAIT ∧ ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .RL) ∨
       (((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .IWAIT ∧ ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .CL0) ∨
       (((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .IWAIT ∧ ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .CL1) ∨
       (((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .CWAIT ∧ ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .RL) ∨
       (((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .CWAIT ∧ ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .AL)))
    (hlong : 1 < ((rbRun ring (renewalBankStart ring seed) pre).1 e).lease.val) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  have hcell := bankWindowJointSourceMismatchLongCell (rbRun ring (renewalBankStart ring seed) pre).2 e (ring.rightNeighbor e)
    ((rbRun ring (renewalBankStart ring seed) pre).1 e) ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)) hx hy hg hcases hlong
  have hreads := bankWindowJointSelectedPairReads ring hn hbank (rbRun ring (renewalBankStart ring seed) pre) e
  have hmodeP : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).mode = ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode := hreads.1.trans hcell.1
  have hctlP : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites e).controller = ((rbRun ring (renewalBankStart ring seed) pre).2.sites e).controller :=
    hreads.2.1.trans hcell.2.1
  have hwP : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites (ring.rightNeighbor e)).worker = .empty := hreads.2.2.trans hcell.2.2
  have hm : ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .RWAIT ∨ ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .IWAIT ∨
      ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .CWAIT := by
    rcases hcases with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ |
      ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inl h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inr h)
  have hret : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .AL ∨ ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .CL0 ∨
      ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .CL1 ∨ ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .RL := by
    rcases hcases with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ |
      ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inl h
  have hRW : ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .RWAIT → ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok ≠ .RL := by
    intro hr htr
    rcases hcases with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ |
      ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩
    · rw [htr] at h'
      cases h'
    · rw [htr] at h'
      cases h'
    · rw [htr] at h'
      cases h'
    · rw [hr] at h
      cases h
    · rw [hr] at h
      cases h
    · rw [hr] at h
      cases h
    · rw [hr] at h
      cases h
    · rw [hr] at h
      cases h
  have htokNE : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok ≠ .E := by
    intro h
    rcases hret with h' | h' | h' | h' <;> rw [h] at h' <;> cases h'
  have hrwOld : ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .RWAIT →
      ((rbRun ring (renewalBankStart ring seed) pre).2.sites e).controller = .waiting [] → False := by
    intro hr hc
    rcases (bankWindowJointResetWaitFront ring (rbRun ring (renewalBankStart ring seed) pre) e hJ hx hg hr hc).2 with
      h | h | h
    · rcases hret with h' | h' | h' | h' <;> rw [h] at h' <;> cases h'
    · exact hRW hr h
    · exact htokNE h
  obtain ⟨atoms, hctl⟩ := bankWindowJointWaitingControllerOfPhase ring (rbRun ring (renewalBankStart ring seed) pre)
    e hJ hx hm
  apply bankWindowOverlapSourceAlignedCleanRootFieldsAt ring hn hbank seed pre e
  · intro h1 h2
    rw [hmodeP] at h1
    rw [hctlP] at h2
    exact hrwOld h1 h2
  · exact bankWindowJointPostAlignedCleanOfOld ring hn seed pre e hx
      (bankWindowJointWaitSourceOldAlignedClean ring (rbRun ring (renewalBankStart ring seed) pre) e hJ hx hg hm
        hrwOld (fun _ => htokNE))
      (bankWindowJointUntaintedOfEmpty (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) (ring.rightNeighbor e) hwP)
  · intro q o hc _
    rw [hctlP, hctl] at hc
    cases hc

/-- M2-a: grant-free PACK-zero wait source whose first responder PACK
changes (OLD e+ PACK not 1), lease > 1. The source keeps mode and
controller, the responder site is cleared and gets PACK 1. The OLD window
is incomplete with proto limit 0, so an OLD (RWAIT, waiting []) source is
impossible (bankWindowJointResetWaitFront would make e+ PACK 1), the OLD
aligned digits are clean (bankWindowJointWaitSourceOldAlignedClean, orphan
clause), and bankWindowOverlapSourceAlignedCleanRootFieldsAt applies even
when the repaired digit makes the POST window complete.
Consumer: the M2 SRC dispatch bankWindowOverlapSourceRootFieldsAt. -/
theorem bankWindowOverlapSourceChangedLongWaitRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n)) (e : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hx : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val = 0)
    (hy : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val ≠ 1)
    (hg : ((rbRun ring (renewalBankStart ring seed) pre).1 e).grant = false)
    (hm : (((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .RWAIT ∨ ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .IWAIT ∨
        ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .CWAIT))
    (hlong : 1 < ((rbRun ring (renewalBankStart ring seed) pre).1 e).lease.val) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  have hcell := bankWindowJointSourceChangedLongCell (rbRun ring (renewalBankStart ring seed) pre).2 e (ring.rightNeighbor e)
    ((rbRun ring (renewalBankStart ring seed) pre).1 e) ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)) hx hy hg hm hlong
  have hreads := bankWindowJointSelectedPairReads ring hn hbank (rbRun ring (renewalBankStart ring seed) pre) e
  have hmodeP : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).mode = ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode := hreads.1.trans hcell.1
  have hctlP : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites e).controller = ((rbRun ring (renewalBankStart ring seed) pre).2.sites e).controller :=
    hreads.2.1.trans hcell.2.1
  have hwP : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites (ring.rightNeighbor e)).worker = .empty := hreads.2.2.trans hcell.2.2
  have hrwOld : ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .RWAIT →
      ((rbRun ring (renewalBankStart ring seed) pre).2.sites e).controller = .waiting [] → False := by
    intro hr hc
    exact hy (bankWindowJointResetWaitFront ring (rbRun ring (renewalBankStart ring seed) pre) e hJ hx hg hr hc).1
  obtain ⟨atoms, hctl⟩ := bankWindowJointWaitingControllerOfPhase ring (rbRun ring (renewalBankStart ring seed) pre)
    e hJ hx hm
  apply bankWindowOverlapSourceAlignedCleanRootFieldsAt ring hn hbank seed pre e
  · intro h1 h2
    rw [hmodeP] at h1
    rw [hctlP] at h2
    exact hrwOld h1 h2
  · exact bankWindowJointPostAlignedCleanOfOld ring hn seed pre e hx
      (bankWindowJointWaitSourceOldAlignedClean ring (rbRun ring (renewalBankStart ring seed) pre) e hJ hx hg hm
        hrwOld (fun hc => absurd (hc 1 (by
          have : 0 < (compileAdvice (ceilLogTwo n)).b := by
            change 0 < (compileAdvice (ceilLogTwo n)).s + 11
            omega
          omega)) hy))
      (bankWindowJointUntaintedOfEmpty (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) (ring.rightNeighbor e) hwP)
  · intro q o hc _
    rw [hctlP, hctl] at hc
    cases hc

/-- M2-j: grant-free PACK-zero wait source meeting a non-return token on
an aligned PACK-one responder with lease > 1 (continuing wait), any OLD
window: the eleven source-owned clauses are the Root bundle
bankWindowOverlapSourceLongWaitOwnClauses, proto and orphan the M3 row
bankWindowOverlapNonreturnLongWaitPrefixOrphan.
Consumer: the M2 SRC dispatch bankWindowOverlapSourceRootFieldsAt. -/
theorem bankWindowOverlapSourceLongWaitRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n)) (e : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hx : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val = 0)
    (hy : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val = 1)
    (hg : ((rbRun ring (renewalBankStart ring seed) pre).1 e).grant = false)
    (hm : (((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .RWAIT ∨ ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .IWAIT ∨
        ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .CWAIT))
    (hlong : 1 < ((rbRun ring (renewalBankStart ring seed) pre).1 e).lease.val)
    (hret : isRetTok ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = false) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  obtain ⟨hproto, horphan⟩ := bankWindowOverlapNonreturnLongWaitPrefixOrphan
    ring hn hbank seed pre e hJ hx hy hg hm hlong hret
  exact bankWindowRootFieldsAtOfSourceOwnClauses ring _ e
    (bankWindowOverlapSourceLongWaitOwnClauses ring hn hbank seed pre e hJ hx
      hy hg hm hlong hret) hproto horphan

/-- OLD (RWAIT, waiting []) at a PACK-zero grant-free root facing RL at
e+: the e+ worker is a pending receipt. Complete window: OLD resetWait
puts its front at digit one (every earlier digit token is E), with a
pending worker. Incomplete window: OLD proto clause three makes the
front token RR, so the front is not e+ and e+ would carry E.
Consumer: bankWindowOverlapSourceInheritedReturnRootFieldsAt (M2-b
inherited sub-row). -/
theorem bankWindowJointResetWaitFrontRl {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n) (e : Fin n)
    (hJ : BankWindowExact ring r)
    (hx : (r.1 e).pack.val = 0) (hg : (r.1 e).grant = false)
    (hm : (r.1 e).mode = .RWAIT)
    (hctl : (r.2.sites e).controller = .waiting [])
    (ht : (r.1 (ring.rightNeighbor e)).tok = .RL) :
    ∃ rho : RenewalBankReceipt n, (r.2.sites (ring.rightNeighbor e)).worker = .pending rho := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  by_cases hc : Counter.Complete ring r.1 e
  · obtain ⟨j, rho, hw, _, _, hE, _⟩ := hJ.resetWait e ⟨hc, hg⟩ hm hctl
    by_cases hj : j.val = 0
    · have hs : Counter.site ring e (j.val + 1) = (ring.rightNeighbor e) := by
        rw [hj] <;> rfl
      rw [hs] at hw
      exact ⟨rho, hw⟩
    · have h0 := hE ⟨0, hb⟩ (by show 0 < j.val; omega)
      change (r.1 (ring.rightNeighbor e)).tok = .E at h0
      rw [ht] at h0
      cases h0
  · obtain ⟨limit, hproto⟩ :=
      bankWindowOverlapSourceActiveIncompleteProto ring r e hx hc
    obtain ⟨j, _, rho, _, htk, _, hE⟩ :=
      (hJ.proto e limit hproto).2.2.1 ⟨hm, hctl⟩
    by_cases hj : j.val = 0
    · have hs : Counter.site ring e (j.val + 1) = (ring.rightNeighbor e) := by
        rw [hj] <;> rfl
      rw [hs, ht] at htk
      cases htk
    · have h0 := hE ⟨0, hb⟩ (by show 0 < j.val; omega)
      change (r.1 (ring.rightNeighbor e)).tok = .E at h0
      rw [ht] at h0
      cases h0

/-- Cell and memory row, matched RL/RWAIT or CL0/CWAIT return carried by a
payload worker: source to ARMED, controller the returned payload of that
worker, responder worker erased.
Consumer: bankWindowOverlapSourceInheritedReturnRootFieldsAt. -/
theorem bankWindowJointSourcePayloadReturnCell {n : Nat} {c : Compiled}
    (m : RenewalBankMemory n) (e dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1) (hg : x.grant = false)
    (hrow : (x.mode = .RWAIT ∧ y.tok = .RL) ∨ (x.mode = .CWAIT ∧ y.tok = .CL0))
    (q : RenewalBankPayload n) (hw : (m.sites dest).worker = .payload q) :
    (Counter.resetBankOld x y).1.mode = .ARMED ∧
    (renewalBankPairMemory c m e dest x y).1.controller =
      .active (renewalBankReturned (m.sites e).controller
        (.payload q) dest) ∧
    (renewalBankPairMemory c m e dest x y).2.worker = .empty := by
  have hb : 0 < c.b := by
    change 0 < c.s + 11
    omega
  have hbz : c.b ≠ 0 := by omega
  have hwide : c.b ≠ 1 := by
    change c.s + 11 ≠ 1
    omega
  have hp : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  have hpost : packNext x.pack.val y.pack.val c.b = 1 := by
    rw [hx, hy]
    exact hp
  rcases hrow with ⟨hm, ht⟩ | ⟨hm, ht⟩ <;> refine ⟨?_, ?_⟩ <;>
    first
    | (unfold Counter.resetBankOld
       rw [hpost]
       simp [bankPair, bankCell, hx, hy, hg, hm, ht, hb, hbz, hpost,
         isRetTok, isWaitMode, Id.run_pure, Id.run_bind]
       all_goals (try simp only [if_neg hbz, if_true, Id.run_pure])
       all_goals (try rfl))
    | (simp [renewalBankPairMemory, renewalBankWaitSlot, bankCell, hx, hy, hg,
        hm, ht, hb, hbz, hp, hwide, hw, isRetTok, isWaitMode, Id.run_pure,
        Id.run_bind])

/-- Inherited sub-row of M2-b and M2-d: grant-free PACK-zero source in
RWAIT meeting RL, or in CWAIT meeting CL0, on an aligned PACK-one
responder whose worker is an origin-free payload, any OLD window. The
POST source is ARMED with the origin-free returned controller and e+ is
erased. OLD (RWAIT, waiting []) would need a pending RL worker
(bankWindowJointResetWaitFrontRl), so the OLD aligned digits off e+ are
clean (bankWindowJointWaitSourceOldAlignedClean) and
bankWindowOverlapSourceAlignedCleanRootFieldsAt applies.
Consumer: the M2 SRC dispatch bankWindowOverlapSourceRootFieldsAt. -/
theorem bankWindowOverlapSourceInheritedReturnRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n)) (e : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hx : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val = 0)
    (hy : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val = 1)
    (hg : ((rbRun ring (renewalBankStart ring seed) pre).1 e).grant = false)
    (hrow : (((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .RWAIT ∧ ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .RL) ∨
      (((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .CWAIT ∧ ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .CL0))
    (q : RenewalBankPayload n)
    (hq : ((rbRun ring (renewalBankStart ring seed) pre).2.sites (ring.rightNeighbor e)).worker = .payload q)
    (ho : q.origin = none) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  have hcell := bankWindowJointSourcePayloadReturnCell (rbRun ring (renewalBankStart ring seed) pre).2 e (ring.rightNeighbor e)
    ((rbRun ring (renewalBankStart ring seed) pre).1 e) ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)) hx hy hg hrow q hq
  have hreads := bankWindowJointSelectedPairReads ring hn hbank (rbRun ring (renewalBankStart ring seed) pre) e
  have hmodeP : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 e).mode = .ARMED := hreads.1.trans hcell.1
  have hctlP := hreads.2.1.trans hcell.2.1
  have hwP : ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).2.sites (ring.rightNeighbor e)).worker = .empty := hreads.2.2.trans hcell.2.2
  have horig : (renewalBankReturned ((rbRun ring (renewalBankStart ring seed) pre).2.sites e).controller
      (.payload q) (ring.rightNeighbor e)).origin = none := by
    simp [renewalBankReturned, renewalBankWorkerPayload, ho]
  have hm : ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .RWAIT ∨ ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .IWAIT ∨
      ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .CWAIT := by
    rcases hrow with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  have htokNE : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok ≠ .E := by
    intro h
    rcases hrow with ⟨_, h'⟩ | ⟨_, h'⟩ <;> rw [h] at h' <;> cases h'
  have hrwOld : ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .RWAIT →
      ((rbRun ring (renewalBankStart ring seed) pre).2.sites e).controller = .waiting [] → False := by
    intro hr hc
    rcases hrow with ⟨_, h'⟩ | ⟨h, _⟩
    · obtain ⟨rho, hw⟩ := bankWindowJointResetWaitFrontRl ring (rbRun ring (renewalBankStart ring seed) pre) e hJ hx
        hg hr hc h'
      rw [hq] at hw
      cases hw
    · rw [hr] at h
      cases h
  apply bankWindowOverlapSourceAlignedCleanRootFieldsAt ring hn hbank seed pre e
  · intro h _
    rw [hmodeP] at h
    cases h
  · exact bankWindowJointPostAlignedCleanOfOld ring hn seed pre e hx
      (bankWindowJointWaitSourceOldAlignedClean ring (rbRun ring (renewalBankStart ring seed) pre) e hJ hx hg hm
        hrwOld (fun _ => htokNE))
      (bankWindowJointUntaintedOfEmpty (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) (ring.rightNeighbor e) hwP)
  · intro q' o' hc ho'
    rw [hctlP] at hc
    injection hc with hqq
    rw [← hqq, horig] at ho'
    cases ho'

/-- Weight of a binary digit: 2^d if set, else 0 (local copy of the
BankTrialCompare weight, which is not imported here).
Consumer: bankWindowJointBinaryValueEqKMatched and
bankWindowJointBinaryValueZero. -/
def bankWindowJointBitWeight (c : Bool) (d : Nat) : Nat := if c then 2 ^ d else 0

/-- h 0 + ... + h (m-1), by recursion on the length.
Consumer: bankWindowJointBinaryValueEqKMatched and
bankWindowJointBinaryValueZero. -/
def bankWindowJointNatSum (h : Nat → Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => bankWindowJointNatSum h m + h m

/-- A List.ofFn sum is the recursive sum.
Consumer: bankWindowJointBinaryValueEqKMatched and
bankWindowJointBinaryValueZero. -/
theorem bankWindowJointOfFnSum (h : Nat → Nat) (m : Nat) :
    (List.ofFn (fun j : Fin m => h j.val)).sum = bankWindowJointNatSum h m := by
  induction m with
  | zero => simp [bankWindowJointNatSum]
  | succ m ih =>
      rw [List.ofFn_succ_last, List.sum_append_nat]
      simp only [Fin.val_castSucc, Fin.val_last, List.sum_cons, List.sum_nil,
        Nat.add_zero]
      rw [ih]
      rfl

/-- An m-bit binary sum is below 2^m.
Consumer: bankWindowJointBinaryInjective. -/
theorem bankWindowJointBinaryLt (f : Nat → Bool) (m : Nat) :
    bankWindowJointNatSum (fun d => bankWindowJointBitWeight (f d) d) m < 2 ^ m := by
  induction m with
  | zero => show 0 < 2 ^ 0; decide
  | succ m ih =>
      have hp : 2 ^ (m + 1) = 2 ^ m * 2 := Nat.pow_succ 2 m
      show bankWindowJointNatSum (fun d => bankWindowJointBitWeight (f d) d) m +
        bankWindowJointBitWeight (f m) m < 2 ^ (m + 1)
      cases hfm : f m with
      | false =>
          have h0 : bankWindowJointBitWeight false m = 0 := rfl
          rw [h0]
          omega
      | true =>
          have h1 : bankWindowJointBitWeight true m = 2 ^ m := rfl
          rw [h1]
          omega

/-- Two m-bit words with the same binary value agree digitwise.
Consumer: bankWindowJointBinaryValueEqKMatched. -/
theorem bankWindowJointBinaryInjective (f g : Nat → Bool) (m : Nat) :
    bankWindowJointNatSum (fun d => bankWindowJointBitWeight (f d) d) m =
      bankWindowJointNatSum (fun d => bankWindowJointBitWeight (g d) d) m →
    ∀ l, l < m → f l = g l := by
  induction m with
  | zero =>
      intro _ l hl
      exact absurd hl (Nat.not_lt_zero l)
  | succ m ih =>
      intro heq l hl
      have hF := bankWindowJointBinaryLt f m
      have hG := bankWindowJointBinaryLt g m
      have heq' : bankWindowJointNatSum (fun d => bankWindowJointBitWeight (f d) d) m +
          bankWindowJointBitWeight (f m) m =
        bankWindowJointNatSum (fun d => bankWindowJointBitWeight (g d) d) m +
          bankWindowJointBitWeight (g m) m := heq
      have h0 : bankWindowJointBitWeight false m = 0 := rfl
      have h1 : bankWindowJointBitWeight true m = 2 ^ m := rfl
      have hmm : f m = g m ∧
          bankWindowJointNatSum (fun d => bankWindowJointBitWeight (f d) d) m =
            bankWindowJointNatSum (fun d => bankWindowJointBitWeight (g d) d) m := by
        cases hfm : f m with
        | false =>
            cases hgm : g m with
            | false =>
                rw [hfm, hgm, h0] at heq'
                exact ⟨rfl, by omega⟩
            | true =>
                rw [hfm, hgm, h0, h1] at heq'
                exfalso
                omega
        | true =>
            cases hgm : g m with
            | false =>
                rw [hfm, hgm, h0, h1] at heq'
                exfalso
                omega
            | true =>
                rw [hfm, hgm, h1] at heq'
                exact ⟨rfl, by omega⟩
      by_cases hlm : l = m
      · subst hlm
        exact hmm.1
      · exact ih hmm.2 l (by omega)

/-- An all-zero word has binary value zero.
Consumer: bankWindowJointBinaryValueZero. -/
theorem bankWindowJointNatSumZero (f : Nat → Bool) (m : Nat)
    (h : ∀ l, l < m → f l = false) :
    bankWindowJointNatSum (fun d => bankWindowJointBitWeight (f d) d) m = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
      show bankWindowJointNatSum (fun d => bankWindowJointBitWeight (f d) d) m +
        bankWindowJointBitWeight (f m) m = 0
      rw [ih (fun l hl => h l (by omega)), h m (by omega)]
      rfl

/-- An origin whose digits all carry bit false has binary value zero.
Consumer: bankWindowOverlapSourceResetReturnRootFieldsAt (birth row
M2-b: heads 0 equals the POST value). -/
theorem bankWindowJointBinaryValueZero {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (o : RenewalBankOrigin n)
    (h : ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      (C (Counter.site ring o.root (j.val + 1))).bit = false) :
    bankOriginBinaryValue ring C o = 0 := by
  have hv : bankOriginBinaryValue ring C o =
      bankWindowJointNatSum (fun d => bankWindowJointBitWeight
        ((C (Counter.site ring o.root (d + 1))).bit) d) (compileAdvice (ceilLogTwo n)).b := by
    unfold bankOriginBinaryValue
    exact bankWindowJointOfFnSum (fun d => bankWindowJointBitWeight
      ((C (Counter.site ring o.root (d + 1))).bit) d) (compileAdvice (ceilLogTwo n)).b
  rw [hv]
  exact bankWindowJointNatSumZero _ _ (fun l hl => h ⟨l, hl⟩)

/-- On the BANK band, an origin whose binary value equals K has every
digit bit equal to theta (theta spells K in b bits:
bankTrialProbabilityThetaBinaryEqualsK; binary words are injective).
Consumer: bankWindowOverlapSourceCompareReturnRootFieldsAt (M2-d: the CL0
mismatch flag gives value ≠ K, hence value < K). -/
theorem bankWindowJointBinaryValueEqKMatched {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (o : RenewalBankOrigin n)
    (hK : bankOriginBinaryValue ring r.1 o = (compileAdvice (ceilLogTwo n)).K) :
    bankComparatorPrefixMatched ring r o (compileAdvice (ceilLogTwo n)).b := by
  have hq : 3 ≤ ceilLogTwo n := by
    have hs : (compileAdvice (ceilLogTwo n)).useSmall = decide (ceilLogTwo n ≤ qStar) := rfl
    rw [hs] at hbank
    have hnot : ¬ ceilLogTwo n ≤ qStar := of_decide_eq_false hbank
    change ¬ ceilLogTwo n ≤ 79 at hnot
    omega
  have htheta := bankTrialProbabilityThetaBinaryEqualsK (ceilLogTwo n) hq
  have hv : bankOriginBinaryValue ring r.1 o =
      bankWindowJointNatSum (fun d => bankWindowJointBitWeight
        ((r.1 (Counter.site ring o.root (d + 1))).bit) d) (compileAdvice (ceilLogTwo n)).b := by
    unfold bankOriginBinaryValue
    exact bankWindowJointOfFnSum (fun d => bankWindowJointBitWeight
      ((r.1 (Counter.site ring o.root (d + 1))).bit) d) (compileAdvice (ceilLogTwo n)).b
  have ht : bankTrialLiveThetaBinary (ceilLogTwo n) =
      bankWindowJointNatSum (fun d => bankWindowJointBitWeight
        ((compileAdvice (ceilLogTwo n)).theta d) d) (compileAdvice (ceilLogTwo n)).b := by
    unfold bankTrialLiveThetaBinary
    exact bankWindowJointOfFnSum (fun d => bankWindowJointBitWeight
      ((compileAdvice (ceilLogTwo n)).theta d) d) (compileAdvice (ceilLogTwo n)).b
  have hall := bankWindowJointBinaryInjective
    (fun d => (r.1 (Counter.site ring o.root (d + 1))).bit)
    (fun d => (compileAdvice (ceilLogTwo n)).theta d) (compileAdvice (ceilLogTwo n)).b (by rw [← hv, ← ht, hK, htheta])
  intro j _
  exact hall j.val j.isLt

/-- If every POST digit of e carries token E, no POST comparator worker
has its origin rooted at e: such a worker sits on the digit of e indexed
by its PACK (ReceiptInv.workerSite) and carries a live comparison token.
Consumer: bankWindowOverlapSourceCompareReturnRootFieldsAt and
bankWindowOverlapSourceResetReturnRootFieldsAt. -/
theorem bankWindowJointNoComparatorOfEmptyTokens {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n)) (e : Fin n)
    (htok : ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ((renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 (Counter.site ring e (j.val + 1))).tok = .E) :
    ∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
      o.root = e → BankComparatorOriginWorker ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) o i p → False := by
  intro o i p hroot hcomp
  obtain ⟨hw, ho, hlive⟩ := hcomp
  have hrun : rbRun ring (renewalBankStart ring seed) (pre ++ [e]) = (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) := by
    rw [rbRunAppend]
    rfl
  rw [← hrun] at htok hw hlive
  have hband := bankWindowOverlapGenuineWorkerInBand ring hn hbank seed
    (pre ++ [e]) i p o hw ho
  have hsite := bankWindowGenuineWorkerSiteOfRun ring hn hbank seed
    (pre ++ [e]) i p o hw ho
  generalize rbRun ring (renewalBankStart ring seed) (pre ++ [e]) = X
    at htok hw hlive hband hsite
  rw [hroot] at hsite
  obtain ⟨hlo, hhi⟩ := hband
  -- Term proofs, not omega: omega's auxiliary proof took the kernel 104 s to check here.
  have hk : (X.1 i).pack.val - 1 < (compileAdvice (ceilLogTwo n)).b :=
    Nat.lt_of_lt_of_le (Nat.sub_lt hlo Nat.one_pos) hhi
  have hsucc : (X.1 i).pack.val - 1 + 1 = (X.1 i).pack.val := Nat.sub_add_cancel hlo
  have hc : (X.1 (Counter.site ring e ((X.1 i).pack.val - 1 + 1))).tok = .E :=
    htok ⟨(X.1 i).pack.val - 1, hk⟩
  rw [hsucc, ← hsite] at hc
  rw [hc] at hlive
  rcases hlive with h | h | h | h <;> cases h

/-- The eleven source-owned clauses at a root that is ARMED with a genuine
active controller p of origin o, every digit token E, heads equal to the
binary value and value below K, and no comparator worker rooted there.
Every other clause is guarded by another mode or by an inherited
controller.
Consumer: bankWindowOverlapSourceCompareReturnRootFieldsAt and
bankWindowOverlapSourceResetReturnRootFieldsAt. -/
theorem bankWindowJointArmedOwnClausesOfReturn {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n) (root : Fin n)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hmode : (r.1 root).mode = .ARMED)
    (hactive : (r.2.sites root).controller = .active p)
    (horigin : p.origin = some o)
    (hnoComparator : ∀ (o' : RenewalBankOrigin n) (i : Fin n)
      (q : RenewalBankPayload n), o'.root = root →
      BankComparatorOriginWorker ring r o' i q → False)
    (htokens : ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      (r.1 (Counter.site ring root (j.val + 1))).tok = .E)
    (hheads : p.heads = bankOriginBinaryValue ring r.1 o)
    (hlt : bankOriginBinaryValue ring r.1 o < (compileAdvice (ceilLogTwo n)).K) :
    bankWindowOverlapSourceOwnClauses ring r root := by
  unfold bankWindowOverlapSourceOwnClauses
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o' i q hroot hw
    exact False.elim (hnoComparator o' i q hroot hw)
  · intro o' i q hroot hw _
    exact False.elim (hnoComparator o' i q hroot hw)
  · intro o' i q hroot hw _
    exact False.elim (hnoComparator o' i q hroot hw)
  · intro o' i q hroot hw _
    exact False.elim (hnoComparator o' i q hroot hw)
  · intro _ hinherited
    unfold BankWindowInheritedController at hinherited
    rcases hinherited with ⟨atoms, hc, _⟩ | ⟨q, hc, hnone⟩
    · rw [hactive] at hc
      cases hc
    · rw [hactive] at hc
      cases hc
      rw [horigin] at hnone
      cases hnone
  · intro _ hm
    rw [hmode] at hm
    cases hm
  · intro o' q _ _ hctl hqorigin
    have hq : q = p := by
      rw [hactive] at hctl
      cases hctl
      rfl
    subst q
    have ho : o' = o := Option.some.inj (hqorigin.symm.trans horigin)
    subst o'
    refine ⟨htokens, hheads, fun _ => hlt, ?_⟩
    intro h
    rw [hmode] at h
    cases h
  · intro o' i q _ hm
    rw [hmode] at hm
    cases hm
  · intro o' i q hroot _ _ hm
    rw [hroot, hmode] at hm
    cases hm
  · intro _ hm
    rw [hmode] at hm
    cases hm
  · intro _ hm
    rw [hmode] at hm
    cases hm

/-- Cell row of a matched RL/RWAIT or CL0/CWAIT return: both bits kept,
the responder token erased.
Consumer: bankWindowJointMatchedReturnEndpointReads. -/
theorem bankWindowJointSourceMatchedReturnBits {c : Compiled} (x y : Agent c)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1) (hg : x.grant = false)
    (hrow : (x.mode = .RWAIT ∧ y.tok = .RL) ∨ (x.mode = .CWAIT ∧ y.tok = .CL0)) :
    (Counter.resetBankOld x y).1.bit = x.bit ∧
    (Counter.resetBankOld x y).2.bit = y.bit ∧
    (Counter.resetBankOld x y).2.tok = .E := by
  have hb : 0 < c.b := by
    change 0 < c.s + 11
    omega
  have hbz : c.b ≠ 0 := by omega
  have hp : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  rcases hrow with ⟨hm, ht⟩ | ⟨hm, ht⟩ <;>
    simp [Counter.resetBankOld, bankPair, bankCell, hx, hy, hg, hm, ht, hp,
      hbz, hb, isRetTok, Id.run_pure, Id.run_bind]
  all_goals (try simp only [if_neg hbz, if_true, Id.run_pure])
  all_goals (try rfl)

/-- POST endpoint reads of a matched RL/RWAIT or CL0/CWAIT return at a
grant-free PACK-zero source with an aligned PACK-one responder.
Consumer: bankWindowJointMatchedReturnDigitReads. -/
theorem bankWindowJointMatchedReturnEndpointReads {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hx : (r.1 e).pack.val = 0) (hy : (r.1 (ring.rightNeighbor e)).pack.val = 1)
    (hg : (r.1 e).grant = false)
    (hrow : ((r.1 e).mode = .RWAIT ∧ (r.1 (ring.rightNeighbor e)).tok = .RL) ∨
      ((r.1 e).mode = .CWAIT ∧ (r.1 (ring.rightNeighbor e)).tok = .CL0)) :
    ((renewalBankNext ring r e).1 e).bit = (r.1 e).bit ∧
    ((renewalBankNext ring r e).1 (ring.rightNeighbor e)).bit = (r.1 (ring.rightNeighbor e)).bit ∧
    ((renewalBankNext ring r e).1 (ring.rightNeighbor e)).tok = .E := by
  have hraw := bankWindowJointSourceMatchedReturnBits (r.1 e) (r.1 (ring.rightNeighbor e)) hx hy
    hg hrow
  have htrip := bankWindowClosureSelectedBankTrip ring hn hbank r e
  have hsrc := congrArg (fun t : Mode × Bool × BTok => t.2.1) htrip.1
  have hdst := congrArg (fun t : Mode × Bool × BTok => t.2.1) htrip.2
  have htok := congrArg (fun t : Mode × Bool × BTok => t.2.2) htrip.2
  change ((renewalBankNext ring r e).1 e).bit =
    (Counter.resetBankOld (r.1 e) (r.1 (ring.rightNeighbor e))).1.bit at hsrc
  change ((renewalBankNext ring r e).1 (ring.rightNeighbor e)).bit =
    (Counter.resetBankOld (r.1 e) (r.1 (ring.rightNeighbor e))).2.bit at hdst
  change ((renewalBankNext ring r e).1 (ring.rightNeighbor e)).tok =
    (Counter.resetBankOld (r.1 e) (r.1 (ring.rightNeighbor e))).2.tok at htok
  exact ⟨hsrc.trans hraw.1, hdst.trans hraw.2.1, htok.trans hraw.2.2⟩

/-- Matched RL/RWAIT or CL0/CWAIT return whose OLD window has e+ as its
only token: every POST digit token of e is E, and every origin rooted at
e keeps its binary value (bits framed).
Consumer: bankWindowOverlapSourceCompareReturnRootFieldsAt and
bankWindowOverlapSourceResetReturnRootFieldsAt. -/
theorem bankWindowJointMatchedReturnDigitReads {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hx : (r.1 e).pack.val = 0) (hy : (r.1 (ring.rightNeighbor e)).pack.val = 1)
    (hg : (r.1 e).grant = false)
    (hrow : ((r.1 e).mode = .RWAIT ∧ (r.1 (ring.rightNeighbor e)).tok = .RL) ∨
      ((r.1 e).mode = .CWAIT ∧ (r.1 (ring.rightNeighbor e)).tok = .CL0))
    (honly : bankWindowOnlyToken ring r e (ring.rightNeighbor e))
    (o : RenewalBankOrigin n) (hroot : o.root = e) :
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ((renewalBankNext ring r e).1 (Counter.site ring e (j.val + 1))).tok =
        .E) ∧
    bankOriginBinaryValue ring (renewalBankNext ring r e).1 o =
      bankOriginBinaryValue ring r.1 o := by
  have hreads := bankWindowJointMatchedReturnEndpointReads ring hn hbank r e
    hx hy hg hrow
  have hallBits := bankWindowOverlapSelectedBitFrame ring r e hreads.1
    hreads.2.1
  have hbits : bankWindowReadDigitBits ring r (renewalBankNext ring r e)
      o.root := by
    intro j
    exact hallBits (Counter.site ring o.root (j.val + 1))
  have hvalue := bankWindowOverlapComparatorBinaryBitTransport ring r
    (renewalBankNext ring r e) o hbits
  refine ⟨?_, hvalue⟩
  intro j
  by_cases hfirst : j.val = 0
  · have hsite : Counter.site ring e (j.val + 1) = (ring.rightNeighbor e) := by
      rw [hfirst] <;> rfl
    rw [hsite]
    exact hreads.2.2
  · have hlimit : j.val + 1 ≤ (compileAdvice (ceilLogTwo n)).b + 1 := by
      have hj := j.isLt
      omega
    have hsrc : Counter.site ring e (j.val + 1) ≠ e := by
      have hd := bankWindowIncidenceSiteDistinct ring hbank e 0 (j.val + 1)
        (by omega) hlimit
      change e ≠ Counter.site ring e (j.val + 1) at hd
      exact hd.symm
    have hdst : Counter.site ring e (j.val + 1) ≠ (ring.rightNeighbor e) := by
      have hd := bankWindowIncidenceSiteDistinct ring hbank e 1 (j.val + 1)
        (by omega) hlimit
      change ring.rightNeighbor e ≠ Counter.site ring e (j.val + 1) at hd
      exact hd.symm
    have hf := (bankWindowExactOffPairFrame ring r e
      (Counter.site ring e (j.val + 1)) hsrc hdst).1
    have htokOld : (r.1 (Counter.site ring e (j.val + 1))).tok = .E := by
      by_cases he : (r.1 (Counter.site ring e (j.val + 1))).tok = .E
      · exact he
      · exact False.elim (hdst (honly j he))
    have htokFrame := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok) hf
    exact htokFrame.trans htokOld

/-- Digit one of e is e+; if the OLD e+ worker is tainted and e+ is
aligned, the OLD window of a grant-free PACK-zero source in a wait mode
(RWAIT only with an inherited list) is complete with an empty waiting
list: an inherited list contradicts inheritedClean (complete) or OLD
proto clause two (incomplete; the proto limit is at least one since e+
is aligned), and IWAIT/CWAIT incomplete windows contradict OLD proto
clause four.
Consumer: bankWindowOverlapSourceCompareReturnRootFieldsAt and
bankWindowOverlapSourceResetReturnRootFieldsAt. -/
theorem bankWindowJointTaintedResponderScope {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n) (e : Fin n)
    (hJ : BankWindowExact ring r)
    (hx : (r.1 e).pack.val = 0) (hy : (r.1 (ring.rightNeighbor e)).pack.val = 1)
    (hg : (r.1 e).grant = false)
    (hm : (r.1 e).mode = .RWAIT ∨ (r.1 e).mode = .IWAIT ∨
      (r.1 e).mode = .CWAIT)
    (htaint : BankWindowTainted r (ring.rightNeighbor e)) :
    (r.2.sites e).controller = .waiting [] ∧
    ((r.1 e).mode ≠ .RWAIT → Counter.Complete ring r.1 e) := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  obtain ⟨atoms, hctl⟩ := bankWindowJointWaitingControllerOfPhase ring r e hJ
    hx hm
  have hnotReset : (r.1 e).mode ≠ .RESET := by
    rcases hm with h | h | h <;> rw [h] <;> intro hh <;> cases hh
  have hlimOf : ∀ limit : Nat, BankWindowProtoRun ring r e limit →
      0 + 1 ≤ limit := by
    intro limit hproto
    rcases Nat.eq_zero_or_pos limit with h0 | h0
    · exfalso
      apply hproto.2.2
      rw [h0]
      exact hy
    · omega
  have hlist : atoms = [] := by
    by_cases hne : atoms = []
    · exact hne
    · exfalso
      by_cases hc : Counter.Complete ring r.1 e
      · exact hJ.inheritedClean e ⟨hc, hg⟩ (Or.inl ⟨atoms, hctl, hne⟩)
          ⟨0, hb⟩ htaint
      · obtain ⟨limit, hproto⟩ :=
          bankWindowOverlapSourceActiveIncompleteProto ring r e hx hc
        exact (hJ.proto e limit hproto).2.1 (Or.inl ⟨atoms, hctl, hne⟩)
          ⟨0, hb⟩ (hlimOf limit hproto) htaint
  subst hlist
  refine ⟨hctl, ?_⟩
  intro hrw
  by_cases hc : Counter.Complete ring r.1 e
  · exact hc
  · exfalso
    obtain ⟨limit, hproto⟩ :=
      bankWindowOverlapSourceActiveIncompleteProto ring r e hx hc
    exact (hJ.proto e limit hproto).2.2.2 hnotReset hrw ⟨0, hb⟩
      (hlimOf limit hproto) htaint

/-- M2-d, genuine part: grant-free PACK-zero CWAIT source meeting CL0 on
an aligned PACK-one responder whose worker is not an origin-free payload.
The CL0 worker is then a genuine payload rooted at e
(ReceiptInv.workerSite), so the OLD window is complete with waiting []
(bankWindowJointTaintedResponderScope). The POST source is ARMED with the
genuine returned controller (bankWindowOverlapSourceCountingCwaitClZeroReturnFields);
POST armedExact: every digit token E (OLD compareExact only-token at e+,
e+ erased), heads equal to the binary value (bits framed), and value < K:
value ≤ K by compareExact and value ≠ K because CL0 flags a mismatch
(phaseFlags) while value K would match theta everywhere
(bankWindowJointBinaryValueEqKMatched).
Consumer: the M2 SRC dispatch bankWindowOverlapSourceRootFieldsAt. -/
theorem bankWindowOverlapSourceCompareReturnRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n)) (e : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hx : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val = 0)
    (hy : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val = 1)
    (hg : ((rbRun ring (renewalBankStart ring seed) pre).1 e).grant = false)
    (hm : ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .CWAIT)
    (ht : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .CL0)
    (hgen : ¬ ∃ q : RenewalBankPayload n,
      ((rbRun ring (renewalBankStart ring seed) pre).2.sites (ring.rightNeighbor e)).worker = .payload q ∧ q.origin = none) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  obtain ⟨p, hp⟩ : ∃ p : RenewalBankPayload n,
      ((rbRun ring (renewalBankStart ring seed) pre).2.sites (ring.rightNeighbor e)).worker = .payload p := by
    have h := (hJ.frame (ring.rightNeighbor e)).2
    rw [ht] at h
    exact h
  obtain ⟨o, ho⟩ : ∃ o : RenewalBankOrigin n, p.origin = some o := by
    cases ho : p.origin with
    | none => exact False.elim (hgen ⟨p, hp, ho⟩)
    | some o => exact ⟨o, rfl⟩
  have hsite := bankWindowGenuineWorkerSiteOfRun ring hn hbank seed pre
    (ring.rightNeighbor e) p o hp ho
  rw [hy] at hsite
  have hnb : ring.rightNeighbor o.root = (ring.rightNeighbor e) := hsite.symm
  have hroot : o.root = e := Counter.resetTrialNeighborInjective ring hnb
  have hscopeFacts := bankWindowJointTaintedResponderScope ring (rbRun ring (renewalBankStart ring seed) pre) e hJ hx
    hy hg (Or.inr (Or.inr hm)) (Or.inr ⟨p, o, hp, ho⟩)
  have hctl := hscopeFacts.1
  have hc : Counter.Complete ring (rbRun ring (renewalBankStart ring seed) pre).1 e :=
    hscopeFacts.2 (by rw [hm]; intro hh; cases hh)
  obtain ⟨hmodeP, _, q, hactive, _, hqo, hqh, _⟩ :=
    bankWindowOverlapSourceCountingCwaitClZeroReturnFields ring hn hbank seed
      pre e hJ ⟨hc, hg⟩ hm hctl p o hp ho hroot ht
  have hmis := bankWindowOverlapSourceCountingCwaitClZeroMismatch ring (rbRun ring (renewalBankStart ring seed) pre) e
    hJ hm hctl p o hp ho hroot ht
  have honly : bankWindowOnlyToken ring (rbRun ring (renewalBankStart ring seed) pre) e (ring.rightNeighbor e) := by
    have h := (hJ.compareExact o (ring.rightNeighbor e) p hp ho (by rw [hroot]; exact hm)
      (by rw [hroot]; exact hctl)).1
    rw [hroot] at h
    exact h
  have hreads := bankWindowJointMatchedReturnDigitReads ring hn hbank (rbRun ring (renewalBankStart ring seed) pre) e
    hx hy hg (Or.inr ⟨hm, ht⟩) honly o hroot
  have hlt : bankOriginBinaryValue ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e).1 o < (compileAdvice (ceilLogTwo n)).K := by
    rw [hreads.2]
    have hne : bankOriginBinaryValue ring (rbRun ring (renewalBankStart ring seed) pre).1 o ≠ (compileAdvice (ceilLogTwo n)).K := by
      intro hK
      exact hmis.1 (bankWindowJointBinaryValueEqKMatched ring hbank (rbRun ring (renewalBankStart ring seed) pre) o hK)
    have hle := hmis.2
    omega
  have hown := bankWindowJointArmedOwnClausesOfReturn ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e q o hmodeP
    hactive hqo
    (bankWindowJointNoComparatorOfEmptyTokens ring hn hbank seed pre e
      hreads.1)
    hreads.1 (hqh.trans hreads.2.symm) hlt
  exact bankWindowOverlapSourceCompleteRootFieldsAt ring hn seed pre e hc hown

/-- M2-b, genuine part: grant-free PACK-zero RWAIT source meeting RL on an
aligned PACK-one responder whose worker is not an origin-free payload. A
genuine payload is rooted at e and forces waiting [] with a tainted e+
(bankWindowJointTaintedResponderScope), but then the reset front sits at
e+ with a pending worker (bankWindowJointResetWaitFrontRl): impossible.
So the worker is a pending receipt rho, the list is empty, the row is a
birth (renewalBankBirth = some o with o.root = e), the OLD window is
complete with e+ its only token and a zero prefix
(bankWindowOverlapSourceOwnRwaitBirthCertificate). POST armedExact: every
digit token E, heads 0, value 0 (bits framed, zero prefix) and 0 < K.
Consumer: the M2 SRC dispatch bankWindowOverlapSourceRootFieldsAt. -/
theorem bankWindowOverlapSourceResetReturnRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n)) (e : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hx : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val = 0)
    (hy : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val = 1)
    (hg : ((rbRun ring (renewalBankStart ring seed) pre).1 e).grant = false)
    (hm : ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .RWAIT)
    (ht : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .RL)
    (hgen : ¬ ∃ q : RenewalBankPayload n,
      ((rbRun ring (renewalBankStart ring seed) pre).2.sites (ring.rightNeighbor e)).worker = .payload q ∧ q.origin = none) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hshape : (∃ rho : RenewalBankReceipt n,
        ((rbRun ring (renewalBankStart ring seed) pre).2.sites (ring.rightNeighbor e)).worker = .pending rho) ∨
      (∃ p : RenewalBankPayload n,
        ((rbRun ring (renewalBankStart ring seed) pre).2.sites (ring.rightNeighbor e)).worker = .payload p) := by
    have h := (hJ.frame (ring.rightNeighbor e)).2
    rw [ht] at h
    exact h
  obtain ⟨rho, hw⟩ : ∃ rho : RenewalBankReceipt n,
      ((rbRun ring (renewalBankStart ring seed) pre).2.sites (ring.rightNeighbor e)).worker = .pending rho := by
    rcases hshape with h | ⟨p, hp⟩
    · exact h
    · exfalso
      cases ho : p.origin with
      | none => exact hgen ⟨p, hp, ho⟩
      | some o =>
          have hscopeFacts := bankWindowJointTaintedResponderScope ring (rbRun ring (renewalBankStart ring seed) pre) e
            hJ hx hy hg (Or.inl hm) (Or.inr ⟨p, o, hp, ho⟩)
          obtain ⟨rho, hw⟩ := bankWindowJointResetWaitFrontRl ring (rbRun ring (renewalBankStart ring seed) pre) e hJ
            hx hg hm hscopeFacts.1 ht
          rw [hp] at hw
          cases hw
  have hscopeFacts := bankWindowJointTaintedResponderScope ring (rbRun ring (renewalBankStart ring seed) pre) e
    hJ hx hy hg (Or.inl hm) (Or.inl ⟨rho, hw⟩)
  have hctl := hscopeFacts.1
  have hp1 : packNext 0 1 (compileAdvice (ceilLogTwo n)).b = 1 := by
    simp [packNext, hb]
  have hbirth : renewalBankBirth ring (rbRun ring (renewalBankStart ring seed) pre).1 (rbRun ring (renewalBankStart ring seed) pre).2 e =
      some { service := (rbRun ring (renewalBankStart ring seed) pre).2.service, root := e, receipt := rho } := by
    have hrow : Counter.resetRootRow
        (bankCell ((rbRun ring (renewalBankStart ring seed) pre).1 e) ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val)
        (bankCell ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)) ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val)
        (packNext ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val (compileAdvice (ceilLogTwo n)).b)
        (compileAdvice (ceilLogTwo n)).b = .resetReturn := by
      rw [hx, hy, hp1]
      simp [Counter.resetRootRow, bankCell, hg, hm, ht, isRetTok]
    unfold renewalBankBirth
    rw [if_pos hrow, hw]
  have hc : Counter.Complete ring (rbRun ring (renewalBankStart ring seed) pre).1 e :=
    bankWindowClosureBirthComplete ring (rbRun ring (renewalBankStart ring seed) pre) e _ hJ hbirth
  obtain ⟨_, hmodeP, ⟨q, hactive, hqo, hqh⟩, honly, hzero⟩ :=
    bankWindowOverlapSourceOwnRwaitBirthCertificate ring hn hbank seed pre e
      _ hJ hbirth
  have hreads := bankWindowJointMatchedReturnDigitReads ring hn hbank (rbRun ring (renewalBankStart ring seed) pre) e
    hx hy hg (Or.inl ⟨hm, ht⟩) honly
    { service := (rbRun ring (renewalBankStart ring seed) pre).2.service, root := e, receipt := rho } rfl
  have hzeroVal : bankOriginBinaryValue ring (rbRun ring (renewalBankStart ring seed) pre).1
      { service := (rbRun ring (renewalBankStart ring seed) pre).2.service, root := e, receipt := rho } = 0 :=
    bankWindowJointBinaryValueZero ring (rbRun ring (renewalBankStart ring seed) pre).1 _
      (fun j => hzero j (by have := j.isLt; omega))
  have hq3 : 3 ≤ ceilLogTwo n := by
    have hs : (compileAdvice (ceilLogTwo n)).useSmall = decide (ceilLogTwo n ≤ qStar) := rfl
    have hbank' := hbank
    rw [hs] at hbank'
    have hnot : ¬ ceilLogTwo n ≤ qStar := of_decide_eq_false hbank'
    change ¬ ceilLogTwo n ≤ 79 at hnot
    omega
  have hKpos : 0 < (compileAdvice (ceilLogTwo n)).K := by
    change 0 < 2 * ceilLogTwo n + productionKappa (ceilLogTwo n)
    omega
  have hown := bankWindowJointArmedOwnClausesOfReturn ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e q _ hmodeP
    hactive hqo
    (bankWindowJointNoComparatorOfEmptyTokens ring hn hbank seed pre e
      hreads.1)
    hreads.1 (by rw [hreads.2, hzeroVal]; exact hqh)
    (by rw [hreads.2, hzeroVal]; exact hKpos)
  exact bankWindowOverlapSourceCompleteRootFieldsAt ring hn seed pre e hc hown

/-- M2-k, the SRC dispatch over the OLD state of the selected PACK-zero
source e (bankPair first-match order): grant; changed responder (exit
rows, or the long-lease wait row M2-a); RESET launch (complete or not);
return tokens (matched RL/RWAIT M2-b, AL/IWAIT M2-c, CL0/CWAIT M2-d,
CL1/CWAIT M2-e, ARMED/CSTART M2-g, mismatched with short lease M2-f or
long lease); ARMED/CSTART facing E (genuine A0/A1/S0/S1 rows, inherited
M2-h) or a non-return token (collision); wait modes facing a non-return
token (short lease M2-i, long lease M2-j). Matched RL/RWAIT and CL0/CWAIT
split on the e+ worker: origin-free payload
(bankWindowOverlapSourceInheritedReturnRootFieldsAt), otherwise the birth
row bankWindowOverlapSourceResetReturnRootFieldsAt (M2-b) and the genuine
comparison return bankWindowOverlapSourceCompareReturnRootFieldsAt (M2-d).
Consumer: bankWindowExactStep. -/
theorem bankWindowOverlapSourceRootFieldsAt {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n)) (e : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre))
    (hx : ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val = 0) :
    BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
  by_cases hgt : ((rbRun ring (renewalBankStart ring seed) pre).1 e).grant = true
  · exact bankWindowOverlapRootGrantRootFieldsAt ring hn hbank seed pre e hJ
      hx hgt
  have hgb : ((rbRun ring (renewalBankStart ring seed) pre).1 e).grant = false := by simpa using hgt
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hone : packNext 0 ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val (compileAdvice (ceilLogTwo n)).b = 1 := by
    simp [packNext, hb]
  by_cases hyc : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val ≠ 1
  · have hy := hyc
    have hch : packNext ((rbRun ring (renewalBankStart ring seed) pre).1 e).pack.val ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val (compileAdvice (ceilLogTwo n)).b ≠
        ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val := by
      rw [hx, hone]
      intro h
      exact hy h.symm
    have hexit := bankWindowOverlapChangedSourceExitRootFieldsAt ring hn hbank
      seed pre e hJ hx hch
    have hwait : (((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .RWAIT ∨ ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .IWAIT ∨
        ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .CWAIT) →
        BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
      intro hw
      by_cases hl : 1 < ((rbRun ring (renewalBankStart ring seed) pre).1 e).lease.val
      · exact bankWindowOverlapSourceChangedLongWaitRootFieldsAt ring hn hbank
          seed pre e hJ hx hy hgb hw hl
      · exact hexit (Or.inr (Or.inr (Or.inr ⟨hw, by omega⟩)))
    cases hm : ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode
    · exact hexit (Or.inl hm)
    · exact hwait (Or.inl hm)
    · exact hexit (Or.inr (Or.inl hm))
    · exact hwait (Or.inr (Or.inl hm))
    · exact hexit (Or.inr (Or.inr (Or.inl hm)))
    · exact hwait (Or.inr (Or.inr hm))
  have hy : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).pack.val = 1 := by omega
  have hmis : ((((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .RWAIT ∧ ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .AL) ∨
       (((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .RWAIT ∧ ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .CL0) ∨
       (((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .RWAIT ∧ ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .CL1) ∨
       (((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .IWAIT ∧ ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .RL) ∨
       (((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .IWAIT ∧ ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .CL0) ∨
       (((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .IWAIT ∧ ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .CL1) ∨
       (((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .CWAIT ∧ ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .RL) ∨
       (((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .CWAIT ∧ ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .AL)) →
      BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
    intro hcases
    by_cases hl : ((rbRun ring (renewalBankStart ring seed) pre).1 e).lease.val ≤ 1
    · exact bankWindowOverlapSourceMismatchTimeoutRootFieldsAt ring hn hbank
        seed pre e hJ hx hy hgb hcases hl
    · exact bankWindowOverlapSourceMismatchLongRootFieldsAt ring hn hbank seed
        pre e hJ hx hy hgb hcases (by omega)
  have hnonret : (((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .RWAIT ∨ ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .IWAIT ∨
        ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .CWAIT) →
      isRetTok ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = false →
      BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
    intro hw hret
    by_cases hl : ((rbRun ring (renewalBankStart ring seed) pre).1 e).lease.val ≤ 1
    · exact bankWindowOverlapSourceShortWaitRootFieldsAt ring hn hbank seed pre
        e hJ hx hy hgb hw hl hret
    · exact bankWindowOverlapSourceLongWaitRootFieldsAt ring hn hbank seed pre
        e hJ hx hy hgb hw (by omega) hret
  have hactiveRow : (((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .ARMED ∨ ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode = .CSTART) →
      isRetTok ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = false →
      (∀ (p : RenewalBankPayload n) (o : RenewalBankOrigin n),
        ((rbRun ring (renewalBankStart ring seed) pre).2.sites e).controller = .active p → p.origin = some o →
        ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .E →
        BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e) →
      BankWindowRootFieldsAt ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) e := by
    intro hphase hret hgen
    by_cases hE : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = .E
    · obtain ⟨p, hactive⟩ := bankWindowJointActiveControllerOfPhase ring (rbRun ring (renewalBankStart ring seed) pre)
        e hJ hx hphase
      cases ho : p.origin with
      | none =>
          exact bankWindowOverlapSourceInheritedActiveRootFieldsAt ring hn hbank
            seed pre e hJ hx hy hgb hphase hE p hactive ho
      | some o => exact hgen p o hactive ho hE
    · exact bankWindowOverlapSourceActiveCollisionRootFieldsAt ring hn hbank
        seed pre e hJ hx hy hgb hphase hret hE
  cases hm : ((rbRun ring (renewalBankStart ring seed) pre).1 e).mode
  · by_cases hc : Counter.Complete ring (rbRun ring (renewalBankStart ring seed) pre).1 e
    · exact bankWindowOverlapSourceResetLaunchRootFieldsAt ring hn hbank seed
        pre e hJ ⟨hc, hgb⟩ hm
    · exact bankWindowOverlapSourceResetLaunchIncompleteRootFieldsAt ring hn
        hbank seed pre e hc hx hy hgb hm
  · -- RWAIT
    cases ht : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok
    · exact hnonret (Or.inl hm) (by simp [ht, isRetTok])
    · exact hnonret (Or.inl hm) (by simp [ht, isRetTok])
    · by_cases hinh : ∃ q : RenewalBankPayload n,
          ((rbRun ring (renewalBankStart ring seed) pre).2.sites (ring.rightNeighbor e)).worker = .payload q ∧ q.origin = none
      · obtain ⟨q, hq, ho⟩ := hinh
        exact bankWindowOverlapSourceInheritedReturnRootFieldsAt ring hn hbank
          seed pre e hJ hx hy hgb (Or.inl ⟨hm, ht⟩) q hq ho
      · exact bankWindowOverlapSourceResetReturnRootFieldsAt ring hn hbank seed
          pre e hJ hx hy hgb hm ht hinh
    · exact hnonret (Or.inl hm) (by simp [ht, isRetTok])
    · exact hmis (Or.inl ⟨hm, ht⟩)
    · exact hnonret (Or.inl hm) (by simp [ht, isRetTok])
    · exact hnonret (Or.inl hm) (by simp [ht, isRetTok])
    · exact hmis (Or.inr (Or.inl ⟨hm, ht⟩))
    · exact hmis (Or.inr (Or.inr (Or.inl ⟨hm, ht⟩)))
  · -- ARMED
    by_cases hret : isRetTok ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = true
    · exact bankWindowOverlapSourceActiveReturnRootFieldsAt ring hn hbank seed
        pre e hJ hx hy hgb (Or.inl hm) hret
    · apply hactiveRow (Or.inl hm) (by simpa using hret)
      intro p o hactive ho _
      cases hbit : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).bit with
      | false =>
          exact bankWindowOverlapSourceArmedSetGenuineRootFieldsAt ring hn hbank
            seed pre e hJ hx hgb hm p o hactive ho hbit
      | true =>
          exact bankWindowOverlapSourceArmedIssueGenuineRootFieldsAt ring hn
            hbank seed pre e hJ hx hgb hm p o hactive ho hbit
  · -- IWAIT
    cases ht : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok
    · exact hnonret (Or.inr (Or.inl hm)) (by simp [ht, isRetTok])
    · exact hnonret (Or.inr (Or.inl hm)) (by simp [ht, isRetTok])
    · exact hmis (Or.inr (Or.inr (Or.inr (Or.inl ⟨hm, ht⟩))))
    · exact hnonret (Or.inr (Or.inl hm)) (by simp [ht, isRetTok])
    · exact bankWindowOverlapSourceIwaitReturnRootFieldsAt ring hn hbank seed
        pre e hJ hx hy hgb hm ht
    · exact hnonret (Or.inr (Or.inl hm)) (by simp [ht, isRetTok])
    · exact hnonret (Or.inr (Or.inl hm)) (by simp [ht, isRetTok])
    · exact hmis (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hm, ht⟩)))))
    · exact hmis (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hm, ht⟩))))))
  · -- CSTART
    by_cases hret : isRetTok ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok = true
    · exact bankWindowOverlapSourceActiveReturnRootFieldsAt ring hn hbank seed
        pre e hJ hx hy hgb (Or.inr hm) hret
    · apply hactiveRow (Or.inr hm) (by simpa using hret)
      intro p o hactive ho _
      by_cases hth : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).bit = (compileAdvice (ceilLogTwo n)).theta 0
      · exact bankWindowOverlapSourceCstartMatchGenuineRootFieldsAt ring hn
          hbank seed pre e hJ hx hgb hm p o hactive ho hth
      · exact bankWindowOverlapSourceCstartMismatchGenuineRootFieldsAt ring hn
          hbank seed pre e hJ hx hgb hm p o hactive ho hth
  · -- CWAIT
    cases ht : ((rbRun ring (renewalBankStart ring seed) pre).1 (ring.rightNeighbor e)).tok
    · exact hnonret (Or.inr (Or.inr hm)) (by simp [ht, isRetTok])
    · exact hnonret (Or.inr (Or.inr hm)) (by simp [ht, isRetTok])
    · exact hmis (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hm, ht⟩)))))))
    · exact hnonret (Or.inr (Or.inr hm)) (by simp [ht, isRetTok])
    · exact hmis (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hm, ht⟩)))))))
    · exact hnonret (Or.inr (Or.inr hm)) (by simp [ht, isRetTok])
    · exact hnonret (Or.inr (Or.inr hm)) (by simp [ht, isRetTok])
    · by_cases hinh : ∃ q : RenewalBankPayload n,
          ((rbRun ring (renewalBankStart ring seed) pre).2.sites (ring.rightNeighbor e)).worker = .payload q ∧ q.origin = none
      · obtain ⟨q, hq, ho⟩ := hinh
        exact bankWindowOverlapSourceInheritedReturnRootFieldsAt ring hn hbank
          seed pre e hJ hx hy hgb (Or.inr ⟨hm, ht⟩) q hq ho
      · exact bankWindowOverlapSourceCompareReturnRootFieldsAt ring hn hbank
          seed pre e hJ hx hy hgb hm ht hinh
    · exact bankWindowOverlapSourceClOneRootFieldsAt ring hn hbank seed pre e hJ
        hx hy hgb hm ht

/-- R11: one BANK scheduler edge preserves the BANK window exactness
invariant J on every reached state of the rooted renewal run. Every root
other than the selected PACK-zero source is dispatched by
bankWindowExactStepOfSourceRoot; the selected source root is
bankWindowOverlapSourceRootFieldsAt.
Consumer: the J run invariant (induction over the scheduler word) and the
L3 headline chain. -/
theorem bankWindowExactStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n)) (e : Fin n)
    (hJ : BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre)) :
    BankWindowExact ring (renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e) :=
  bankWindowExactStepOfSourceRoot ring hn hbank seed pre e hJ
    (fun hx => bankWindowOverlapSourceRootFieldsAt ring hn hbank seed pre e hJ
      hx)

end L3.BankWindow

#print axioms L3.BankWindow.bankWindowOverlapJointProtoInterior
#print axioms L3.BankWindow.bankWindowOverlapRootForeignProtoJoint
#print axioms L3.BankWindow.bankWindowOverlapRootJointFields
#print axioms L3.BankWindow.bankWindowExactOfRootFields
#print axioms L3.BankWindow.bankWindowOverlapOutsideCompareExactField
#print axioms L3.BankWindow.bankWindowOverlapOutsideRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapRootSourceForeignNoScope
#print axioms L3.BankWindow.bankWindowOverlapRootSourceForeignRootFieldsAt
#print axioms L3.BankWindow.bankWindowRootFieldsAtOfReset
#print axioms L3.BankWindow.bankWindowOverlapChangedResponderRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapIncomingGrantOrArmedRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapRepairIncompleteForeignRootFieldsAt
#print axioms L3.BankWindow.bankWindowEmptyControllerNotInherited
#print axioms L3.BankWindow.bankWindowOverlapRootGrantRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapChangedSourceExitRootFieldsAt
#print axioms L3.BankWindow.bankWindowJointSuccessorInjective
#print axioms L3.BankWindow.bankWindowOverlapRepairCompletedForeignRootFieldsAt
#print axioms L3.BankWindow.bankWindowJointIdPureFst
#print axioms L3.BankWindow.bankWindowJointIdPureSnd
#print axioms L3.BankWindow.bankWindowJointPairNonrootModes
#print axioms L3.BankWindow.bankWindowJointEndpointNonrootReset
#print axioms L3.BankWindow.bankWindowRootFieldsAtOfNonroot
#print axioms L3.BankWindow.bankWindowOverlapSourceNonrootRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapResponderNonrootRootFieldsAt
#print axioms L3.BankWindow.bankWindowJointIncomingZeroModeKeepOrResetCell
#print axioms L3.BankWindow.bankWindowJointIncomingModeKeepOrReset
#print axioms L3.BankWindow.bankWindowRootFieldsAtOfFrozen
#print axioms L3.BankWindow.bankWindowOverlapIncomingStableRootFieldsAt
#print axioms L3.BankWindow.bankWindowRootFieldsAtOfDigitReads
#print axioms L3.BankWindow.bankWindowJointIdlePairCell
#print axioms L3.BankWindow.bankWindowJointIdlePairReads
#print axioms L3.BankWindow.bankWindowOverlapStableIdlePairRootFieldsAt
#print axioms L3.BankWindow.bankWindowResetControllerEmpty
#print axioms L3.BankWindow.bankWindowOverlapForeignResetRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapStableInteriorInheritedRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapStableInteriorUntaintedRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapRepairCompleteRootFieldsAt
#print axioms L3.BankWindow.bankWindowJointAlignedSourceLive
#print axioms L3.BankWindow.bankWindowJointAlignedResponderLive
#print axioms L3.BankWindow.bankWindowJointAlignedWorkers
#print axioms L3.BankWindow.bankWindowJointTopEdgeTokens
#print axioms L3.BankWindow.bankWindowJointSpacerEdgeTokens
#print axioms L3.BankWindow.bankWindowJointStableEdgeShape
#print axioms L3.BankWindow.bankWindowJointStableEdgeComparatorPreimage
#print axioms L3.BankWindow.bankWindowOverlapStableNonrootPhaseFields
#print axioms L3.BankWindow.bankWindowOverlapStableFrozenPairRootFieldsAt
#print axioms L3.BankWindow.bankWindowJointAlignedQuietCells
#print axioms L3.BankWindow.bankWindowOverlapStableQuietPairReads
#print axioms L3.BankWindow.bankWindowJointTopTurnCells
#print axioms L3.BankWindow.bankWindowOverlapTopComparisonTurnCurrentFields
#print axioms L3.BankWindow.bankWindowOverlapStableCwaitMovedRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapStableCwaitNoGenuineRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapStableCwaitRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapStableNonrootOutOfScopeRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapTopGhostStableRootFieldsAt
#print axioms L3.BankWindow.bankWindowJointWaitingControllerShape
#print axioms L3.BankWindow.bankWindowJointSourceRootRwaitAlignedNotCwait
#print axioms L3.BankWindow.bankWindowJointSourceRootRwaitChangedNotCwait
#print axioms L3.BankWindow.bankWindowJointSourceRootIwaitAlignedNotCwait
#print axioms L3.BankWindow.bankWindowJointSourceRootIwaitChangedNotCwait
#print axioms L3.BankWindow.bankWindowJointSourceRootWaitNotCwait
#print axioms L3.BankWindow.bankWindowJointResponderChangedControllerEmpty
#print axioms L3.BankWindow.bankWindowJointResponderZeroControllerSlot
#print axioms L3.BankWindow.bankWindowJointSourceRootWaitingKept
#print axioms L3.BankWindow.bankWindowJointCwaitWaitingStepBack
#print axioms L3.BankWindow.bankWindowJointCwaitWaitingNoBirth
#print axioms L3.BankWindow.bankWindowJointCwaitWaitingNoOrigin
#print axioms L3.BankWindow.bankWindowOverlapStableCwaitWaitingRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapStableRwaitAssembly
#print axioms L3.BankWindow.bankWindowJointAlignedQuietWaitCells
#print axioms L3.BankWindow.bankWindowOverlapStableCellsUnchangedReads
#print axioms L3.BankWindow.bankWindowJointAlignedRrForwardCells
#print axioms L3.BankWindow.bankWindowJointAlignedRlBackCells
#print axioms L3.BankWindow.bankWindowOverlapStableRwaitRootFieldsAt
#print axioms L3.BankWindow.bankWindowJointBirthRootRwait
#print axioms L3.BankWindow.bankWindowJointOfFnSumUpdate
#print axioms L3.BankWindow.bankWindowJointBinaryValueBitSet
#print axioms L3.BankWindow.bankWindowJointLeTwoPowCeilLog
#print axioms L3.BankWindow.bankWindowJointCeilLogLe
#print axioms L3.BankWindow.bankWindowJointSuccLeTwoPow
#print axioms L3.BankWindow.bankWindowJointKBelowWidth
#print axioms L3.BankWindow.bankWindowJointAlignedIrToggleCells
#print axioms L3.BankWindow.bankWindowJointAlignedAlBackCells
#print axioms L3.BankWindow.bankWindowOverlapStableIwaitMovedRootFieldsAt
#print axioms L3.BankWindow.bankWindowJointBinaryValueCongr
#print axioms L3.BankWindow.bankWindowOverlapStableIwaitNoGenuineRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapStableIwaitRootFieldsAt
#print axioms L3.BankWindow.bankWindowRootFieldsAtOfSourceOwnClauses
#print axioms L3.BankWindow.bankWindowOverlapSourceCompleteRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapSourceResetLaunchRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapSourceRwaitNonreturnExpiryRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapSourceArmedSetRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapSourceArmedSetGenuineRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapSourceArmedIssueRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapSourceArmedIssueGenuineRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapSourceCstartIssueRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapSourceCstartMatchRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapSourceCstartMatchGenuineRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapSourceCstartMismatchRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapSourceCstartMismatchGenuineRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapSourceIwaitAlRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapSourceIwaitExpiredRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapSourceCwaitClOneRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapSourceCwaitExpiredRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapSourceWaitTimedOutRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapSourceActiveCollisionRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapSourceCleanCompleteRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapSourceCleanEmptyRootFieldsAt
#print axioms L3.BankWindow.bankWindowJointSupportOfNotOutside
#print axioms L3.BankWindow.bankWindowJointDigitOfNotOutside
#print axioms L3.BankWindow.bankWindowOverlapStableIncompleteCwaitRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapStableForeignRootFieldsAt
#print axioms L3.BankWindow.bankWindowExactStepOfSourceRoot
#print axioms L3.BankWindow.bankWindowOverlapSourceResetLaunchIncompleteRootFieldsAt
#print axioms L3.BankWindow.bankWindowJointSourceResetExitController
#print axioms L3.BankWindow.bankWindowOverlapSourceResetExitRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapSourceClOneRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapSourceMismatchTimeoutRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapSourceShortWaitRootFieldsAt
#print axioms L3.BankWindow.bankWindowJointSourceNoOwnGenuineOfAlignedClean
#print axioms L3.BankWindow.bankWindowOverlapSourceAlignedCleanRootFieldsAt
#print axioms L3.BankWindow.bankWindowJointUntaintedOfWorker
#print axioms L3.BankWindow.bankWindowJointSourceInheritedAlignedClean
#print axioms L3.BankWindow.bankWindowJointSourceActiveReturnMode
#print axioms L3.BankWindow.bankWindowJointSourceActiveReturnMemory
#print axioms L3.BankWindow.bankWindowJointSourceActiveReturnNotGenuine
#print axioms L3.BankWindow.bankWindowJointActiveControllerOfPhase
#print axioms L3.BankWindow.bankWindowOverlapSourceActiveReturnRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapSourceInheritedActiveRootFieldsAt
#print axioms L3.BankWindow.bankWindowJointSelectedPairReads
#print axioms L3.BankWindow.bankWindowJointUntaintedOfEmpty
#print axioms L3.BankWindow.bankWindowJointWaitingControllerOfPhase
#print axioms L3.BankWindow.bankWindowJointPostAlignedCleanOfOld
#print axioms L3.BankWindow.bankWindowJointWaitSourceOldAlignedClean
#print axioms L3.BankWindow.bankWindowJointResetWaitFront
#print axioms L3.BankWindow.bankWindowJointSourceIwaitReturnCell
#print axioms L3.BankWindow.bankWindowJointSourceMismatchLongCell
#print axioms L3.BankWindow.bankWindowJointSourceChangedLongCell
#print axioms L3.BankWindow.bankWindowOverlapSourceIwaitReturnRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapSourceMismatchLongRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapSourceChangedLongWaitRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapSourceLongWaitRootFieldsAt
#print axioms L3.BankWindow.bankWindowJointResetWaitFrontRl
#print axioms L3.BankWindow.bankWindowJointSourcePayloadReturnCell
#print axioms L3.BankWindow.bankWindowOverlapSourceInheritedReturnRootFieldsAt
#print axioms L3.BankWindow.bankWindowJointOfFnSum
#print axioms L3.BankWindow.bankWindowJointBinaryLt
#print axioms L3.BankWindow.bankWindowJointBinaryInjective
#print axioms L3.BankWindow.bankWindowJointNatSumZero
#print axioms L3.BankWindow.bankWindowJointBinaryValueZero
#print axioms L3.BankWindow.bankWindowJointBinaryValueEqKMatched
#print axioms L3.BankWindow.bankWindowJointNoComparatorOfEmptyTokens
#print axioms L3.BankWindow.bankWindowJointArmedOwnClausesOfReturn
#print axioms L3.BankWindow.bankWindowJointSourceMatchedReturnBits
#print axioms L3.BankWindow.bankWindowJointMatchedReturnEndpointReads
#print axioms L3.BankWindow.bankWindowJointMatchedReturnDigitReads
#print axioms L3.BankWindow.bankWindowJointTaintedResponderScope
#print axioms L3.BankWindow.bankWindowOverlapSourceCompareReturnRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapSourceResetReturnRootFieldsAt
#print axioms L3.BankWindow.bankWindowOverlapSourceRootFieldsAt
#print axioms L3.BankWindow.bankWindowExactStep
