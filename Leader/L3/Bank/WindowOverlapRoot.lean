import Leader.L3.Bank.WindowOverlap
import Leader.L3.Bank.ComparatorExclusive
import Leader.L3.Bank.HeadThreshold
import Leader.L3.Bank.CounterRows

/-!
R11 group-13: authentic selected root, foreign-owner obligations.
The actual successor is renewalBankNext on the real rbRun prefix.

This module proves geometric exclusion for complete foreign windows,
POST worker provenance from the real ReceiptInv, all four foreign
proto clauses for a root-source service (including first mismatch),
and the CWAIT remote comparator phase/flag clauses.

Other row/field combinations are not asserted.
-/

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

private abbrev bankWindowRootBefore {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) : RenewalBankReference n :=
  rbRun ring (renewalBankStart ring seed) pre

private abbrev bankWindowRootAfter {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) (e : Fin n) : RenewalBankReference n :=
  renewalBankNext ring (bankWindowRootBefore ring seed pre) e

/-- B.7: the real root-source PACK zero is retained by the
selected source, while the selected responder gets PACK one.
Consumer: the foreign-carrier and proto-prefix split. -/
theorem bankWindowRootSourceRoles {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (hx : (r.1 e).pack.val = 0) :
    ((renewalBankNext ring r e).1 e).pack.val = 0 ∧
    ((renewalBankNext ring r e).1
      (ring.rightNeighbor e)).pack.val = 1 := by
  have hne := (clockNeighborDifferent ring
    (by omega : 2 ≤ n) e).symm
  have hsource := bankWindowClosureRepairNonresponderPackFixed
    ring (by omega : 2 ≤ n) r e e hne
  have hdest := bankWindowExactResponderPack ring r e
    (clockNeighborDifferent ring (by omega : 2 ≤ n) e)
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  constructor
  · exact hsource.trans hx
  · rw [hdest, hx]
    simp [packNext, hb]

/-- The genuine extended-run ReceiptInv excludes pending and
origin-some payloads from the POST source PACK-zero site.
At the selected PACK-one responder, every authenticated pending
or genuine payload has origin root equal to this source root.
Consumer: foreign root comparison read-set transport. -/
theorem bankWindowRootSelectedCarrierOwnership {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hx : ((bankWindowRootBefore ring seed pre).1 e).pack.val = 0) :
    BankInFlightAligned ring (bankWindowRootAfter ring seed pre e) ∧
    (∀ rho : RenewalBankReceipt n,
      ((bankWindowRootAfter ring seed pre e).2.sites e).worker ≠
        .pending rho) ∧
    (∀ (p : RenewalBankPayload n) (o : RenewalBankOrigin n),
      ((bankWindowRootAfter ring seed pre e).2.sites e).worker =
        .payload p → p.origin = some o → False) ∧
    (∀ rho : RenewalBankReceipt n,
      ((bankWindowRootAfter ring seed pre e).2.sites
        (ring.rightNeighbor e)).worker = .pending rho →
      rho.root = e) ∧
    (∀ (p : RenewalBankPayload n) (o : RenewalBankOrigin n),
      ((bankWindowRootAfter ring seed pre e).2.sites
        (ring.rightNeighbor e)).worker = .payload p →
      p.origin = some o → o.root = e) := by
  have hroles := bankWindowRootSourceRoles ring hn
    (bankWindowRootBefore ring seed pre) e hx
  have hreceipt := bankWindowOverlapPostReceipt
    ring hn hbank seed pre e
  have hown := bankWindowOverlapAlignedCarrierOwnRoot
    ring seed (pre ++ [e])
    (bankWindowRootAfter ring seed pre e)
    hreceipt e (ring.rightNeighbor e) 1
    (by omega)
    (by change 1 ≤ (compileAdvice (ceilLogTwo n)).s + 11; omega)
    rfl hroles.2
  have hpostRun :
      rbRun ring (renewalBankStart ring seed) (pre ++ [e]) =
        bankWindowRootAfter ring seed pre e := by
    rw [rbRunAppend]
    rfl
  have hframe := (bankWindowOverlapGlobalAndDisjoint
    ring hn hbank seed pre e hJ).1
  refine ⟨hframe, ?_, ?_, hown.1, hown.2⟩
  · intro rho hp
    obtain ⟨_, _, k, hk, _, _, hpack, _⟩ :=
      hreceipt.pending e rho hp
    rw [hroles.1] at hpack
    omega
  · intro p o hw ho
    have hwrun :
        ((rbRun ring (renewalBankStart ring seed)
          (pre ++ [e])).2.sites e).worker = .payload p := by
      rw [hpostRun]
      exact hw
    have hband := bankWindowOverlapGenuineWorkerInBand
      ring hn hbank seed (pre ++ [e]) e p o hwrun ho
    rw [hpostRun] at hband
    rw [hroles.1] at hband
    omega

/-- A selected OLD PACK-zero source cannot intersect another
OLD complete root's aligned digit interval if that root is not
either endpoint. This is a real geometric consequence, not a
claim that independent windows partition the ring.
Consumer: the remote CWAIT and root-read frame. -/
theorem bankWindowRootForeignCompleteOutside {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n)
    (e foreign : Fin n)
    (hx : (r.1 e).pack.val = 0)
    (hforeign : foreign ≠ e ∧
      foreign ≠ ring.rightNeighbor e)
    (hcomplete : Counter.Complete ring r.1 foreign) :
    Counter.OutsideSites (q := ceilLogTwo n)
      ring foreign e := by
  intro k hk
  constructor
  · intro he
    cases k with
    | zero =>
        exact hforeign.1
          (by simpa only [Counter.site] using he.symm)
    | succ j =>
        have hp : (r.1 e).pack.val = j + 1 := by
          rw [he]
          exact hcomplete (j + 1) hk
        omega
  · intro hy
    cases k with
    | zero =>
        exact hforeign.2
          (by simpa only [Counter.site] using hy.symm)
    | succ j =>
        have hsource :
            e = Counter.site ring foreign j :=
          Counter.resetTrialSitePredecessor
            ring foreign e j hy
        cases j with
        | zero =>
            exact hforeign.1
              (by simpa only [Counter.site] using hsource.symm)
        | succ m =>
            have hp : (r.1 e).pack.val = m + 1 := by
              rw [hsource]
              exact hcomplete (m + 1) (by omega)
            omega

/-- Every physical and ghost field of another complete
window is framed on the selected source-root edge, and
its grant-free scope is equivalent before and after.
Consumer: root-row foreign phase read sets. -/
theorem bankWindowRootForeignCompleteFrame {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalBankReference n) (e foreign : Fin n)
    (hx : (r.1 e).pack.val = 0)
    (hforeign : foreign ≠ e ∧
      foreign ≠ ring.rightNeighbor e)
    (hcomplete : Counter.Complete ring r.1 foreign) :
    (∀ k : Nat, k ≤ (compileAdvice (ceilLogTwo n)).b →
      (renewalBankNext ring r e).1
        (Counter.site ring foreign k) =
          r.1 (Counter.site ring foreign k) ∧
      (renewalBankNext ring r e).2.sites
        (Counter.site ring foreign k) =
          r.2.sites (Counter.site ring foreign k)) ∧
    (BankWindowScope ring (renewalBankNext ring r e) foreign ↔
      BankWindowScope ring r foreign) := by
  have houtside := bankWindowRootForeignCompleteOutside
    ring r e foreign hx hforeign hcomplete
  exact ⟨bankWindowExactOffWindowFrame
    ring r foreign e houtside,
    bankWindowClosureOffWindowScope
      ring r foreign e houtside⟩

/-- A foreign origin cannot have its genuine worker on either
selected endpoint of an OLD PACK-zero root row. This resolves
the *free i* site read before the origin-bit read is considered.
Consumer: post phaseFlags and phaseUnique. -/
theorem bankWindowRootForeignWorkerOffPair {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hx : ((bankWindowRootBefore ring seed pre).1 e).pack.val = 0)
    (o : RenewalBankOrigin n)
    (i : Fin n) (p : RenewalBankPayload n)
    (hforeign : o.root ≠ e)
    (hw : ((bankWindowRootAfter ring seed pre e).2.sites i).worker =
      .payload p)
    (ho : p.origin = some o) :
    i ≠ e ∧ i ≠ ring.rightNeighbor e := by
  obtain ⟨_, _, hsource, _, htarget⟩ :=
    bankWindowRootSelectedCarrierOwnership
      ring hn hbank seed pre e hJ hx
  constructor
  · intro hi
    subst i
    exact hsource p o hw ho
  · intro hi
    subst i
    have hroot := htarget p o hw ho
    exact hforeign hroot

/-- Properly aligned digits of any POST foreign proto prefix
avoid a real root-source edge: a responder aligned at k>0
forces its predecessor to carry k-1, incompatible with the
selected source's immutable zero PACK, except when k=1
and the foreign root is the selected source.
Consumer: full four-clause proto transport. -/
theorem bankWindowRootForeignProtoPrefixAvoid {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e foreign : Fin n) (limit : Nat)
    (hx : ((bankWindowRootBefore ring seed pre).1 e).pack.val = 0)
    (hforeign : foreign ≠ e ∧
      foreign ≠ ring.rightNeighbor e)
    (hproto : BankWindowProtoRun ring
      (bankWindowRootAfter ring seed pre e) foreign limit) :
    ∀ k : Nat, k ≤ limit →
      e ≠ Counter.site ring foreign k ∧
      ring.rightNeighbor e ≠ Counter.site ring foreign k := by
  have hsrc := (bankWindowRootSourceRoles ring hn
    (bankWindowRootBefore ring seed pre) e hx).1
  intro k hk
  constructor
  · intro he
    cases k with
    | zero =>
        exact hforeign.1
          (by simpa only [Counter.site] using he.symm)
    | succ j =>
        have hp := hproto.2.1 (j + 1) hk
        rw [← he, hsrc] at hp
        omega
  · intro hy
    cases k with
    | zero =>
        exact hforeign.2
          (by simpa only [Counter.site] using hy.symm)
    | succ j =>
        have hs :
            e = Counter.site ring foreign j :=
          Counter.resetTrialSitePredecessor
            ring foreign e j hy
        cases j with
        | zero =>
            exact hforeign.1
              (by simpa only [Counter.site] using hs.symm)
        | succ m =>
            have hp := hproto.2.1 (m + 1) (by omega)
            rw [← hs, hsrc] at hp
            omega

/-- The exact four J.proto consequences, including the real
pending RR witness and the two separate taint exclusions.
Consumers: all root-row subclasses and the final J overlap. -/
def BankWindowRootForeignProtoField {n : Nat}
    (ring : DirectedRing n)
    (s : RenewalBankReference n)
    (root : Fin n) (limit : Nat) : Prop :=
  (∀ (p : RenewalBankPayload n) (o : RenewalBankOrigin n),
    (s.2.sites root).controller = .active p →
      p.origin = some o → False) ∧
  (BankWindowInheritedController s root →
    ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      j.val + 1 ≤ limit →
      ¬ BankWindowTainted s
        (Counter.site ring root (j.val + 1))) ∧
  (((s.1 root).mode = .RWAIT ∧
      (s.2.sites root).controller = .waiting []) →
    ∃ j : Fin (compileAdvice (ceilLogTwo n)).b,
      j.val + 1 ≤ limit ∧
      ∃ rho : RenewalBankReceipt n,
        (s.2.sites (Counter.site ring root (j.val + 1))).worker =
          .pending rho ∧
        (s.1 (Counter.site ring root (j.val + 1))).tok = .RR ∧
        bankWindowZeroPrefix ring s root (j.val + 1) ∧
        (∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
          k.val < j.val →
          (s.1 (Counter.site ring root (k.val + 1))).tok = .E)) ∧
  ((s.1 root).mode ≠ .RESET →
    (s.1 root).mode ≠ .RWAIT →
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        j.val + 1 ≤ limit →
        ¬ BankWindowTainted s
          (Counter.site ring root (j.val + 1)))

/-- All four POST proto clauses for any foreign root distinct
from the selected endpoints, on any authentic OLD PACK-zero
root-source service. The only possible incident proto read is
the FIRST incorrect PACK at limit+1, already handled by the
installed group-13 PFX boundary lemma. All other reads are
off-pair. Consumer: root-row items 5--8. -/
theorem bankWindowRootForeignProtoStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e foreign : Fin n) (limit : Nat)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hx : ((bankWindowRootBefore ring seed pre).1 e).pack.val = 0)
    (hforeign : foreign ≠ e ∧
      foreign ≠ ring.rightNeighbor e)
    (hproto : BankWindowProtoRun ring
      (bankWindowRootAfter ring seed pre e) foreign limit) :
    BankWindowRootForeignProtoField ring
      (bankWindowRootAfter ring seed pre e) foreign limit := by
  have hprefix := bankWindowRootForeignProtoPrefixAvoid
    ring hn seed pre e foreign limit hx hforeign hproto
  by_cases hboundary :
      e = Counter.site ring foreign (limit + 1) ∨
      ring.rightNeighbor e =
        Counter.site ring foreign (limit + 1)
  · exact bankWindowOverlapProtoForeignInterior
      ring hn hbank seed pre e foreign limit hJ
      hboundary hproto
  · have hpackAvoid :
        ∀ k : Nat, k ≤ limit + 1 →
          Counter.site ring foreign k ≠ e ∧
          Counter.site ring foreign k ≠ ring.rightNeighbor e := by
      intro k hk
      by_cases hproper : k ≤ limit
      · have hf := hprefix k hproper
        exact ⟨hf.1.symm, hf.2.symm⟩
      · have hlast : k = limit + 1 := by omega
        subst k
        constructor
        · intro he
          exact hboundary (Or.inl he.symm)
        · intro hy
          exact hboundary (Or.inr hy.symm)
    have hsegment :
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          Counter.site ring foreign (j.val + 1) ≠ e ∧
          Counter.site ring foreign (j.val + 1) ≠
            ring.rightNeighbor e := by
      intro j hj
      exact hpackAvoid (j.val + 1) (by omega)
    exact bankWindowExactDisjointProtoStep ring
      (bankWindowRootBefore ring seed pre)
      e foreign limit hJ hforeign hpackAvoid hsegment hproto

/-- Foreign CWAIT genuine comparator. The selected root's two
sites cannot host a foreign authenticated worker. OLD J then
forces the foreign origin window complete; geometry keeps all
its bits/tokens unchanged, so the post exact phaseUnique and
phaseFlags consequences follow from the existing read-set
transport. Consumer: item-8 foreign comparison, all root rows. -/
theorem bankWindowRootForeignComparatorStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hx : ((bankWindowRootBefore ring seed pre).1 e).pack.val = 0)
    (o : RenewalBankOrigin n)
    (i : Fin n) (p : RenewalBankPayload n)
    (hforeign : o.root ≠ e ∧
      o.root ≠ ring.rightNeighbor e)
    (hworker : BankComparatorOriginWorker ring
      (bankWindowRootAfter ring seed pre e) o i p)
    (hmode : ((bankWindowRootAfter ring seed pre e).1 o.root).mode =
      .CWAIT) :
    Counter.Complete ring
      (bankWindowRootAfter ring seed pre e).1 o.root ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankTrialLiveComparisonToken
        ((bankWindowRootAfter ring seed pre e).1
          (Counter.site ring o.root (j.val + 1))).tok →
        Counter.site ring o.root (j.val + 1) = i) ∧
    ((((bankWindowRootAfter ring seed pre e).1 i).tok = .CR1 →
      bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        ((bankWindowRootAfter ring seed pre e).1 i).pack.val) ∧
     (((bankWindowRootAfter ring seed pre e).1 i).tok = .CR0 →
      ¬ bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        ((bankWindowRootAfter ring seed pre e).1 i).pack.val) ∧
     (((bankWindowRootAfter ring seed pre e).1 i).tok = .CL1 →
      bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        (compileAdvice (ceilLogTwo n)).b) ∧
     (((bankWindowRootAfter ring seed pre e).1 i).tok = .CL0 →
      ¬ bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        (compileAdvice (ceilLogTwo n)).b)) := by
  have hfree := bankWindowRootForeignWorkerOffPair
    ring hn hbank seed pre e hJ hx o i p hforeign.1
    hworker.1 hworker.2.1
  have hf := bankWindowExactOffPairAtomicReads ring
    (bankWindowRootBefore ring seed pre) e i
    hfree.1 hfree.2
  have hrootFrame := bankWindowExactOffPairAtomicReads ring
    (bankWindowRootBefore ring seed pre) e o.root
    hforeign.1 hforeign.2
  have hworkerOld : BankComparatorOriginWorker ring
      (bankWindowRootBefore ring seed pre) o i p := by
    refine ⟨hf.2.2.2.2.2.1.symm.trans hworker.1,
      hworker.2.1, ?_⟩
    have ht := hworker.2.2
    rw [hf.2.2.1] at ht
    exact ht
  have hmodeOld :
      ((bankWindowRootBefore ring seed pre).1 o.root).mode =
        .CWAIT :=
    hrootFrame.2.1.symm.trans hmode
  have hcompleteOld := hJ.phaseComplete o i p
    hworkerOld hmodeOld
  have houtside := bankWindowRootForeignCompleteOutside
    ring (bankWindowRootBefore ring seed pre)
    e o.root hx hforeign hcompleteOld
  have hcomplete :
      Counter.Complete ring
        (bankWindowRootAfter ring seed pre e).1 o.root :=
    (bankWindowClosureOffWindowAlignedPrefix ring
      (bankWindowRootBefore ring seed pre)
      o.root e houtside
      (compileAdvice (ceilLogTwo n)).b
      (Nat.le_refl _)).mpr hcompleteOld
  have htokWindow : bankWindowReadDigitTokens ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) o.root := by
    intro j
    have ht := (bankWindowExactOffWindowFrame ring
      (bankWindowRootBefore ring seed pre) o.root e
      houtside (j.val + 1) (by omega)).1
    exact congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok) ht
  have hbitWindow : bankWindowReadDigitBits ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) o.root := by
    intro j
    have ht := (bankWindowExactOffWindowFrame ring
      (bankWindowRootBefore ring seed pre) o.root e
      houtside (j.val + 1) (by omega)).1
    exact congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.bit) ht
  have hphaseRead : bankWindowPhaseExcludesReadSet
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) o i p :=
    ⟨hf.2.2.1, hf.2.2.2.2.2.1, hrootFrame.2.1⟩
  have hunique := bankWindowPhaseUniqueReadTransport ring
    (bankWindowRootBefore ring seed pre)
    (bankWindowRootAfter ring seed pre e)
    o i p hJ ⟨hphaseRead, htokWindow⟩
    hworker hmode
  have hflags := bankWindowPhaseFlagsReadTransport ring
    (bankWindowRootBefore ring seed pre)
    (bankWindowRootAfter ring seed pre e)
    o i p hJ ⟨hphaseRead, hf.1, hbitWindow⟩
    hworker hmode
  exact ⟨hcomplete, hunique, hflags⟩

/-- Item 5, grant-free RESET launch: the real root enters RWAIT,
clears the first bit and issues RR. An unrelated partial root
preserves ALL four J.proto clauses, including its pending witness
if the selected first-mismatch read is incident. -/
theorem bankWindowOverlapRootLaunchForeignPrefix {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (root foreign : Fin n) (limit : Nat)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hscope : BankWindowScope ring
      (bankWindowRootBefore ring seed pre) root)
    (hmode :
      ((bankWindowRootBefore ring seed pre).1 root).mode = .RESET)
    (hforeign : foreign ≠ root ∧
      foreign ≠ ring.rightNeighbor root)
    (hproto : BankWindowProtoRun ring
      (bankWindowRootAfter ring seed pre root) foreign limit) :
    BankWindowRootForeignProtoField ring
      (bankWindowRootAfter ring seed pre root) foreign limit ∧
    ((bankWindowRootAfter ring seed pre root).1 root).mode =
      .RWAIT ∧
    ((bankWindowRootAfter ring seed pre root).1
      (ring.rightNeighbor root)).bit = false ∧
    ((bankWindowRootAfter ring seed pre root).1
      (ring.rightNeighbor root)).tok = .RR := by
  have hx :
      ((bankWindowRootBefore ring seed pre).1 root).pack.val = 0 := by
    change ((bankWindowRootBefore ring seed pre).1
      (Counter.site ring root 0)).pack.val = 0
    exact hscope.1 0 (by omega)
  have hy :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor root)).pack.val = 1 := by
    change ((bankWindowRootBefore ring seed pre).1
      (Counter.site ring root 1)).pack.val = 1
    exact hscope.1 1
      (by change 1 ≤ (compileAdvice (ceilLogTwo n)).s + 11; omega)
  exact ⟨bankWindowRootForeignProtoStep ring hn hbank
      seed pre root foreign limit hJ hx hforeign hproto,
    bankWindowClosureResetLaunchPhysicalPair ring hn hbank
      (bankWindowRootBefore ring seed pre) root
      hx hy hscope.2 hmode⟩

/-- Item 6, actual RL birth (not merely an inherited RL token):
old J authenticates the complete reset-return and the physical
root becomes ARMED; the other root's proto fields survive. -/
theorem bankWindowOverlapRootReturnForeignPrefix {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (root foreign : Fin n) (limit : Nat)
    (o : RenewalBankOrigin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hbirth : renewalBankBirth ring
      (bankWindowRootBefore ring seed pre).1
      (bankWindowRootBefore ring seed pre).2 root = some o)
    (hforeign : foreign ≠ root ∧
      foreign ≠ ring.rightNeighbor root)
    (hproto : BankWindowProtoRun ring
      (bankWindowRootAfter ring seed pre root) foreign limit) :
    BankWindowRootForeignProtoField ring
      (bankWindowRootAfter ring seed pre root) foreign limit ∧
    Counter.Complete ring
      (bankWindowRootBefore ring seed pre).1 root ∧
    ((bankWindowRootAfter ring seed pre root).1 root).mode =
      .ARMED := by
  have hx := (bankWindowBirthOldReceipt ring
    (bankWindowRootBefore ring seed pre).1
    (bankWindowRootBefore ring seed pre).2 root o hbirth).1
  exact ⟨bankWindowRootForeignProtoStep ring hn hbank
      seed pre root foreign limit hJ hx hforeign hproto,
    bankWindowClosureBirthComplete ring
      (bankWindowRootBefore ring seed pre)
      root o hJ hbirth,
    bankWindowClosureBirthPostArmed ring
      (by omega : 2 ≤ n) hbank
      (bankWindowRootBefore ring seed pre)
      root o hbirth⟩

/-- Item 6, RWAIT expiry without a return token: the authentic
root resets and clears its controller, while the foreign proto
proof has not borrowed a post-J assumption. -/
theorem bankWindowOverlapRootExpiryForeignPrefix {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (root foreign : Fin n) (limit : Nat)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hscope : BankWindowScope ring
      (bankWindowRootBefore ring seed pre) root)
    (hmode :
      ((bankWindowRootBefore ring seed pre).1 root).mode = .RWAIT)
    (htok :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor root)).tok = .E)
    (hlease :
      ((bankWindowRootBefore ring seed pre).1 root).lease.val ≤ 1)
    (hforeign : foreign ≠ root ∧
      foreign ≠ ring.rightNeighbor root)
    (hproto : BankWindowProtoRun ring
      (bankWindowRootAfter ring seed pre root) foreign limit) :
    BankWindowRootForeignProtoField ring
      (bankWindowRootAfter ring seed pre root) foreign limit ∧
    Counter.Complete ring
      (bankWindowRootAfter ring seed pre root).1 root ∧
    ((bankWindowRootAfter ring seed pre root).1 root).mode =
      .RESET ∧
    ((bankWindowRootAfter ring seed pre root).2.sites root).controller =
      .empty := by
  have hx :
      ((bankWindowRootBefore ring seed pre).1 root).pack.val = 0 := by
    change ((bankWindowRootBefore ring seed pre).1
      (Counter.site ring root 0)).pack.val = 0
    exact hscope.1 0 (by omega)
  exact ⟨bankWindowRootForeignProtoStep ring hn hbank
      seed pre root foreign limit hJ hx hforeign hproto,
    bankWindowClosureRootWaitTimeout ring hn hbank
      (bankWindowRootBefore ring seed pre) root hscope.1
      hscope.2 hmode htok hlease⟩

/-- Item 7, genuine ARMED/IR issue: the outgoing head worker is
derived from the OLD genuine controller and increments its value.
Every foreign proto clause is simultaneously retained. -/
theorem bankWindowOverlapRootIssueForeignOrigin {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (root foreign : Fin n) (limit : Nat)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hscope : BankWindowScope ring
      (bankWindowRootBefore ring seed pre) root)
    (hmode :
      ((bankWindowRootBefore ring seed pre).1 root).mode = .ARMED)
    (hactive :
      ((bankWindowRootBefore ring seed pre).2.sites root).controller =
        .active p)
    (horigin : p.origin = some o)
    (hbit :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor root)).bit = true)
    (hforeign : foreign ≠ root ∧
      foreign ≠ ring.rightNeighbor root)
    (hproto : BankWindowProtoRun ring
      (bankWindowRootAfter ring seed pre root) foreign limit) :
    BankWindowRootForeignProtoField ring
      (bankWindowRootAfter ring seed pre root) foreign limit ∧
    Counter.Complete ring
      (bankWindowRootAfter ring seed pre root).1 root ∧
    ((bankWindowRootAfter ring seed pre root).2.sites root).controller =
      .waiting [] ∧
    ((bankWindowRootAfter ring seed pre root).2.sites
      (ring.rightNeighbor root)).worker =
        .payload (renewalBankHead p) ∧
    (renewalBankHead p).origin = some o ∧
    (renewalBankHead p).heads =
      bankOriginBinaryValue ring
        (bankWindowRootBefore ring seed pre).1 o + 1 := by
  have hx :
      ((bankWindowRootBefore ring seed pre).1 root).pack.val = 0 := by
    change ((bankWindowRootBefore ring seed pre).1
      (Counter.site ring root 0)).pack.val = 0
    exact hscope.1 0 (by omega)
  exact ⟨bankWindowRootForeignProtoStep ring hn hbank
      seed pre root foreign limit hJ hx hforeign hproto,
    bankWindowClosureArmedIssueGenuine ring hn
      (bankWindowRootBefore ring seed pre) root
      hJ hscope hmode p o hactive horigin hbit⟩

/-- Item 7, CSTART/CR issue: no foreign origin is created.
The selected worker retains the OLD exact origin and heads,
and foreign proto/taint obligations are preserved. -/
theorem bankWindowOverlapRootCompareIssueForeignOrigin {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (root foreign : Fin n) (limit : Nat)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hscope : BankWindowScope ring
      (bankWindowRootBefore ring seed pre) root)
    (hmode :
      ((bankWindowRootBefore ring seed pre).1 root).mode = .CSTART)
    (hactive :
      ((bankWindowRootBefore ring seed pre).2.sites root).controller =
        .active p)
    (horigin : p.origin = some o)
    (hforeign : foreign ≠ root ∧
      foreign ≠ ring.rightNeighbor root)
    (hproto : BankWindowProtoRun ring
      (bankWindowRootAfter ring seed pre root) foreign limit) :
    BankWindowRootForeignProtoField ring
      (bankWindowRootAfter ring seed pre root) foreign limit ∧
    Counter.Complete ring
      (bankWindowRootAfter ring seed pre root).1 root ∧
    ((bankWindowRootAfter ring seed pre root).2.sites root).controller =
      .waiting [] ∧
    ((bankWindowRootAfter ring seed pre root).2.sites
      (ring.rightNeighbor root)).worker = .payload p ∧
    p.origin = some o ∧
    p.heads = bankOriginBinaryValue ring
      (bankWindowRootBefore ring seed pre).1 o ∧
    p.atoms = [] := by
  have hx :
      ((bankWindowRootBefore ring seed pre).1 root).pack.val = 0 := by
    change ((bankWindowRootBefore ring seed pre).1
      (Counter.site ring root 0)).pack.val = 0
    exact hscope.1 0 (by omega)
  exact ⟨bankWindowRootForeignProtoStep ring hn hbank
      seed pre root foreign limit hJ hx hforeign hproto,
    bankWindowClosureCstartIssueGenuine ring hn
      (bankWindowRootBefore ring seed pre) root
      hJ hscope hmode p o hactive horigin⟩

/-- Item 8, a genuine IWAIT/AL return is forwarded into the
selected controller without changing its origin or exact heads.
The selected worker clears; all other proto fields survive. -/
theorem bankWindowOverlapRootWaitForeignIncrement {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (root foreign : Fin n) (limit : Nat)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hscope : BankWindowScope ring
      (bankWindowRootBefore ring seed pre) root)
    (hmode :
      ((bankWindowRootBefore ring seed pre).1 root).mode = .IWAIT)
    (hwait :
      ((bankWindowRootBefore ring seed pre).2.sites root).controller =
        .waiting [])
    (hworker :
      ((bankWindowRootBefore ring seed pre).2.sites
        (ring.rightNeighbor root)).worker = .payload p)
    (horigin : p.origin = some o)
    (hroot : o.root = root)
    (htok :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor root)).tok = .AL)
    (hforeign : foreign ≠ root ∧
      foreign ≠ ring.rightNeighbor root)
    (hproto : BankWindowProtoRun ring
      (bankWindowRootAfter ring seed pre root) foreign limit) :
    BankWindowRootForeignProtoField ring
      (bankWindowRootAfter ring seed pre root) foreign limit ∧
    ∃ q : RenewalBankPayload n,
      ((bankWindowRootAfter ring seed pre root).2.sites root).controller =
        .active q ∧
      ((bankWindowRootAfter ring seed pre root).2.sites
        (ring.rightNeighbor root)).worker = .empty ∧
      q.origin = some o ∧
      q.heads = bankOriginBinaryValue ring
        (bankWindowRootBefore ring seed pre).1 o ∧
      q.atoms = [] := by
  have hx :
      ((bankWindowRootBefore ring seed pre).1 root).pack.val = 0 := by
    change ((bankWindowRootBefore ring seed pre).1
      (Counter.site ring root 0)).pack.val = 0
    exact hscope.1 0 (by omega)
  have hprotoPost := bankWindowRootForeignProtoStep
    ring hn hbank seed pre root foreign limit
    hJ hx hforeign hproto
  obtain ⟨_, q, hc, hw, ho, hh, ha⟩ :=
    bankWindowClosureIncrementReturnExactGhost ring hn
      (bankWindowRootBefore ring seed pre) root hJ hscope
      hmode hwait p o hworker horigin hroot htok
  exact ⟨hprotoPost, q, hc, hw, ho, hh, ha⟩

/-- Item 8, a genuine CWAIT/CL0 return carries the true
comparison head back into the root without inherited atoms.
The newly returned origin is authenticated, and all foreign
proto field instances are preserved. -/
theorem bankWindowOverlapRootWaitForeignComparison {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (root foreign : Fin n) (limit : Nat)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hscope : BankWindowScope ring
      (bankWindowRootBefore ring seed pre) root)
    (hmode :
      ((bankWindowRootBefore ring seed pre).1 root).mode = .CWAIT)
    (hwait :
      ((bankWindowRootBefore ring seed pre).2.sites root).controller =
        .waiting [])
    (hworker :
      ((bankWindowRootBefore ring seed pre).2.sites
        (ring.rightNeighbor root)).worker = .payload p)
    (horigin : p.origin = some o)
    (hroot : o.root = root)
    (htok :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor root)).tok = .CL0)
    (hforeign : foreign ≠ root ∧
      foreign ≠ ring.rightNeighbor root)
    (hproto : BankWindowProtoRun ring
      (bankWindowRootAfter ring seed pre root) foreign limit) :
    BankWindowRootForeignProtoField ring
      (bankWindowRootAfter ring seed pre root) foreign limit ∧
    ∃ q : RenewalBankPayload n,
      ((bankWindowRootAfter ring seed pre root).2.sites root).controller =
        .active q ∧
      ((bankWindowRootAfter ring seed pre root).2.sites
        (ring.rightNeighbor root)).worker = .empty ∧
      q.origin = some o ∧
      q.heads = bankOriginBinaryValue ring
        (bankWindowRootBefore ring seed pre).1 o ∧
      q.atoms = [] := by
  have hx :
      ((bankWindowRootBefore ring seed pre).1 root).pack.val = 0 := by
    change ((bankWindowRootBefore ring seed pre).1
      (Counter.site ring root 0)).pack.val = 0
    exact hscope.1 0 (by omega)
  have hprotoPost := bankWindowRootForeignProtoStep
    ring hn hbank seed pre root foreign limit
    hJ hx hforeign hproto
  obtain ⟨_, q, hc, hw, ho, hh, ha⟩ :=
    bankWindowClosureCompareReturnExactGhost ring hn
      (bankWindowRootBefore ring seed pre) root hJ hscope
      hmode hwait p o hworker horigin hroot htok
  exact ⟨hprotoPost, q, hc, hw, ho, hh, ha⟩

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

/-! Real root service, foreign orphan activation. -/

/-- J.orphan for another root after a genuine PACK-zero source
service. Its named aligned tainted digit must be off-pair.
If the OLD prefix were complete, the POST prefix would be
complete too: a PACK-zero source cannot change an aligned
positive-offset responder except at the first digit of its
own root. OLD J.orphan therefore proves the actual POST row.
Consumer: R11 group-13 root rows 5--8. -/
theorem bankWindowRootForeignOrphanOnSource {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e foreign : Fin n)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hx : ((bankWindowRootBefore ring seed pre).1 e).pack.val = 0)
    (hforeign : foreign ≠ e ∧
      foreign ≠ ring.rightNeighbor e)
    (howner : BankWindowOrphanOwner ring
      (bankWindowRootAfter ring seed pre e) foreign j)
    (htainted : BankWindowTainted
      (bankWindowRootAfter ring seed pre e)
      (Counter.site ring foreign (j.val + 1))) :
    ((bankWindowRootAfter ring seed pre e).1 foreign).mode = .RESET ∨
      (((bankWindowRootAfter ring seed pre e).1 foreign).mode =
        .RWAIT ∧
        ((bankWindowRootAfter ring seed pre e).2.sites
          foreign).controller = .waiting []) := by
  have hroles := bankWindowRootSourceRoles ring hn
    (bankWindowRootBefore ring seed pre) e hx
  have hsource :
      Counter.site ring foreign (j.val + 1) ≠ e := by
    intro he
    have hv := howner.2.1
    rw [he, hroles.1] at hv
    omega
  have hdest :
      Counter.site ring foreign (j.val + 1) ≠
        ring.rightNeighbor e := by
    intro he
    have hv := howner.2.1
    rw [he, hroles.2] at hv
    have hjzero : j.val = 0 := by omega
    have hnext :
        ring.rightNeighbor e =
          Counter.site ring foreign (0 + 1) := by
      rw [hjzero] at he
      exact he.symm
    have hprevious := Counter.resetTrialSitePredecessor
      ring foreign e 0 hnext
    change e = foreign at hprevious
    exact hforeign.1 hprevious.symm
  have hrootFrame := bankWindowExactOffPairFrame ring
    (bankWindowRootBefore ring seed pre) e foreign
    hforeign.1 hforeign.2
  have hdigitFrame := bankWindowExactOffPairFrame ring
    (bankWindowRootBefore ring seed pre) e
    (Counter.site ring foreign (j.val + 1))
    hsource hdest
  have hrootOld :
      ((bankWindowRootBefore ring seed pre).1 foreign).pack.val =
        0 := by
    have hf := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.pack.val)
      hrootFrame.1
    exact hf.symm.trans howner.1
  have hdigitOld :
      ((bankWindowRootBefore ring seed pre).1
        (Counter.site ring foreign (j.val + 1))).pack.val =
        j.val + 1 := by
    have hf := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.pack.val)
      hdigitFrame.1
    exact hf.symm.trans howner.2.1
  have hwrongOld :
      ¬ (∀ k : Nat, k ≤ j.val + 1 →
        ((bankWindowRootBefore ring seed pre).1
          (Counter.site ring foreign k)).pack.val = k) := by
    intro hprefix
    apply howner.2.2
    intro k hk
    by_cases hselected :
        Counter.site ring foreign k = ring.rightNeighbor e
    · cases k with
      | zero =>
          have heq : foreign = ring.rightNeighbor e := by
            simpa only [Counter.site] using hselected
          exact False.elim (hforeign.2 heq)
      | succ m =>
          have hnext :
              ring.rightNeighbor e =
                Counter.site ring foreign (m + 1) := by
            simpa only [Nat.succ_eq_add_one] using hselected.symm
          have hprevious := Counter.resetTrialSitePredecessor
            ring foreign e m hnext
          have hp := hprefix m (by omega)
          rw [← hprevious, hx] at hp
          have hmzero : m = 0 := by omega
          rw [hmzero] at hprevious
          change e = foreign at hprevious
          exact False.elim (hforeign.1 hprevious.symm)
    · exact (bankWindowClosureRepairNonresponderPackFixed
        ring (by omega : 2 ≤ n)
        (bankWindowRootBefore ring seed pre)
        e (Counter.site ring foreign k) hselected).trans
        (hprefix k hk)
  have hownerOld : BankWindowOrphanOwner ring
      (bankWindowRootBefore ring seed pre) foreign j :=
    ⟨hrootOld, hdigitOld, hwrongOld⟩
  have hworkerFrame := congrArg
    (fun a : RenewalBankSite n => a.worker) hdigitFrame.2
  have htaintedOld : BankWindowTainted
      (bankWindowRootBefore ring seed pre)
      (Counter.site ring foreign (j.val + 1)) := by
    rcases htainted with ⟨rho, hp⟩ |
        ⟨p, o, hp, ho⟩
    · exact Or.inl ⟨rho, hworkerFrame.symm.trans hp⟩
    · exact Or.inr ⟨p, o, hworkerFrame.symm.trans hp, ho⟩
  have hmodeFrame := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.mode)
    hrootFrame.1
  have hcontrollerFrame := congrArg
    (fun a : RenewalBankSite n => a.controller) hrootFrame.2
  rcases hJ.orphan foreign j hownerOld htaintedOld with
      hreset | ⟨hwait, hcontroller⟩
  · exact Or.inl (hmodeFrame.trans hreset)
  · exact Or.inr ⟨hmodeFrame.trans hwait,
      hcontrollerFrame.trans hcontroller⟩

/-- PACK-zero root service gives its responder PACK one. The
new responder cannot be a complete rooted window, an incomplete
proto-root, or an orphan root. Consumer: root grant's adjacent
responder activation. -/
theorem bankWindowRootResponderNoRootActivation {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (hx : (r.1 e).pack.val = 0) :
    ¬ BankWindowScope ring (renewalBankNext ring r e)
      (ring.rightNeighbor e) ∧
    (∀ limit : Nat,
      ¬ BankWindowProtoRun ring (renewalBankNext ring r e)
        (ring.rightNeighbor e) limit) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ¬ BankWindowOrphanOwner ring (renewalBankNext ring r e)
        (ring.rightNeighbor e) j) := by
  have hy := (bankWindowRootSourceRoles ring hn r e hx).2
  refine ⟨?_, ?_, ?_⟩
  · intro hs
    have hzero := hs.1 0 (by omega)
    change ((renewalBankNext ring r e).1
      (ring.rightNeighbor e)).pack.val = 0 at hzero
    omega
  · intro limit hp
    have hzero := hp.2.1 0 (by omega)
    change ((renewalBankNext ring r e).1
      (ring.rightNeighbor e)).pack.val = 0 at hzero
    omega
  · intro j ho
    have hzero := ho.1
    omega

/-! PACK-changing responder / newly activated owner. -/

/-- The changed responder's physical mode is RESET, so its own
new proto field follows from the R7 controller frame if it
becomes PACK zero; if not, proto and orphan antecedents are
false. Its CWAIT and all other active comparison phases are
false even when another genuine worker exists remotely.
Consumer: XD root activation and the newly adjacent root. -/
theorem bankWindowOverlapChangedResponderOwnerFields {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hchanged :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val) :
    ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).mode = .RESET ∧
    (∀ limit : Nat,
      BankWindowProtoRun ring
        (bankWindowRootAfter ring seed pre e)
        (ring.rightNeighbor e) limit →
      BankWindowRootForeignProtoField ring
        (bankWindowRootAfter ring seed pre e)
        (ring.rightNeighbor e) limit) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowOrphanOwner ring
        (bankWindowRootAfter ring seed pre e)
        (ring.rightNeighbor e) j →
      BankWindowTainted (bankWindowRootAfter ring seed pre e)
        (Counter.site ring (ring.rightNeighbor e) (j.val + 1)) →
      ((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).mode = .RESET ∨
      (((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).mode = .RWAIT ∧
        ((bankWindowRootAfter ring seed pre e).2.sites
          (ring.rightNeighbor e)).controller = .waiting [])) ∧
    (∀ (o : RenewalBankOrigin n) (i : Fin n)
      (p : RenewalBankPayload n),
      o.root = ring.rightNeighbor e →
      BankComparatorOriginWorker ring
        (bankWindowRootAfter ring seed pre e) o i p →
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode
        ≠ .ARMED ∧
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode
        ≠ .CSTART ∧
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode
        ≠ .IWAIT ∧
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode
        ≠ .CWAIT) := by
  have hrow := bankWindowClosureChangedResponderNoOrigin
    ring (by omega : 2 ≤ n) hbank
    (bankWindowRootBefore ring seed pre) e hchanged
  have hframe := bankWindowExactFrameStep
    ring hn hbank seed pre e hJ
  refine ⟨hrow.1, ?_, ?_, ?_⟩
  · intro limit hp
    by_cases hpack :
        ((bankWindowRootAfter ring seed pre e).1
          (ring.rightNeighbor e)).pack.val = 0
    · have hreset := bankWindowIncomingResetOwnerFields
        ring (bankWindowRootBefore ring seed pre)
        (ring.rightNeighbor e) e hpack hrow.1 hframe
      exact hreset.2.2.1 limit hp
    · have hzero := hp.2.1 0 (by omega)
      change ((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).pack.val = 0 at hzero
      exact False.elim (hpack hzero)
  · intro j _ _
    exact Or.inl hrow.1
  · intro o i p hroot _hworker
    have hm :
        ((bankWindowRootAfter ring seed pre e).1 o.root).mode =
          .RESET := by
      rw [hroot]
      exact hrow.1
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      (intro hbad; rw [hm] at hbad; cases hbad)

/-- A changed PACK responder that makes a FOREIGN window complete
cannot create a proto-run or orphan owner at that root. OLD
J.proto forbids a surviving genuine active controller there.
If its old incomplete root was CWAIT/empty-wait, OLD
J.compareExact excludes all genuine originated workers after
the real changed-role keep-or-erase row. Consumer: repair
activation of J.armedExact and J.compareExact. -/
theorem bankWindowOverlapRepairCompletedForeignFields {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e foreign : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hforeign : foreign ≠ e ∧
      foreign ≠ ring.rightNeighbor e)
    (hchanged :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val)
    (hcomplete : Counter.Complete ring
      (bankWindowRootAfter ring seed pre e).1 foreign)
    (hnot : ¬ Counter.Complete ring
      (bankWindowRootBefore ring seed pre).1 foreign) :
    (∀ limit : Nat,
      ¬ BankWindowProtoRun ring
        (bankWindowRootAfter ring seed pre e) foreign limit) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ¬ BankWindowOrphanOwner ring
        (bankWindowRootAfter ring seed pre e) foreign j) ∧
    (∀ (p : RenewalBankPayload n) (o : RenewalBankOrigin n),
      ((bankWindowRootAfter ring seed pre e).2.sites
        foreign).controller = .active p →
      p.origin = some o → False) ∧
    (((bankWindowRootAfter ring seed pre e).1 foreign).mode =
        .CWAIT →
      ((bankWindowRootAfter ring seed pre e).2.sites
        foreign).controller = .waiting [] →
      ∀ (i : Fin n) (p : RenewalBankPayload n)
        (o : RenewalBankOrigin n),
        o.root = foreign →
        ((bankWindowRootAfter ring seed pre e).2.sites i).worker =
          .payload p →
        p.origin = some o → False) := by
  obtain ⟨t, ht, hsite, _hwrong, _hother⟩ :=
    bankWindowClosureRepairFirstMismatchAtResponder
      ring (by omega : 2 ≤ n)
      (bankWindowRootBefore ring seed pre)
      e foreign hcomplete hnot
  have hpos : 1 ≤ t := by
    by_cases hzero : t = 0
    · rw [hzero] at hsite
      change foreign = ring.rightNeighbor e at hsite
      exact False.elim (hforeign.2 hsite)
    · omega
  let digit : Fin (compileAdvice (ceilLogTwo n)).b :=
    ⟨t - 1,
      (show t - 1 < (compileAdvice (ceilLogTwo n)).b by omega)⟩
  have htarget :
      ring.rightNeighbor e =
        Counter.site ring foreign (digit.val + 1) := by
    change ring.rightNeighbor e =
      Counter.site ring foreign (t - 1 + 1)
    have heq : t - 1 + 1 = t := by omega
    rw [heq]
    exact hsite.symm
  have hrootFrame := bankWindowExactOffPairFrame ring
    (bankWindowRootBefore ring seed pre)
    e foreign hforeign.1 hforeign.2
  have hactive := bankWindowClosureRepairNonincidentGenuineController
    ring hn (bankWindowRootBefore ring seed pre)
    e foreign hJ digit hchanged htarget hcomplete
    hforeign.1 hforeign.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro limit hp
    have hlimit := hp.1
    exact hp.2.2 (hcomplete (limit + 1) (by omega))
  · intro j ho
    exact ho.2.2 (fun k hk =>
      hcomplete k (by have hj := j.isLt; omega))
  · intro p o hc ho
    exact hactive p o hc ho
  · intro hmode hwait i p o horoot hw ho
    have hmodeOld :
        ((bankWindowRootBefore ring seed pre).1 foreign).mode =
          .CWAIT :=
      (congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.mode)
        hrootFrame.1).symm.trans hmode
    have hwaitOld :
        ((bankWindowRootBefore ring seed pre).2.sites
          foreign).controller = .waiting [] :=
      (congrArg (fun a : RenewalBankSite n => a.controller)
        hrootFrame.2).symm.trans hwait
    exact bankWindowClosureRepairCwaitNoOwnWorker
      ring hn hbank (bankWindowRootBefore ring seed pre)
      e foreign hJ hnot hmodeOld hwaitOld
      hchanged i p o horoot hw ho

/-! Incoming responder root, including changed and continuing
real owner rows. -/

/-- If an incoming PACK-zero root keeps its role, mode and ghost
controller, its foreign-overlap proto and orphan clauses
transport exactly from OLD J. These mode/controller equalities
are literal selected-row facts, not a POST-J assumption.
Consumer: stable incoming RWAIT/IWAIT/CWAIT owner. -/
theorem bankWindowOverlapIncomingStableOwnerFields {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n)
    (hJ : BankWindowExact ring r)
    (root e : Fin n)
    (hy : ring.rightNeighbor e = root)
    (hpackOld : (r.1 root).pack.val = 0)
    (hpackPost : ((renewalBankNext ring r e).1 root).pack.val = 0)
    (hmodeKeep :
      ((renewalBankNext ring r e).1 root).mode =
        (r.1 root).mode)
    (hcontrollerKeep :
      ((renewalBankNext ring r e).2.sites root).controller =
        (r.2.sites root).controller) :
    (∀ limit : Nat,
      BankWindowProtoRun ring (renewalBankNext ring r e)
        root limit →
      BankWindowRootForeignProtoField ring
        (renewalBankNext ring r e) root limit) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowOrphanOwner ring (renewalBankNext ring r e)
        root j →
      BankWindowTainted (renewalBankNext ring r e)
        (Counter.site ring root (j.val + 1)) →
      ((renewalBankNext ring r e).1 root).mode = .RESET ∨
      (((renewalBankNext ring r e).1 root).mode = .RWAIT ∧
        ((renewalBankNext ring r e).2.sites root).controller =
          .waiting [])) := by
  constructor
  · intro limit hp
    exact bankWindowIncomingProtoOwnerSurvivor ring hbank
      r hJ root e hy hpackOld hpackPost
      hmodeKeep hcontrollerKeep limit hp
  · intro j ho ht
    exact bankWindowIncomingOrphanOwnerSurvivor ring hbank
      r hJ root e hy hpackOld hpackPost
      hmodeKeep hcontrollerKeep j ho ht

/-- If an incoming OLD PACK-zero root becomes a nonzero
responder, all rooted proto/orphan/scope tests become false.
The changed physical role forces RESET, eliminating newly
activated CWAIT comparison guards at that incoming root.
Consumer: incoming-root changed-responder branch of group 13. -/
theorem bankWindowOverlapIncomingBrokenOwnerFields {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hy :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val = 0)
    (hpost :
      ((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).pack.val ≠ 0) :
    ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).mode = .RESET ∧
    ¬ BankWindowScope ring
      (bankWindowRootAfter ring seed pre e)
      (ring.rightNeighbor e) ∧
    (∀ limit : Nat,
      ¬ BankWindowProtoRun ring
        (bankWindowRootAfter ring seed pre e)
        (ring.rightNeighbor e) limit) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ¬ BankWindowOrphanOwner ring
        (bankWindowRootAfter ring seed pre e)
        (ring.rightNeighbor e) j) := by
  have hchanged :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val := by
    intro hsame
    have hrole := bankWindowExactResponderPack ring
      (bankWindowRootBefore ring seed pre) e
      (clockNeighborDifferent ring (by omega : 2 ≤ n) e)
    exact hpost (hrole.trans (hsame.trans hy))
  have hmode := (bankWindowClosureChangedResponderNoOrigin
    ring (by omega : 2 ≤ n) hbank
    (bankWindowRootBefore ring seed pre) e hchanged).1
  have hpart := (bankWindowOverlapIncomingRootJoint
    ring hn hbank seed pre e hJ hy).2.2.1 hpost
  exact ⟨hmode, hpart.1, hpart.2.1, hpart.2.2⟩

/-! Actual source-root comparison read sets, without an
unproved post-invariant on the foreign origin. -/

/-- Group-13 phaseExcludes: a genuine comparator of a foreign
root is off both endpoints of the source PACK-zero service,
so its worker, token and origin mode are identical in OLD
and POST. The existing read-set contract applies literally.
Consumer: every R0/RWAIT/ARMED/CSTART/IWAIT/CWAIT root row. -/
theorem bankWindowRootForeignPhaseExcludesOnSource {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hx : ((bankWindowRootBefore ring seed pre).1 e).pack.val = 0)
    (o : RenewalBankOrigin n)
    (i : Fin n) (p : RenewalBankPayload n)
    (hforeign : o.root ≠ e ∧
      o.root ≠ ring.rightNeighbor e)
    (hworker : BankComparatorOriginWorker ring
      (bankWindowRootAfter ring seed pre e) o i p) :
    ((bankWindowRootAfter ring seed pre e).1 o.root).mode
        ≠ .ARMED ∧
    ((bankWindowRootAfter ring seed pre e).1 o.root).mode
        ≠ .CSTART ∧
    ((bankWindowRootAfter ring seed pre e).1 o.root).mode
        ≠ .IWAIT := by
  have hoff := bankWindowRootForeignWorkerOffPair
    ring hn hbank seed pre e hJ hx o i p hforeign.1
    hworker.1 hworker.2.1
  have hfree := bankWindowExactOffPairAtomicReads ring
    (bankWindowRootBefore ring seed pre) e i hoff.1 hoff.2
  have hroot := bankWindowExactOffPairAtomicReads ring
    (bankWindowRootBefore ring seed pre) e o.root
    hforeign.1 hforeign.2
  exact bankWindowPhaseExcludesReadTransport ring
    (bankWindowRootBefore ring seed pre)
    (bankWindowRootAfter ring seed pre e)
    o i p hJ
    ⟨hfree.2.2.1, hfree.2.2.2.2.2.1, hroot.2.1⟩
    hworker

/-- Group-13 compareExact: a POST genuine worker of a foreign
CWAIT root with empty waiting controller is an OLD genuine
worker at the same free site. OLD J.compareExact forces its
comparison token, and OLD J.phaseComplete forces its whole
origin PACK interval aligned. The complete foreign window is
outside the selected PACK-zero source edge; read-set transport
then gives POST OnlyToken, live comparator token, exact heads,
and the K bound. Consumer: item-8 foreign comparison and
all authentic root-source rows. -/
theorem bankWindowRootForeignCompareExactOnSource {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hx : ((bankWindowRootBefore ring seed pre).1 e).pack.val = 0)
    (o : RenewalBankOrigin n)
    (i : Fin n) (p : RenewalBankPayload n)
    (hforeign : o.root ≠ e ∧
      o.root ≠ ring.rightNeighbor e)
    (hworker :
      ((bankWindowRootAfter ring seed pre e).2.sites i).worker =
        .payload p)
    (horigin : p.origin = some o)
    (hmode : ((bankWindowRootAfter ring seed pre e).1 o.root).mode =
      .CWAIT)
    (hcontroller :
      ((bankWindowRootAfter ring seed pre e).2.sites
        o.root).controller = .waiting []) :
    bankWindowOnlyToken ring
      (bankWindowRootAfter ring seed pre e) o.root i ∧
    BankTrialLiveComparisonToken
      ((bankWindowRootAfter ring seed pre e).1 i).tok ∧
    p.heads = bankOriginBinaryValue ring
      (bankWindowRootAfter ring seed pre e).1 o ∧
    bankOriginBinaryValue ring
      (bankWindowRootAfter ring seed pre e).1 o ≤
      (compileAdvice (ceilLogTwo n)).K := by
  have hoff := bankWindowRootForeignWorkerOffPair
    ring hn hbank seed pre e hJ hx o i p
    hforeign.1 hworker horigin
  have hfree := bankWindowExactOffPairAtomicReads ring
    (bankWindowRootBefore ring seed pre) e i hoff.1 hoff.2
  have hroot := bankWindowExactOffPairAtomicReads ring
    (bankWindowRootBefore ring seed pre) e o.root
    hforeign.1 hforeign.2
  have hworkerOld :
      ((bankWindowRootBefore ring seed pre).2.sites i).worker =
        .payload p :=
    hfree.2.2.2.2.2.1.symm.trans hworker
  have hmodeOld :
      ((bankWindowRootBefore ring seed pre).1 o.root).mode =
        .CWAIT :=
    hroot.2.1.symm.trans hmode
  have hcontrollerOld :
      ((bankWindowRootBefore ring seed pre).2.sites
        o.root).controller = .waiting [] :=
    hroot.2.2.2.2.2.2.symm.trans hcontroller
  have hcomparisonOld := hJ.compareExact o i p
    hworkerOld horigin hmodeOld hcontrollerOld
  have hcomparatorOld : BankComparatorOriginWorker ring
      (bankWindowRootBefore ring seed pre) o i p :=
    ⟨hworkerOld, horigin, hcomparisonOld.2.1⟩
  have hcompleteOld := hJ.phaseComplete o i p
    hcomparatorOld hmodeOld
  have houtside := bankWindowRootForeignCompleteOutside
    ring (bankWindowRootBefore ring seed pre)
    e o.root hx hforeign hcompleteOld
  have htoks : bankWindowReadDigitTokens ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) o.root := by
    intro j
    have hframe := (bankWindowExactOffWindowFrame ring
      (bankWindowRootBefore ring seed pre)
      o.root e houtside (j.val + 1)
      (by have hj := j.isLt; omega)).1
    exact congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
      hframe
  have hbits : bankWindowReadDigitBits ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) o.root := by
    intro j
    have hframe := (bankWindowExactOffWindowFrame ring
      (bankWindowRootBefore ring seed pre)
      o.root e houtside (j.val + 1)
      (by have hj := j.isLt; omega)).1
    exact congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.bit)
      hframe
  have hread : bankWindowCompareExactReadSet ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) o i p :=
    ⟨hroot.2.1, hroot.2.2.2.2.2.2,
      hfree.2.2.2.2.2.1, hfree.2.2.1, htoks, hbits⟩
  exact bankWindowCompareExactReadTransport ring
    (bankWindowRootBefore ring seed pre)
    (bankWindowRootAfter ring seed pre e)
    o i p hJ hread hworker horigin hmode hcontroller

/-- A newly completed FOREIGN window obtained by one real
changed-PACK responder cannot contain ANY POST genuine worker
whose origin is that foreign root while the root is not RESET
or RWAIT. Indeed OLD J.proto/orphan forbid all POST taint in
that interval (bankWindowClosureRepairNonresetPhaseDigitsClean);
the real extended ReceiptInv and genuine-worker in-band theorem
place the worker at an actual digit offset of that interval.
This eliminates the otherwise newly activated phaseFlags,
phaseComplete, phaseUnique and compareExact antecedents in
the CWAIT branch without assuming an empty waiting controller.
Consumer: R11 group-13 changed-responder phase activation. -/
theorem bankWindowOverlapRepairCompletedForeignNoOriginWorker {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e foreign : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hforeign : foreign ≠ e ∧
      foreign ≠ ring.rightNeighbor e)
    (hchanged :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val)
    (hcomplete : Counter.Complete ring
      (bankWindowRootAfter ring seed pre e).1 foreign)
    (hnot : ¬ Counter.Complete ring
      (bankWindowRootBefore ring seed pre).1 foreign)
    (hnotReset :
      ((bankWindowRootAfter ring seed pre e).1 foreign).mode
        ≠ .RESET)
    (hnotRwait :
      ((bankWindowRootAfter ring seed pre e).1 foreign).mode
        ≠ .RWAIT)
    (i : Fin n) (p : RenewalBankPayload n)
    (o : RenewalBankOrigin n)
    (hroot : o.root = foreign)
    (hworker :
      ((bankWindowRootAfter ring seed pre e).2.sites i).worker =
        .payload p)
    (horigin : p.origin = some o) : False := by
  obtain ⟨t, ht, hsite, _hwrong, _hother⟩ :=
    bankWindowClosureRepairFirstMismatchAtResponder
      ring (by omega : 2 ≤ n)
      (bankWindowRootBefore ring seed pre)
      e foreign hcomplete hnot
  have hpos : 1 ≤ t := by
    by_cases hzero : t = 0
    · rw [hzero] at hsite
      change foreign = ring.rightNeighbor e at hsite
      exact False.elim (hforeign.2 hsite)
    · omega
  let repairDigit : Fin (compileAdvice (ceilLogTwo n)).b :=
    ⟨t - 1,
      (show t - 1 < (compileAdvice (ceilLogTwo n)).b by omega)⟩
  have htarget :
      ring.rightNeighbor e =
        Counter.site ring foreign (repairDigit.val + 1) := by
    change ring.rightNeighbor e =
      Counter.site ring foreign (t - 1 + 1)
    have heq : t - 1 + 1 = t := by omega
    rw [heq]
    exact hsite.symm
  have hrootFrame := bankWindowExactOffPairFrame ring
    (bankWindowRootBefore ring seed pre)
    e foreign hforeign.1 hforeign.2
  have hmodeEq := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.mode)
    hrootFrame.1
  have hnotOldReset :
      ((bankWindowRootBefore ring seed pre).1 foreign).mode
        ≠ .RESET := by
    intro hm
    exact hnotReset (hmodeEq.trans hm)
  have hnotOldRwait :
      ((bankWindowRootBefore ring seed pre).1 foreign).mode
        ≠ .RWAIT := by
    intro hm
    exact hnotRwait (hmodeEq.trans hm)
  have hclean := bankWindowClosureRepairNonresetPhaseDigitsClean
    ring hn hbank (bankWindowRootBefore ring seed pre)
    e foreign hJ repairDigit hchanged htarget hcomplete
    hnotOldReset hnotOldRwait
  have hpostRun :
      rbRun ring (renewalBankStart ring seed) (pre ++ [e]) =
        bankWindowRootAfter ring seed pre e := by
    rw [rbRunAppend]
    rfl
  have hworkerRun :
      ((rbRun ring (renewalBankStart ring seed)
        (pre ++ [e])).2.sites i).worker = .payload p := by
    rw [hpostRun]
    exact hworker
  have hband := bankWindowOverlapGenuineWorkerInBand
    ring hn hbank seed (pre ++ [e]) i p o
    hworkerRun horigin
  have hsiteOrigin := bankWindowGenuineWorkerSiteOfRun
    ring hn hbank seed (pre ++ [e]) i p o
    hworkerRun horigin
  rw [hpostRun] at hband hsiteOrigin
  let workerDigit : Fin (compileAdvice (ceilLogTwo n)).b :=
    ⟨((bankWindowRootAfter ring seed pre e).1 i).pack.val - 1,
      (show ((bankWindowRootAfter ring seed pre e).1 i).pack.val - 1 <
        (compileAdvice (ceilLogTwo n)).b by omega)⟩
  have hrole :
      workerDigit.val + 1 =
        ((bankWindowRootAfter ring seed pre e).1 i).pack.val := by
    change
      ((bankWindowRootAfter ring seed pre e).1 i).pack.val - 1 + 1 =
        ((bankWindowRootAfter ring seed pre e).1 i).pack.val
    omega
  have hsiteWorker :
      Counter.site ring foreign (workerDigit.val + 1) = i := by
    rw [hrole, ← hroot]
    exact hsiteOrigin.symm
  have htaint : BankWindowTainted
      (bankWindowRootAfter ring seed pre e)
      (Counter.site ring foreign (workerDigit.val + 1)) := by
    rw [hsiteWorker]
    exact Or.inr ⟨p, o, hworker, horigin⟩
  exact (hclean workerDigit) htaint

end L3.BankWindow

namespace L3.BankWindow
open L3.BankHeadThreshold
open L3.BankCounterRows

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open L3.BankComparatorExclusive
open Classical

set_option autoImplicit false
set_option Elab.async false

/-! Changed-PACK responder: foreign aligned reads and orphan. -/

/-- A real selected edge cannot destroy an OLD aligned foreign
PACK prefix when its responder is not that prefix's root.
If the responder is the k-th digit, its OLD predecessor is
the (k-1)-st digit; the literal packNext fixed point applies.
Consumer: the changed-PACK J.orphan and foreign CWAIT cases. -/
theorem bankWindowOverlapForeignPrefixCannotBreak {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalBankReference n)
    (e root : Fin n) (last : Nat)
    (hroot : root ≠ ring.rightNeighbor e)
    (hbound : last ≤ (compileAdvice (ceilLogTwo n)).b)
    (hold : ∀ k : Nat, k ≤ last →
      (r.1 (Counter.site ring root k)).pack.val = k) :
    ∀ k : Nat, k ≤ last →
      ((renewalBankNext ring r e).1
        (Counter.site ring root k)).pack.val = k := by
  intro k hk
  by_cases htarget :
      Counter.site ring root k = ring.rightNeighbor e
  · cases k with
    | zero =>
        have heq : root = ring.rightNeighbor e := by
          simpa only [Counter.site] using htarget
        exact False.elim (hroot heq)
    | succ j =>
        have hsrc : e = Counter.site ring root j :=
          Counter.resetTrialSitePredecessor ring root e j
            (by simpa only [Nat.succ_eq_add_one] using htarget.symm)
        have hsrcRole : (r.1 e).pack.val = j := by
          rw [hsrc]
          exact hold j (by omega)
        have hdstRole :
            (r.1 (ring.rightNeighbor e)).pack.val = j + 1 := by
          rw [← htarget]
          exact hold (j + 1) hk
        have hpostRole :
            ((renewalBankNext ring r e).1
              (ring.rightNeighbor e)).pack.val = j + 1 := by
          have hstep := bankWindowExactResponderPack ring r e
            (clockNeighborDifferent ring (by omega : 2 ≤ n) e)
          rw [hstep, hsrcRole, hdstRole]
          exact bankWindowExactPackNextInside
            (compileAdvice (ceilLogTwo n)).b j (by omega)
        rw [htarget]
        exact hpostRole
  · exact (bankWindowClosureRepairNonresponderPackFixed
      ring (by omega : 2 ≤ n) r e
      (Counter.site ring root k) htarget).trans
      (hold k hk)

/-- When the responder PACK changes, any foreign POST orphan
whose root is off-pair and whose named digit is tainted was
already an OLD orphan with the same named taint. The responder
cannot be the named digit, because it has an empty new worker;
a previously complete prefix cannot become incomplete by
the aligned-prefix fixed-point lemma above. Consumer:
J.orphan for the non-PACK-zero repair row, including kept
source worker and erased responder worker. -/
theorem bankWindowOverlapRepairForeignOrphanStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hforeign : root ≠ e ∧ root ≠ ring.rightNeighbor e)
    (hchanged :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val)
    (howner : BankWindowOrphanOwner ring
      (bankWindowRootAfter ring seed pre e) root j)
    (htainted : BankWindowTainted
      (bankWindowRootAfter ring seed pre e)
      (Counter.site ring root (j.val + 1))) :
    ((bankWindowRootAfter ring seed pre e).1 root).mode = .RESET ∨
      (((bankWindowRootAfter ring seed pre e).1 root).mode = .RWAIT ∧
        ((bankWindowRootAfter ring seed pre e).2.sites
          root).controller = .waiting []) := by
  have hclean := bankWindowClosureChangedDigitClean ring hn hbank
    (bankWindowRootBefore ring seed pre) e hchanged
  have hnotTarget :
      Counter.site ring root (j.val + 1) ≠ ring.rightNeighbor e := by
    intro heq
    have ht : BankWindowTainted
        (bankWindowRootAfter ring seed pre e)
        (ring.rightNeighbor e) := by
      rw [← heq]
      exact htainted
    exact hclean.2.2.2.1 ht
  have hrootFrame := bankWindowExactOffPairFrame ring
    (bankWindowRootBefore ring seed pre) e root
    hforeign.1 hforeign.2
  have hrootRole : ((bankWindowRootBefore ring seed pre).1
      root).pack.val = 0 := by
    have hf := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
        a.pack.val) hrootFrame.1
    exact hf.symm.trans howner.1
  have hnamedRole :
      ((bankWindowRootBefore ring seed pre).1
        (Counter.site ring root (j.val + 1))).pack.val =
          j.val + 1 :=
    (bankWindowClosureRepairNonresponderPackFixed
      ring (by omega : 2 ≤ n)
      (bankWindowRootBefore ring seed pre) e
      (Counter.site ring root (j.val + 1))
      hnotTarget).symm.trans howner.2.1
  have hbroken :
      ¬ (∀ k : Nat, k ≤ j.val + 1 →
        ((bankWindowRootBefore ring seed pre).1
          (Counter.site ring root k)).pack.val = k) := by
    intro hprefix
    exact howner.2.2
      (bankWindowOverlapForeignPrefixCannotBreak
        ring hn (bankWindowRootBefore ring seed pre)
        e root (j.val + 1) hforeign.2
        (by have hj := j.isLt; omega) hprefix)
  have holdOwner : BankWindowOrphanOwner ring
      (bankWindowRootBefore ring seed pre) root j :=
    ⟨hrootRole, hnamedRole, hbroken⟩
  have holdTaint := bankWindowClosureChangedTaintOld
    ring hn hbank (bankWindowRootBefore ring seed pre)
    e hchanged (Counter.site ring root (j.val + 1)) htainted
  have hmodeFrame := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.mode)
    hrootFrame.1
  have hcontrollerFrame := congrArg
    (fun a : RenewalBankSite n => a.controller)
    hrootFrame.2
  rcases hJ.orphan root j holdOwner holdTaint with
      hreset | ⟨hwait, hcontrol⟩
  · exact Or.inl (hmodeFrame.trans hreset)
  · exact Or.inr ⟨hmodeFrame.trans hwait,
      hcontrollerFrame.trans hcontrol⟩

/-- If a foreign CWAIT/empty-wait owner is still incomplete
after a changed responder, it owns no genuine POST worker.
The prefix fixed-point lemma makes its OLD window incomplete;
the installed changed-worker keep-or-erase and OLD J.compareExact
then exclude any worker of that origin. Consumer: phaseFlags,
phaseComplete, phaseUnique and compareExact at that owner. -/
theorem bankWindowOverlapRepairIncompleteForeignCwaitNoWorker {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hforeign : root ≠ e ∧ root ≠ ring.rightNeighbor e)
    (hchanged :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val)
    (hnot : ¬ Counter.Complete ring
      (bankWindowRootAfter ring seed pre e).1 root)
    (hmode : ((bankWindowRootAfter ring seed pre e).1
      root).mode = .CWAIT)
    (hwait : ((bankWindowRootAfter ring seed pre e).2.sites
      root).controller = .waiting []) :
    ∀ (i : Fin n) (p : RenewalBankPayload n)
      (o : RenewalBankOrigin n),
      o.root = root →
      ((bankWindowRootAfter ring seed pre e).2.sites i).worker =
        .payload p → p.origin = some o → False := by
  have holdIncomplete :
      ¬ Counter.Complete ring
        (bankWindowRootBefore ring seed pre).1 root := by
    intro hc
    exact hnot (bankWindowOverlapForeignPrefixCannotBreak
      ring hn (bankWindowRootBefore ring seed pre)
      e root (compileAdvice (ceilLogTwo n)).b
      hforeign.2 (Nat.le_refl _) hc)
  have hrootFrame := bankWindowExactOffPairFrame ring
    (bankWindowRootBefore ring seed pre) e root
    hforeign.1 hforeign.2
  have hmodeOld :
      ((bankWindowRootBefore ring seed pre).1 root).mode =
        .CWAIT :=
    (congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.mode)
      hrootFrame.1).symm.trans hmode
  have hwaitOld :
      ((bankWindowRootBefore ring seed pre).2.sites
        root).controller = .waiting [] :=
    (congrArg
      (fun a : RenewalBankSite n => a.controller)
      hrootFrame.2).symm.trans hwait
  exact bankWindowClosureRepairCwaitNoOwnWorker
    ring hn hbank (bankWindowRootBefore ring seed pre)
    e root hJ holdIncomplete hmodeOld hwaitOld hchanged

end L3.BankWindow


namespace L3.BankWindow
open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open L3.BankComparatorExclusive
open L3.BankHeadThreshold
open L3.BankCounterRows
open Classical

/-! Exact changed-responder worker outcomes. The pair does not
transfer an OLD nonroot worker into its new responder role. -/

/-- An OLD pending RR on a nonzero BANK digit is retained at
that very source when the selected responder PACK changes.
The source's physical RR and bit are unchanged, and the
responder's worker is cleared. Source role bounds come from
the real-run ReceiptInv.pending clause, not extra state
assumptions. Consumer: the newly extended foreign proto
RWAIT pending-front witness at the repair source. -/
theorem bankWindowOverlapRepairPendingRrKeeps {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n) (rho : RenewalBankReceipt n)
    (hchanged :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val)
    (hrr : ((bankWindowRootBefore ring seed pre).1 e).tok = .RR)
    (hpending :
      ((bankWindowRootBefore ring seed pre).2.sites e).worker =
        .pending rho) :
    ((bankWindowRootAfter ring seed pre e).1 e).tok = .RR ∧
    ((bankWindowRootAfter ring seed pre e).1 e).bit =
      ((bankWindowRootBefore ring seed pre).1 e).bit ∧
    ((bankWindowRootAfter ring seed pre e).2.sites e).worker =
      .pending rho ∧
    ((bankWindowRootAfter ring seed pre e).2.sites
      (ring.rightNeighbor e)).worker = .empty := by
  have hreceipt := rbReceiptInvBankWordOfInv
    ring (by omega : 2 ≤ n) seed hbank pre
  obtain ⟨_, _, k, hk, hb, _, hpack, _⟩ :=
    hreceipt.pending e rho hpending
  have hlow :
      1 ≤ ((bankWindowRootBefore ring seed pre).1 e).pack.val := by
    rw [hpack]
    exact hk
  have hhigh :
      ((bankWindowRootBefore ring seed pre).1 e).pack.val ≤
        (compileAdvice (ceilLogTwo n)).b := by
    rw [hpack]
    exact hb
  have hnonzero :
      ((bankWindowRootBefore ring seed pre).1 e).pack.val ≠ 0 := by
    omega
  have hraw :
      (Counter.resetBankOld
        ((bankWindowRootBefore ring seed pre).1 e)
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e))).1.tok = .RR ∧
      (Counter.resetBankOld
        ((bankWindowRootBefore ring seed pre).1 e)
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e))).1.bit =
      ((bankWindowRootBefore ring seed pre).1 e).bit := by
    simp [Counter.resetBankOld, bankPair, bankCell,
      hnonzero, hlow, hhigh, hchanged, hrr]
  have hsourceGhost :
      (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
        (bankWindowRootBefore ring seed pre).2 e
        (ring.rightNeighbor e)
        ((bankWindowRootBefore ring seed pre).1 e)
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e))).1.worker =
      ((bankWindowRootBefore ring seed pre).2.sites e).worker := by
    simp [renewalBankPairMemory, bankCell,
      hnonzero, hlow, hhigh, hchanged, hrr]
  have htargetGhost :
      (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
        (bankWindowRootBefore ring seed pre).2 e
        (ring.rightNeighbor e)
        ((bankWindowRootBefore ring seed pre).1 e)
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e))).2.worker = .empty := by
    simp [renewalBankPairMemory, bankCell,
      hnonzero, hlow, hhigh, hchanged, hrr]
  have htrip := bankWindowClosureSelectedBankTrip
    ring hn hbank (bankWindowRootBefore ring seed pre) e
  have ht := congrArg
    (fun t : Mode × Bool × BTok => t.2.2) htrip.1
  change ((bankWindowRootAfter ring seed pre e).1 e).tok =
    (Counter.resetBankOld
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).1.tok at ht
  have hbit := congrArg
    (fun t : Mode × Bool × BTok => t.2.1) htrip.1
  change ((bankWindowRootAfter ring seed pre e).1 e).bit =
    (Counter.resetBankOld
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).1.bit at hbit
  have hghost := (rbReferenceSelectedPairFrame
    ring (by omega : 2 ≤ n)
    (bankWindowRootBefore ring seed pre) e).2.2
  have hsource := congrArg
    (fun s : RenewalBankSite n => s.worker) hghost.1
  change ((bankWindowRootAfter ring seed pre e).2.sites e).worker =
    (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
      (bankWindowRootBefore ring seed pre).2 e
      (ring.rightNeighbor e)
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).1.worker at hsource
  have htarget := congrArg
    (fun s : RenewalBankSite n => s.worker) hghost.2
  change ((bankWindowRootAfter ring seed pre e).2.sites
    (ring.rightNeighbor e)).worker =
    (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
      (bankWindowRootBefore ring seed pre).2 e
      (ring.rightNeighbor e)
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).2.worker at htarget
  exact ⟨ht.trans hraw.1, hbit.trans hraw.2,
    hsource.trans (hsourceGhost.trans hpending),
    htarget.trans htargetGhost⟩

/-- Every strictly earlier foreign digit is an exact full
physical-and-ghost frame when the selected nonroot source is
a later digit in the same geometric interval. Consumer:
newly extended J.proto front and zero-prefix preservation. -/
theorem bankWindowOverlapRepairEarlierSiteFrame {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n)
    (e root : Fin n) (sourceOffset t : Nat)
    (hsource : e = Counter.site ring root sourceOffset)
    (hbound : sourceOffset ≤ (compileAdvice (ceilLogTwo n)).b)
    (hearlier : t < sourceOffset) :
    (renewalBankNext ring r e).1 (Counter.site ring root t) =
      r.1 (Counter.site ring root t) ∧
    (renewalBankNext ring r e).2.sites (Counter.site ring root t) =
      r.2.sites (Counter.site ring root t) := by
  have hsourceNe :
      Counter.site ring root t ≠ e := by
    rw [hsource]
    exact bankWindowIncidenceSiteDistinct ring hbank root
      t sourceOffset hearlier (by omega)
  have htargetNe :
      Counter.site ring root t ≠ ring.rightNeighbor e := by
    rw [hsource]
    change Counter.site ring root t ≠
      Counter.site ring root (sourceOffset + 1)
    exact bankWindowIncidenceSiteDistinct ring hbank root
      t (sourceOffset + 1) (by omega) (by omega)
  exact bankWindowExactOffPairFrame ring r e
    (Counter.site ring root t) hsourceNe htargetNe

end L3.BankWindow


namespace L3.BankWindow
open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open L3.BankComparatorExclusive
open L3.BankHeadThreshold
open L3.BankCounterRows
open Classical

/-! A repaired proper proto prefix has a concrete OLD first
mismatch at the responder and no fictitious new front. -/

theorem bankWindowOverlapInheritedRootExcludesEmptyModes {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n)
    (hJ : BankWindowExact ring r)
    (hrole : (r.1 root).pack.val = 0)
    (hinherited : BankWindowInheritedController r root) :
    (r.1 root).mode ≠ .RESET ∧
    ¬ ((r.1 root).mode = .RWAIT ∧
      (r.2.sites root).controller = .waiting []) := by
  constructor
  · intro hreset
    have hshape := (hJ.frame root).1
    have hempty : (r.2.sites root).controller = .empty := by
      simpa [bankInFlightControllerShape, hrole, hreset] using hshape
    rcases hinherited with ⟨atoms, hc, _⟩ | ⟨p, hc, _⟩
    · rw [hempty] at hc
      cases hc
    · rw [hempty] at hc
      cases hc
  · intro hh
    rcases hinherited with ⟨atoms, hc, hne⟩ |
        ⟨p, hc, _⟩
    · rw [hh.2] at hc
      have hz : atoms = [] := by
        cases hc
        rfl
      exact hne hz
    · rw [hh.2] at hc
      cases hc


end L3.BankWindow

namespace L3.BankWindow
open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open L3.BankComparatorExclusive
open L3.BankHeadThreshold
open L3.BankCounterRows
open Classical

theorem bankWindowOverlapRepairExtendedProtoOld {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n) (k limit : Nat)
    (hsource : e = Counter.site ring root k)
    (hk : 1 ≤ k) (hinterior : k < limit)
    (hchanged :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val)
    (hproto : BankWindowProtoRun ring
      (bankWindowRootAfter ring seed pre e) root limit) :
    BankWindowProtoRun ring
      (bankWindowRootBefore ring seed pre) root k ∧
    ((bankWindowRootBefore ring seed pre).1 e).pack.val = k ∧
    ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val ≠ k + 1 ∧
    root ≠ e ∧ root ≠ ring.rightNeighbor e := by
  have hlimit : limit < (compileAdvice (ceilLogTwo n)).b :=
    hproto.1
  have hnext :
      ring.rightNeighbor e = Counter.site ring root (k + 1) := by
    rw [hsource]
    rfl
  have hsrcNe :
      e ≠ ring.rightNeighbor e :=
    (clockNeighborDifferent ring (by omega : 2 ≤ n) e).symm
  have hsrcFixed := bankWindowClosureRepairNonresponderPackFixed
    ring (by omega : 2 ≤ n)
    (bankWindowRootBefore ring seed pre) e e hsrcNe
  have hsrcPost :
      ((bankWindowRootAfter ring seed pre e).1 e).pack.val = k := by
    have hsiteRole := hproto.2.1 k (by omega)
    rw [← hsource] at hsiteRole
    exact hsiteRole
  have hsrcOld :
      ((bankWindowRootBefore ring seed pre).1 e).pack.val = k :=
    hsrcFixed.symm.trans hsrcPost
  have hdestPost :
      ((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).pack.val = k + 1 := by
    rw [hnext]
    exact hproto.2.1 (k + 1) (by omega)
  have hdestRole := bankWindowExactResponderPack ring
    (bankWindowRootBefore ring seed pre) e
    (clockNeighborDifferent ring (by omega : 2 ≤ n) e)
  have hstep : packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b = k + 1 :=
    hdestRole.symm.trans hdestPost
  have hwrong :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val ≠ k + 1 := by
    intro hh
    exact hchanged (hstep.trans hh.symm)
  have hprefix :
      ∀ t : Nat, t ≤ k →
        ((bankWindowRootBefore ring seed pre).1
          (Counter.site ring root t)).pack.val = t := by
    intro t ht
    have havoid :
        Counter.site ring root t ≠ ring.rightNeighbor e := by
      rw [hnext]
      exact bankWindowIncidenceSiteDistinct ring hbank root
        t (k + 1) (by omega) (by omega)
    have hf := bankWindowClosureRepairNonresponderPackFixed
      ring (by omega : 2 ≤ n)
      (bankWindowRootBefore ring seed pre) e
      (Counter.site ring root t) havoid
    exact hf.symm.trans (hproto.2.1 t (by omega))
  have hrootSource : root ≠ e := by
    rw [hsource]
    have hh := bankWindowIncidenceSiteDistinct
      ring hbank root 0 k (by omega) (by omega)
    change root ≠ Counter.site ring root k at hh
    exact hh
  have hrootTarget : root ≠ ring.rightNeighbor e := by
    rw [hnext]
    have hh := bankWindowIncidenceSiteDistinct
      ring hbank root 0 (k + 1) (by omega) (by omega)
    change root ≠ Counter.site ring root (k + 1) at hh
    exact hh
  have hprotoOld : BankWindowProtoRun ring
      (bankWindowRootBefore ring seed pre) root k :=
    ⟨(by omega), hprefix,
      (by rw [← hnext]; exact hwrong)⟩
  exact ⟨hprotoOld, hsrcOld, hwrong,
    hrootSource, hrootTarget⟩

theorem bankWindowOverlapRepairExtendedProtoRrFront {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n) (k limit : Nat)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hsource : e = Counter.site ring root k)
    (hk : 1 ≤ k) (hinterior : k < limit)
    (hchanged :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val)
    (hproto : BankWindowProtoRun ring
      (bankWindowRootAfter ring seed pre e) root limit)
    (hmode :
      ((bankWindowRootAfter ring seed pre e).1 root).mode = .RWAIT)
    (hcontroller :
      ((bankWindowRootAfter ring seed pre e).2.sites
        root).controller = .waiting []) :
    ∃ j : Fin (compileAdvice (ceilLogTwo n)).b,
      j.val + 1 ≤ limit ∧
      ∃ rho : RenewalBankReceipt n,
        ((bankWindowRootAfter ring seed pre e).2.sites
          (Counter.site ring root (j.val + 1))).worker =
            .pending rho ∧
        ((bankWindowRootAfter ring seed pre e).1
          (Counter.site ring root (j.val + 1))).tok = .RR ∧
        bankWindowZeroPrefix ring
          (bankWindowRootAfter ring seed pre e)
          root (j.val + 1) ∧
        (∀ t : Fin (compileAdvice (ceilLogTwo n)).b,
          t.val < j.val →
          ((bankWindowRootAfter ring seed pre e).1
            (Counter.site ring root (t.val + 1))).tok = .E) := by
  obtain ⟨hprotoOld, _, _, hrootSource, hrootTarget⟩ :=
    bankWindowOverlapRepairExtendedProtoOld
      ring hn hbank seed pre e root k limit
      hsource hk hinterior hchanged hproto
  have hrootFrame := bankWindowExactOffPairFrame ring
    (bankWindowRootBefore ring seed pre) e root
    hrootSource hrootTarget
  have hmodeOld :
      ((bankWindowRootBefore ring seed pre).1 root).mode = .RWAIT :=
    (congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.mode)
      hrootFrame.1).symm.trans hmode
  have hcontrolOld :
      ((bankWindowRootBefore ring seed pre).2.sites
        root).controller = .waiting [] :=
    (congrArg (fun a : RenewalBankSite n => a.controller)
      hrootFrame.2).symm.trans hcontroller
  obtain ⟨front, hfront, rho, hw, ht, hz, hearlier⟩ :=
    (hJ.proto root k hprotoOld).2.2.1
      ⟨hmodeOld, hcontrolOld⟩
  have hfrontLimit : front.val + 1 ≤ limit := by omega
  have hbound : k ≤ (compileAdvice (ceilLogTwo n)).b := by
    have hl := hproto.1
    omega
  by_cases hbefore : front.val + 1 < k
  · refine ⟨front, hfrontLimit, rho, ?_, ?_, ?_, ?_⟩
    · have hf := (bankWindowOverlapRepairEarlierSiteFrame
        ring hbank (bankWindowRootBefore ring seed pre)
        e root k (front.val + 1) hsource hbound hbefore).2
      exact (congrArg
        (fun s : RenewalBankSite n => s.worker) hf).trans hw
    · have hf := (bankWindowOverlapRepairEarlierSiteFrame
        ring hbank (bankWindowRootBefore ring seed pre)
        e root k (front.val + 1) hsource hbound hbefore).1
      exact (congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
        hf).trans ht
    · intro t htle
      have hsmall : t.val + 1 < k := by omega
      have hf := (bankWindowOverlapRepairEarlierSiteFrame
        ring hbank (bankWindowRootBefore ring seed pre)
        e root k (t.val + 1) hsource hbound hsmall).1
      exact (congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.bit)
        hf).trans (hz t htle)
    · intro t htlt
      have hsmall : t.val + 1 < k := by omega
      have hf := (bankWindowOverlapRepairEarlierSiteFrame
        ring hbank (bankWindowRootBefore ring seed pre)
        e root k (t.val + 1) hsource hbound hsmall).1
      exact (congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
        hf).trans (hearlier t htlt)
  · have hfrontEq : front.val + 1 = k := by omega
    have hfrontSite :
        Counter.site ring root (front.val + 1) = e := by
      rw [hfrontEq]
      exact hsource.symm
    have hworkerSource :
        ((bankWindowRootBefore ring seed pre).2.sites e).worker =
          .pending rho := by
      rw [← hfrontSite]
      exact hw
    have htokenSource :
        ((bankWindowRootBefore ring seed pre).1 e).tok = .RR := by
      rw [← hfrontSite]
      exact ht
    obtain ⟨htokenPost, hbitPost, hworkerPost, _⟩ :=
      bankWindowOverlapRepairPendingRrKeeps
        ring hn hbank seed pre e rho
        hchanged htokenSource hworkerSource
    refine ⟨front, hfrontLimit, rho, ?_, ?_, ?_, ?_⟩
    · rw [hfrontSite]
      exact hworkerPost
    · rw [hfrontSite]
      exact htokenPost
    · intro t htle
      by_cases htouch : t.val + 1 = k
      · have hsite : Counter.site ring root (t.val + 1) = e := by
          rw [htouch]
          exact hsource.symm
        have hzeroOld :
            ((bankWindowRootBefore ring seed pre).1 e).bit = false := by
          rw [← hsite]
          exact hz t htle
        rw [hsite]
        exact hbitPost.trans hzeroOld
      · have hsmall : t.val + 1 < k := by omega
        have hf := (bankWindowOverlapRepairEarlierSiteFrame
          ring hbank (bankWindowRootBefore ring seed pre)
          e root k (t.val + 1) hsource hbound hsmall).1
        exact (congrArg
          (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.bit)
          hf).trans (hz t htle)
    · intro t htlt
      have hsmall : t.val + 1 < k := by omega
      have hf := (bankWindowOverlapRepairEarlierSiteFrame
        ring hbank (bankWindowRootBefore ring seed pre)
        e root k (t.val + 1) hsource hbound hsmall).1
      exact (congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
        hf).trans (hearlier t htlt)

theorem bankWindowOverlapRepairExtendedProtoTailMode {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n) (k limit : Nat)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hsource : e = Counter.site ring root k)
    (hk : 1 ≤ k) (hinterior : k < limit)
    (hchanged :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val)
    (hproto : BankWindowProtoRun ring
      (bankWindowRootAfter ring seed pre e) root limit)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (hafter : k < j.val + 1)
    (hwithin : j.val + 1 ≤ limit)
    (htainted : BankWindowTainted
      (bankWindowRootAfter ring seed pre e)
      (Counter.site ring root (j.val + 1))) :
    ((bankWindowRootBefore ring seed pre).1 root).mode = .RESET ∨
    (((bankWindowRootBefore ring seed pre).1 root).mode = .RWAIT ∧
      ((bankWindowRootBefore ring seed pre).2.sites
        root).controller = .waiting []) := by
  obtain ⟨hprotoOld, _, _, _, _⟩ :=
    bankWindowOverlapRepairExtendedProtoOld
      ring hn hbank seed pre e root k limit
      hsource hk hinterior hchanged hproto
  have hnext :
      ring.rightNeighbor e = Counter.site ring root (k + 1) := by
    rw [hsource]
    rfl
  by_cases htouch : j.val + 1 = k + 1
  · have hsite :
        Counter.site ring root (j.val + 1) =
          ring.rightNeighbor e := by
      rw [htouch]
      exact hnext.symm
    have hclean := bankWindowClosureChangedDigitClean
      ring hn hbank (bankWindowRootBefore ring seed pre)
      e hchanged
    have ht : BankWindowTainted
        (bankWindowRootAfter ring seed pre e)
        (ring.rightNeighbor e) := by
      rw [← hsite]
      exact htainted
    exact False.elim (hclean.2.2.2.1 ht)
  · have hlater : k + 1 < j.val + 1 := by omega
    have hnotTarget :
        Counter.site ring root (j.val + 1) ≠
          ring.rightNeighbor e := by
      rw [hnext]
      exact (bankWindowIncidenceSiteDistinct ring hbank root
        (k + 1) (j.val + 1) hlater (by omega)).symm
    have hnamedOld :
        ((bankWindowRootBefore ring seed pre).1
          (Counter.site ring root (j.val + 1))).pack.val =
            j.val + 1 := by
      have hf := bankWindowClosureRepairNonresponderPackFixed
        ring (by omega : 2 ≤ n)
        (bankWindowRootBefore ring seed pre) e
        (Counter.site ring root (j.val + 1)) hnotTarget
      exact hf.symm.trans (hproto.2.1 (j.val + 1) hwithin)
    have hbadPrefix :
        ¬ (∀ t : Nat, t ≤ j.val + 1 →
          ((bankWindowRootBefore ring seed pre).1
            (Counter.site ring root t)).pack.val = t) := by
      intro hprefix
      exact hprotoOld.2.2 (hprefix (k + 1) (by omega))
    have hrootZero :
        ((bankWindowRootBefore ring seed pre).1 root).pack.val = 0 := by
      change ((bankWindowRootBefore ring seed pre).1
        (Counter.site ring root 0)).pack.val = 0
      exact hprotoOld.2.1 0 (by omega)
    have holdOwner : BankWindowOrphanOwner ring
        (bankWindowRootBefore ring seed pre) root j :=
      ⟨hrootZero, hnamedOld, hbadPrefix⟩
    have holdTaint := bankWindowClosureChangedTaintOld
      ring hn hbank (bankWindowRootBefore ring seed pre)
      e hchanged (Counter.site ring root (j.val + 1)) htainted
    exact hJ.orphan root j holdOwner holdTaint

theorem bankWindowOverlapRepairExtendedProtoForeign {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n) (k limit : Nat)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hsource : e = Counter.site ring root k)
    (hk : 1 ≤ k) (hinterior : k < limit)
    (hchanged :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val)
    (hproto : BankWindowProtoRun ring
      (bankWindowRootAfter ring seed pre e) root limit) :
    BankWindowRootForeignProtoField ring
      (bankWindowRootAfter ring seed pre e) root limit := by
  obtain ⟨hprotoOld, _, _, hrootSource, hrootTarget⟩ :=
    bankWindowOverlapRepairExtendedProtoOld
      ring hn hbank seed pre e root k limit
      hsource hk hinterior hchanged hproto
  have hold := hJ.proto root k hprotoOld
  have hrootFrame := bankWindowExactOffPairFrame ring
    (bankWindowRootBefore ring seed pre) e root
    hrootSource hrootTarget
  have hmodeFrame := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.mode)
    hrootFrame.1
  have hcontrollerFrame := congrArg
    (fun a : RenewalBankSite n => a.controller)
    hrootFrame.2
  have hrootZero :
      ((bankWindowRootBefore ring seed pre).1 root).pack.val = 0 := by
    change ((bankWindowRootBefore ring seed pre).1
      (Counter.site ring root 0)).pack.val = 0
    exact hprotoOld.2.1 0 (by omega)
  have htaintBack := bankWindowClosureChangedTaintOld
    ring hn hbank (bankWindowRootBefore ring seed pre)
    e hchanged
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p o hactive ho
    exact hold.1 p o
      (hcontrollerFrame.symm.trans hactive) ho
  · intro hinherited j hj htaint
    have hinheritedOld : BankWindowInheritedController
        (bankWindowRootBefore ring seed pre) root := by
      unfold BankWindowInheritedController at hinherited ⊢
      rw [hcontrollerFrame] at hinherited
      exact hinherited
    by_cases hfirst : j.val + 1 ≤ k
    · exact (hold.2.1 hinheritedOld j hfirst)
        (htaintBack (Counter.site ring root (j.val + 1)) htaint)
    · have hrestriction := bankWindowOverlapRepairExtendedProtoTailMode
        ring hn hbank seed pre e root k limit hJ
        hsource hk hinterior hchanged hproto j
        (by omega) hj htaint
      have hmodeEx := bankWindowOverlapInheritedRootExcludesEmptyModes
        ring (bankWindowRootBefore ring seed pre)
        root hJ hrootZero hinheritedOld
      rcases hrestriction with hreset | hwait
      · exact hmodeEx.1 hreset
      · exact hmodeEx.2 hwait
  · intro hwait
    exact bankWindowOverlapRepairExtendedProtoRrFront
      ring hn hbank seed pre e root k limit hJ
      hsource hk hinterior hchanged hproto hwait.1 hwait.2
  · intro hnotReset hnotRwait j hj htaint
    have hnotOldReset :
        ((bankWindowRootBefore ring seed pre).1 root).mode ≠
          .RESET := by
      intro hm
      exact hnotReset (hmodeFrame.trans hm)
    have hnotOldRwait :
        ((bankWindowRootBefore ring seed pre).1 root).mode ≠
          .RWAIT := by
      intro hm
      exact hnotRwait (hmodeFrame.trans hm)
    by_cases hfirst : j.val + 1 ≤ k
    · exact (hold.2.2.2 hnotOldReset hnotOldRwait
        j hfirst)
        (htaintBack (Counter.site ring root (j.val + 1)) htaint)
    · rcases bankWindowOverlapRepairExtendedProtoTailMode
        ring hn hbank seed pre e root k limit hJ
        hsource hk hinterior hchanged hproto j
        (by omega) hj htaint with hreset | hwait
      · exact hnotOldReset hreset
      · exact hnotOldRwait hwait.1

theorem bankWindowOverlapRepairSourceComparisonBackward {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hlow : 1 ≤ (r.1 e).pack.val)
    (hhigh : (r.1 e).pack.val ≤
      (compileAdvice (ceilLogTwo n)).b)
    (hchanged :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      (r.1 (ring.rightNeighbor e)).pack.val)
    (hpost : BankTrialLiveComparisonToken
      ((renewalBankNext ring r e).1 e).tok) :
    BankTrialLiveComparisonToken (r.1 e).tok := by
  have hnonzero : (r.1 e).pack.val ≠ 0 := by omega
  have hraw :
      (Counter.resetBankOld (r.1 e)
        (r.1 (ring.rightNeighbor e))).1.tok =
        (r.1 e).tok ∨
      (Counter.resetBankOld (r.1 e)
        (r.1 (ring.rightNeighbor e))).1.tok = .E := by
    cases ht : (r.1 e).tok <;>
      simp [Counter.resetBankOld, bankPair, bankCell,
        hnonzero, hlow, hhigh, hchanged, ht] <;>
      (first
        | exact Or.inl rfl
        | exact Or.inr rfl
        | (split <;>
            (first | exact Or.inl rfl | exact Or.inr rfl)))
  have htrip := (bankWindowClosureSelectedBankTrip
    ring hn hbank r e).1
  have htok := congrArg
    (fun t : Mode × Bool × BTok => t.2.2) htrip
  change ((renewalBankNext ring r e).1 e).tok =
    (Counter.resetBankOld (r.1 e)
      (r.1 (ring.rightNeighbor e))).1.tok at htok
  rcases hraw with hsame | hempty
  · have hpostOld := htok.trans hsame
    rw [hpostOld] at hpost
    exact hpost
  · have hpostEmpty := htok.trans hempty
    rw [hpostEmpty] at hpost
    simp [BankTrialLiveComparisonToken] at hpost

theorem bankWindowOverlapRepairComparatorBackward {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hchanged :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val)
    (hnonroot :
      ((bankWindowRootBefore ring seed pre).1 e).pack.val ≠ 0)
    (o : RenewalBankOrigin n) (i : Fin n)
    (p : RenewalBankPayload n)
    (hpost : BankComparatorOriginWorker ring
      (bankWindowRootAfter ring seed pre e) o i p) :
    BankComparatorOriginWorker ring
      (bankWindowRootBefore ring seed pre) o i p := by
  by_cases hsource : i = e
  · subst i
    rcases bankWindowClosureChangedWorkerChoice ring hn hbank
      (bankWindowRootBefore ring seed pre) e hchanged e with
      hkeep | hempty
    · have holdWorker :
          ((bankWindowRootBefore ring seed pre).2.sites e).worker =
            .payload p :=
        hkeep.symm.trans hpost.1
      have hband := bankWindowOverlapGenuineWorkerInBand
        ring hn hbank seed pre e p o holdWorker hpost.2.1
      have holdToken := bankWindowOverlapRepairSourceComparisonBackward
        ring hn hbank (bankWindowRootBefore ring seed pre)
        e hband.1 hband.2 hchanged hpost.2.2
      exact ⟨holdWorker, hpost.2.1, holdToken⟩
    · rcases hpost with ⟨hworker, _, _⟩
      rw [hempty] at hworker
      cases hworker
  · by_cases htarget : i = ring.rightNeighbor e
    · subst i
      have hclean := bankWindowClosureChangedDigitClean
        ring hn hbank (bankWindowRootBefore ring seed pre)
        e hchanged
      exact False.elim (hclean.2.2.2.1
        (Or.inr ⟨p, o, hpost.1, hpost.2.1⟩))
    · have hframe := bankWindowExactOffPairFrame ring
        (bankWindowRootBefore ring seed pre)
        e i hsource htarget
      have htoken := congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
        hframe.1
      have hworker := congrArg
        (fun a : RenewalBankSite n => a.worker) hframe.2
      have hpostToken : BankTrialLiveComparisonToken
          ((renewalBankNext ring
            (bankWindowRootBefore ring seed pre) e).1 i).tok :=
        hpost.2.2
      have holdToken : BankTrialLiveComparisonToken
          ((bankWindowRootBefore ring seed pre).1 i).tok := by
        rw [htoken] at hpostToken
        exact hpostToken
      exact ⟨hworker.symm.trans hpost.1, hpost.2.1,
        holdToken⟩

theorem bankWindowOverlapRepairForeignPhaseExcludes {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hchanged :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val)
    (hnonroot :
      ((bankWindowRootBefore ring seed pre).1 e).pack.val ≠ 0)
    (o : RenewalBankOrigin n) (i : Fin n)
    (p : RenewalBankPayload n)
    (hforeign : o.root ≠ e ∧
      o.root ≠ ring.rightNeighbor e)
    (hcomp : BankComparatorOriginWorker ring
      (bankWindowRootAfter ring seed pre e) o i p) :
    ((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠
        .ARMED ∧
    ((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠
        .CSTART ∧
    ((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠
        .IWAIT := by
  have holdComp := bankWindowOverlapRepairComparatorBackward
    ring hn hbank seed pre e hchanged hnonroot o i p hcomp
  have hold := hJ.phaseExcludes o i p holdComp
  have hframe := (bankWindowExactOffPairFrame ring
    (bankWindowRootBefore ring seed pre)
    e o.root hforeign.1 hforeign.2).1
  have hm := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.mode)
    hframe
  exact ⟨
    (fun h => hold.1 (hm.symm.trans h)),
    (fun h => hold.2.1 (hm.symm.trans h)),
    (fun h => hold.2.2 (hm.symm.trans h))⟩

theorem bankWindowOverlapRepairIncompleteForeignNoComparator {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hchanged :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val)
    (hnonroot :
      ((bankWindowRootBefore ring seed pre).1 e).pack.val ≠ 0)
    (hforeign : root ≠ e ∧
      root ≠ ring.rightNeighbor e)
    (hnot : ¬ Counter.Complete ring
      (bankWindowRootAfter ring seed pre e).1 root)
    (hmode : ((bankWindowRootAfter ring seed pre e).1 root).mode =
      .CWAIT)
    (o : RenewalBankOrigin n) (i : Fin n)
    (p : RenewalBankPayload n)
    (hroot : o.root = root)
    (hcomp : BankComparatorOriginWorker ring
      (bankWindowRootAfter ring seed pre e) o i p) : False := by
  have holdComp := bankWindowOverlapRepairComparatorBackward
    ring hn hbank seed pre e hchanged hnonroot o i p hcomp
  have hframe := (bankWindowExactOffPairFrame ring
    (bankWindowRootBefore ring seed pre)
    e root hforeign.1 hforeign.2).1
  have hmodeOld :
      ((bankWindowRootBefore ring seed pre).1 o.root).mode =
        .CWAIT := by
    rw [hroot]
    exact (congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.mode)
      hframe).symm.trans hmode
  have hcompleteOld := hJ.phaseComplete o i p
    holdComp hmodeOld
  have hcompletePost : Counter.Complete ring
      (bankWindowRootAfter ring seed pre e).1 root :=
    bankWindowOverlapForeignPrefixCannotBreak ring hn
      (bankWindowRootBefore ring seed pre) e root
      (compileAdvice (ceilLogTwo n)).b hforeign.2
      (Nat.le_refl _)
      (by rw [← hroot]; exact hcompleteOld)
  exact hnot hcompletePost

theorem bankWindowOverlapRepairForeignProtoStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n) (limit : Nat)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hforeign : root ≠ e ∧ root ≠ ring.rightNeighbor e)
    (hchanged :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val)
    (hnonroot :
      ((bankWindowRootBefore ring seed pre).1 e).pack.val ≠ 0)
    (hproto : BankWindowProtoRun ring
      (bankWindowRootAfter ring seed pre e) root limit) :
    BankWindowRootForeignProtoField ring
      (bankWindowRootAfter ring seed pre e) root limit := by
  by_cases hboundary :
      e = Counter.site ring root (limit + 1) ∨
      ring.rightNeighbor e =
        Counter.site ring root (limit + 1)
  · exact bankWindowOverlapProtoForeignInterior
      ring hn hbank seed pre e root limit hJ
      hboundary hproto
  · by_cases hproper :
        ∃ k : Nat, k ≤ limit ∧
          ring.rightNeighbor e = Counter.site ring root k
    · obtain ⟨t, ht, htarget⟩ := hproper
      have htpos : 1 ≤ t := by
        by_cases htzero : t = 0
        · rw [htzero] at htarget
          change ring.rightNeighbor e = root at htarget
          exact False.elim (hforeign.2 htarget.symm)
        · omega
      have hsource :
          e = Counter.site ring root (t - 1) := by
        have hnext : t - 1 + 1 = t := by omega
        apply Counter.resetTrialSitePredecessor ring root e (t - 1)
        rw [hnext]
        exact htarget
      have hsrcPos : 1 ≤ t - 1 := by
        by_cases htfirst : t = 1
        · have heq : e = root := by
            rw [htfirst] at hsource
            change e = Counter.site ring root 0 at hsource
            exact hsource
          exact False.elim (hforeign.1 heq.symm)
        · omega
      exact bankWindowOverlapRepairExtendedProtoForeign
        ring hn hbank seed pre e root (t - 1) limit hJ
        hsource hsrcPos (by omega) hchanged hproto
    · have hpackAvoid :
          ∀ t : Nat, t ≤ limit + 1 →
            Counter.site ring root t ≠ e ∧
            Counter.site ring root t ≠ ring.rightNeighbor e := by
        intro t ht
        constructor
        · intro hsrc
          have hsrcEq : e = Counter.site ring root t :=
            hsrc.symm
          by_cases hlast : t = limit + 1
          · apply hboundary
            exact Or.inl (by rw [hlast] at hsrcEq; exact hsrcEq)
          · have hsmall : t ≤ limit := by omega
            have hnext :
                ring.rightNeighbor e =
                  Counter.site ring root (t + 1) := by
              rw [hsrcEq]
              rfl
            by_cases hinside : t + 1 ≤ limit
            · exact hproper ⟨t + 1, hinside, hnext⟩
            · have heq : t = limit := by omega
              apply hboundary
              exact Or.inr (by rw [heq] at hnext; exact hnext)
        · intro hdst
          by_cases hlast : t = limit + 1
          · apply hboundary
            exact Or.inr
              (by rw [hlast] at hdst; exact hdst.symm)
          · exact hproper ⟨t, (by omega), hdst.symm⟩
      have hsegment :
          ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
            j.val + 1 ≤ limit →
            Counter.site ring root (j.val + 1) ≠ e ∧
            Counter.site ring root (j.val + 1) ≠
              ring.rightNeighbor e := by
        intro j hj
        exact hpackAvoid (j.val + 1) (by omega)
      exact bankWindowExactDisjointProtoStep ring
        (bankWindowRootBefore ring seed pre) e root limit
        hJ hforeign hpackAvoid hsegment hproto

theorem bankWindowOverlapRepairIncompleteForeignFieldBundle {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hnonroot :
      ((bankWindowRootBefore ring seed pre).1 e).pack.val ≠ 0)
    (hchanged :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val)
    (hforeign : root ≠ e ∧
      root ≠ ring.rightNeighbor e)
    (hincomplete : ¬ Counter.Complete ring
      (bankWindowRootAfter ring seed pre e).1 root) :
    (∀ limit : Nat,
      BankWindowProtoRun ring
        (bankWindowRootAfter ring seed pre e) root limit →
      BankWindowRootForeignProtoField ring
        (bankWindowRootAfter ring seed pre e) root limit) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowOrphanOwner ring
        (bankWindowRootAfter ring seed pre e) root j →
      BankWindowTainted
        (bankWindowRootAfter ring seed pre e)
        (Counter.site ring root (j.val + 1)) →
      ((bankWindowRootAfter ring seed pre e).1 root).mode = .RESET ∨
      (((bankWindowRootAfter ring seed pre e).1 root).mode =
        .RWAIT ∧
        ((bankWindowRootAfter ring seed pre e).2.sites
          root).controller = .waiting [])) ∧
    (∀ (o : RenewalBankOrigin n) (i : Fin n)
      (p : RenewalBankPayload n),
      o.root = root →
      BankComparatorOriginWorker ring
        (bankWindowRootAfter ring seed pre e) o i p →
      ((bankWindowRootAfter ring seed pre e).1 root).mode
        ≠ .ARMED ∧
      ((bankWindowRootAfter ring seed pre e).1 root).mode
        ≠ .CSTART ∧
      ((bankWindowRootAfter ring seed pre e).1 root).mode
        ≠ .IWAIT) ∧
    (∀ (o : RenewalBankOrigin n) (i : Fin n)
      (p : RenewalBankPayload n),
      o.root = root →
      BankComparatorOriginWorker ring
        (bankWindowRootAfter ring seed pre e) o i p →
      ((bankWindowRootAfter ring seed pre e).1 root).mode =
        .CWAIT → False) ∧
    (∀ (o : RenewalBankOrigin n) (i : Fin n)
      (p : RenewalBankPayload n),
      o.root = root →
      ((bankWindowRootAfter ring seed pre e).2.sites i).worker =
        .payload p →
      p.origin = some o →
      ((bankWindowRootAfter ring seed pre e).1 root).mode =
        .CWAIT →
      ((bankWindowRootAfter ring seed pre e).2.sites
        root).controller = .waiting [] → False) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro limit hproto
    exact bankWindowOverlapRepairForeignProtoStep ring hn hbank
      seed pre e root limit hJ hforeign hchanged hnonroot hproto
  · intro j howner htainted
    exact bankWindowOverlapRepairForeignOrphanStep ring hn hbank
      seed pre e root j hJ hforeign hchanged howner htainted
  · intro o i p hroot hcomp
    have hphase := bankWindowOverlapRepairForeignPhaseExcludes
      ring hn hbank seed pre e hJ hchanged hnonroot
      o i p
      ⟨(by rw [hroot]; exact hforeign.1),
       (by rw [hroot]; exact hforeign.2)⟩ hcomp
    rw [hroot] at hphase
    exact hphase
  · intro o i p hroot hcomp hmode
    exact bankWindowOverlapRepairIncompleteForeignNoComparator
      ring hn hbank seed pre e root hJ
      hchanged hnonroot hforeign hincomplete
      hmode o i p hroot hcomp
  · intro o i p hroot hworker horigin hmode hcontroller
    exact bankWindowOverlapRepairIncompleteForeignCwaitNoWorker
      ring hn hbank seed pre e root hJ hforeign
      hchanged hincomplete hmode hcontroller
      i p o hroot hworker horigin


end L3.BankWindow

namespace L3.BankWindow
open L3.BankHeadThreshold
open L3.BankCounterRows

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open L3.BankComparatorExclusive
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- A stable-PACK real BANK edge preserves the PACK field at every
site, including the selected responder. Consumer: the foreign proto
and orphan PACK antecedents in the stable nonroot rows. -/
theorem bankWindowOverlapStablePackFrame {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hstable :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val) :
    ∀ z : Fin n,
      ((bankWindowRootAfter ring seed pre e).1 z).pack.val =
        ((bankWindowRootBefore ring seed pre).1 z).pack.val := by
  intro z
  by_cases hz : z = ring.rightNeighbor e
  · subst z
    exact (bankWindowExactResponderPack ring
      (bankWindowRootBefore ring seed pre) e
      (clockNeighborDifferent ring
        (by omega : 2 ≤ n) e)).trans hstable
  · exact bankWindowClosureRepairNonresponderPackFixed
      ring (by omega : 2 ≤ n)
      (bankWindowRootBefore ring seed pre) e z hz

/-- The stable-PACK successor cannot create a foreign partial proto
prefix or change its first mismatch. Consumer: stable foreign
proto read-set classification. -/
theorem bankWindowOverlapStableProtoBackward {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n) (limit : Nat)
    (hstable :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val)
    (hproto : BankWindowProtoRun ring
      (bankWindowRootAfter ring seed pre e) root limit) :
    BankWindowProtoRun ring
      (bankWindowRootBefore ring seed pre) root limit := by
  have hp := bankWindowOverlapStablePackFrame
    ring hn seed pre e hstable
  refine ⟨hproto.1, ?_, ?_⟩
  · intro k hk
    exact (hp (Counter.site ring root k)).symm.trans
      (hproto.2.1 k hk)
  · intro hcorrect
    exact hproto.2.2
      ((hp (Counter.site ring root (limit + 1))).trans
        hcorrect)

/-- The named owner and its broken prefix are preserved as a PACK
fact even when its tainted worker is involved in a stable selected
pair. Consumer: stable foreign orphan collision analysis. -/
theorem bankWindowOverlapStableOrphanOwnerBackward {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (hstable :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val)
    (howner : BankWindowOrphanOwner ring
      (bankWindowRootAfter ring seed pre e) root j) :
    BankWindowOrphanOwner ring
      (bankWindowRootBefore ring seed pre) root j := by
  have hp := bankWindowOverlapStablePackFrame
    ring hn seed pre e hstable
  refine ⟨?_, ?_, ?_⟩
  · exact (hp root).symm.trans howner.1
  · exact (hp (Counter.site ring root (j.val + 1))).symm.trans
      howner.2.1
  · intro hprefix
    apply howner.2.2
    intro k hk
    exact (hp (Counter.site ring root k)).trans
      (hprefix k hk)

/-- All four foreign proto clauses on a real stable-PACK edge when
the selected pair avoids the proper digit segment. The first
mismatch itself may be incident: its PACK is still preserved.
Consumer: stable foreign PFX off-segment and mismatch-boundary rows. -/
theorem bankWindowOverlapStableForeignProtoOffSegment {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n) (limit : Nat)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hforeign : root ≠ e ∧
      root ≠ ring.rightNeighbor e)
    (hstable :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val)
    (hsegment :
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        j.val + 1 ≤ limit →
        Counter.site ring root (j.val + 1) ≠ e ∧
        Counter.site ring root (j.val + 1) ≠
          ring.rightNeighbor e)
    (hproto : BankWindowProtoRun ring
      (bankWindowRootAfter ring seed pre e) root limit) :
    BankWindowRootForeignProtoField ring
      (bankWindowRootAfter ring seed pre e) root limit := by
  have hpack : bankWindowReadPackPrefix ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) root
      (limit + 1) := by
    intro k _hk
    exact bankWindowOverlapStablePackFrame
      ring hn seed pre e hstable (Counter.site ring root k)
  have hroot := bankWindowExactOffPairAtomicReads ring
    (bankWindowRootBefore ring seed pre) e root
    hforeign.1 hforeign.2
  have hreads :
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        j.val + 1 ≤ limit →
        bankWindowReadTok
          (bankWindowRootBefore ring seed pre)
          (bankWindowRootAfter ring seed pre e)
          (Counter.site ring root (j.val + 1)) ∧
        bankWindowReadBit
          (bankWindowRootBefore ring seed pre)
          (bankWindowRootAfter ring seed pre e)
          (Counter.site ring root (j.val + 1)) ∧
        bankWindowReadWorker
          (bankWindowRootBefore ring seed pre)
          (bankWindowRootAfter ring seed pre e)
          (Counter.site ring root (j.val + 1)) := by
    intro j hj
    have hf := bankWindowExactOffPairAtomicReads ring
      (bankWindowRootBefore ring seed pre) e
      (Counter.site ring root (j.val + 1))
      (hsegment j hj).1 (hsegment j hj).2
    exact ⟨hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.2.1⟩
  exact bankWindowProtoReadTransport ring
    (bankWindowRootBefore ring seed pre)
    (bankWindowRootAfter ring seed pre e)
    root limit hJ
    ⟨hpack, hroot.2.1, hroot.2.2.2.2.2.2, hreads⟩
    hproto

/-- An orphan whose named digit is off both selected endpoints
has its entire consequence framed in a stable-PACK row, even
when the incomplete PACK prefix crosses the selected edge.
Consumer: foreign orphan off-pair stable row. -/
theorem bankWindowOverlapStableForeignOrphanOffPair {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hforeign : root ≠ e ∧
      root ≠ ring.rightNeighbor e)
    (hstable :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val)
    (hname : Counter.site ring root (j.val + 1) ≠ e ∧
      Counter.site ring root (j.val + 1) ≠
        ring.rightNeighbor e)
    (howner : BankWindowOrphanOwner ring
      (bankWindowRootAfter ring seed pre e) root j)
    (htainted : BankWindowTainted
      (bankWindowRootAfter ring seed pre e)
      (Counter.site ring root (j.val + 1))) :
    ((bankWindowRootAfter ring seed pre e).1 root).mode = .RESET ∨
    (((bankWindowRootAfter ring seed pre e).1 root).mode = .RWAIT ∧
      ((bankWindowRootAfter ring seed pre e).2.sites root).controller =
        .waiting []) := by
  have hpack : bankWindowReadPackPrefix ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) root
      (j.val + 1) := by
    intro k _hk
    exact bankWindowOverlapStablePackFrame
      ring hn seed pre e hstable (Counter.site ring root k)
  have hroot := bankWindowExactOffPairAtomicReads ring
    (bankWindowRootBefore ring seed pre) e root
    hforeign.1 hforeign.2
  have hnamed := bankWindowExactOffPairAtomicReads ring
    (bankWindowRootBefore ring seed pre) e
    (Counter.site ring root (j.val + 1)) hname.1 hname.2
  exact bankWindowOrphanReadTransport ring
    (bankWindowRootBefore ring seed pre)
    (bankWindowRootAfter ring seed pre e)
    root j hJ
    ⟨hpack, hroot.2.1, hroot.2.2.2.2.2.2,
      hnamed.2.2.2.2.2.1⟩
    howner htainted

theorem bankWindowOverlapIncomingBrokenMultiwindowFields {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hy : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = 0)
    (hpost : ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).pack.val ≠ 0) :
    (∀ k : Nat, 1 ≤ k →
      k ≤ (compileAdvice (ceilLogTwo n)).b →
      (bankWindowRootAfter ring seed pre e).1
        (Counter.site ring (ring.rightNeighbor e) k) =
        (bankWindowRootBefore ring seed pre).1
          (Counter.site ring (ring.rightNeighbor e) k) ∧
      (bankWindowRootAfter ring seed pre e).2.sites
        (Counter.site ring (ring.rightNeighbor e) k) =
        (bankWindowRootBefore ring seed pre).2.sites
          (Counter.site ring (ring.rightNeighbor e) k)) ∧
    ¬ BankWindowScope ring
      (bankWindowRootAfter ring seed pre e) (ring.rightNeighbor e) ∧
    (∀ limit : Nat,
      ¬ BankWindowProtoRun ring
        (bankWindowRootAfter ring seed pre e)
        (ring.rightNeighbor e) limit) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ¬ BankWindowOrphanOwner ring
        (bankWindowRootAfter ring seed pre e)
        (ring.rightNeighbor e) j) ∧
    (∀ (o : RenewalBankOrigin n) (i : Fin n)
      (p : RenewalBankPayload n),
      o.root = ring.rightNeighbor e →
      BankComparatorOriginWorker ring
        (bankWindowRootAfter ring seed pre e) o i p →
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode
        ≠ .ARMED ∧
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode
        ≠ .CSTART ∧
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode
        ≠ .IWAIT ∧
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode
        ≠ .CWAIT) := by
  have hroot := bankWindowOverlapIncomingRootJoint
    ring hn hbank seed pre e hJ hy
  have hbroken := bankWindowOverlapIncomingBrokenOwnerFields
    ring hn hbank seed pre e hJ hy hpost
  refine ⟨?_, hbroken.2.1, hbroken.2.2.1,
    hbroken.2.2.2, ?_⟩
  · intro k hk hb
    exact hroot.2.1 k hk hb
  · intro o i p horoot _hcomp
    have hm :
        ((bankWindowRootAfter ring seed pre e).1 o.root).mode =
          .RESET := by
      rw [horoot]
      exact hbroken.1
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      (intro hbad; rw [hm] at hbad; cases hbad)

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

/-- A broken PACK prefix remains broken after extending its named
aligned digit by one more aligned digit. The explicit Fin.val
conversion supplies the numerical bound omitted by omega in an
earlier proof attempt. Consumer: stable foreign orphan source collision. -/
theorem bankWindowOverlapStableOrphanNextOld {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e root : Fin n)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (hbelow : j.val + 1 < (compileAdvice (ceilLogTwo n)).b)
    (hsource : e = Counter.site ring root (j.val + 1))
    (howner : BankWindowOrphanOwner ring r root j)
    (htargetRole :
      (r.1 (ring.rightNeighbor e)).pack.val = j.val + 2) :
    BankWindowOrphanOwner ring r root
      (⟨j.val + 1, hbelow⟩ :
        Fin (compileAdvice (ceilLogTwo n)).b) := by
  have hnext :
      ring.rightNeighbor e =
        Counter.site ring root (j.val + 2) := by
    rw [hsource]
    rfl
  refine ⟨howner.1, ?_, ?_⟩
  · change
      (r.1 (Counter.site ring root (j.val + 2))).pack.val =
        j.val + 2
    rw [← hnext]
    exact htargetRole
  · intro hprefix
    apply howner.2.2
    intro k hk
    have hkForward : k ≤ j.val + 1 + 1 := by omega
    have hkFin :
        k ≤
          (⟨j.val + 1, hbelow⟩ :
            Fin (compileAdvice (ceilLogTwo n)).b).val + 1 := by
      change k ≤ j.val + 1 + 1
      exact hkForward
    exact hprefix k hkFin

/-- A real tainted responder lies in the digit band. A stable
PACK edge from a top-digit source would instead put that
responder at b+1. The explicit b+1 <= b intermediate
certificate replaces the failing raw omega call.
Consumer: stable foreign orphan top-source collision. -/
theorem bankWindowOverlapStableTopTaintedResponderImpossible {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (htop :
      ((bankWindowRootBefore ring seed pre).1 e).pack.val =
        (compileAdvice (ceilLogTwo n)).b)
    (hstable :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val)
    (htainted : BankWindowTainted
      (bankWindowRootBefore ring seed pre)
      (ring.rightNeighbor e)) : False := by
  have hband := bankWindowOverlapReachableTaintedInBand
    ring hn hbank seed pre (ring.rightNeighbor e) htainted
  have hnonzero :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val ≠ 0 :=
    Nat.ne_of_gt hband.1
  have hstep :
      packNext
        (compileAdvice (ceilLogTwo n)).b
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      (compileAdvice (ceilLogTwo n)).b + 1 := by
    simp [packNext, hnonzero]
  have hstableTop :
      packNext
        (compileAdvice (ceilLogTwo n)).b
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val := by
    have hs := hstable
    rw [htop] at hs
    exact hs
  have hsuccessor :
      (compileAdvice (ceilLogTwo n)).b + 1 =
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val :=
    hstep.symm.trans hstableTop
  have hcontradiction :
      (compileAdvice (ceilLogTwo n)).b + 1 ≤
        (compileAdvice (ceilLogTwo n)).b := by
    calc
      (compileAdvice (ceilLogTwo n)).b + 1 =
          ((bankWindowRootBefore ring seed pre).1
            (ring.rightNeighbor e)).pack.val := hsuccessor
      _ ≤ (compileAdvice (ceilLogTwo n)).b := hband.2
  omega

/-- The selected responder's named aligned PACK digit forces
the selected predecessor to carry the immediately preceding
PACK index on a stable edge. The first digit case is excluded
by the foreign-root geometry. Consumer: stable foreign orphan
selected-responder collision. -/
theorem bankWindowOverlapStableResponderPredecessorRole {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (hforeign : root ≠ e)
    (hresponder :
      ring.rightNeighbor e = Counter.site ring root (j.val + 1))
    (hstable :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val)
    (howner : BankWindowOrphanOwner ring
      (bankWindowRootAfter ring seed pre e) root j) :
    e = Counter.site ring root j.val ∧
    1 ≤ j.val ∧
    ((bankWindowRootBefore ring seed pre).1 e).pack.val =
      j.val := by
  have hprevious : e = Counter.site ring root j.val :=
    Counter.resetTrialSitePredecessor
      ring root e j.val hresponder
  have hjpositive : 1 ≤ j.val := by
    by_cases hz : j.val = 0
    · have hrootSite : e = root := by
        have hp := hprevious
        rw [hz] at hp
        change e = root at hp
        exact hp
      exact False.elim (hforeign hrootSite.symm)
    · omega
  have hpostResponder :
      ((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).pack.val = j.val + 1 :=
    (congrArg
      (fun z : Fin n =>
        ((bankWindowRootAfter ring seed pre e).1 z).pack.val)
      hresponder).trans howner.2.1
  have holdResponder :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val = j.val + 1 :=
    (bankWindowOverlapStablePackFrame
      ring hn seed pre e hstable
      (ring.rightNeighbor e)).symm.trans hpostResponder
  have hroleEq :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        (j.val + 1)
        (compileAdvice (ceilLogTwo n)).b = j.val + 1 := by
    have hs := hstable
    rw [holdResponder] at hs
    exact hs
  have hrole :
      ((bankWindowRootBefore ring seed pre).1 e).pack.val =
        j.val := by
    by_cases hlow :
        ((bankWindowRootBefore ring seed pre).1 e).pack.val <
          (compileAdvice (ceilLogTwo n)).b
    · have hforward :
          packNext
            ((bankWindowRootBefore ring seed pre).1 e).pack.val
            (j.val + 1) (compileAdvice (ceilLogTwo n)).b =
          ((bankWindowRootBefore ring seed pre).1 e).pack.val + 1 := by
        simp [packNext, hlow]
      rw [hforward] at hroleEq
      omega
    · by_cases htop :
          ((bankWindowRootBefore ring seed pre).1 e).pack.val =
            (compileAdvice (ceilLogTwo n)).b
      · have hnonzero : j.val + 1 ≠ 0 := by omega
        have htopStep :
            packNext (compileAdvice (ceilLogTwo n)).b
              (j.val + 1) (compileAdvice (ceilLogTwo n)).b =
            (compileAdvice (ceilLogTwo n)).b + 1 := by
          simp [packNext, hnonzero]
        rw [htop, htopStep] at hroleEq
        have hjbound := j.isLt
        omega
      · have hspacer :
            packNext
              ((bankWindowRootBefore ring seed pre).1 e).pack.val
              (j.val + 1) (compileAdvice (ceilLogTwo n)).b = 0 := by
          simp [packNext, hlow, htop]
        rw [hspacer] at hroleEq
        omega
  exact ⟨hprevious, hjpositive, hrole⟩

/-- If an old named orphan has an aligned selected predecessor,
then the preceding digit inherits the broken-prefix witness.
The Fin predecessor bound is changed to a natural-index bound
before arithmetic. Consumer: stable responder orphan taint
pulled back to the old source. -/
theorem bankWindowOverlapStableOrphanPreviousOld {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e root : Fin n)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (hprevious : e = Counter.site ring root j.val)
    (hjpositive : 1 ≤ j.val)
    (howner : BankWindowOrphanOwner ring r root j)
    (hsourceRole : (r.1 e).pack.val = j.val) :
    ∃ previous : Fin (compileAdvice (ceilLogTwo n)).b,
      previous.val + 1 = j.val ∧
      BankWindowOrphanOwner ring r root previous := by
  have hindexBound :
      j.val - 1 < (compileAdvice (ceilLogTwo n)).b := by
    have hjbound := j.isLt
    omega
  refine ⟨⟨j.val - 1, hindexBound⟩, ?_, ?_⟩
  · change j.val - 1 + 1 = j.val
    omega
  · refine ⟨howner.1, ?_, ?_⟩
    · change
        (r.1 (Counter.site ring root (j.val - 1 + 1))).pack.val =
          j.val - 1 + 1
      have hindex : j.val - 1 + 1 = j.val := by omega
      rw [hindex, ← hprevious]
      exact hsourceRole
    · intro hprefix
      apply howner.2.2
      intro k hk
      by_cases hlast : k = j.val + 1
      · rw [hlast]
        exact howner.2.1
      · have hkbelow : k ≤ j.val := by omega
        have hkPrevious :
            k ≤ (⟨j.val - 1, hindexBound⟩ :
              Fin (compileAdvice (ceilLogTwo n)).b).val + 1 := by
          change k ≤ j.val - 1 + 1
          omega
        exact hprefix k hkPrevious

theorem bankWindowOverlapStableForeignOrphanOnSource {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hforeign : root ≠ e ∧
      root ≠ ring.rightNeighbor e)
    (hsource : e = Counter.site ring root (j.val + 1))
    (hstable :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val)
    (howner : BankWindowOrphanOwner ring
      (bankWindowRootAfter ring seed pre e) root j)
    (htainted : BankWindowTainted
      (bankWindowRootAfter ring seed pre e)
      (Counter.site ring root (j.val + 1))) :
    ((bankWindowRootAfter ring seed pre e).1 root).mode = .RESET ∨
    (((bankWindowRootAfter ring seed pre e).1 root).mode = .RWAIT ∧
      ((bankWindowRootAfter ring seed pre e).2.sites root).controller =
        .waiting []) := by
  have holdOwner := bankWindowOverlapStableOrphanOwnerBackward
    ring hn seed pre e root j hstable howner
  have hrootFrame := bankWindowExactOffPairFrame ring
    (bankWindowRootBefore ring seed pre) e root
    hforeign.1 hforeign.2
  have hmodeFrame := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.mode)
    hrootFrame.1
  have hcontrollerFrame := congrArg
    (fun s : RenewalBankSite n => s.controller)
    hrootFrame.2
  have hlift :
      ((bankWindowRootBefore ring seed pre).1 root).mode = .RESET ∨
      (((bankWindowRootBefore ring seed pre).1 root).mode = .RWAIT ∧
        ((bankWindowRootBefore ring seed pre).2.sites root).controller =
          .waiting []) →
      ((bankWindowRootAfter ring seed pre e).1 root).mode = .RESET ∨
      (((bankWindowRootAfter ring seed pre e).1 root).mode = .RWAIT ∧
        ((bankWindowRootAfter ring seed pre e).2.sites root).controller =
          .waiting []) := by
    intro h
    rcases h with hr | ⟨hr, hc⟩
    · exact Or.inl (hmodeFrame.trans hr)
    · exact Or.inr ⟨hmodeFrame.trans hr,
        hcontrollerFrame.trans hc⟩
  have hpostSource :
      ((bankWindowRootAfter ring seed pre e).1 e).pack.val =
        j.val + 1 := by
    exact (congrArg
      (fun z : Fin n =>
        ((bankWindowRootAfter ring seed pre e).1 z).pack.val)
      hsource).trans howner.2.1
  have holdSourceRole :
      ((bankWindowRootBefore ring seed pre).1 e).pack.val =
        j.val + 1 :=
    (bankWindowOverlapStablePackFrame
      ring hn seed pre e hstable e).symm.trans hpostSource
  have hnonroot :
      ((bankWindowRootBefore ring seed pre).1 e).pack.val ≠ 0 := by
    rw [holdSourceRole]
    omega
  have hpostTaint : BankWindowTainted
      (bankWindowRootAfter ring seed pre e) e := by
    simpa only [← hsource] using htainted
  rcases bankWindowOverlapNonrootPairTaintPreimage
      ring (by omega : 2 ≤ n)
      (bankWindowRootBefore ring seed pre)
      e e hnonroot (Or.inl rfl) hpostTaint with
      holdSourceTaint | holdTargetTaint
  · have hnamedOld : BankWindowTainted
        (bankWindowRootBefore ring seed pre)
        (Counter.site ring root (j.val + 1)) := by
      rw [← hsource]
      exact holdSourceTaint
    exact hlift (hJ.orphan root j holdOwner hnamedOld)
  · by_cases hbelow :
        j.val + 1 < (compileAdvice (ceilLogTwo n)).b
    · have hnextSite :
          ring.rightNeighbor e =
            Counter.site ring root (j.val + 2) := by
        rw [hsource]
        rfl
      have hnextPack :
          packNext (j.val + 1)
            ((bankWindowRootBefore ring seed pre).1
              (ring.rightNeighbor e)).pack.val
            (compileAdvice (ceilLogTwo n)).b =
            j.val + 2 := by
        simp [packNext, hbelow]
      have htargetRole :
          ((bankWindowRootBefore ring seed pre).1
            (ring.rightNeighbor e)).pack.val = j.val + 2 := by
        have hs := hstable
        rw [holdSourceRole] at hs
        exact hs.symm.trans hnextPack
      have hnextOwner : BankWindowOrphanOwner ring
          (bankWindowRootBefore ring seed pre) root
          (⟨j.val + 1, hbelow⟩ :
            Fin (compileAdvice (ceilLogTwo n)).b) :=
        bankWindowOverlapStableOrphanNextOld
          ring (bankWindowRootBefore ring seed pre)
          e root j hbelow hsource holdOwner htargetRole
      have hnextTaint : BankWindowTainted
          (bankWindowRootBefore ring seed pre)
          (Counter.site ring root (j.val + 2)) := by
        rw [← hnextSite]
        exact holdTargetTaint
      exact hlift (hJ.orphan root
        (⟨j.val + 1, hbelow⟩ :
          Fin (compileAdvice (ceilLogTwo n)).b)
        hnextOwner hnextTaint)
    · have htop :
          j.val + 1 = (compileAdvice (ceilLogTwo n)).b := by
        have hj := j.isLt
        omega
      have hsourceTop :
          ((bankWindowRootBefore ring seed pre).1 e).pack.val =
            (compileAdvice (ceilLogTwo n)).b :=
        holdSourceRole.trans htop
      exact False.elim
        (bankWindowOverlapStableTopTaintedResponderImpossible
          ring hn hbank seed pre e
          hsourceTop hstable holdTargetTaint)


/-- Complete stable PACK selected-responder orphan collision. A
POST tainted responder has an OLD tainted source or responder.
The former belongs to the previous old orphan prefix; the latter
to the same named old orphan. Consumer: J.orphan, stable nonroot
RR/RL/IR/CR responder collision. -/
theorem bankWindowOverlapStableForeignOrphanOnResponder {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hforeign : root ≠ e ∧ root ≠ ring.rightNeighbor e)
    (hresponder :
      ring.rightNeighbor e = Counter.site ring root (j.val + 1))
    (hstable :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val)
    (howner : BankWindowOrphanOwner ring
      (bankWindowRootAfter ring seed pre e) root j)
    (htainted : BankWindowTainted
      (bankWindowRootAfter ring seed pre e)
      (Counter.site ring root (j.val + 1))) :
    ((bankWindowRootAfter ring seed pre e).1 root).mode = .RESET ∨
    (((bankWindowRootAfter ring seed pre e).1 root).mode = .RWAIT ∧
      ((bankWindowRootAfter ring seed pre e).2.sites root).controller =
        .waiting []) := by
  have hprevious := bankWindowOverlapStableResponderPredecessorRole
    ring hn seed pre e root j hforeign.1 hresponder hstable howner
  have holdOwner := bankWindowOverlapStableOrphanOwnerBackward
    ring hn seed pre e root j hstable howner
  have hrootFrame := bankWindowExactOffPairFrame ring
    (bankWindowRootBefore ring seed pre) e root
    hforeign.1 hforeign.2
  have hmodeFrame := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.mode)
    hrootFrame.1
  have hcontrollerFrame := congrArg
    (fun s : RenewalBankSite n => s.controller)
    hrootFrame.2
  have hlift :
      ((bankWindowRootBefore ring seed pre).1 root).mode = .RESET ∨
      (((bankWindowRootBefore ring seed pre).1 root).mode = .RWAIT ∧
        ((bankWindowRootBefore ring seed pre).2.sites root).controller =
          .waiting []) →
      ((bankWindowRootAfter ring seed pre e).1 root).mode = .RESET ∨
      (((bankWindowRootAfter ring seed pre e).1 root).mode = .RWAIT ∧
        ((bankWindowRootAfter ring seed pre e).2.sites root).controller =
          .waiting []) := by
    intro h
    rcases h with hreset | ⟨hwait, hc⟩
    · exact Or.inl (hmodeFrame.trans hreset)
    · exact Or.inr ⟨hmodeFrame.trans hwait,
        hcontrollerFrame.trans hc⟩
  have hsourceNonzero :
      ((bankWindowRootBefore ring seed pre).1 e).pack.val ≠ 0 := by
    rw [hprevious.2.2]
    omega
  have hpostResponderTaint : BankWindowTainted
      (bankWindowRootAfter ring seed pre e)
      (ring.rightNeighbor e) := by
    simpa only [← hresponder] using htainted
  rcases bankWindowOverlapNonrootPairTaintPreimage
      ring (by omega : 2 ≤ n)
      (bankWindowRootBefore ring seed pre) e
      (ring.rightNeighbor e) hsourceNonzero
      (Or.inr rfl) hpostResponderTaint with
      holdSourceTaint | holdResponderTaint
  · obtain ⟨previous, hindex, hownerPrevious⟩ :=
      bankWindowOverlapStableOrphanPreviousOld
        ring (bankWindowRootBefore ring seed pre)
        e root j hprevious.1 hprevious.2.1
        holdOwner hprevious.2.2
    have hsite :
        Counter.site ring root (previous.val + 1) = e := by
      rw [hindex]
      exact hprevious.1.symm
    have htaintPrevious : BankWindowTainted
        (bankWindowRootBefore ring seed pre)
        (Counter.site ring root (previous.val + 1)) := by
      rw [hsite]
      exact holdSourceTaint
    exact hlift (hJ.orphan root previous
      hownerPrevious htaintPrevious)
  · have htaintOld : BankWindowTainted
        (bankWindowRootBefore ring seed pre)
        (Counter.site ring root (j.val + 1)) := by
      rw [← hresponder]
      exact holdResponderTaint
    exact hlift (hJ.orphan root j holdOwner htaintOld)

/-- All stable-PACK foreign orphan locations, including the
selected source, selected responder, and fully off-pair named
digit. Consumer: complete foreign J.orphan field in nonroot
stable-PACK RR/RL/IR/CR rows. -/
theorem bankWindowOverlapStableForeignOrphanStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hforeign : root ≠ e ∧ root ≠ ring.rightNeighbor e)
    (hstable :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val)
    (howner : BankWindowOrphanOwner ring
      (bankWindowRootAfter ring seed pre e) root j)
    (htainted : BankWindowTainted
      (bankWindowRootAfter ring seed pre e)
      (Counter.site ring root (j.val + 1))) :
    ((bankWindowRootAfter ring seed pre e).1 root).mode = .RESET ∨
    (((bankWindowRootAfter ring seed pre e).1 root).mode = .RWAIT ∧
      ((bankWindowRootAfter ring seed pre e).2.sites root).controller =
        .waiting []) := by
  by_cases hsource : Counter.site ring root (j.val + 1) = e
  · exact bankWindowOverlapStableForeignOrphanOnSource
      ring hn hbank seed pre e root j hJ
      hforeign hsource.symm hstable howner htainted
  · by_cases hresponder :
        Counter.site ring root (j.val + 1) = ring.rightNeighbor e
    · exact bankWindowOverlapStableForeignOrphanOnResponder
        ring hn hbank seed pre e root j hJ
        hforeign hresponder.symm hstable howner htainted
    · exact bankWindowOverlapStableForeignOrphanOffPair
        ring hn seed pre e root j hJ hforeign hstable
        ⟨hsource, hresponder⟩ howner htainted


theorem bankWindowOverlapForeignComparisonOffWindow {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (o : RenewalBankOrigin n) (i : Fin n)
    (p : RenewalBankPayload n)
    (hforeign : o.root ≠ e ∧
      o.root ≠ ring.rightNeighbor e)
    (hfree : i ≠ e ∧ i ≠ ring.rightNeighbor e)
    (houtside : Counter.OutsideSites (q := ceilLogTwo n)
      ring o.root e)
    (hworker : BankComparatorOriginWorker ring
      (bankWindowRootAfter ring seed pre e) o i p)
    (hmode : ((bankWindowRootAfter ring seed pre e).1
      o.root).mode = .CWAIT) :
    Counter.Complete ring
      (bankWindowRootAfter ring seed pre e).1 o.root ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankTrialLiveComparisonToken
        ((bankWindowRootAfter ring seed pre e).1
          (Counter.site ring o.root (j.val + 1))).tok →
      Counter.site ring o.root (j.val + 1) = i) ∧
    ((((bankWindowRootAfter ring seed pre e).1 i).tok = .CR1 →
      bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        ((bankWindowRootAfter ring seed pre e).1 i).pack.val) ∧
     (((bankWindowRootAfter ring seed pre e).1 i).tok = .CR0 →
      ¬ bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        ((bankWindowRootAfter ring seed pre e).1 i).pack.val) ∧
     (((bankWindowRootAfter ring seed pre e).1 i).tok = .CL1 →
      bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        (compileAdvice (ceilLogTwo n)).b) ∧
     (((bankWindowRootAfter ring seed pre e).1 i).tok = .CL0 →
      ¬ bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        (compileAdvice (ceilLogTwo n)).b)) := by
  have hf := bankWindowExactOffPairAtomicReads ring
    (bankWindowRootBefore ring seed pre) e i hfree.1 hfree.2
  have hroot := bankWindowExactOffPairAtomicReads ring
    (bankWindowRootBefore ring seed pre) e o.root
    hforeign.1 hforeign.2
  have hworkerOld : BankComparatorOriginWorker ring
      (bankWindowRootBefore ring seed pre) o i p :=
    ⟨hf.2.2.2.2.2.1.symm.trans hworker.1,
      hworker.2.1,
      by
        have htokenPost := hworker.2.2
        rw [hf.2.2.1] at htokenPost
        exact htokenPost⟩
  have hmodeOld :
      ((bankWindowRootBefore ring seed pre).1 o.root).mode =
        .CWAIT :=
    hroot.2.1.symm.trans hmode
  have hcompleteOld := hJ.phaseComplete o i p
    hworkerOld hmodeOld
  have hcomplete :
      Counter.Complete ring
        (bankWindowRootAfter ring seed pre e).1 o.root :=
    (bankWindowClosureOffWindowAlignedPrefix ring
      (bankWindowRootBefore ring seed pre) o.root e
      houtside (compileAdvice (ceilLogTwo n)).b
      (Nat.le_refl _)).mpr hcompleteOld
  have htoks : bankWindowReadDigitTokens ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) o.root := by
    intro j
    have ht := (bankWindowExactOffWindowFrame ring
      (bankWindowRootBefore ring seed pre) o.root e
      houtside (j.val + 1) (by have hj := j.isLt; omega)).1
    exact congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok) ht
  have hbits : bankWindowReadDigitBits ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) o.root := by
    intro j
    have ht := (bankWindowExactOffWindowFrame ring
      (bankWindowRootBefore ring seed pre) o.root e
      houtside (j.val + 1) (by have hj := j.isLt; omega)).1
    exact congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.bit) ht
  have hphaseReads : bankWindowPhaseExcludesReadSet
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) o i p :=
    ⟨hf.2.2.1, hf.2.2.2.2.2.1, hroot.2.1⟩
  have hunique := bankWindowPhaseUniqueReadTransport ring
    (bankWindowRootBefore ring seed pre)
    (bankWindowRootAfter ring seed pre e)
    o i p hJ ⟨hphaseReads, htoks⟩ hworker hmode
  have hflags := bankWindowPhaseFlagsReadTransport ring
    (bankWindowRootBefore ring seed pre)
    (bankWindowRootAfter ring seed pre e)
    o i p hJ ⟨hphaseReads, hf.1, hbits⟩
    hworker hmode
  exact ⟨hcomplete, hunique, hflags⟩


/-- Actual incoming-root RWAIT/IWAIT/CWAIT continuation or expiry:
long-lease rows keep the owner mode/controller exactly, and
short-lease rows RESET the owner. In both outcomes the full
proto and orphan fields hold; no post-step J is assumed.
Consumer: incoming-root multiwindow stable-responder branch. -/
theorem bankWindowOverlapIncomingWaitMultiwindowFields {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hy : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = 0)
    (hpost : ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).pack.val = 0)
    (hg : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).grant = false)
    (hm :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).mode = .RWAIT ∨
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).mode = .IWAIT ∨
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).mode = .CWAIT) :
    (∀ limit : Nat,
      BankWindowProtoRun ring
        (bankWindowRootAfter ring seed pre e)
        (ring.rightNeighbor e) limit →
      BankWindowRootForeignProtoField ring
        (bankWindowRootAfter ring seed pre e)
        (ring.rightNeighbor e) limit) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowOrphanOwner ring
        (bankWindowRootAfter ring seed pre e)
        (ring.rightNeighbor e) j →
      BankWindowTainted
        (bankWindowRootAfter ring seed pre e)
        (Counter.site ring (ring.rightNeighbor e) (j.val + 1)) →
      ((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).mode = .RESET ∨
      (((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).mode = .RWAIT ∧
        ((bankWindowRootAfter ring seed pre e).2.sites
          (ring.rightNeighbor e)).controller = .waiting [])) := by
  have hframe := bankWindowExactFrameStep
    ring hn hbank seed pre e hJ
  have hrow :
      (1 < ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).lease.val →
      ((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).mode =
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).mode ∧
      ((bankWindowRootAfter ring seed pre e).2.sites
        (ring.rightNeighbor e)).controller =
      ((bankWindowRootBefore ring seed pre).2.sites
        (ring.rightNeighbor e)).controller) ∧
      (((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).lease.val ≤ 1 →
      ((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).mode = .RESET ∧
      ((bankWindowRootAfter ring seed pre e).2.sites
        (ring.rightNeighbor e)).controller = .empty) := by
    rcases hm with hr | hi | hc
    · have hcore := bankWindowIncomingRootCoreStep
        ring hn hbank seed pre e hJ hy
      have hwait := hcore.2.2.2.2.2 hpost hg hr
      constructor
      · intro hl
        have hk := hwait.1 hl
        exact ⟨hk.1.trans hr.symm, hk.2⟩
      · exact hwait.2
    · have hwait := bankWindowIncomingIwaitExact
        ring hn hbank seed pre e hJ hy hpost hg hi
      constructor
      · intro hl
        have hk := hwait.1 hl
        exact ⟨hk.1.trans hi.symm, hk.2⟩
      · exact hwait.2
    · have hwait := bankWindowIncomingCwaitExact
        ring hn hbank seed pre e hJ hy hpost hg hc
      constructor
      · intro hl
        have hk := hwait.1 hl
        exact ⟨hk.1.trans hc.symm, hk.2⟩
      · exact hwait.2
  by_cases hlong :
      1 < ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).lease.val
  · have hkeep := hrow.1 hlong
    exact bankWindowOverlapIncomingStableOwnerFields
      ring hbank (bankWindowRootBefore ring seed pre)
      hJ (ring.rightNeighbor e) e rfl hy hpost
      hkeep.1 hkeep.2
  · have hshort :
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).lease.val ≤ 1 := by
      omega
    have hreset := hrow.2 hshort
    have hfields := bankWindowIncomingResetOwnerFields
      ring (bankWindowRootBefore ring seed pre)
      (ring.rightNeighbor e) e hpost hreset.1 hframe
    exact ⟨hfields.2.2.1, hfields.2.2.2⟩


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

/-- On an authentic incoming PACK-zero edge whose responder remains
PACK zero, the source cannot itself have PACK zero. Consumer: incoming
grant, ARMED, and CSTART physical row analysis. -/
theorem bankWindowOverlapIncomingSourceNonzero {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 0)
    (hpost :
      ((renewalBankNext ring r e).1
        (ring.rightNeighbor e)).pack.val = 0) :
    (r.1 e).pack.val ≠ 0 := by
  have hstep := bankWindowExactResponderPack ring r e
    (clockNeighborDifferent ring (by omega : 2 ≤ n) e)
  have heq :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b = 0 :=
    hstep.symm.trans hpost
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  intro hz
  rw [hz, hy] at heq
  simp [packNext, hb] at heq

/-- Literal BANK physical responder modes for the nonroot-to-zero
edge: granted and ARMED roots reset, while an ungranted CSTART
root retains its mode. Consumer: incoming owner field bundles. -/
theorem bankWindowOverlapIncomingZeroBankModes
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : x.role ≠ 0) (hy : y.role = 0) :
    ((y.grant = true ∨ y.mode = .ARMED) →
      (bankPair x y 0 b theta).2.mode = .RESET) ∧
    (y.grant = false → y.mode = .CSTART →
      (bankPair x y 0 b theta).2.mode = .CSTART) := by
  constructor
  · intro hgate
    rcases hgate with hgrant | harmed
    · simp [bankPair, hx, hy, hgrant, isWaitMode] <;>
        repeat (first | rfl | split)
    · cases hg : y.grant with
      | false =>
          simp [bankPair, hx, hy, hg, harmed, isWaitMode] <;>
            repeat (first | rfl | split)
      | true =>
          simp [bankPair, hx, hy, hg, isWaitMode] <;>
            repeat (first | rfl | split)
  · intro hgrant hstart
    simp [bankPair, hx, hy, hgrant, hstart, isWaitMode] <;>
      repeat (first | rfl | split)

/-- The actual masked BANK edge has the literal grant/ARMED reset
and ungranted CSTART survival modes, without any POST-J premise.
Consumer: incoming grant and CSTART proto/orphan bundles. -/
theorem bankWindowOverlapIncomingZeroPhysicalModes {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 0)
    (hpost : ((renewalBankNext ring r e).1
      (ring.rightNeighbor e)).pack.val = 0) :
    (((r.1 (ring.rightNeighbor e)).grant = true ∨
      (r.1 (ring.rightNeighbor e)).mode = .ARMED) →
      ((renewalBankNext ring r e).1
        (ring.rightNeighbor e)).mode = .RESET) ∧
    ((r.1 (ring.rightNeighbor e)).grant = false →
      (r.1 (ring.rightNeighbor e)).mode = .CSTART →
      ((renewalBankNext ring r e).1
        (ring.rightNeighbor e)).mode = .CSTART) := by
  have hx := bankWindowOverlapIncomingSourceNonzero
    ring hn r e hy hpost
  have hstep := bankWindowExactResponderPack ring r e
    (clockNeighborDifferent ring (by omega : 2 ≤ n) e)
  have hpack :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b = 0 :=
    hstep.symm.trans hpost
  have htriple := (bankWindowClosureSelectedBankTrip
    ring hn hbank r e).2
  have hmode := congrArg
    (fun t : Mode × Bool × BTok => t.1) htriple
  change ((renewalBankNext ring r e).1
    (ring.rightNeighbor e)).mode =
    (Counter.resetBankOld
      (r.1 e) (r.1 (ring.rightNeighbor e))).2.mode at hmode
  unfold Counter.resetBankOld at hmode
  rw [hpack] at hmode
  have hsymbol := bankWindowOverlapIncomingZeroBankModes
    (bankCell (r.1 e) (r.1 e).pack.val)
    (bankCell (r.1 (ring.rightNeighbor e))
      (r.1 (ring.rightNeighbor e)).pack.val)
    (compileAdvice (ceilLogTwo n)).b
    (compileAdvice (ceilLogTwo n)).theta
    (by change (r.1 e).pack.val ≠ 0; exact hx)
    (by change (r.1 (ring.rightNeighbor e)).pack.val = 0; exact hy)
  constructor
  · intro hgate
    have hcellGate :
        (bankCell (r.1 (ring.rightNeighbor e))
          (r.1 (ring.rightNeighbor e)).pack.val).grant = true ∨
        (bankCell (r.1 (ring.rightNeighbor e))
          (r.1 (ring.rightNeighbor e)).pack.val).mode = .ARMED := by
      change (r.1 (ring.rightNeighbor e)).grant = true ∨
        (r.1 (ring.rightNeighbor e)).mode = .ARMED
      exact hgate
    exact hmode.trans (hsymbol.1 hcellGate)
  · intro hgrant hstart
    have hcGrant :
        (bankCell (r.1 (ring.rightNeighbor e))
          (r.1 (ring.rightNeighbor e)).pack.val).grant = false := by
      change (r.1 (ring.rightNeighbor e)).grant = false
      exact hgrant
    have hcStart :
        (bankCell (r.1 (ring.rightNeighbor e))
          (r.1 (ring.rightNeighbor e)).pack.val).mode = .CSTART := by
      change (r.1 (ring.rightNeighbor e)).mode = .CSTART
      exact hstart
    exact hmode.trans (hsymbol.2 hcGrant hcStart)

/-- A true old incoming grant or an ARMED incoming root exits
physically to RESET, and the actual post-frame rules out any
controller, proto witness requiring genuine active data, or
tainted orphan in an unrestricted phase. Consumer: IN/B0 grant
and ARMED owner-field cases, including PACK-changing exits. -/
theorem bankWindowOverlapIncomingGrantOrArmedOwnerFields {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hy : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = 0)
    (hgate :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).grant = true ∨
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).mode = .ARMED) :
    ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).mode = .RESET ∧
    ((bankWindowRootAfter ring seed pre e).2.sites
      (ring.rightNeighbor e)).controller = .empty ∧
    (∀ limit : Nat,
      BankWindowProtoRun ring
        (bankWindowRootAfter ring seed pre e)
        (ring.rightNeighbor e) limit →
      BankWindowRootForeignProtoField ring
        (bankWindowRootAfter ring seed pre e)
        (ring.rightNeighbor e) limit) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowOrphanOwner ring
        (bankWindowRootAfter ring seed pre e)
        (ring.rightNeighbor e) j →
      BankWindowTainted (bankWindowRootAfter ring seed pre e)
        (Counter.site ring (ring.rightNeighbor e) (j.val + 1)) →
      ((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).mode = .RESET ∨
      (((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).mode = .RWAIT ∧
        ((bankWindowRootAfter ring seed pre e).2.sites
          (ring.rightNeighbor e)).controller = .waiting [])) := by
  have hframe := bankWindowExactFrameStep
    ring hn hbank seed pre e hJ
  by_cases hpost :
      ((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).pack.val = 0
  · have hmode := (bankWindowOverlapIncomingZeroPhysicalModes
      ring hn hbank (bankWindowRootBefore ring seed pre)
      e hy hpost).1 hgate
    have hreset := bankWindowIncomingResetOwnerFields
      ring (bankWindowRootBefore ring seed pre)
      (ring.rightNeighbor e) e hpost hmode hframe
    exact ⟨hmode, hreset.1, hreset.2.2.1, hreset.2.2.2⟩
  · have hbroken := bankWindowOverlapIncomingBrokenOwnerFields
      ring hn hbank seed pre e hJ hy hpost
    have hcontroller :
        ((bankWindowRootAfter ring seed pre e).2.sites
          (ring.rightNeighbor e)).controller = .empty := by
      have hshape := (hframe (ring.rightNeighbor e)).1
      simpa [bankInFlightControllerShape, hpost] using hshape
    refine ⟨hbroken.1, hcontroller, ?_, ?_⟩
    · intro limit hp
      exact False.elim (hbroken.2.2.1 limit hp)
    · intro j ho _ht
      exact False.elim (hbroken.2.2.2 j ho)

/-- A continuing incoming CSTART owner has the same controller
as before its nonroot-predecessor encounter. The post-shape
excludes an erased active controller; CSTART is not a waiting
mode and therefore its wait-slot operation is the identity.
Consumer: CSTART incoming proto/orphan owner survival. -/
theorem bankWindowOverlapIncomingCstartControllerKeep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hy : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = 0)
    (hpost : ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).pack.val = 0)
    (hgrant : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).grant = false)
    (hstart : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).mode = .CSTART) :
    ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).mode = .CSTART ∧
    ((bankWindowRootAfter ring seed pre e).2.sites
      (ring.rightNeighbor e)).controller =
      ((bankWindowRootBefore ring seed pre).2.sites
        (ring.rightNeighbor e)).controller := by
  have hmode := (bankWindowOverlapIncomingZeroPhysicalModes
    ring hn hbank (bankWindowRootBefore ring seed pre)
    e hy hpost).2 hgrant hstart
  have hframe := bankWindowExactFrameStep
    ring hn hbank seed pre e hJ
  have hactive :
      ∃ p : RenewalBankPayload n,
        ((bankWindowRootAfter ring seed pre e).2.sites
          (ring.rightNeighbor e)).controller = .active p := by
    have hshape := (hframe (ring.rightNeighbor e)).1
    simpa [bankInFlightControllerShape, hpost, hmode] using hshape
  have hnotEmpty :
      ((bankWindowRootAfter ring seed pre e).2.sites
        (ring.rightNeighbor e)).controller ≠ .empty := by
    intro he
    obtain ⟨p, hp⟩ := hactive
    rw [he] at hp
    cases hp
  have hx := bankWindowOverlapIncomingSourceNonzero
    ring hn (bankWindowRootBefore ring seed pre) e hy hpost
  have hpair := (rbBankNonrootControllerPair
    (compileAdvice (ceilLogTwo n))
    (bankWindowRootBefore ring seed pre).2
    e (ring.rightNeighbor e)
    ((bankWindowRootBefore ring seed pre).1 e)
    ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)) hx).2
  have hghost := congrArg
    (fun s : RenewalBankSite n => s.controller)
    (rbReferenceSelectedPairFrame ring
      (by omega : 2 ≤ n)
      (bankWindowRootBefore ring seed pre) e).2.2.2
  change
    ((bankWindowRootAfter ring seed pre e).2.sites
      (ring.rightNeighbor e)).controller =
    (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
      (bankWindowRootBefore ring seed pre).2
      e (ring.rightNeighbor e)
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).2.controller at hghost
  have hslot :
      renewalBankWaitSlot
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).mode
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).lease.val
        ((bankWindowRootBefore ring seed pre).2.sites
          (ring.rightNeighbor e)).controller =
        ((bankWindowRootBefore ring seed pre).2.sites
          (ring.rightNeighbor e)).controller := by
    simp [renewalBankWaitSlot, hstart, isWaitMode]
  constructor
  · exact hmode
  · rcases hpair with hempty | hwait
    · have he := hghost.trans hempty
      exact False.elim (hnotEmpty he)
    · exact hghost.trans (hwait.trans hslot)

/-- Both PACK-changing exits and ungranted continuing CSTART
incoming rows preserve the exact proto and orphan fields.
Consumer: IN/B0 CSTART item of the multiwindow assembly. -/
theorem bankWindowOverlapIncomingCstartOwnerFields {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hy : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = 0)
    (hgrant : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).grant = false)
    (hstart : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).mode = .CSTART) :
    (∀ limit : Nat,
      BankWindowProtoRun ring
        (bankWindowRootAfter ring seed pre e)
        (ring.rightNeighbor e) limit →
      BankWindowRootForeignProtoField ring
        (bankWindowRootAfter ring seed pre e)
        (ring.rightNeighbor e) limit) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowOrphanOwner ring
        (bankWindowRootAfter ring seed pre e)
        (ring.rightNeighbor e) j →
      BankWindowTainted (bankWindowRootAfter ring seed pre e)
        (Counter.site ring (ring.rightNeighbor e) (j.val + 1)) →
      ((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).mode = .RESET ∨
      (((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).mode = .RWAIT ∧
        ((bankWindowRootAfter ring seed pre e).2.sites
          (ring.rightNeighbor e)).controller = .waiting [])) := by
  by_cases hpost :
      ((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).pack.val = 0
  · have hkeep := bankWindowOverlapIncomingCstartControllerKeep
      ring hn hbank seed pre e hJ hy hpost hgrant hstart
    exact bankWindowOverlapIncomingStableOwnerFields
      ring hbank (bankWindowRootBefore ring seed pre)
      hJ (ring.rightNeighbor e) e rfl hy hpost
      (hkeep.1.trans hstart.symm) hkeep.2
  · have hbroken := bankWindowOverlapIncomingBrokenOwnerFields
      ring hn hbank seed pre e hJ hy hpost
    constructor
    · intro limit hp
      exact False.elim (hbroken.2.2.1 limit hp)
    · intro j ho _ht
      exact False.elim (hbroken.2.2.2 j ho)

/-- For the genuine origin at an incoming PACK-zero responder,
neither selected endpoint can be its worker site. The source
case uses the actual incoming provenance theorem; the root site
cannot have a genuine worker because its PACK remains zero.
Consumer: incoming CWAIT comparison-token and worker collision
split, before invoking the off-pair comparison lemmas. -/
theorem bankWindowOverlapIncomingGenuineWorkerOffPair {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hy : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = 0)
    (hpost : ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).pack.val = 0)
    (o : RenewalBankOrigin n) (i : Fin n)
    (p : RenewalBankPayload n)
    (hroot : o.root = ring.rightNeighbor e)
    (hworker : ((bankWindowRootAfter ring seed pre e).2.sites i).worker =
      .payload p)
    (horigin : p.origin = some o) :
    i ≠ e ∧ i ≠ o.root := by
  have hrun :
      rbRun ring (renewalBankStart ring seed) (pre ++ [e]) =
        bankWindowRootAfter ring seed pre e := by
    rw [rbRunAppend]
    rfl
  have hworkerRun :
      ((rbRun ring (renewalBankStart ring seed)
        (pre ++ [e])).2.sites i).worker = .payload p := by
    rw [hrun]
    exact hworker
  have hband := bankWindowOverlapGenuineWorkerInBand
    ring hn hbank seed (pre ++ [e]) i p o hworkerRun horigin
  rw [hrun] at hband
  constructor
  · intro hi
    have hsourceWorker :
        ((bankWindowRootAfter ring seed pre e).2.sites e).worker =
          .payload p := by
      have hw := hworker
      rw [hi] at hw
      exact hw
    exact bankWindowIncomingSourceNoResponderOrigin
      ring hn hbank seed pre e hy hpost p o
      hroot hsourceWorker horigin
  · intro hi
    have hzero :
        ((bankWindowRootAfter ring seed pre e).1 i).pack.val = 0 := by
      rw [hi, hroot]
      exact hpost
    have hpositive := hband.1
    rw [hzero] at hpositive
    omega

/-- A CWAIT owner at an incoming PACK-zero responder retains
the entire genuine comparison package. Selected-pair workers
belonging to this root are excluded by real ReceiptInv; for all
remaining workers the unchanged digit window transfers
phaseComplete, phaseUnique, phaseFlags, and compareExact from
OLD J. Consumer: all incoming CWAIT comparison obligations. -/
theorem bankWindowOverlapIncomingCurrentComparisonFields {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hy : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = 0)
    (hpost : ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).pack.val = 0)
    (hgrant : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).grant = false)
    (hmodeOld : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).mode = .CWAIT)
    (hmode : ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).mode = .CWAIT)
    (o : RenewalBankOrigin n) (i : Fin n)
    (p : RenewalBankPayload n)
    (hroot : o.root = ring.rightNeighbor e)
    (hworker : BankComparatorOriginWorker ring
      (bankWindowRootAfter ring seed pre e) o i p)
    (hcontroller : ((bankWindowRootAfter ring seed pre e).2.sites
      o.root).controller = .waiting []) :
    Counter.Complete ring
      (bankWindowRootAfter ring seed pre e).1 o.root ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankTrialLiveComparisonToken
        ((bankWindowRootAfter ring seed pre e).1
          (Counter.site ring o.root (j.val + 1))).tok →
      Counter.site ring o.root (j.val + 1) = i) ∧
    ((((bankWindowRootAfter ring seed pre e).1 i).tok = .CR1 →
      bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        ((bankWindowRootAfter ring seed pre e).1 i).pack.val) ∧
     (((bankWindowRootAfter ring seed pre e).1 i).tok = .CR0 →
      ¬ bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        ((bankWindowRootAfter ring seed pre e).1 i).pack.val) ∧
     (((bankWindowRootAfter ring seed pre e).1 i).tok = .CL1 →
      bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        (compileAdvice (ceilLogTwo n)).b) ∧
     (((bankWindowRootAfter ring seed pre e).1 i).tok = .CL0 →
      ¬ bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        (compileAdvice (ceilLogTwo n)).b)) ∧
    (bankWindowOnlyToken ring
      (bankWindowRootAfter ring seed pre e) o.root i ∧
     BankTrialLiveComparisonToken
       ((bankWindowRootAfter ring seed pre e).1 i).tok ∧
     p.heads = bankOriginBinaryValue ring
       (bankWindowRootAfter ring seed pre e).1 o ∧
     bankOriginBinaryValue ring
       (bankWindowRootAfter ring seed pre e).1 o ≤
       (compileAdvice (ceilLogTwo n)).K) := by
  have hwait := bankWindowIncomingCwaitExact
    ring hn hbank seed pre e hJ hy hpost hgrant hmodeOld
  have hlong :
      1 < ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).lease.val := by
    by_cases hl :
        1 < ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).lease.val
    · exact hl
    · have hshort :
          ((bankWindowRootBefore ring seed pre).1
            (ring.rightNeighbor e)).lease.val ≤ 1 := by omega
      have hreset := (hwait.2 hshort).1
      have hbad : Mode.RESET = Mode.CWAIT := hreset.symm.trans hmode
      cases hbad
  have hcontrollerKeep :
      ((bankWindowRootAfter ring seed pre e).2.sites o.root).controller =
      ((bankWindowRootBefore ring seed pre).2.sites o.root).controller := by
    rw [hroot]
    exact (hwait.1 hlong).2
  have hoff := bankWindowOverlapIncomingGenuineWorkerOffPair
    ring hn hbank seed pre e hy hpost o i p
    hroot hworker.1 hworker.2.1
  have hright : i ≠ ring.rightNeighbor e := by
    intro hi
    exact hoff.2 (hi.trans hroot.symm)
  have hrootModeOld :
      ((bankWindowRootBefore ring seed pre).1 o.root).mode =
        .CWAIT := by
    rw [hroot]
    exact hmodeOld
  have hframe := bankWindowExactOffPairAtomicReads ring
    (bankWindowRootBefore ring seed pre) e i hoff.1 hright
  have hworkerOld : BankComparatorOriginWorker ring
      (bankWindowRootBefore ring seed pre) o i p := by
    refine ⟨hframe.2.2.2.2.2.1.symm.trans hworker.1,
      hworker.2.1, ?_⟩
    have ht := hworker.2.2
    rw [hframe.2.2.1] at ht
    exact ht
  have hcompleteOld := hJ.phaseComplete o i p
    hworkerOld hrootModeOld
  have hcomplete :
      Counter.Complete ring
        (bankWindowRootAfter ring seed pre e).1 o.root := by
    intro k hk
    have hp := bankWindowIncomingPackReadSetFrame
      ring hbank (bankWindowRootBefore ring seed pre)
      o.root e hroot.symm
      (by rw [hroot]; exact hy)
      (by rw [hroot]; exact hpost) k hk
    exact hp.trans (hcompleteOld k hk)
  have hflags := bankWindowIncomingComparatorOffPairSurvivor
    ring hbank (bankWindowRootBefore ring seed pre)
    hJ e i o p hroot.symm hoff.1 hoff.2
    hrootModeOld hworker
  have hcompare := bankWindowIncomingCompareOffPairSurvivor
    ring hbank (bankWindowRootBefore ring seed pre)
    hJ e i o p hroot.symm hoff.1 hoff.2
    hrootModeOld hcontrollerKeep hworker.1 hworker.2.1
    hcontroller
  exact ⟨hcomplete, hflags.1, hflags.2, hcompare⟩

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

/-- Assemble every foreign-root proto branch using only the actual
stable-PACK interior producer as a missing dependency. The source
PACK-zero, changed-responder, first-mismatch, and off-segment rows
are discharged by already imported results. Consumer: the foreign
J.proto field of the group-13 root overlap assembly. -/
theorem bankWindowOverlapRootForeignProtoWithInterior {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hbankWindowOverlapProtoInteriorAll :
      ∀ (root : Fin n) (k limit : Nat),
        root ≠ e ∧ root ≠ ring.rightNeighbor e →
        e = Counter.site ring root k →
        1 ≤ k → k < limit →
        packNext
          ((bankWindowRootBefore ring seed pre).1 e).pack.val
          ((bankWindowRootBefore ring seed pre).1
            (ring.rightNeighbor e)).pack.val
          (compileAdvice (ceilLogTwo n)).b =
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val →
        BankWindowProtoRun ring
          (bankWindowRootAfter ring seed pre e) root limit →
        BankWindowRootForeignProtoField ring
          (bankWindowRootAfter ring seed pre e) root limit) :
    ∀ (root : Fin n) (limit : Nat),
      root ≠ e ∧ root ≠ ring.rightNeighbor e →
      BankWindowProtoRun ring
        (bankWindowRootAfter ring seed pre e) root limit →
      BankWindowRootForeignProtoField ring
        (bankWindowRootAfter ring seed pre e) root limit := by
  intro root limit hforeign hproto
  by_cases hrootSource :
      ((bankWindowRootBefore ring seed pre).1 e).pack.val = 0
  · exact bankWindowRootForeignProtoStep
      ring hn hbank seed pre e root limit
      hJ hrootSource hforeign hproto
  · by_cases hstable :
        packNext
          ((bankWindowRootBefore ring seed pre).1 e).pack.val
          ((bankWindowRootBefore ring seed pre).1
            (ring.rightNeighbor e)).pack.val
          (compileAdvice (ceilLogTwo n)).b =
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
    · by_cases hboundary :
          e = Counter.site ring root (limit + 1) ∨
          ring.rightNeighbor e =
            Counter.site ring root (limit + 1)
      · exact bankWindowOverlapProtoForeignInterior
          ring hn hbank seed pre e root limit
          hJ hboundary hproto
      · by_cases hproper :
            ∃ t : Nat, t ≤ limit ∧
              ring.rightNeighbor e = Counter.site ring root t
        · obtain ⟨t, ht, htarget⟩ := hproper
          have htpos : 1 ≤ t := by
            by_cases hzero : t = 0
            · have hsite := htarget
              rw [hzero] at hsite
              change ring.rightNeighbor e = root at hsite
              exact False.elim (hforeign.2 hsite.symm)
            · omega
          have hsource :
              e = Counter.site ring root (t - 1) := by
            have hnext : t - 1 + 1 = t := by omega
            apply Counter.resetTrialSitePredecessor
              ring root e (t - 1)
            rw [hnext]
            exact htarget
          have hsrcPos : 1 ≤ t - 1 := by
            by_cases hfirst : t = 1
            · have hrootSite : e = root := by
                have hs := hsource
                rw [hfirst] at hs
                change e = root at hs
                exact hs
              exact False.elim (hforeign.1 hrootSite.symm)
            · omega
          exact hbankWindowOverlapProtoInteriorAll
            root (t - 1) limit hforeign hsource
            hsrcPos (by omega) hstable hproto
        · have hsegment :
              ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
                j.val + 1 ≤ limit →
                Counter.site ring root (j.val + 1) ≠ e ∧
                Counter.site ring root (j.val + 1) ≠
                  ring.rightNeighbor e := by
            intro j hj
            constructor
            · intro hsource
              have hsourceSite :
                  e = Counter.site ring root (j.val + 1) :=
                hsource.symm
              have hnext :
                  ring.rightNeighbor e =
                    Counter.site ring root (j.val + 2) := by
                rw [hsourceSite]
                rfl
              by_cases hinside : j.val + 2 ≤ limit
              · exact hproper ⟨j.val + 2, hinside, hnext⟩
              · have hlast : j.val + 2 = limit + 1 := by omega
                apply hboundary
                exact Or.inr (by rw [hlast] at hnext; exact hnext)
            · intro htarget
              exact hproper ⟨j.val + 1, hj, htarget.symm⟩
          exact bankWindowOverlapStableForeignProtoOffSegment
            ring hn seed pre e root limit
            hJ hforeign hstable hsegment hproto
    · exact bankWindowOverlapRepairForeignProtoStep
        ring hn hbank seed pre e root limit
        hJ hforeign hstable hrootSource hproto

/-- Foreign orphan preservation over every authentic root, stable
nonroot, or changed-PACK selected pair, without a proto/interior
hypothesis. Consumer: complete foreign J.orphan group-13 field. -/
theorem bankWindowOverlapRootForeignOrphanAll {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre)) :
    ∀ (root : Fin n)
      (j : Fin (compileAdvice (ceilLogTwo n)).b),
      root ≠ e ∧ root ≠ ring.rightNeighbor e →
      BankWindowOrphanOwner ring
        (bankWindowRootAfter ring seed pre e) root j →
      BankWindowTainted
        (bankWindowRootAfter ring seed pre e)
        (Counter.site ring root (j.val + 1)) →
      ((bankWindowRootAfter ring seed pre e).1 root).mode = .RESET ∨
      (((bankWindowRootAfter ring seed pre e).1 root).mode = .RWAIT ∧
        ((bankWindowRootAfter ring seed pre e).2.sites
          root).controller = .waiting []) := by
  intro root j hforeign howner htainted
  by_cases hx :
      ((bankWindowRootBefore ring seed pre).1 e).pack.val = 0
  · exact bankWindowRootForeignOrphanOnSource
      ring hn hbank seed pre e root j
      hJ hx hforeign howner htainted
  · by_cases hstable :
        packNext
          ((bankWindowRootBefore ring seed pre).1 e).pack.val
          ((bankWindowRootBefore ring seed pre).1
            (ring.rightNeighbor e)).pack.val
          (compileAdvice (ceilLogTwo n)).b =
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
    · exact bankWindowOverlapStableForeignOrphanStep
        ring hn hbank seed pre e root j
        hJ hforeign hstable howner htainted
    · exact bankWindowOverlapRepairForeignOrphanStep
        ring hn hbank seed pre e root j
        hJ hforeign hstable howner htainted


/-- Authentic incoming waiting owner: if the POST physical mode
still agrees with an OLD RWAIT/IWAIT/CWAIT mode, the lease could
not have expired, and the real ghost waiting controller is framed.
Consumer: all three global incoming waiting-phase fields. -/
theorem bankWindowOverlapIncomingWaitingKeepsController {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hy : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = 0)
    (hpost : ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).pack.val = 0)
    (hg : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).grant = false)
    (hm :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).mode = .RWAIT ∨
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).mode = .IWAIT ∨
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).mode = .CWAIT)
    (hmodeKeep :
      ((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).mode =
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).mode) :
    1 < ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).lease.val ∧
    ((bankWindowRootAfter ring seed pre e).2.sites
      (ring.rightNeighbor e)).controller =
    ((bankWindowRootBefore ring seed pre).2.sites
      (ring.rightNeighbor e)).controller := by
  rcases hm with hr | hi | hc
  · have hcore := bankWindowIncomingRootCoreStep
      ring hn hbank seed pre e hJ hy
    have hrow := hcore.2.2.2.2.2 hpost hg hr
    by_cases hlong :
        1 < ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).lease.val
    · exact ⟨hlong, (hrow.1 hlong).2⟩
    · have hshort :
          ((bankWindowRootBefore ring seed pre).1
            (ring.rightNeighbor e)).lease.val ≤ 1 := by omega
      have hreset := (hrow.2 hshort).1
      have hbad : Mode.RESET = Mode.RWAIT :=
        hreset.symm.trans (hmodeKeep.trans hr)
      cases hbad
  · have hrow := bankWindowIncomingIwaitExact
      ring hn hbank seed pre e hJ hy hpost hg hi
    by_cases hlong :
        1 < ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).lease.val
    · exact ⟨hlong, (hrow.1 hlong).2⟩
    · have hshort :
          ((bankWindowRootBefore ring seed pre).1
            (ring.rightNeighbor e)).lease.val ≤ 1 := by omega
      have hreset := (hrow.2 hshort).1
      have hbad : Mode.RESET = Mode.IWAIT :=
        hreset.symm.trans (hmodeKeep.trans hi)
      cases hbad
  · have hrow := bankWindowIncomingCwaitExact
      ring hn hbank seed pre e hJ hy hpost hg hc
    by_cases hlong :
        1 < ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).lease.val
    · exact ⟨hlong, (hrow.1 hlong).2⟩
    · have hshort :
          ((bankWindowRootBefore ring seed pre).1
            (ring.rightNeighbor e)).lease.val ≤ 1 := by omega
      have hreset := (hrow.2 hshort).1
      have hbad : Mode.RESET = Mode.CWAIT :=
        hreset.symm.trans (hmodeKeep.trans hc)
      cases hbad

/-- The full RR/RL leftmost pending-front and RL suffix
certificate on an incoming RWAIT owner, with the lease condition
derived from the POST mode rather than assumed. Consumer:
J.resetWait in the incoming-root stable-PACK case. -/
theorem bankWindowOverlapIncomingResetWaitField {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hy : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = 0)
    (hpost : ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).pack.val = 0)
    (hg : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).grant = false)
    (hm : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).mode = .RWAIT)
    (hnew : ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).mode = .RWAIT)
    (hscope : BankWindowScope ring
      (bankWindowRootAfter ring seed pre e)
      (ring.rightNeighbor e))
    (hcontroller : ((bankWindowRootAfter ring seed pre e).2.sites
      (ring.rightNeighbor e)).controller = .waiting []) :
    ∃ (j : Fin (compileAdvice (ceilLogTwo n)).b)
      (rho : RenewalBankReceipt n),
      ((bankWindowRootAfter ring seed pre e).2.sites
        (Counter.site ring (ring.rightNeighbor e) (j.val + 1))).worker =
          .pending rho ∧
      (((bankWindowRootAfter ring seed pre e).1
        (Counter.site ring (ring.rightNeighbor e) (j.val + 1))).tok =
          .RR ∨
       ((bankWindowRootAfter ring seed pre e).1
        (Counter.site ring (ring.rightNeighbor e) (j.val + 1))).tok =
          .RL) ∧
      bankWindowZeroPrefix ring
        (bankWindowRootAfter ring seed pre e)
        (ring.rightNeighbor e) (j.val + 1) ∧
      (∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
        k.val < j.val →
        ((bankWindowRootAfter ring seed pre e).1
          (Counter.site ring (ring.rightNeighbor e)
            (k.val + 1))).tok = .E) ∧
      (((bankWindowRootAfter ring seed pre e).1
        (Counter.site ring (ring.rightNeighbor e) (j.val + 1))).tok =
          .RL →
        bankWindowOnlyToken ring
          (bankWindowRootAfter ring seed pre e)
          (ring.rightNeighbor e)
          (Counter.site ring (ring.rightNeighbor e) (j.val + 1)) ∧
        bankWindowZeroPrefix ring
          (bankWindowRootAfter ring seed pre e)
          (ring.rightNeighbor e)
          (compileAdvice (ceilLogTwo n)).b) := by
  have hmodeKeep :
      ((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).mode =
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).mode :=
    hnew.trans hm.symm
  have hlong := (bankWindowOverlapIncomingWaitingKeepsController
    ring hn hbank seed pre e hJ hy hpost hg
    (Or.inl hm) hmodeKeep).1
  exact (bankWindowIncomingResetWaitSurvivor
    ring hn hbank seed pre e hJ hy hpost hg hm hlong).2
    hscope hcontroller

/-- Both incoming waiting-mode taint uniqueness clauses at every
POST digit, with ghost/controller survival established from the
real BANK lease row. Consumer: J.iwaitTaintedUnique and
J.cwaitTaintedUnique at the incoming root. -/
theorem bankWindowOverlapIncomingWaitTaintedFields {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hy : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = 0)
    (hpost : ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).pack.val = 0)
    (hg : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).grant = false)
    (hscope : BankWindowScope ring
      (bankWindowRootAfter ring seed pre e)
      (ring.rightNeighbor e))
    (hcontroller : ((bankWindowRootAfter ring seed pre e).2.sites
      (ring.rightNeighbor e)).controller = .waiting []) :
    (((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).mode = .IWAIT →
      ((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).mode = .IWAIT →
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        BankWindowTainted (bankWindowRootAfter ring seed pre e)
          (Counter.site ring (ring.rightNeighbor e) (j.val + 1)) →
        ∃ o p,
          ((bankWindowRootAfter ring seed pre e).2.sites
            (Counter.site ring (ring.rightNeighbor e)
              (j.val + 1))).worker = .payload p ∧
          p.origin = some o ∧ o.root = ring.rightNeighbor e ∧
          bankWindowOnlyToken ring
            (bankWindowRootAfter ring seed pre e)
            (ring.rightNeighbor e)
            (Counter.site ring (ring.rightNeighbor e) (j.val + 1))) ∧
    (((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).mode = .CWAIT →
      ((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).mode = .CWAIT →
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        BankWindowTainted (bankWindowRootAfter ring seed pre e)
          (Counter.site ring (ring.rightNeighbor e) (j.val + 1)) →
        ∃ o p,
          ((bankWindowRootAfter ring seed pre e).2.sites
            (Counter.site ring (ring.rightNeighbor e)
              (j.val + 1))).worker = .payload p ∧
          p.origin = some o ∧ o.root = ring.rightNeighbor e ∧
          BankTrialLiveComparisonToken
            ((bankWindowRootAfter ring seed pre e).1
              (Counter.site ring (ring.rightNeighbor e)
                (j.val + 1))).tok ∧
          bankWindowOnlyToken ring
            (bankWindowRootAfter ring seed pre e)
            (ring.rightNeighbor e)
            (Counter.site ring (ring.rightNeighbor e) (j.val + 1))) := by
  constructor
  · intro hmodeOld hmodePost
    have hmodeKeep :
        ((bankWindowRootAfter ring seed pre e).1
          (ring.rightNeighbor e)).mode =
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).mode :=
      hmodePost.trans hmodeOld.symm
    have hkeep := (bankWindowOverlapIncomingWaitingKeepsController
      ring hn hbank seed pre e hJ hy hpost hg
      (Or.inr (Or.inl hmodeOld)) hmodeKeep).2
    exact bankWindowIncomingIwaitTaintedSurvivor
      ring hbank (bankWindowRootBefore ring seed pre)
      hJ (ring.rightNeighbor e) e rfl hy hpost hg
      hmodeOld hkeep hscope hcontroller
  · intro hmodeOld hmodePost
    have hmodeKeep :
        ((bankWindowRootAfter ring seed pre e).1
          (ring.rightNeighbor e)).mode =
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).mode :=
      hmodePost.trans hmodeOld.symm
    have hkeep := (bankWindowOverlapIncomingWaitingKeepsController
      ring hn hbank seed pre e hJ hy hpost hg
      (Or.inr (Or.inr hmodeOld)) hmodeKeep).2
    exact bankWindowIncomingCwaitTaintedSurvivor
      ring hbank (bankWindowRootBefore ring seed pre)
      hJ (ring.rightNeighbor e) e rfl hy hpost hg
      hmodeOld hkeep hscope hcontroller

/-- Promote the installed digitwise IWAIT survivor to an arbitrary
genuine POST worker site. The worker offset is not assumed: the
actual extended-run ReceiptInv and genuine in-band certificate
identify it as a physical counter digit before invoking OLD J.
Consumer: global J.incrementExact at a surviving incoming root. -/
theorem bankWindowOverlapIncomingIncrementExactField {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hy : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = 0)
    (hpost : ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).pack.val = 0)
    (hg : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).grant = false)
    (hm : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).mode = .IWAIT)
    (hnew : ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).mode = .IWAIT)
    (hscope : BankWindowScope ring
      (bankWindowRootAfter ring seed pre e)
      (ring.rightNeighbor e))
    (hcontroller : ((bankWindowRootAfter ring seed pre e).2.sites
      (ring.rightNeighbor e)).controller = .waiting [])
    (o : RenewalBankOrigin n) (i : Fin n)
    (p : RenewalBankPayload n)
    (hworker : ((bankWindowRootAfter ring seed pre e).2.sites
      i).worker = .payload p)
    (ho : p.origin = some o)
    (horoot : o.root = ring.rightNeighbor e) :
    bankWindowOnlyToken ring
      (bankWindowRootAfter ring seed pre e)
      (ring.rightNeighbor e) i ∧
    (((((bankWindowRootAfter ring seed pre e).1 i).tok = .IR ∧
       bankWindowZeroPrefix ring
         (bankWindowRootAfter ring seed pre e)
         (ring.rightNeighbor e)
         ((bankWindowRootAfter ring seed pre e).1 i).pack.val ∧
       p.heads = bankOriginBinaryValue ring
         (bankWindowRootAfter ring seed pre e).1 o +
         2 ^ ((bankWindowRootAfter ring seed pre e).1 i).pack.val ∧
       bankOriginBinaryValue ring
         (bankWindowRootAfter ring seed pre e).1 o +
         2 ^ ((bankWindowRootAfter ring seed pre e).1 i).pack.val ≤
           (compileAdvice (ceilLogTwo n)).K) ∨
      (((bankWindowRootAfter ring seed pre e).1 i).tok = .AL ∧
       p.heads = bankOriginBinaryValue ring
         (bankWindowRootAfter ring seed pre e).1 o ∧
       bankOriginBinaryValue ring
         (bankWindowRootAfter ring seed pre e).1 o ≤
           (compileAdvice (ceilLogTwo n)).K))) := by
  have hmodeKeep :
      ((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).mode =
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).mode :=
    hnew.trans hm.symm
  have hcontrollerKeep :=
    (bankWindowOverlapIncomingWaitingKeepsController
      ring hn hbank seed pre e hJ hy hpost hg
      (Or.inr (Or.inl hm)) hmodeKeep).2
  have hword :
      rbRun ring (renewalBankStart ring seed) (pre ++ [e]) =
        bankWindowRootAfter ring seed pre e := by
    rw [rbRunAppend]
    rfl
  have hworkerWord :
      ((rbRun ring (renewalBankStart ring seed)
        (pre ++ [e])).2.sites i).worker = .payload p := by
    rw [hword]
    exact hworker
  have hband := bankWindowOverlapGenuineWorkerInBand
    ring hn hbank seed (pre ++ [e]) i p o hworkerWord ho
  rw [hword] at hband
  have hsiteWorker := bankWindowIncomingPostWorkerAnchor
    ring hn hbank seed pre e i o p hworker ho
    hband.1 hband.2
  have hindexBound :
      ((bankWindowRootAfter ring seed pre e).1 i).pack.val - 1 <
        (compileAdvice (ceilLogTwo n)).b := by omega
  have hindexEq :
      ((bankWindowRootAfter ring seed pre e).1 i).pack.val - 1 + 1 =
        ((bankWindowRootAfter ring seed pre e).1 i).pack.val := by
    omega
  have hsite :
      Counter.site ring (ring.rightNeighbor e)
        (((bankWindowRootAfter ring seed pre e).1 i).pack.val - 1 + 1) =
      i := by
    rw [hindexEq]
    have hs := hsiteWorker
    rw [horoot] at hs
    exact hs.symm
  have hworkerDigit :
      ((bankWindowRootAfter ring seed pre e).2.sites
        (Counter.site ring (ring.rightNeighbor e)
          (((bankWindowRootAfter ring seed pre e).1 i).pack.val - 1 + 1))).worker =
            .payload p := by
    rw [hsite]
    exact hworker
  have hdigit := bankWindowIncomingIncrementDigitSurvivor
    ring hbank (bankWindowRootBefore ring seed pre)
    hJ (ring.rightNeighbor e) e o p
    (⟨((bankWindowRootAfter ring seed pre e).1 i).pack.val - 1,
      hindexBound⟩ : Fin (compileAdvice (ceilLogTwo n)).b)
    rfl horoot hy hpost hg hm hcontrollerKeep
    hscope hcontroller hworkerDigit ho
  rw [hsite] at hdigit
  exact hdigit

/-- At a real incoming grant-free CSTART root, every active
origin controller has its actual own root by the POST ReceiptInv.
Its uncapped binary value and entire E-token digit window are
transported from OLD J; no foreign-origin bit hypothesis is
added. Consumer: incoming CSTART branch of J.armedExact. -/
theorem bankWindowOverlapIncomingCstartArmedExactField {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hy : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = 0)
    (hpost : ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).pack.val = 0)
    (hg : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).grant = false)
    (hm : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).mode = .CSTART)
    (hscope : BankWindowScope ring
      (bankWindowRootAfter ring seed pre e)
      (ring.rightNeighbor e))
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hactive : ((bankWindowRootAfter ring seed pre e).2.sites
      (ring.rightNeighbor e)).controller = .active p)
    (horigin : p.origin = some o) :
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ((bankWindowRootAfter ring seed pre e).1
        (Counter.site ring (ring.rightNeighbor e)
          (j.val + 1))).tok = .E) ∧
    p.heads = bankOriginBinaryValue ring
      (bankWindowRootAfter ring seed pre e).1 o ∧
    (((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).mode = .ARMED →
      bankOriginBinaryValue ring
        (bankWindowRootAfter ring seed pre e).1 o <
          (compileAdvice (ceilLogTwo n)).K) ∧
    (((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).mode = .CSTART →
      bankOriginBinaryValue ring
        (bankWindowRootAfter ring seed pre e).1 o ≤
          (compileAdvice (ceilLogTwo n)).K) := by
  have hkeep := bankWindowOverlapIncomingCstartControllerKeep
    ring hn hbank seed pre e hJ hy hpost hg hm
  have hroot := (bankWindowOverlapPostReceipt
    ring hn hbank seed pre e).activeRoot
    (ring.rightNeighbor e) p o hactive horigin
  have hscopeOld := bankWindowIncomingScopeBackward
    ring hbank (bankWindowRootBefore ring seed pre)
    (ring.rightNeighbor e) e rfl hy hpost hg hscope
  have hactiveOld :
      ((bankWindowRootBefore ring seed pre).2.sites
        (ring.rightNeighbor e)).controller = .active p :=
    hkeep.2.symm.trans hactive
  have hold := hJ.armedExact
    (ring.rightNeighbor e) o p hscopeOld
    (Or.inr hm) hactiveOld horigin
  have hvalue := bankWindowIncomingBinaryValueReadSetFrame
    ring hbank (bankWindowRootBefore ring seed pre)
    e o hroot
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    have hindex : j.val + 1 ≤ (compileAdvice (ceilLogTwo n)).b := by
      have hj := j.isLt
      omega
    have hf := (bankWindowIncomingDigitReadSetFrame
      ring hbank (bankWindowRootBefore ring seed pre)
      (ring.rightNeighbor e) e rfl (j.val + 1)
      (by omega) hindex).1
    have htok := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok) hf
    exact htok.trans (hold.1 j)
  · exact hold.2.1.trans hvalue.symm
  · intro hpostArmed
    have hbad : Mode.CSTART = Mode.ARMED :=
      hkeep.1.symm.trans hpostArmed
    cases hbad
  · intro _hpostStart
    rw [hvalue]
    exact hold.2.2.2 hm

/-- The literal stable interior CR0/CR1 token collision erases
both genuine worker slots if the responder carries another
comparison, carry-return, or other-return token. Neither a new
comparator nor a return worker is minted by this collision.
Consumer: selected pair phaseFlags/compareExact collision cases. -/
theorem bankWindowOverlapInteriorComparisonCollisionMemory {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (k : Nat)
    (hk : 1 ≤ k) (hbelow : k < c.b)
    (hx : x.pack.val = k) (hy : y.pack.val = k + 1)
    (hsource : x.tok = .CR0 ∨ x.tok = .CR1)
    (htarget : y.tok = .AL ∨ y.tok = .CL0 ∨
      y.tok = .CL1 ∨ y.tok = .CR0 ∨ y.tok = .CR1) :
    (renewalBankPairMemory c m e dest x y).1.worker = .empty ∧
    (renewalBankPairMemory c m e dest x y).2.worker = .empty := by
  have hle : k ≤ c.b := by omega
  have hnonzero : k ≠ 0 := by omega
  have hnotTop : k ≠ c.b := by omega
  have hnextLe : k + 1 ≤ c.b := by omega
  have hnextPos : 1 ≤ k + 1 := by omega
  have hnextNonzero : k + 1 ≠ 0 := by omega
  have hrole : packNext k (k + 1) c.b = k + 1 := by
    simp [packNext, hbelow]
  rcases hsource with hcr | hcr <;>
    rcases htarget with ht | ht | ht | ht | ht <;>
    simp [renewalBankPairMemory, bankCell, hx, hy,
      hk, hbelow, hle, hnonzero, hnotTop, hnextLe,
      hnextPos, hnextNonzero, hrole, hcr, ht,
      Id.run_pure, Id.run_bind]

/-- Actual selected pair after a CR0/CR1 collision has no
worker at either endpoint. Every supposed POST genuine-origin
comparator at either endpoint is therefore impossible, so its
phaseFlags and compareExact implications are vacuous on this
specific collision row. Consumer: group-13 interior collision. -/
theorem bankWindowOverlapInteriorComparisonCollisionNoWorker {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n) (k : Nat)
    (hk : 1 ≤ k)
    (hbelow : k < (compileAdvice (ceilLogTwo n)).b)
    (hx : ((bankWindowRootBefore ring seed pre).1 e).pack.val = k)
    (hy : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = k + 1)
    (hsource :
      ((bankWindowRootBefore ring seed pre).1 e).tok = .CR0 ∨
      ((bankWindowRootBefore ring seed pre).1 e).tok = .CR1)
    (htarget :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .AL ∨
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .CL0 ∨
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .CL1 ∨
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .CR0 ∨
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .CR1) :
    ((bankWindowRootAfter ring seed pre e).2.sites e).worker = .empty ∧
    ((bankWindowRootAfter ring seed pre e).2.sites
      (ring.rightNeighbor e)).worker = .empty := by
  have hlocal := bankWindowOverlapInteriorComparisonCollisionMemory
    (compileAdvice (ceilLogTwo n))
    (bankWindowRootBefore ring seed pre).2
    e (ring.rightNeighbor e)
    ((bankWindowRootBefore ring seed pre).1 e)
    ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e))
    k hk hbelow hx hy hsource htarget
  have hp := (rbReferenceSelectedPairFrame ring
    (by omega : 2 ≤ n)
    (bankWindowRootBefore ring seed pre) e).2.2
  have hsrc := congrArg
    (fun s : RenewalBankSite n => s.worker) hp.1
  have hdst := congrArg
    (fun s : RenewalBankSite n => s.worker) hp.2
  change ((bankWindowRootAfter ring seed pre e).2.sites e).worker =
    (renewalBankPairMemory
      (compileAdvice (ceilLogTwo n))
      (bankWindowRootBefore ring seed pre).2
      e (ring.rightNeighbor e)
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).1.worker at hsrc
  change ((bankWindowRootAfter ring seed pre e).2.sites
      (ring.rightNeighbor e)).worker =
    (renewalBankPairMemory
      (compileAdvice (ceilLogTwo n))
      (bankWindowRootBefore ring seed pre).2
      e (ring.rightNeighbor e)
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).2.worker at hdst
  exact ⟨hsrc.trans hlocal.1, hdst.trans hlocal.2⟩

/-- In the literal interior CL0/CL1 return row an empty-token
source receives precisely the old responder worker, and the
responder worker is erased. This supplies the ghost half of the
genuine comparison-return transfer without a hypothetical
post-step invariant. Consumer: selected CL return compareExact. -/
theorem bankWindowOverlapInteriorComparisonReturnMemory {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (k : Nat)
    (hk : 1 ≤ k) (hbelow : k < c.b)
    (hx : x.pack.val = k) (hy : y.pack.val = k + 1)
    (hsource : x.tok = .E)
    (htarget : y.tok = .CL0 ∨ y.tok = .CL1) :
    (renewalBankPairMemory c m e dest x y).1.worker =
      (m.sites dest).worker ∧
    (renewalBankPairMemory c m e dest x y).2.worker = .empty := by
  have hle : k ≤ c.b := by omega
  have hnonzero : k ≠ 0 := by omega
  have hnotTop : k ≠ c.b := by omega
  have hnextLe : k + 1 ≤ c.b := by omega
  have hnextPos : 1 ≤ k + 1 := by omega
  have hnextNonzero : k + 1 ≠ 0 := by omega
  have hrole : packNext k (k + 1) c.b = k + 1 := by
    simp [packNext, hbelow]
  rcases htarget with hcl | hcl <;>
    simp [renewalBankPairMemory, bankCell, hx, hy,
      hk, hbelow, hle, hnonzero, hnotTop, hnextLe,
      hnextPos, hnextNonzero, hrole, hsource, hcl,
      Id.run_pure, Id.run_bind]

/-- Actual ghost copying and responder erasure for an interior
genuine CL0/CL1 return, with unchanged aligned PACK roles.
Consumer: the CL-return worker preimage used by J.compareExact. -/
theorem bankWindowOverlapInteriorComparisonReturnWorkers {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n) (k : Nat)
    (hk : 1 ≤ k)
    (hbelow : k < (compileAdvice (ceilLogTwo n)).b)
    (hx : ((bankWindowRootBefore ring seed pre).1 e).pack.val = k)
    (hy : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = k + 1)
    (hsource : ((bankWindowRootBefore ring seed pre).1 e).tok = .E)
    (htarget :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .CL0 ∨
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .CL1) :
    ((bankWindowRootAfter ring seed pre e).2.sites e).worker =
      ((bankWindowRootBefore ring seed pre).2.sites
        (ring.rightNeighbor e)).worker ∧
    ((bankWindowRootAfter ring seed pre e).2.sites
      (ring.rightNeighbor e)).worker = .empty := by
  have hlocal := bankWindowOverlapInteriorComparisonReturnMemory
    (compileAdvice (ceilLogTwo n))
    (bankWindowRootBefore ring seed pre).2
    e (ring.rightNeighbor e)
    ((bankWindowRootBefore ring seed pre).1 e)
    ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e))
    k hk hbelow hx hy hsource htarget
  have hp := (rbReferenceSelectedPairFrame ring
    (by omega : 2 ≤ n)
    (bankWindowRootBefore ring seed pre) e).2.2
  have hsrc := congrArg
    (fun s : RenewalBankSite n => s.worker) hp.1
  have hdst := congrArg
    (fun s : RenewalBankSite n => s.worker) hp.2
  change ((bankWindowRootAfter ring seed pre e).2.sites e).worker =
    (renewalBankPairMemory
      (compileAdvice (ceilLogTwo n))
      (bankWindowRootBefore ring seed pre).2
      e (ring.rightNeighbor e)
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).1.worker at hsrc
  change ((bankWindowRootAfter ring seed pre e).2.sites
      (ring.rightNeighbor e)).worker =
    (renewalBankPairMemory
      (compileAdvice (ceilLogTwo n))
      (bankWindowRootBefore ring seed pre).2
      e (ring.rightNeighbor e)
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).2.worker at hdst
  exact ⟨hsrc.trans hlocal.1, hdst.trans hlocal.2⟩

/-- On an authentic CR0/CR1 advance with an empty responder
token, the selected source worker is erased and the exact old
source worker moves to the responder. The existing public
interior IR/CR forwarding lemma supplies the complete ghost
outcome, without a fresh payload or post-J assumption.
Consumer: interior CR advance phaseFlags/compareExact transport. -/
theorem bankWindowOverlapInteriorComparisonAdvanceWorkers {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n) (k : Nat)
    (hk : 1 ≤ k)
    (hbelow : k < (compileAdvice (ceilLogTwo n)).b)
    (hx : ((bankWindowRootBefore ring seed pre).1 e).pack.val = k)
    (hy : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = k + 1)
    (hsource :
      ((bankWindowRootBefore ring seed pre).1 e).tok = .CR0 ∨
      ((bankWindowRootBefore ring seed pre).1 e).tok = .CR1)
    (hempty :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .E) :
    ((bankWindowRootAfter ring seed pre e).2.sites e).worker = .empty ∧
    ((bankWindowRootAfter ring seed pre e).2.sites
      (ring.rightNeighbor e)).worker =
    ((bankWindowRootBefore ring seed pre).2.sites e).worker := by
  exact bankWindowClosureInteriorIrCrWorkerForward
    ring hn (bankWindowRootBefore ring seed pre)
    e k hk hbelow hx hy (Or.inr hsource) hempty

/-- Bundle precisely the accessible group-13 post fields: global
frame, both payload-shape clauses, all foreign proto prefixes
under the one interior producer interface, and every foreign
orphan restriction. The same-pair genuine comparator rows and
root-local wait/active clauses have separate theorems and are
NOT asserted as a full BankWindowExact step here.
Consumer: joint-module assembly before bankWindowExactStep. -/
theorem bankWindowOverlapRootFields {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hbankWindowOverlapProtoInteriorAll :
      ∀ (root : Fin n) (k limit : Nat),
        root ≠ e ∧ root ≠ ring.rightNeighbor e →
        e = Counter.site ring root k →
        1 ≤ k → k < limit →
        packNext
          ((bankWindowRootBefore ring seed pre).1 e).pack.val
          ((bankWindowRootBefore ring seed pre).1
            (ring.rightNeighbor e)).pack.val
          (compileAdvice (ceilLogTwo n)).b =
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val →
        BankWindowProtoRun ring
          (bankWindowRootAfter ring seed pre e) root limit →
        BankWindowRootForeignProtoField ring
          (bankWindowRootAfter ring seed pre e) root limit) :
    BankInFlightAligned ring (bankWindowRootAfter ring seed pre e) ∧
    (∀ (i : Fin n) (p : RenewalBankPayload n),
      p ∈ rbSiteLivePayloads
        ((bankWindowRootAfter ring seed pre e).2.sites i) →
      p.origin = none → p.atoms ≠ [] ∧ p.heads = 0) ∧
    (∀ (i : Fin n) (p : RenewalBankPayload n)
      (o : RenewalBankOrigin n),
      p ∈ rbSiteLivePayloads
        ((bankWindowRootAfter ring seed pre e).2.sites i) →
      p.origin = some o → p.atoms = []) ∧
    (∀ (root : Fin n) (limit : Nat),
      root ≠ e ∧ root ≠ ring.rightNeighbor e →
      BankWindowProtoRun ring
        (bankWindowRootAfter ring seed pre e) root limit →
      BankWindowRootForeignProtoField ring
        (bankWindowRootAfter ring seed pre e) root limit) ∧
    (∀ (root : Fin n)
      (j : Fin (compileAdvice (ceilLogTwo n)).b),
      root ≠ e ∧ root ≠ ring.rightNeighbor e →
      BankWindowOrphanOwner ring
        (bankWindowRootAfter ring seed pre e) root j →
      BankWindowTainted
        (bankWindowRootAfter ring seed pre e)
        (Counter.site ring root (j.val + 1)) →
      ((bankWindowRootAfter ring seed pre e).1 root).mode = .RESET ∨
      (((bankWindowRootAfter ring seed pre e).1 root).mode = .RWAIT ∧
        ((bankWindowRootAfter ring seed pre e).2.sites
          root).controller = .waiting [])) := by
  have hglobal := bankWindowOverlapGlobalAndDisjoint
    ring hn hbank seed pre e hJ
  have hproto := bankWindowOverlapRootForeignProtoWithInterior
    ring hn hbank seed pre e hJ
    hbankWindowOverlapProtoInteriorAll
  have horphan := bankWindowOverlapRootForeignOrphanAll
    ring hn hbank seed pre e hJ
  exact ⟨hglobal.1, hglobal.2.1, hglobal.2.2.1,
    hproto, horphan⟩

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

/-- Exact physical BANK output on an aligned CR forward pair.
The source token is retired and the responder receives CR1
precisely if the old token is CR1 and the new digit agrees
with its theta bit. Both physical bits remain unchanged.
Consumer: genuine comparison phaseFlags and compareExact. -/
theorem bankWindowOverlapInteriorComparisonAdvancePhysical
    {c : Compiled} (x y : Agent c) (k : Nat)
    (hk : 1 ≤ k) (hbelow : k < c.b)
    (hx : x.pack.val = k) (hy : y.pack.val = k + 1)
    (hcr : x.tok = .CR0 ∨ x.tok = .CR1)
    (hempty : y.tok = .E) :
    (Counter.resetBankOld x y).1.tok = .E ∧
    (Counter.resetBankOld x y).2.tok =
      (if x.tok = .CR1 ∧ y.bit = c.theta k
       then .CR1 else .CR0) ∧
    (Counter.resetBankOld x y).1.bit = x.bit ∧
    (Counter.resetBankOld x y).2.bit = y.bit := by
  have hle : k ≤ c.b := by omega
  have hnz : k ≠ 0 := by omega
  have hne : k ≠ c.b := by omega
  have hnextLe : k + 1 ≤ c.b := by omega
  have hnextPos : 1 ≤ k + 1 := by omega
  have hnextNz : k + 1 ≠ 0 := by omega
  have hrole : packNext k (k + 1) c.b = k + 1 := by
    simp [packNext, hbelow]
  rcases hcr with hzero | hone
  · simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hk, hbelow, hle, hnz, hne,
      hnextLe, hnextPos, hnextNz, hrole,
      hzero, hempty, Id.run_pure, Id.run_bind]
  · by_cases hbit : y.bit = c.theta k
    · simp [Counter.resetBankOld, bankPair, bankCell,
        hx, hy, hk, hbelow, hle, hnz, hne,
        hnextLe, hnextPos, hnextNz, hrole,
        hone, hempty, hbit, Id.run_pure, Id.run_bind]
    · simp [Counter.resetBankOld, bankPair, bankCell,
        hx, hy, hk, hbelow, hle, hnz, hne,
        hnextLe, hnextPos, hnextNz, hrole,
        hone, hempty, hbit, Id.run_pure, Id.run_bind]

/-- The aligned CL return reverses the token direction: the
responder becomes empty and the predecessor inherits the same
CL0/CL1 outcome, with both bits fixed.
Consumer: comparison-return phaseFlags/compareExact. -/
theorem bankWindowOverlapInteriorComparisonReturnPhysical
    {c : Compiled} (x y : Agent c) (k : Nat)
    (hk : 1 ≤ k) (hbelow : k < c.b)
    (hx : x.pack.val = k) (hy : y.pack.val = k + 1)
    (hempty : x.tok = .E)
    (hcl : y.tok = .CL0 ∨ y.tok = .CL1) :
    (Counter.resetBankOld x y).1.tok = y.tok ∧
    (Counter.resetBankOld x y).2.tok = .E ∧
    (Counter.resetBankOld x y).1.bit = x.bit ∧
    (Counter.resetBankOld x y).2.bit = y.bit := by
  have hle : k ≤ c.b := by omega
  have hnz : k ≠ 0 := by omega
  have hne : k ≠ c.b := by omega
  have hnextLe : k + 1 ≤ c.b := by omega
  have hnextPos : 1 ≤ k + 1 := by omega
  have hnextNz : k + 1 ≠ 0 := by omega
  have hrole : packNext k (k + 1) c.b = k + 1 := by
    simp [packNext, hbelow]
  rcases hcl with hzero | hone
  · simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hk, hbelow, hle, hnz, hne,
      hnextLe, hnextPos, hnextNz, hrole,
      hempty, hzero, Id.run_pure, Id.run_bind]
  · simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hk, hbelow, hle, hnz, hne,
      hnextLe, hnextPos, hnextNz, hrole,
      hempty, hone, Id.run_pure, Id.run_bind]

/-- Prefix extension for an actual origin-indexed BANK bit
window. Its last digit is independently tested; it cannot
be inferred from CR1 at the predecessor alone.
Consumer: CR advance with positive/negative comparison flags. -/
theorem bankWindowOverlapComparatorPrefixExtension {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (o : RenewalBankOrigin n) (k : Nat)
    (hk : k < (compileAdvice (ceilLogTwo n)).b) :
    bankComparatorPrefixMatched ring r o (k + 1) ↔
      bankComparatorPrefixMatched ring r o k ∧
      (r.1 (Counter.site ring o.root (k + 1))).bit =
        (compileAdvice (ceilLogTwo n)).theta k := by
  constructor
  · intro hnext
    constructor
    · intro j hj
      exact hnext j (by omega)
    · have hbit := hnext
        (⟨k, hk⟩ : Fin (compileAdvice (ceilLogTwo n)).b)
        (by change k + 1 ≤ k + 1; omega)
      change
        (r.1 (Counter.site ring o.root (k + 1))).bit =
          (compileAdvice (ceilLogTwo n)).theta k at hbit
      exact hbit
  · rintro ⟨hprefix, hlast⟩
    intro j hj
    by_cases hlow : j.val + 1 ≤ k
    · exact hprefix j hlow
    · have heq : j.val = k := by omega
      rw [heq]
      exact hlast

/-- All comparison-prefix flags transport across an edge when
each origin digit bit is physically framed.
Consumer: CR/CL selected pair phaseFlags transfer. -/
theorem bankWindowOverlapComparatorPrefixBitTransport {n : Nat}
    (ring : DirectedRing n)
    (r s : RenewalBankReference n)
    (o : RenewalBankOrigin n) (last : Nat)
    (hbits : bankWindowReadDigitBits ring r s o.root) :
    bankComparatorPrefixMatched ring s o last ↔
      bankComparatorPrefixMatched ring r o last := by
  constructor
  · intro h j hj
    exact (hbits j).symm.trans (h j hj)
  · intro h j hj
    exact (hbits j).trans (h j hj)

/-- The full uncapped genuine-origin comparison credit is
invariant when the origin's digit bits are framed. No power
arithmetic is evaluated, only the equality of the two List.ofFn
summands is transferred.
Consumer: CR/CL selected pair compareExact credit. -/
theorem bankWindowOverlapComparatorBinaryBitTransport {n : Nat}
    (ring : DirectedRing n)
    (r s : RenewalBankReference n)
    (o : RenewalBankOrigin n)
    (hbits : bankWindowReadDigitBits ring r s o.root) :
    bankOriginBinaryValue ring s.1 o =
      bankOriginBinaryValue ring r.1 o := by
  unfold bankOriginBinaryValue
  have hterms :
      (fun j : Fin (compileAdvice (ceilLogTwo n)).b =>
        if (s.1 (Counter.site ring o.root (j.val + 1))).bit
        then 2 ^ j.val else 0) =
      (fun j : Fin (compileAdvice (ceilLogTwo n)).b =>
        if (r.1 (Counter.site ring o.root (j.val + 1))).bit
        then 2 ^ j.val else 0) := by
    funext j
    rw [hbits j]
  exact congrArg
    (fun f : Fin (compileAdvice (ceilLogTwo n)).b → Nat =>
      (List.ofFn f).sum) hterms

/-- The selected physical CR advance, not merely an abstract
bankPair, fixes both bits and stamps the precise post token
after BANK masking. Consumer: J.phaseFlags on moving CR workers. -/
theorem bankWindowOverlapInteriorComparisonAdvanceSelected {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n) (k : Nat)
    (hk : 1 ≤ k)
    (hbelow : k < (compileAdvice (ceilLogTwo n)).b)
    (hx : ((bankWindowRootBefore ring seed pre).1 e).pack.val = k)
    (hy : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = k + 1)
    (hcr :
      ((bankWindowRootBefore ring seed pre).1 e).tok = .CR0 ∨
      ((bankWindowRootBefore ring seed pre).1 e).tok = .CR1)
    (hempty :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .E) :
    ((bankWindowRootAfter ring seed pre e).1 e).tok = .E ∧
    ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).tok =
      (if ((bankWindowRootBefore ring seed pre).1 e).tok = .CR1 ∧
          ((bankWindowRootBefore ring seed pre).1
            (ring.rightNeighbor e)).bit =
              (compileAdvice (ceilLogTwo n)).theta k
       then .CR1 else .CR0) ∧
    ((bankWindowRootAfter ring seed pre e).1 e).bit =
      ((bankWindowRootBefore ring seed pre).1 e).bit ∧
    ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).bit =
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).bit := by
  have hphysical := bankWindowOverlapInteriorComparisonAdvancePhysical
    ((bankWindowRootBefore ring seed pre).1 e)
    ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e))
    k hk hbelow hx hy hcr hempty
  have htrip := bankWindowClosureSelectedBankTrip ring hn hbank
    (bankWindowRootBefore ring seed pre) e
  have hsourceTok := congrArg
    (fun t : Mode × Bool × BTok => t.2.2) htrip.1
  have htargetTok := congrArg
    (fun t : Mode × Bool × BTok => t.2.2) htrip.2
  have hsourceBit := congrArg
    (fun t : Mode × Bool × BTok => t.2.1) htrip.1
  have htargetBit := congrArg
    (fun t : Mode × Bool × BTok => t.2.1) htrip.2
  change ((bankWindowRootAfter ring seed pre e).1 e).tok =
    (Counter.resetBankOld
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).1.tok at hsourceTok
  change ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).tok =
    (Counter.resetBankOld
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).2.tok at htargetTok
  change ((bankWindowRootAfter ring seed pre e).1 e).bit =
    (Counter.resetBankOld
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).1.bit at hsourceBit
  change ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).bit =
    (Counter.resetBankOld
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).2.bit at htargetBit
  exact ⟨hsourceTok.trans hphysical.1,
    htargetTok.trans hphysical.2.1,
    hsourceBit.trans hphysical.2.2.1,
    htargetBit.trans hphysical.2.2.2⟩

/-- The selected physical CL return keeps both bits and copies
the returning token back to the predecessor. The ghost return
worker was independently established in the previous row.
Consumer: J.phaseFlags/compareExact on moving CL workers. -/
theorem bankWindowOverlapInteriorComparisonReturnSelected {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n) (k : Nat)
    (hk : 1 ≤ k)
    (hbelow : k < (compileAdvice (ceilLogTwo n)).b)
    (hx : ((bankWindowRootBefore ring seed pre).1 e).pack.val = k)
    (hy : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = k + 1)
    (hempty : ((bankWindowRootBefore ring seed pre).1 e).tok = .E)
    (hcl :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .CL0 ∨
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .CL1) :
    ((bankWindowRootAfter ring seed pre e).1 e).tok =
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok ∧
    ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).tok = .E ∧
    ((bankWindowRootAfter ring seed pre e).1 e).bit =
      ((bankWindowRootBefore ring seed pre).1 e).bit ∧
    ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).bit =
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).bit := by
  have hphysical := bankWindowOverlapInteriorComparisonReturnPhysical
    ((bankWindowRootBefore ring seed pre).1 e)
    ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e))
    k hk hbelow hx hy hempty hcl
  have htrip := bankWindowClosureSelectedBankTrip ring hn hbank
    (bankWindowRootBefore ring seed pre) e
  have hsourceTok := congrArg
    (fun t : Mode × Bool × BTok => t.2.2) htrip.1
  have htargetTok := congrArg
    (fun t : Mode × Bool × BTok => t.2.2) htrip.2
  have hsourceBit := congrArg
    (fun t : Mode × Bool × BTok => t.2.1) htrip.1
  have htargetBit := congrArg
    (fun t : Mode × Bool × BTok => t.2.1) htrip.2
  change ((bankWindowRootAfter ring seed pre e).1 e).tok =
    (Counter.resetBankOld
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).1.tok at hsourceTok
  change ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).tok =
    (Counter.resetBankOld
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).2.tok at htargetTok
  change ((bankWindowRootAfter ring seed pre e).1 e).bit =
    (Counter.resetBankOld
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).1.bit at hsourceBit
  change ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).bit =
    (Counter.resetBankOld
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).2.bit at htargetBit
  exact ⟨hsourceTok.trans hphysical.1,
    htargetTok.trans hphysical.2.1,
    hsourceBit.trans hphysical.2.2.1,
    htargetBit.trans hphysical.2.2.2⟩

/-- The only possible bit changes in a real selected pair are
at its endpoints. If both endpoint bits are fixed, every site
and therefore every origin's full digit-bit window is framed.
Consumer: selected CR/CL phaseFlags and compareExact. -/
theorem bankWindowOverlapSelectedBitFrame {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n)
    (hsource :
      ((renewalBankNext ring r e).1 e).bit = (r.1 e).bit)
    (hresponder :
      ((renewalBankNext ring r e).1
        (ring.rightNeighbor e)).bit =
        (r.1 (ring.rightNeighbor e)).bit) :
    ∀ z : Fin n,
      ((renewalBankNext ring r e).1 z).bit = (r.1 z).bit := by
  intro z
  by_cases hz : z = e
  · subst z
    exact hsource
  · by_cases hy : z = ring.rightNeighbor e
    · subst z
      exact hresponder
    · exact congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.bit)
        (bankWindowExactOffPairFrame ring r e z hz hy).1

/-- The genuinely originated CR0/CR1 source moves its comparison
flag one digit right. The CR1 branch extends the exact matched
prefix by one tested physical bit; the CR0 branch either inherits
an old mismatch or discovers a new mismatch at the responder.
Both CL flag clauses are impossible on this moving CR worker.
Consumer: J.phaseFlags for the selected comparison-advance pair. -/
theorem bankWindowOverlapInteriorComparisonAdvanceFlags {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n) (k : Nat)
    (hk : 1 ≤ k)
    (hbelow : k < (compileAdvice (ceilLogTwo n)).b)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hx : ((bankWindowRootBefore ring seed pre).1 e).pack.val = k)
    (hy : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = k + 1)
    (hcr :
      ((bankWindowRootBefore ring seed pre).1 e).tok = .CR0 ∨
      ((bankWindowRootBefore ring seed pre).1 e).tok = .CR1)
    (hempty :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .E)
    (o : RenewalBankOrigin n) (p : RenewalBankPayload n)
    (hworker :
      ((bankWindowRootBefore ring seed pre).2.sites e).worker =
        .payload p)
    (horigin : p.origin = some o)
    (hmode : ((bankWindowRootBefore ring seed pre).1 o.root).mode =
      .CWAIT) :
    (((bankWindowRootAfter ring seed pre e).1
       (ring.rightNeighbor e)).tok = .CR1 →
      bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        ((bankWindowRootAfter ring seed pre e).1
          (ring.rightNeighbor e)).pack.val) ∧
    (((bankWindowRootAfter ring seed pre e).1
       (ring.rightNeighbor e)).tok = .CR0 →
      ¬ bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        ((bankWindowRootAfter ring seed pre e).1
          (ring.rightNeighbor e)).pack.val) ∧
    (((bankWindowRootAfter ring seed pre e).1
       (ring.rightNeighbor e)).tok = .CL1 →
      bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        (compileAdvice (ceilLogTwo n)).b) ∧
    (((bankWindowRootAfter ring seed pre e).1
       (ring.rightNeighbor e)).tok = .CL0 →
      ¬ bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        (compileAdvice (ceilLogTwo n)).b) := by
  have hphysical := bankWindowOverlapInteriorComparisonAdvanceSelected
    ring hn hbank seed pre e k hk hbelow hx hy hcr hempty
  have hbitsGlobal := bankWindowOverlapSelectedBitFrame ring
    (bankWindowRootBefore ring seed pre) e
    hphysical.2.2.1 hphysical.2.2.2
  have hbits : bankWindowReadDigitBits ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) o.root := by
    intro j
    exact hbitsGlobal (Counter.site ring o.root (j.val + 1))
  have hprefixTransport := bankWindowOverlapComparatorPrefixBitTransport
    ring (bankWindowRootBefore ring seed pre)
    (bankWindowRootAfter ring seed pre e) o
    (k + 1) hbits
  have hprefixExtension := bankWindowOverlapComparatorPrefixExtension
    ring (bankWindowRootBefore ring seed pre) o k hbelow
  have htokenOld :
      BankTrialLiveComparisonToken
        ((bankWindowRootBefore ring seed pre).1 e).tok := by
    rcases hcr with hzero | hone
    · simp [BankTrialLiveComparisonToken, hzero]
    · simp [BankTrialLiveComparisonToken, hone]
  have hcompOld : BankComparatorOriginWorker ring
      (bankWindowRootBefore ring seed pre) o e p :=
    ⟨hworker, horigin, htokenOld⟩
  have holdFlags := hJ.phaseFlags o e p hcompOld hmode
  have hstable :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val := by
    rw [hx, hy]
    simp [packNext, hbelow]
  have hpack : ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).pack.val = k + 1 := by
    have hres := bankWindowExactResponderPack ring
      (bankWindowRootBefore ring seed pre) e
      (clockNeighborDifferent ring (by omega : 2 ≤ n) e)
    rw [hres, hx, hy]
    simp [packNext, hbelow]
  have hsite : e = Counter.site ring o.root k := by
    have hh := bankWindowGenuineWorkerSiteOfRun
      ring hn hbank seed pre e p o hworker horigin
    rw [hx] at hh
    exact hh
  have hnextSite :
      ring.rightNeighbor e =
        Counter.site ring o.root (k + 1) := by
    rw [hsite]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hpostCR1
    have hcondition :
        ((bankWindowRootBefore ring seed pre).1 e).tok = .CR1 ∧
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).bit =
          (compileAdvice (ceilLogTwo n)).theta k := by
      by_cases hc :
          ((bankWindowRootBefore ring seed pre).1 e).tok = .CR1 ∧
          ((bankWindowRootBefore ring seed pre).1
            (ring.rightNeighbor e)).bit =
            (compileAdvice (ceilLogTwo n)).theta k
      · exact hc
      · have he :
            ((bankWindowRootAfter ring seed pre e).1
              (ring.rightNeighbor e)).tok = .CR0 := by
          rw [hphysical.2.1, if_neg hc]
        rw [he] at hpostCR1
        cases hpostCR1
    have hprefixOld :
        bankComparatorPrefixMatched ring
          (bankWindowRootBefore ring seed pre) o k := by
      have hh := holdFlags.1 hcondition.1
      rw [hx] at hh
      exact hh
    have hlast :
        ((bankWindowRootBefore ring seed pre).1
          (Counter.site ring o.root (k + 1))).bit =
        (compileAdvice (ceilLogTwo n)).theta k := by
      rw [← hnextSite]
      exact hcondition.2
    have hprefixNext := hprefixExtension.mpr
      ⟨hprefixOld, hlast⟩
    have hprefixPost := hprefixTransport.mpr hprefixNext
    rw [hpack]
    exact hprefixPost
  · intro hpostCR0 hpostMatched
    have hmatchNext :
        bankComparatorPrefixMatched ring
          (bankWindowRootBefore ring seed pre) o (k + 1) := by
      have hpostAt :
          bankComparatorPrefixMatched ring
            (bankWindowRootAfter ring seed pre e) o (k + 1) := by
        rw [hpack] at hpostMatched
        exact hpostMatched
      exact hprefixTransport.mp hpostAt
    have hparts := hprefixExtension.mp hmatchNext
    by_cases hone :
        ((bankWindowRootBefore ring seed pre).1 e).tok = .CR1
    · have hlast :
          ((bankWindowRootBefore ring seed pre).1
            (ring.rightNeighbor e)).bit =
            (compileAdvice (ceilLogTwo n)).theta k := by
        rw [hnextSite]
        exact hparts.2
      have hcondition :
          ((bankWindowRootBefore ring seed pre).1 e).tok = .CR1 ∧
          ((bankWindowRootBefore ring seed pre).1
            (ring.rightNeighbor e)).bit =
              (compileAdvice (ceilLogTwo n)).theta k :=
        ⟨hone, hlast⟩
      have hpostOne :
          ((bankWindowRootAfter ring seed pre e).1
            (ring.rightNeighbor e)).tok = .CR1 := by
        rw [hphysical.2.1, if_pos hcondition]
      rw [hpostOne] at hpostCR0
      cases hpostCR0
    · have hzero :
          ((bankWindowRootBefore ring seed pre).1 e).tok = .CR0 := by
        rcases hcr with hz | ho
        · exact hz
        · exact False.elim (hone ho)
      have hbad := holdFlags.2.1 hzero
      rw [hx] at hbad
      exact hbad hparts.1
  · intro hpostCL1
    have hnot :
        ((bankWindowRootAfter ring seed pre e).1
          (ring.rightNeighbor e)).tok ≠ .CL1 := by
      rw [hphysical.2.1]
      split <;> simp
    exact False.elim (hnot hpostCL1)
  · intro hpostCL0
    have hnot :
        ((bankWindowRootAfter ring seed pre e).1
          (ring.rightNeighbor e)).tok ≠ .CL0 := by
      rw [hphysical.2.1]
      split <;> simp
    exact False.elim (hnot hpostCL0)

/-- If the actual selected source token is erased and OLD
comparison uniqueness names that source, a newly live token at
any origin digit can only be on the responder; off-pair tokens
are framed. Consumer: CR advance compareExact and phaseUnique. -/
theorem bankWindowOverlapOnlyTokenForward {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (e root : Fin n)
    (honly : bankWindowOnlyToken ring r root e)
    (hclear : ((renewalBankNext ring r e).1 e).tok = .E) :
    bankWindowOnlyToken ring (renewalBankNext ring r e)
      root (ring.rightNeighbor e) := by
  intro j hlive
  by_cases hsource :
      Counter.site ring root (j.val + 1) = e
  · have hempty :
        ((renewalBankNext ring r e).1
          (Counter.site ring root (j.val + 1))).tok = .E := by
      rw [hsource]
      exact hclear
    exact False.elim (hlive hempty)
  · by_cases htarget :
        Counter.site ring root (j.val + 1) =
          ring.rightNeighbor e
    · exact htarget
    · have hf := bankWindowExactOffPairFrame ring r e
        (Counter.site ring root (j.val + 1))
        hsource htarget
      have htok := congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
        hf.1
      have hbefore :
          (r.1 (Counter.site ring root (j.val + 1))).tok ≠ .E := by
        intro he
        exact hlive (htok.trans he)
      exact False.elim (hsource (honly j hbefore))

/-- Dually, a returned CL0/CL1 token is unique at the selected
predecessor if the old worker's only token was the responder
and that responder is erased. Consumer: CL return compareExact
and phaseUnique for the actual origin root. -/
theorem bankWindowOverlapOnlyTokenBackward {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) (e root : Fin n)
    (honly : bankWindowOnlyToken ring r root
      (ring.rightNeighbor e))
    (hclear :
      ((renewalBankNext ring r e).1 (ring.rightNeighbor e)).tok =
        .E) :
    bankWindowOnlyToken ring (renewalBankNext ring r e)
      root e := by
  intro j hlive
  by_cases hsource :
      Counter.site ring root (j.val + 1) = e
  · exact hsource
  · by_cases htarget :
        Counter.site ring root (j.val + 1) =
          ring.rightNeighbor e
    · have hempty :
          ((renewalBankNext ring r e).1
            (Counter.site ring root (j.val + 1))).tok = .E := by
        rw [htarget]
        exact hclear
      exact False.elim (hlive hempty)
    · have hf := bankWindowExactOffPairFrame ring r e
        (Counter.site ring root (j.val + 1))
        hsource htarget
      have htok := congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
        hf.1
      have hbefore :
          (r.1 (Counter.site ring root (j.val + 1))).tok ≠ .E := by
        intro he
        exact hlive (htok.trans he)
      have hold := honly j hbefore
      exact False.elim (htarget hold)

/-- An old genuine CL0/CL1 responder is the only source of the
POST predecessor CL0/CL1 token. With the two physical bits
unchanged, the OLD positive or negative full-width comparison
certificate is preserved verbatim. Newly CR0/CR1 flags cannot
appear on this returned worker. Consumer: J.phaseFlags, CL return. -/
theorem bankWindowOverlapInteriorComparisonReturnFlags {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n) (k : Nat)
    (hk : 1 ≤ k)
    (hbelow : k < (compileAdvice (ceilLogTwo n)).b)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hx : ((bankWindowRootBefore ring seed pre).1 e).pack.val = k)
    (hy : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = k + 1)
    (hempty : ((bankWindowRootBefore ring seed pre).1 e).tok = .E)
    (hcl :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .CL0 ∨
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .CL1)
    (o : RenewalBankOrigin n) (p : RenewalBankPayload n)
    (hworker :
      ((bankWindowRootBefore ring seed pre).2.sites
        (ring.rightNeighbor e)).worker = .payload p)
    (horigin : p.origin = some o)
    (hmode : ((bankWindowRootBefore ring seed pre).1 o.root).mode =
      .CWAIT) :
    (((bankWindowRootAfter ring seed pre e).1 e).tok = .CR1 →
      bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        ((bankWindowRootAfter ring seed pre e).1 e).pack.val) ∧
    (((bankWindowRootAfter ring seed pre e).1 e).tok = .CR0 →
      ¬ bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        ((bankWindowRootAfter ring seed pre e).1 e).pack.val) ∧
    (((bankWindowRootAfter ring seed pre e).1 e).tok = .CL1 →
      bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        (compileAdvice (ceilLogTwo n)).b) ∧
    (((bankWindowRootAfter ring seed pre e).1 e).tok = .CL0 →
      ¬ bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        (compileAdvice (ceilLogTwo n)).b) := by
  have hphysical := bankWindowOverlapInteriorComparisonReturnSelected
    ring hn hbank seed pre e k hk hbelow hx hy hempty hcl
  have hbitsGlobal := bankWindowOverlapSelectedBitFrame ring
    (bankWindowRootBefore ring seed pre) e
    hphysical.2.2.1 hphysical.2.2.2
  have hbits : bankWindowReadDigitBits ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) o.root := by
    intro j
    exact hbitsGlobal (Counter.site ring o.root (j.val + 1))
  have hmatch := bankWindowOverlapComparatorPrefixBitTransport
    ring (bankWindowRootBefore ring seed pre)
    (bankWindowRootAfter ring seed pre e) o
    (compileAdvice (ceilLogTwo n)).b hbits
  have htoken :
      BankTrialLiveComparisonToken
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).tok := by
    rcases hcl with hzero | hone
    · simp [BankTrialLiveComparisonToken, hzero]
    · simp [BankTrialLiveComparisonToken, hone]
  have hcompOld : BankComparatorOriginWorker ring
      (bankWindowRootBefore ring seed pre)
      o (ring.rightNeighbor e) p :=
    ⟨hworker, horigin, htoken⟩
  have hflags := hJ.phaseFlags o (ring.rightNeighbor e) p
    hcompOld hmode
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hpost
    have hold : ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .CR1 :=
      hphysical.1.symm.trans hpost
    rcases hcl with hzero | hone
    · rw [hzero] at hold
      cases hold
    · rw [hone] at hold
      cases hold
  · intro hpost
    have hold : ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .CR0 :=
      hphysical.1.symm.trans hpost
    rcases hcl with hzero | hone
    · rw [hzero] at hold
      cases hold
    · rw [hone] at hold
      cases hold
  · intro hpost
    have hold : ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .CL1 :=
      hphysical.1.symm.trans hpost
    exact hmatch.mpr (hflags.2.2.1 hold)
  · intro hpost hmatched
    have hold : ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .CL0 :=
      hphysical.1.symm.trans hpost
    exact (hflags.2.2.2 hold) (hmatch.mp hmatched)

/-- Genuine CR0/CR1 advance preserves the complete POST
compareExact obligations. The OLD comparison worker is
physically moved to the responder, the only live token follows
it, and all digit bits preserve its uncapped head count.
Consumer: J.compareExact and J.phaseUnique, CR advance. -/
theorem bankWindowOverlapInteriorComparisonAdvanceCompareExact {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n) (k : Nat)
    (hk : 1 ≤ k)
    (hbelow : k < (compileAdvice (ceilLogTwo n)).b)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hx : ((bankWindowRootBefore ring seed pre).1 e).pack.val = k)
    (hy : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = k + 1)
    (hcr :
      ((bankWindowRootBefore ring seed pre).1 e).tok = .CR0 ∨
      ((bankWindowRootBefore ring seed pre).1 e).tok = .CR1)
    (hempty :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .E)
    (o : RenewalBankOrigin n) (p : RenewalBankPayload n)
    (hworker :
      ((bankWindowRootBefore ring seed pre).2.sites e).worker =
        .payload p)
    (horigin : p.origin = some o)
    (hmode : ((bankWindowRootBefore ring seed pre).1 o.root).mode =
      .CWAIT)
    (hcontroller :
      ((bankWindowRootBefore ring seed pre).2.sites
        o.root).controller = .waiting []) :
    BankComparatorOriginWorker ring
      (bankWindowRootAfter ring seed pre e)
      o (ring.rightNeighbor e) p ∧
    bankWindowOnlyToken ring
      (bankWindowRootAfter ring seed pre e)
      o.root (ring.rightNeighbor e) ∧
    p.heads = bankOriginBinaryValue ring
      (bankWindowRootAfter ring seed pre e).1 o ∧
    bankOriginBinaryValue ring
      (bankWindowRootAfter ring seed pre e).1 o ≤
      (compileAdvice (ceilLogTwo n)).K := by
  have hphysical := bankWindowOverlapInteriorComparisonAdvanceSelected
    ring hn hbank seed pre e k hk hbelow hx hy hcr hempty
  have hghost := bankWindowOverlapInteriorComparisonAdvanceWorkers
    ring hn seed pre e k hk hbelow hx hy hcr hempty
  have htokenPost :
      BankTrialLiveComparisonToken
        ((bankWindowRootAfter ring seed pre e).1
          (ring.rightNeighbor e)).tok := by
    rw [hphysical.2.1]
    split <;> simp [BankTrialLiveComparisonToken]
  have hworkerPost :
      ((bankWindowRootAfter ring seed pre e).2.sites
        (ring.rightNeighbor e)).worker = .payload p :=
    hghost.2.trans hworker
  have hcurrent : BankComparatorOriginWorker ring
      (bankWindowRootAfter ring seed pre e)
      o (ring.rightNeighbor e) p :=
    ⟨hworkerPost, horigin, htokenPost⟩
  have holdCompare := hJ.compareExact o e p
    hworker horigin hmode hcontroller
  have honly := bankWindowOverlapOnlyTokenForward
    ring (bankWindowRootBefore ring seed pre)
    e o.root holdCompare.1 hphysical.1
  have hbitsGlobal := bankWindowOverlapSelectedBitFrame ring
    (bankWindowRootBefore ring seed pre) e
    hphysical.2.2.1 hphysical.2.2.2
  have hbits : bankWindowReadDigitBits ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) o.root := by
    intro j
    exact hbitsGlobal (Counter.site ring o.root (j.val + 1))
  have hvalue := bankWindowOverlapComparatorBinaryBitTransport
    ring (bankWindowRootBefore ring seed pre)
    (bankWindowRootAfter ring seed pre e) o hbits
  exact ⟨hcurrent, honly, holdCompare.2.2.1.trans hvalue.symm,
    by rw [hvalue]; exact holdCompare.2.2.2⟩

/-- Genuine CL0/CL1 return preserves the POST compareExact
consequences at the predecessor. The old responder payload is
the new source payload, the responder is erased, and the
full-width origin bits, binary credit, and unique token survive.
Consumer: J.compareExact and J.phaseUnique, CL return. -/
theorem bankWindowOverlapInteriorComparisonReturnCompareExact {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n) (k : Nat)
    (hk : 1 ≤ k)
    (hbelow : k < (compileAdvice (ceilLogTwo n)).b)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hx : ((bankWindowRootBefore ring seed pre).1 e).pack.val = k)
    (hy : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = k + 1)
    (hempty : ((bankWindowRootBefore ring seed pre).1 e).tok = .E)
    (hcl :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .CL0 ∨
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .CL1)
    (o : RenewalBankOrigin n) (p : RenewalBankPayload n)
    (hworker :
      ((bankWindowRootBefore ring seed pre).2.sites
        (ring.rightNeighbor e)).worker = .payload p)
    (horigin : p.origin = some o)
    (hmode : ((bankWindowRootBefore ring seed pre).1 o.root).mode =
      .CWAIT)
    (hcontroller :
      ((bankWindowRootBefore ring seed pre).2.sites
        o.root).controller = .waiting []) :
    BankComparatorOriginWorker ring
      (bankWindowRootAfter ring seed pre e) o e p ∧
    bankWindowOnlyToken ring
      (bankWindowRootAfter ring seed pre e) o.root e ∧
    p.heads = bankOriginBinaryValue ring
      (bankWindowRootAfter ring seed pre e).1 o ∧
    bankOriginBinaryValue ring
      (bankWindowRootAfter ring seed pre e).1 o ≤
      (compileAdvice (ceilLogTwo n)).K := by
  have hphysical := bankWindowOverlapInteriorComparisonReturnSelected
    ring hn hbank seed pre e k hk hbelow hx hy hempty hcl
  have hghost := bankWindowOverlapInteriorComparisonReturnWorkers
    ring hn seed pre e k hk hbelow hx hy hempty hcl
  have htokenPost :
      BankTrialLiveComparisonToken
        ((bankWindowRootAfter ring seed pre e).1 e).tok := by
    rw [hphysical.1]
    rcases hcl with hzero | hone
    · simp [BankTrialLiveComparisonToken, hzero]
    · simp [BankTrialLiveComparisonToken, hone]
  have hworkerPost :
      ((bankWindowRootAfter ring seed pre e).2.sites e).worker =
        .payload p :=
    hghost.1.trans hworker
  have hcurrent : BankComparatorOriginWorker ring
      (bankWindowRootAfter ring seed pre e) o e p :=
    ⟨hworkerPost, horigin, htokenPost⟩
  have holdCompare := hJ.compareExact o
    (ring.rightNeighbor e) p hworker horigin hmode hcontroller
  have honly := bankWindowOverlapOnlyTokenBackward
    ring (bankWindowRootBefore ring seed pre)
    e o.root holdCompare.1 hphysical.2.1
  have hbitsGlobal := bankWindowOverlapSelectedBitFrame ring
    (bankWindowRootBefore ring seed pre) e
    hphysical.2.2.1 hphysical.2.2.2
  have hbits : bankWindowReadDigitBits ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) o.root := by
    intro j
    exact hbitsGlobal (Counter.site ring o.root (j.val + 1))
  have hvalue := bankWindowOverlapComparatorBinaryBitTransport
    ring (bankWindowRootBefore ring seed pre)
    (bankWindowRootAfter ring seed pre e) o hbits
  exact ⟨hcurrent, honly, holdCompare.2.2.1.trans hvalue.symm,
    by rw [hvalue]; exact holdCompare.2.2.2⟩

/-- The full current-origin package for an authentic CR advance:
POST worker identity, CWAIT owner, full physical aligned window,
unique live comparison token, all four comparison flags, and
uncapped compareExact. It uses no POST-J assumption.
Consumer: moving-comparator case of global J phase fields. -/
theorem bankWindowOverlapInteriorComparisonAdvanceCurrentFields {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n) (k : Nat)
    (hk : 1 ≤ k)
    (hbelow : k < (compileAdvice (ceilLogTwo n)).b)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hx : ((bankWindowRootBefore ring seed pre).1 e).pack.val = k)
    (hy : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = k + 1)
    (hcr :
      ((bankWindowRootBefore ring seed pre).1 e).tok = .CR0 ∨
      ((bankWindowRootBefore ring seed pre).1 e).tok = .CR1)
    (hempty :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .E)
    (o : RenewalBankOrigin n) (p : RenewalBankPayload n)
    (hworker :
      ((bankWindowRootBefore ring seed pre).2.sites e).worker =
        .payload p)
    (horigin : p.origin = some o)
    (hmode : ((bankWindowRootBefore ring seed pre).1 o.root).mode =
      .CWAIT)
    (hcontroller :
      ((bankWindowRootBefore ring seed pre).2.sites
        o.root).controller = .waiting []) :
    BankComparatorCurrentWorker ring
      (bankWindowRootAfter ring seed pre e)
      o (ring.rightNeighbor e) p ∧
    Counter.Complete ring
      (bankWindowRootAfter ring seed pre e).1 o.root ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankTrialLiveComparisonToken
        ((bankWindowRootAfter ring seed pre e).1
          (Counter.site ring o.root (j.val + 1))).tok →
      Counter.site ring o.root (j.val + 1) =
        ring.rightNeighbor e) ∧
    (((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).tok = .CR1 →
      bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        ((bankWindowRootAfter ring seed pre e).1
          (ring.rightNeighbor e)).pack.val) ∧
    (((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).tok = .CR0 →
      ¬ bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        ((bankWindowRootAfter ring seed pre e).1
          (ring.rightNeighbor e)).pack.val) ∧
    (((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).tok = .CL1 →
      bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        (compileAdvice (ceilLogTwo n)).b) ∧
    (((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).tok = .CL0 →
      ¬ bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        (compileAdvice (ceilLogTwo n)).b) ∧
    (bankWindowOnlyToken ring
      (bankWindowRootAfter ring seed pre e)
        o.root (ring.rightNeighbor e) ∧
      p.heads = bankOriginBinaryValue ring
        (bankWindowRootAfter ring seed pre e).1 o ∧
      bankOriginBinaryValue ring
        (bankWindowRootAfter ring seed pre e).1 o ≤
          (compileAdvice (ceilLogTwo n)).K) := by
  have hcomparison := bankWindowOverlapInteriorComparisonAdvanceCompareExact
    ring hn hbank seed pre e k hk hbelow hJ
    hx hy hcr hempty o p hworker horigin hmode hcontroller
  have hflags := bankWindowOverlapInteriorComparisonAdvanceFlags
    ring hn hbank seed pre e k hk hbelow hJ
    hx hy hcr hempty o p hworker horigin hmode
  have htokenOld :
      BankTrialLiveComparisonToken
        ((bankWindowRootBefore ring seed pre).1 e).tok := by
    rcases hcr with hz | ho
    · simp [BankTrialLiveComparisonToken, hz]
    · simp [BankTrialLiveComparisonToken, ho]
  have hcompOld : BankComparatorOriginWorker ring
      (bankWindowRootBefore ring seed pre) o e p :=
    ⟨hworker, horigin, htokenOld⟩
  have hcompleteOld := hJ.phaseComplete o e p hcompOld hmode
  have hzero :
      ((bankWindowRootBefore ring seed pre).1 o.root).pack.val =
        0 := by
    have hz := hcompleteOld 0 (by omega)
    change ((bankWindowRootBefore ring seed pre).1 o.root).pack.val =
      0 at hz
    exact hz
  have hforeign : o.root ≠ e ∧
      o.root ≠ ring.rightNeighbor e := by
    constructor
    · intro hroot
      rw [hroot, hx] at hzero
      omega
    · intro hroot
      rw [hroot, hy] at hzero
      omega
  have hrootFrame := bankWindowExactOffPairFrame ring
    (bankWindowRootBefore ring seed pre) e o.root
    hforeign.1 hforeign.2
  have hmodePost :
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode =
        .CWAIT :=
    (congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.mode)
      hrootFrame.1).trans hmode
  have hstable :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val := by
    rw [hx, hy]
    simp [packNext, hbelow]
  have hcompletePost :
      Counter.Complete ring
        (bankWindowRootAfter ring seed pre e).1 o.root := by
    intro t ht
    exact (bankWindowOverlapStablePackFrame
      ring hn seed pre e hstable
      (Counter.site ring o.root t)).trans (hcompleteOld t ht)
  have hcurrent : BankComparatorCurrentWorker ring
      (bankWindowRootAfter ring seed pre e)
      o (ring.rightNeighbor e) p :=
    ⟨hcomparison.1, hmodePost⟩
  have hunique :
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        BankTrialLiveComparisonToken
          ((bankWindowRootAfter ring seed pre e).1
            (Counter.site ring o.root (j.val + 1))).tok →
        Counter.site ring o.root (j.val + 1) =
          ring.rightNeighbor e := by
    intro j ht
    apply hcomparison.2.1 j
    intro hempty
    rw [hempty] at ht
    simp [BankTrialLiveComparisonToken] at ht
  exact ⟨hcurrent, hcompletePost, hunique, hflags.1,
    hflags.2.1, hflags.2.2.1, hflags.2.2.2,
    hcomparison.2.1, hcomparison.2.2.1, hcomparison.2.2.2⟩

/-- The full current-origin package for the selected CL return:
the returned source is the unique genuine comparison worker,
its origin remains CWAIT and complete, full-width flags are
unchanged, and the exact binary credit is preserved.
Consumer: moving CL-return case of global J phase fields. -/
theorem bankWindowOverlapInteriorComparisonReturnCurrentFields {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n) (k : Nat)
    (hk : 1 ≤ k)
    (hbelow : k < (compileAdvice (ceilLogTwo n)).b)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hx : ((bankWindowRootBefore ring seed pre).1 e).pack.val = k)
    (hy : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = k + 1)
    (hempty : ((bankWindowRootBefore ring seed pre).1 e).tok = .E)
    (hcl :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .CL0 ∨
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .CL1)
    (o : RenewalBankOrigin n) (p : RenewalBankPayload n)
    (hworker :
      ((bankWindowRootBefore ring seed pre).2.sites
        (ring.rightNeighbor e)).worker = .payload p)
    (horigin : p.origin = some o)
    (hmode : ((bankWindowRootBefore ring seed pre).1 o.root).mode =
      .CWAIT)
    (hcontroller :
      ((bankWindowRootBefore ring seed pre).2.sites
        o.root).controller = .waiting []) :
    BankComparatorCurrentWorker ring
      (bankWindowRootAfter ring seed pre e) o e p ∧
    Counter.Complete ring
      (bankWindowRootAfter ring seed pre e).1 o.root ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankTrialLiveComparisonToken
        ((bankWindowRootAfter ring seed pre e).1
          (Counter.site ring o.root (j.val + 1))).tok →
      Counter.site ring o.root (j.val + 1) = e) ∧
    (((bankWindowRootAfter ring seed pre e).1 e).tok = .CR1 →
      bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        ((bankWindowRootAfter ring seed pre e).1 e).pack.val) ∧
    (((bankWindowRootAfter ring seed pre e).1 e).tok = .CR0 →
      ¬ bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        ((bankWindowRootAfter ring seed pre e).1 e).pack.val) ∧
    (((bankWindowRootAfter ring seed pre e).1 e).tok = .CL1 →
      bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        (compileAdvice (ceilLogTwo n)).b) ∧
    (((bankWindowRootAfter ring seed pre e).1 e).tok = .CL0 →
      ¬ bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        (compileAdvice (ceilLogTwo n)).b) ∧
    (bankWindowOnlyToken ring
      (bankWindowRootAfter ring seed pre e) o.root e ∧
      p.heads = bankOriginBinaryValue ring
        (bankWindowRootAfter ring seed pre e).1 o ∧
      bankOriginBinaryValue ring
        (bankWindowRootAfter ring seed pre e).1 o ≤
          (compileAdvice (ceilLogTwo n)).K) := by
  have hcomparison := bankWindowOverlapInteriorComparisonReturnCompareExact
    ring hn hbank seed pre e k hk hbelow hJ
    hx hy hempty hcl o p hworker horigin hmode hcontroller
  have hflags := bankWindowOverlapInteriorComparisonReturnFlags
    ring hn hbank seed pre e k hk hbelow hJ
    hx hy hempty hcl o p hworker horigin hmode
  have htokenOld :
      BankTrialLiveComparisonToken
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).tok := by
    rcases hcl with hz | ho
    · simp [BankTrialLiveComparisonToken, hz]
    · simp [BankTrialLiveComparisonToken, ho]
  have hcompOld : BankComparatorOriginWorker ring
      (bankWindowRootBefore ring seed pre)
      o (ring.rightNeighbor e) p :=
    ⟨hworker, horigin, htokenOld⟩
  have hcompleteOld := hJ.phaseComplete o
    (ring.rightNeighbor e) p hcompOld hmode
  have hzero :
      ((bankWindowRootBefore ring seed pre).1 o.root).pack.val =
        0 := by
    have hz := hcompleteOld 0 (by omega)
    change ((bankWindowRootBefore ring seed pre).1 o.root).pack.val =
      0 at hz
    exact hz
  have hforeign : o.root ≠ e ∧
      o.root ≠ ring.rightNeighbor e := by
    constructor
    · intro hroot
      rw [hroot, hx] at hzero
      omega
    · intro hroot
      rw [hroot, hy] at hzero
      omega
  have hrootFrame := bankWindowExactOffPairFrame ring
    (bankWindowRootBefore ring seed pre) e o.root
    hforeign.1 hforeign.2
  have hmodePost :
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode =
        .CWAIT :=
    (congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.mode)
      hrootFrame.1).trans hmode
  have hstable :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val := by
    rw [hx, hy]
    simp [packNext, hbelow]
  have hcompletePost :
      Counter.Complete ring
        (bankWindowRootAfter ring seed pre e).1 o.root := by
    intro t ht
    exact (bankWindowOverlapStablePackFrame
      ring hn seed pre e hstable
      (Counter.site ring o.root t)).trans (hcompleteOld t ht)
  have hcurrent : BankComparatorCurrentWorker ring
      (bankWindowRootAfter ring seed pre e) o e p :=
    ⟨hcomparison.1, hmodePost⟩
  have hunique :
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        BankTrialLiveComparisonToken
          ((bankWindowRootAfter ring seed pre e).1
            (Counter.site ring o.root (j.val + 1))).tok →
        Counter.site ring o.root (j.val + 1) = e := by
    intro j ht
    apply hcomparison.2.1 j
    intro hempty
    rw [hempty] at ht
    simp [BankTrialLiveComparisonToken] at ht
  exact ⟨hcurrent, hcompletePost, hunique, hflags.1,
    hflags.2.1, hflags.2.2.1, hflags.2.2.2,
    hcomparison.2.1, hcomparison.2.2.1, hcomparison.2.2.2⟩

/-- The literal CR collision erases both selected comparison
tokens without changing either bit. This is the physical
counterpart of the already proved two-slot ghost erasure.
Consumer: genuine comparison collision phaseFlags and uniqueness. -/
theorem bankWindowOverlapInteriorComparisonCollisionPhysical
    {c : Compiled} (x y : Agent c) (k : Nat)
    (hk : 1 ≤ k) (hbelow : k < c.b)
    (hx : x.pack.val = k) (hy : y.pack.val = k + 1)
    (hcr : x.tok = .CR0 ∨ x.tok = .CR1)
    (htarget : y.tok = .AL ∨ y.tok = .CL0 ∨
      y.tok = .CL1 ∨ y.tok = .CR0 ∨ y.tok = .CR1) :
    (Counter.resetBankOld x y).1.tok = .E ∧
    (Counter.resetBankOld x y).2.tok = .E ∧
    (Counter.resetBankOld x y).1.bit = x.bit ∧
    (Counter.resetBankOld x y).2.bit = y.bit := by
  have hle : k ≤ c.b := by omega
  have hnz : k ≠ 0 := by omega
  have hne : k ≠ c.b := by omega
  have hnextLe : k + 1 ≤ c.b := by omega
  have hnextPos : 1 ≤ k + 1 := by omega
  have hnextNz : k + 1 ≠ 0 := by omega
  have hrole : packNext k (k + 1) c.b = k + 1 := by
    simp [packNext, hbelow]
  rcases hcr with hcase | hcase <;>
    rcases htarget with ht | ht | ht | ht | ht <;>
    simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hk, hbelow, hle, hnz, hne,
      hnextLe, hnextPos, hnextNz, hrole,
      hcase, ht, Id.run_pure, Id.run_bind]

/-- The physical selected endpoints and all origin digit bits
are unchanged by this CR collision, although their tokens and
ghost workers are erased. Thus the collision cannot create a
current comparator at either selected site.
Consumer: global collision case of J.phaseFlags/compareExact. -/
theorem bankWindowOverlapInteriorComparisonCollisionSelected {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n) (k : Nat)
    (hk : 1 ≤ k)
    (hbelow : k < (compileAdvice (ceilLogTwo n)).b)
    (hx : ((bankWindowRootBefore ring seed pre).1 e).pack.val = k)
    (hy : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = k + 1)
    (hcr :
      ((bankWindowRootBefore ring seed pre).1 e).tok = .CR0 ∨
      ((bankWindowRootBefore ring seed pre).1 e).tok = .CR1)
    (htarget :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .AL ∨
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .CL0 ∨
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .CL1 ∨
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .CR0 ∨
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .CR1) :
    ((bankWindowRootAfter ring seed pre e).1 e).tok = .E ∧
    ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).tok = .E ∧
    (∀ z : Fin n,
      ((bankWindowRootAfter ring seed pre e).1 z).bit =
        ((bankWindowRootBefore ring seed pre).1 z).bit) ∧
    (∀ (o : RenewalBankOrigin n) (i : Fin n)
      (p : RenewalBankPayload n),
      (i = e ∨ i = ring.rightNeighbor e) →
      ¬ BankComparatorOriginWorker ring
        (bankWindowRootAfter ring seed pre e) o i p) := by
  have hphysical := bankWindowOverlapInteriorComparisonCollisionPhysical
    ((bankWindowRootBefore ring seed pre).1 e)
    ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e))
    k hk hbelow hx hy hcr htarget
  have htrip := bankWindowClosureSelectedBankTrip ring hn hbank
    (bankWindowRootBefore ring seed pre) e
  have hsourceTok := congrArg
    (fun t : Mode × Bool × BTok => t.2.2) htrip.1
  have htargetTok := congrArg
    (fun t : Mode × Bool × BTok => t.2.2) htrip.2
  have hsourceBit := congrArg
    (fun t : Mode × Bool × BTok => t.2.1) htrip.1
  have htargetBit := congrArg
    (fun t : Mode × Bool × BTok => t.2.1) htrip.2
  change ((bankWindowRootAfter ring seed pre e).1 e).tok =
    (Counter.resetBankOld
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).1.tok at hsourceTok
  change ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).tok =
    (Counter.resetBankOld
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).2.tok at htargetTok
  change ((bankWindowRootAfter ring seed pre e).1 e).bit =
    (Counter.resetBankOld
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).1.bit at hsourceBit
  change ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).bit =
    (Counter.resetBankOld
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).2.bit at htargetBit
  have hclearSource := hsourceTok.trans hphysical.1
  have hclearTarget := htargetTok.trans hphysical.2.1
  have hbits := bankWindowOverlapSelectedBitFrame ring
    (bankWindowRootBefore ring seed pre) e
    (hsourceBit.trans hphysical.2.2.1)
    (htargetBit.trans hphysical.2.2.2)
  have hworkers := bankWindowOverlapInteriorComparisonCollisionNoWorker
    ring hn seed pre e k hk hbelow hx hy hcr htarget
  refine ⟨hclearSource, hclearTarget, hbits, ?_⟩
  intro o i p hselected hcomp
  rcases hselected with hi | hi
  · have hworker :
        ((bankWindowRootAfter ring seed pre e).2.sites i).worker =
          .empty := by
      rw [hi]
      exact hworkers.1
    have hbad := hcomp.1
    rw [hworker] at hbad
    cases hbad
  · have hworker :
        ((bankWindowRootAfter ring seed pre e).2.sites i).worker =
          .empty := by
      rw [hi]
      exact hworkers.2
    have hbad := hcomp.1
    rw [hworker] at hbad
    cases hbad

/-- Erasing both selected tokens cannot introduce a new live
token at any origin digit. Every unselected token is exactly
the old token, so OLD only-token uniqueness transports to POST.
Consumer: surviving off-pair genuine comparison after collision. -/
theorem bankWindowOverlapOnlyTokenBothCleared {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n)
    (e root i : Fin n)
    (honly : bankWindowOnlyToken ring r root i)
    (hsource : ((renewalBankNext ring r e).1 e).tok = .E)
    (htarget : ((renewalBankNext ring r e).1
      (ring.rightNeighbor e)).tok = .E) :
    bankWindowOnlyToken ring (renewalBankNext ring r e) root i := by
  intro j hlive
  by_cases hsrc : Counter.site ring root (j.val + 1) = e
  · have hempty :
        ((renewalBankNext ring r e).1
          (Counter.site ring root (j.val + 1))).tok = .E := by
      rw [hsrc]
      exact hsource
    exact False.elim (hlive hempty)
  · by_cases hdst :
        Counter.site ring root (j.val + 1) = ring.rightNeighbor e
    · have hempty :
          ((renewalBankNext ring r e).1
            (Counter.site ring root (j.val + 1))).tok = .E := by
        rw [hdst]
        exact htarget
      exact False.elim (hlive hempty)
    · have hf := bankWindowExactOffPairFrame ring r e
        (Counter.site ring root (j.val + 1)) hsrc hdst
      have htok := congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
        hf.1
      have holdLive :
          (r.1 (Counter.site ring root (j.val + 1))).tok ≠ .E := by
        intro he
        exact hlive (htok.trans he)
      exact honly j holdLive

/-- Collision cannot change the true origin's comparison flags
or uncapped compareExact if its genuine worker survives at an
unselected site: the two overwritten tokens become E, every
origin digit bit is fixed, and worker, origin mode/controller,
and worker PACK are framed. The physical PACK stays aligned.
Consumer: the off-pair branch of global J.phaseFlags and
J.compareExact in a genuine CR0/CR1 collision. -/
theorem bankWindowOverlapInteriorComparisonCollisionOffPairFields
    {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n) (k : Nat)
    (hk : 1 ≤ k)
    (hbelow : k < (compileAdvice (ceilLogTwo n)).b)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hx : ((bankWindowRootBefore ring seed pre).1 e).pack.val = k)
    (hy : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = k + 1)
    (hcr :
      ((bankWindowRootBefore ring seed pre).1 e).tok = .CR0 ∨
      ((bankWindowRootBefore ring seed pre).1 e).tok = .CR1)
    (htarget :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .AL ∨
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .CL0 ∨
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .CL1 ∨
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .CR0 ∨
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .CR1)
    (o : RenewalBankOrigin n) (i : Fin n)
    (p : RenewalBankPayload n)
    (hforeign : o.root ≠ e ∧
      o.root ≠ ring.rightNeighbor e)
    (hfree : i ≠ e ∧ i ≠ ring.rightNeighbor e)
    (hcomp : BankComparatorOriginWorker ring
      (bankWindowRootAfter ring seed pre e) o i p)
    (hmode : ((bankWindowRootAfter ring seed pre e).1 o.root).mode =
      .CWAIT)
    (hcontroller :
      ((bankWindowRootAfter ring seed pre e).2.sites
        o.root).controller = .waiting []) :
    Counter.Complete ring
      (bankWindowRootAfter ring seed pre e).1 o.root ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankTrialLiveComparisonToken
        ((bankWindowRootAfter ring seed pre e).1
          (Counter.site ring o.root (j.val + 1))).tok →
      Counter.site ring o.root (j.val + 1) = i) ∧
    ((((bankWindowRootAfter ring seed pre e).1 i).tok = .CR1 →
      bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        ((bankWindowRootAfter ring seed pre e).1 i).pack.val) ∧
     (((bankWindowRootAfter ring seed pre e).1 i).tok = .CR0 →
      ¬ bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        ((bankWindowRootAfter ring seed pre e).1 i).pack.val) ∧
     (((bankWindowRootAfter ring seed pre e).1 i).tok = .CL1 →
      bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        (compileAdvice (ceilLogTwo n)).b) ∧
     (((bankWindowRootAfter ring seed pre e).1 i).tok = .CL0 →
      ¬ bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        (compileAdvice (ceilLogTwo n)).b)) ∧
    (bankWindowOnlyToken ring
      (bankWindowRootAfter ring seed pre e) o.root i ∧
     BankTrialLiveComparisonToken
       ((bankWindowRootAfter ring seed pre e).1 i).tok ∧
     p.heads = bankOriginBinaryValue ring
       (bankWindowRootAfter ring seed pre e).1 o ∧
     bankOriginBinaryValue ring
       (bankWindowRootAfter ring seed pre e).1 o ≤
         (compileAdvice (ceilLogTwo n)).K) := by
  have hselected := bankWindowOverlapInteriorComparisonCollisionSelected
    ring hn hbank seed pre e k hk hbelow hx hy hcr htarget
  have hfreeReads := bankWindowExactOffPairAtomicReads ring
    (bankWindowRootBefore ring seed pre) e i hfree.1 hfree.2
  have hrootReads := bankWindowExactOffPairAtomicReads ring
    (bankWindowRootBefore ring seed pre) e o.root
    hforeign.1 hforeign.2
  have hcompOld : BankComparatorOriginWorker ring
      (bankWindowRootBefore ring seed pre) o i p := by
    refine ⟨hfreeReads.2.2.2.2.2.1.symm.trans hcomp.1,
      hcomp.2.1, ?_⟩
    have ht := hcomp.2.2
    rw [hfreeReads.2.2.1] at ht
    exact ht
  have hmodeOld :
      ((bankWindowRootBefore ring seed pre).1 o.root).mode =
        .CWAIT :=
    hrootReads.2.1.symm.trans hmode
  have hcontrollerOld :
      ((bankWindowRootBefore ring seed pre).2.sites
        o.root).controller = .waiting [] :=
    hrootReads.2.2.2.2.2.2.symm.trans hcontroller
  have hbits : bankWindowReadDigitBits ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) o.root := by
    intro j
    exact hselected.2.2.1
      (Counter.site ring o.root (j.val + 1))
  have hflags := bankWindowPhaseFlagsReadTransport ring
    (bankWindowRootBefore ring seed pre)
    (bankWindowRootAfter ring seed pre e)
    o i p hJ
    ⟨⟨hfreeReads.2.2.1, hfreeReads.2.2.2.2.2.1,
      hrootReads.2.1⟩, hfreeReads.1, hbits⟩
    hcomp hmode
  have hcompleteOld := hJ.phaseComplete o i p
    hcompOld hmodeOld
  have hstable :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val := by
    rw [hx, hy]
    simp [packNext, hbelow]
  have hcompletePost :
      Counter.Complete ring
        (bankWindowRootAfter ring seed pre e).1 o.root := by
    intro t ht
    exact (bankWindowOverlapStablePackFrame
      ring hn seed pre e hstable
      (Counter.site ring o.root t)).trans (hcompleteOld t ht)
  have holdCompare := hJ.compareExact o i p
    hcompOld.1 hcompOld.2.1 hmodeOld hcontrollerOld
  have honlyPost := bankWindowOverlapOnlyTokenBothCleared
    ring (bankWindowRootBefore ring seed pre)
    e o.root i holdCompare.1 hselected.1 hselected.2.1
  have htokenPost := hcomp.2.2
  have hvalue := bankWindowOverlapComparatorBinaryBitTransport
    ring (bankWindowRootBefore ring seed pre)
    (bankWindowRootAfter ring seed pre e) o hbits
  have hunique :
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        BankTrialLiveComparisonToken
          ((bankWindowRootAfter ring seed pre e).1
            (Counter.site ring o.root (j.val + 1))).tok →
        Counter.site ring o.root (j.val + 1) = i := by
    intro j ht
    apply honlyPost j
    intro he
    rw [he] at ht
    simp [BankTrialLiveComparisonToken] at ht
  exact ⟨hcompletePost, hunique, hflags,
    honlyPost, htokenPost, holdCompare.2.2.1.trans hvalue.symm,
    by rw [hvalue]; exact holdCompare.2.2.2⟩

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

/--
All five genuine-origin comparator fields for an origin whose
entire BANK window and whose selected worker avoid the service
edge. No assumption about which of the twelve actual RBRow
constructors is selected: this result covers resetLaunch,
resetMove, zeroAccept, resetInheritedReturn, armedHead, carryMove,
compareMove, negativeReturn, timeout, eraseOrSanitize, success,
and frame, provided the two geometric disjointness facts hold.
The real post-step worker is used, rather than a post-J premise.
Consumer: bankWindowOverlapRootAllFields, off-window phase block.
-/
theorem bankWindowOverlapOutsideCurrentPhaseFields {n : Nat}
    (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (o : RenewalBankOrigin n) (i : Fin n)
    (p : RenewalBankPayload n)
    (houtside : Counter.OutsideSites (q := ceilLogTwo n)
      ring o.root e)
    (hfree : i ≠ e ∧ i ≠ ring.rightNeighbor e)
    (hworker : BankComparatorOriginWorker ring
      (bankWindowRootAfter ring seed pre e) o i p)
    (hmode :
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode =
        .CWAIT)
    (hcontroller :
      ((bankWindowRootAfter ring seed pre e).2.sites
        o.root).controller = .waiting []) :
    (((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠
        .ARMED ∧
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠
        .CSTART ∧
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠
        .IWAIT) ∧
    Counter.Complete ring
      (bankWindowRootAfter ring seed pre e).1 o.root ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankTrialLiveComparisonToken
        ((bankWindowRootAfter ring seed pre e).1
          (Counter.site ring o.root (j.val + 1))).tok →
      Counter.site ring o.root (j.val + 1) = i) ∧
    ((((bankWindowRootAfter ring seed pre e).1 i).tok = .CR1 →
      bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        ((bankWindowRootAfter ring seed pre e).1 i).pack.val) ∧
     (((bankWindowRootAfter ring seed pre e).1 i).tok = .CR0 →
      ¬ bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        ((bankWindowRootAfter ring seed pre e).1 i).pack.val) ∧
     (((bankWindowRootAfter ring seed pre e).1 i).tok = .CL1 →
      bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        (compileAdvice (ceilLogTwo n)).b) ∧
     (((bankWindowRootAfter ring seed pre e).1 i).tok = .CL0 →
      ¬ bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        (compileAdvice (ceilLogTwo n)).b)) ∧
    (bankWindowOnlyToken ring
      (bankWindowRootAfter ring seed pre e) o.root i ∧
      BankTrialLiveComparisonToken
        ((bankWindowRootAfter ring seed pre e).1 i).tok ∧
      p.heads = bankOriginBinaryValue ring
        (bankWindowRootAfter ring seed pre e).1 o ∧
      bankOriginBinaryValue ring
        (bankWindowRootAfter ring seed pre e).1 o ≤
        (compileAdvice (ceilLogTwo n)).K) := by
  have hfreeReads := bankWindowExactOffPairAtomicReads ring
    (bankWindowRootBefore ring seed pre) e i
    hfree.1 hfree.2
  have hrootOutside := houtside 0 (by omega)
  have hrootReads := bankWindowExactOffPairAtomicReads ring
    (bankWindowRootBefore ring seed pre) e o.root
    (by simpa only [Counter.site] using hrootOutside.1.symm)
    (by simpa only [Counter.site] using hrootOutside.2.symm)
  have hwindow := bankWindowExactOffWindowFrame ring
    (bankWindowRootBefore ring seed pre) o.root e houtside
  have hpack : bankWindowReadPackPrefix ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) o.root
      (compileAdvice (ceilLogTwo n)).b := by
    intro k hk
    exact congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
        a.pack.val) (hwindow k hk).1
  have htoks : bankWindowReadDigitTokens ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) o.root := by
    intro j
    have hj : j.val + 1 ≤
        (compileAdvice (ceilLogTwo n)).b := by
      have hb := j.isLt
      omega
    exact congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
        a.tok) (hwindow (j.val + 1) hj).1
  have hbits : bankWindowReadDigitBits ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) o.root := by
    intro j
    have hj : j.val + 1 ≤
        (compileAdvice (ceilLogTwo n)).b := by
      have hb := j.isLt
      omega
    exact congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
        a.bit) (hwindow (j.val + 1) hj).1
  have hphaseRead : bankWindowPhaseExcludesReadSet
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) o i p :=
    ⟨hfreeReads.2.2.1,
      hfreeReads.2.2.2.2.2.1,
      hrootReads.2.1⟩
  have hexcludes := bankWindowPhaseExcludesReadTransport ring
    (bankWindowRootBefore ring seed pre)
    (bankWindowRootAfter ring seed pre e)
    o i p hJ hphaseRead hworker
  have hcomplete := bankWindowPhaseCompleteReadTransport ring
    (bankWindowRootBefore ring seed pre)
    (bankWindowRootAfter ring seed pre e)
    o i p hJ ⟨hphaseRead, hpack⟩
    hworker hmode
  have hunique : ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankTrialLiveComparisonToken
        ((bankWindowRootAfter ring seed pre e).1
          (Counter.site ring o.root (j.val + 1))).tok →
      Counter.site ring o.root (j.val + 1) = i := by
    intro j ht
    exact bankWindowPhaseUniqueReadTransport ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e)
      o i p hJ ⟨hphaseRead, htoks⟩
      hworker hmode j ht
  have hflags := bankWindowPhaseFlagsReadTransport ring
    (bankWindowRootBefore ring seed pre)
    (bankWindowRootAfter ring seed pre e)
    o i p hJ ⟨hphaseRead, hfreeReads.1, hbits⟩
    hworker hmode
  have hcompare := bankWindowCompareExactReadTransport ring
    (bankWindowRootBefore ring seed pre)
    (bankWindowRootAfter ring seed pre e)
    o i p hJ
    ⟨hrootReads.2.1, hrootReads.2.2.2.2.2.2,
      hfreeReads.2.2.2.2.2.1,
      hfreeReads.2.2.1, htoks, hbits⟩
    hworker.1 hworker.2.1 hmode hcontroller
  exact ⟨hexcludes, hcomplete, hunique, hflags, hcompare⟩


/--
A genuine-origin POST worker must physically occupy one of its
origin's in-band digit sites, by the real extended rbRun ReceiptInv.
Consequently if its entire origin interval is disjoint from the
selected edge, that worker also avoids both selected endpoints.
This rules out an unframed worker without adding a location
assumption or a POST-J invariant.
Consumer: global phaseExcludes, phaseFlags and compareExact.
-/
theorem bankWindowOverlapOutsideGenuineWorkerOffPair {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e i : Fin n) (p : RenewalBankPayload n)
    (o : RenewalBankOrigin n)
    (houtside : Counter.OutsideSites (q := ceilLogTwo n)
      ring o.root e)
    (hworker :
      ((bankWindowRootAfter ring seed pre e).2.sites i).worker =
        .payload p)
    (horigin : p.origin = some o) :
    i ≠ e ∧ i ≠ ring.rightNeighbor e := by
  have hrun :
      rbRun ring (renewalBankStart ring seed) (pre ++ [e]) =
        bankWindowRootAfter ring seed pre e := by
    rw [rbRunAppend]
    rfl
  have hwordWorker :
      ((rbRun ring (renewalBankStart ring seed)
        (pre ++ [e])).2.sites i).worker = .payload p := by
    rw [hrun]
    exact hworker
  have hband := bankWindowOverlapGenuineWorkerInBand
    ring hn hbank seed (pre ++ [e]) i p o
    hwordWorker horigin
  rw [hrun] at hband
  have hsite := bankWindowIncomingPostWorkerAnchor
    ring hn hbank seed pre e i o p hworker
    horigin hband.1 hband.2
  have hoff := houtside
    ((bankWindowRootAfter ring seed pre e).1 i).pack.val hband.2
  constructor
  · intro hi
    have hselected : e = Counter.site ring o.root
        ((bankWindowRootAfter ring seed pre e).1 i).pack.val :=
      hi.symm.trans hsite
    exact hoff.1 hselected
  · intro hi
    have hselected : ring.rightNeighbor e =
        Counter.site ring o.root
          ((bankWindowRootAfter ring seed pre e).1 i).pack.val :=
      hi.symm.trans hsite
    exact hoff.2 hselected

/--
The exact five-field comparator package holds for every
POST genuine comparator rooted in an off-window origin. No
assumption about the free worker's location is made; it comes
from post-step ReceiptInv. This statement applies uniformly to
all twelve RBRow classes when the origin window avoids the
selected edge.
Consumer: global J phase and compareExact classification.
-/
theorem bankWindowOverlapOutsideOriginCurrentPhaseFields {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (o : RenewalBankOrigin n) (i : Fin n)
    (p : RenewalBankPayload n)
    (houtside : Counter.OutsideSites (q := ceilLogTwo n)
      ring o.root e)
    (hworker : BankComparatorOriginWorker ring
      (bankWindowRootAfter ring seed pre e) o i p)
    (hmode :
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode =
        .CWAIT)
    (hcontroller :
      ((bankWindowRootAfter ring seed pre e).2.sites
        o.root).controller = .waiting []) :
    (((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠
        .ARMED ∧
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠
        .CSTART ∧
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠
        .IWAIT) ∧
    Counter.Complete ring
      (bankWindowRootAfter ring seed pre e).1 o.root ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankTrialLiveComparisonToken
        ((bankWindowRootAfter ring seed pre e).1
          (Counter.site ring o.root (j.val + 1))).tok →
      Counter.site ring o.root (j.val + 1) = i) ∧
    ((((bankWindowRootAfter ring seed pre e).1 i).tok = .CR1 →
      bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        ((bankWindowRootAfter ring seed pre e).1 i).pack.val) ∧
     (((bankWindowRootAfter ring seed pre e).1 i).tok = .CR0 →
      ¬ bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        ((bankWindowRootAfter ring seed pre e).1 i).pack.val) ∧
     (((bankWindowRootAfter ring seed pre e).1 i).tok = .CL1 →
      bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        (compileAdvice (ceilLogTwo n)).b) ∧
     (((bankWindowRootAfter ring seed pre e).1 i).tok = .CL0 →
      ¬ bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        (compileAdvice (ceilLogTwo n)).b)) ∧
    (bankWindowOnlyToken ring
      (bankWindowRootAfter ring seed pre e) o.root i ∧
      BankTrialLiveComparisonToken
        ((bankWindowRootAfter ring seed pre e).1 i).tok ∧
      p.heads = bankOriginBinaryValue ring
        (bankWindowRootAfter ring seed pre e).1 o ∧
      bankOriginBinaryValue ring
        (bankWindowRootAfter ring seed pre e).1 o ≤
        (compileAdvice (ceilLogTwo n)).K) := by
  have hfree := bankWindowOverlapOutsideGenuineWorkerOffPair
    ring hn hbank seed pre e i p o
    houtside hworker.1 hworker.2.1
  exact bankWindowOverlapOutsideCurrentPhaseFields
    ring seed pre e hJ o i p
    houtside hfree hworker hmode hcontroller

/--
The phase-exclusion clause requires neither CWAIT nor an empty
waiting controller. A genuine comparator of an off-window
origin is framed at its real worker site and at its root;
OLD J excludes ARMED, CSTART and IWAIT, even on a frame row
whose classifier still performs private sanitation.
Consumer: global J.phaseExcludes, every RBRow case.
-/
theorem bankWindowOverlapOutsideOriginPhaseExcludes {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (o : RenewalBankOrigin n) (i : Fin n)
    (p : RenewalBankPayload n)
    (houtside : Counter.OutsideSites (q := ceilLogTwo n)
      ring o.root e)
    (hworker : BankComparatorOriginWorker ring
      (bankWindowRootAfter ring seed pre e) o i p) :
    ((bankWindowRootAfter ring seed pre e).1 o.root).mode
      ≠ .ARMED ∧
    ((bankWindowRootAfter ring seed pre e).1 o.root).mode
      ≠ .CSTART ∧
    ((bankWindowRootAfter ring seed pre e).1 o.root).mode
      ≠ .IWAIT := by
  have hfree := bankWindowOverlapOutsideGenuineWorkerOffPair
    ring hn hbank seed pre e i p o
    houtside hworker.1 hworker.2.1
  have hrootOutside := houtside 0 (by omega)
  have hrootReads := bankWindowExactOffPairAtomicReads ring
    (bankWindowRootBefore ring seed pre) e o.root
    (by simpa only [Counter.site] using hrootOutside.1.symm)
    (by simpa only [Counter.site] using hrootOutside.2.symm)
  have hfreeReads := bankWindowExactOffPairAtomicReads ring
    (bankWindowRootBefore ring seed pre) e i hfree.1 hfree.2
  exact bankWindowPhaseExcludesReadTransport ring
    (bankWindowRootBefore ring seed pre)
    (bankWindowRootAfter ring seed pre e)
    o i p hJ
    ⟨hfreeReads.2.2.1, hfreeReads.2.2.2.2.2.1,
      hrootReads.2.1⟩ hworker

/--
The global off-window owner package: inherited-clean taint
exclusion, both authentic IWAIT/CWAIT tainted-worker uniqueness
clauses, the full pending RR/RL resetWait front, and orphan
restriction. The entire prefix has seven atomic reads, even if
the selected RBRow is an erase-or-sanitize or waiting row.
Consumer: J.inheritedClean, J.iwaitTaintedUnique,
J.cwaitTaintedUnique, J.resetWait and J.orphan.
-/
theorem bankWindowOverlapOutsideTaintedOwnerFields {n : Nat}
    (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (houtside : Counter.OutsideSites (q := ceilLogTwo n)
      ring root e) :
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowScope ring
        (bankWindowRootAfter ring seed pre e) root →
      BankWindowInheritedController
        (bankWindowRootAfter ring seed pre e) root →
      ¬ BankWindowTainted
        (bankWindowRootAfter ring seed pre e)
        (Counter.site ring root (j.val + 1))) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowScope ring
        (bankWindowRootAfter ring seed pre e) root →
      ((bankWindowRootAfter ring seed pre e).1 root).mode =
        .IWAIT →
      ((bankWindowRootAfter ring seed pre e).2.sites
        root).controller = .waiting [] →
      BankWindowTainted
        (bankWindowRootAfter ring seed pre e)
        (Counter.site ring root (j.val + 1)) →
      ∃ o p,
        ((bankWindowRootAfter ring seed pre e).2.sites
          (Counter.site ring root (j.val + 1))).worker =
            .payload p ∧
        p.origin = some o ∧ o.root = root ∧
        bankWindowOnlyToken ring
          (bankWindowRootAfter ring seed pre e) root
          (Counter.site ring root (j.val + 1))) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowScope ring
        (bankWindowRootAfter ring seed pre e) root →
      ((bankWindowRootAfter ring seed pre e).1 root).mode =
        .CWAIT →
      ((bankWindowRootAfter ring seed pre e).2.sites
        root).controller = .waiting [] →
      BankWindowTainted
        (bankWindowRootAfter ring seed pre e)
        (Counter.site ring root (j.val + 1)) →
      ∃ o p,
        ((bankWindowRootAfter ring seed pre e).2.sites
          (Counter.site ring root (j.val + 1))).worker =
            .payload p ∧
        p.origin = some o ∧ o.root = root ∧
        BankTrialLiveComparisonToken
          ((bankWindowRootAfter ring seed pre e).1
            (Counter.site ring root (j.val + 1))).tok ∧
        bankWindowOnlyToken ring
          (bankWindowRootAfter ring seed pre e) root
          (Counter.site ring root (j.val + 1))) ∧
    (BankWindowScope ring
        (bankWindowRootAfter ring seed pre e) root →
      ((bankWindowRootAfter ring seed pre e).1 root).mode =
        .RWAIT →
      ((bankWindowRootAfter ring seed pre e).2.sites
        root).controller = .waiting [] →
      ∃ (j : Fin (compileAdvice (ceilLogTwo n)).b)
        (rho : RenewalBankReceipt n),
        ((bankWindowRootAfter ring seed pre e).2.sites
          (Counter.site ring root (j.val + 1))).worker =
            .pending rho ∧
        (((bankWindowRootAfter ring seed pre e).1
          (Counter.site ring root (j.val + 1))).tok = .RR ∨
         ((bankWindowRootAfter ring seed pre e).1
          (Counter.site ring root (j.val + 1))).tok = .RL) ∧
        bankWindowZeroPrefix ring
          (bankWindowRootAfter ring seed pre e) root (j.val + 1) ∧
        (∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
          k.val < j.val →
          ((bankWindowRootAfter ring seed pre e).1
            (Counter.site ring root (k.val + 1))).tok = .E) ∧
        (((bankWindowRootAfter ring seed pre e).1
          (Counter.site ring root (j.val + 1))).tok = .RL →
          bankWindowOnlyToken ring
            (bankWindowRootAfter ring seed pre e) root
            (Counter.site ring root (j.val + 1)) ∧
          bankWindowZeroPrefix ring
            (bankWindowRootAfter ring seed pre e)
            root (compileAdvice (ceilLogTwo n)).b)) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowOrphanOwner ring
        (bankWindowRootAfter ring seed pre e) root j →
      BankWindowTainted
        (bankWindowRootAfter ring seed pre e)
        (Counter.site ring root (j.val + 1)) →
      ((bankWindowRootAfter ring seed pre e).1 root).mode = .RESET ∨
      (((bankWindowRootAfter ring seed pre e).1 root).mode = .RWAIT ∧
        ((bankWindowRootAfter ring seed pre e).2.sites
          root).controller = .waiting [])) := by
  have hrootOutside := houtside 0 (by omega)
  have hrootReads := bankWindowExactOffPairAtomicReads ring
    (bankWindowRootBefore ring seed pre) e root
    (by simpa only [Counter.site] using hrootOutside.1.symm)
    (by simpa only [Counter.site] using hrootOutside.2.symm)
  have hwindow := bankWindowExactOffWindowFrame ring
    (bankWindowRootBefore ring seed pre) root e houtside
  have hpack : bankWindowReadPackPrefix ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) root
      (compileAdvice (ceilLogTwo n)).b := by
    intro k hk
    exact congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
        a.pack.val) (hwindow k hk).1
  have htoks : bankWindowReadDigitTokens ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) root := by
    intro j
    have hj : j.val + 1 ≤
        (compileAdvice (ceilLogTwo n)).b := by
      have hb := j.isLt
      omega
    exact congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
        a.tok) (hwindow (j.val + 1) hj).1
  have hbits : bankWindowReadDigitBits ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) root := by
    intro j
    have hj : j.val + 1 ≤
        (compileAdvice (ceilLogTwo n)).b := by
      have hb := j.isLt
      omega
    exact congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
        a.bit) (hwindow (j.val + 1) hj).1
  have hworkers :
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        bankWindowReadWorker
          (bankWindowRootBefore ring seed pre)
          (bankWindowRootAfter ring seed pre e)
          (Counter.site ring root (j.val + 1)) := by
    intro j
    have hj : j.val + 1 ≤
        (compileAdvice (ceilLogTwo n)).b := by
      have hb := j.isLt
      omega
    exact congrArg
      (fun a : RenewalBankSite n => a.worker)
      (hwindow (j.val + 1) hj).2
  have hgrant := hrootReads.2.2.2.2.1
  have hmode := hrootReads.2.1
  have hcontroller := hrootReads.2.2.2.2.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j hscope hinherited htainted
    exact bankWindowInheritedCleanReadTransport ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e)
      root j hJ
      ⟨hpack, hgrant, hcontroller, hworkers j⟩
      hscope hinherited htainted
  · intro j hscope hm hc htainted
    exact bankWindowIwaitTaintedUniqueReadTransport ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e)
      root j hJ
      ⟨hpack, hgrant, hmode, hcontroller, htoks, hworkers j⟩
      hscope hm hc htainted
  · intro j hscope hm hc htainted
    exact bankWindowCwaitTaintedUniqueReadTransport ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e)
      root j hJ
      ⟨hpack, hgrant, hmode, hcontroller, htoks, hworkers j⟩
      hscope hm hc htainted
  · intro hscope hm hc
    exact bankWindowResetWaitReadTransport ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e)
      root hJ
      ⟨hpack, hgrant, hmode, hcontroller,
        hbits, htoks, hworkers⟩
      hscope hm hc
  · intro j howner htainted
    have hj : j.val + 1 ≤
        (compileAdvice (ceilLogTwo n)).b := by
      have hb := j.isLt
      omega
    have hpShort : bankWindowReadPackPrefix ring
        (bankWindowRootBefore ring seed pre)
        (bankWindowRootAfter ring seed pre e)
        root (j.val + 1) := by
      intro k hk
      exact hpack k (by omega)
    exact bankWindowOrphanReadTransport ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e)
      root j hJ
      ⟨hpShort, hmode, hcontroller, hworkers j⟩
      howner htainted

/--
At an off-window complete root, a genuine POST active
controller retains the full ARMED/CSTART digit-token, exact
heads, and strict/non-strict K bounds from OLD J. Actual
POST ReceiptInv.activeRoot identifies the foreign origin
whose digit-bit interval must be read.
Consumer: J.armedExact in every disjoint RBRow branch.
-/
theorem bankWindowOverlapOutsideArmedExactField {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (houtside : Counter.OutsideSites (q := ceilLogTwo n)
      ring root e)
    (o : RenewalBankOrigin n) (p : RenewalBankPayload n)
    (hscope : BankWindowScope ring
      (bankWindowRootAfter ring seed pre e) root)
    (hphase :
      ((bankWindowRootAfter ring seed pre e).1 root).mode =
        .ARMED ∨
      ((bankWindowRootAfter ring seed pre e).1 root).mode =
        .CSTART)
    (hactive :
      ((bankWindowRootAfter ring seed pre e).2.sites
        root).controller = .active p)
    (horigin : p.origin = some o) :
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ((bankWindowRootAfter ring seed pre e).1
        (Counter.site ring root (j.val + 1))).tok = .E) ∧
    p.heads = bankOriginBinaryValue ring
      (bankWindowRootAfter ring seed pre e).1 o ∧
    (((bankWindowRootAfter ring seed pre e).1 root).mode =
        .ARMED →
      bankOriginBinaryValue ring
        (bankWindowRootAfter ring seed pre e).1 o <
        (compileAdvice (ceilLogTwo n)).K) ∧
    (((bankWindowRootAfter ring seed pre e).1 root).mode =
        .CSTART →
      bankOriginBinaryValue ring
        (bankWindowRootAfter ring seed pre e).1 o ≤
        (compileAdvice (ceilLogTwo n)).K) := by
  have hrootOrigin := (bankWindowOverlapPostReceipt
    ring hn hbank seed pre e).activeRoot
    root p o hactive horigin
  have hrootOutside := houtside 0 (by omega)
  have hrootReads := bankWindowExactOffPairAtomicReads ring
    (bankWindowRootBefore ring seed pre) e root
    (by simpa only [Counter.site] using hrootOutside.1.symm)
    (by simpa only [Counter.site] using hrootOutside.2.symm)
  have hwindow := bankWindowExactOffWindowFrame ring
    (bankWindowRootBefore ring seed pre) root e houtside
  have hpack : bankWindowReadPackPrefix ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) root
      (compileAdvice (ceilLogTwo n)).b := by
    intro k hk
    exact congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
        a.pack.val) (hwindow k hk).1
  have htoks : bankWindowReadDigitTokens ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) root := by
    intro j
    have hj : j.val + 1 ≤
        (compileAdvice (ceilLogTwo n)).b := by
      have hb := j.isLt
      omega
    exact congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
        a.tok) (hwindow (j.val + 1) hj).1
  have hbits : bankWindowReadDigitBits ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) root := by
    intro j
    have hj : j.val + 1 ≤
        (compileAdvice (ceilLogTwo n)).b := by
      have hb := j.isLt
      omega
    exact congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
        a.bit) (hwindow (j.val + 1) hj).1
  have hbitsOrigin : bankWindowReadDigitBits ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) o.root := by
    rw [← hrootOrigin]
    exact hbits
  exact bankWindowArmedExactReadTransport ring
    (bankWindowRootBefore ring seed pre)
    (bankWindowRootAfter ring seed pre e)
    root o p hJ
    ⟨hpack, hrootReads.2.2.2.2.1,
      hrootReads.2.1,
      hrootReads.2.2.2.2.2.2, htoks, hbitsOrigin⟩
    hscope hphase hactive horigin

/--
At an off-window IWAIT root every POST genuinely originated
worker belonging to that root is an actual digit carrier, so
its role, token and ghost slot are framed too. The uncapped
IR/AL increment credit and only-token facts follow from OLD J
without an independently assumed worker location.
Consumer: J.incrementExact in every disjoint RBRow branch.
-/
theorem bankWindowOverlapOutsideIncrementExactField {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (houtside : Counter.OutsideSites (q := ceilLogTwo n)
      ring root e)
    (o : RenewalBankOrigin n) (i : Fin n)
    (p : RenewalBankPayload n)
    (hscope : BankWindowScope ring
      (bankWindowRootAfter ring seed pre e) root)
    (hmode :
      ((bankWindowRootAfter ring seed pre e).1 root).mode =
        .IWAIT)
    (hcontroller :
      ((bankWindowRootAfter ring seed pre e).2.sites
        root).controller = .waiting [])
    (hworker :
      ((bankWindowRootAfter ring seed pre e).2.sites i).worker =
        .payload p)
    (horigin : p.origin = some o)
    (horoot : o.root = root) :
    bankWindowOnlyToken ring
      (bankWindowRootAfter ring seed pre e) root i ∧
    (((((bankWindowRootAfter ring seed pre e).1 i).tok = .IR ∧
       bankWindowZeroPrefix ring
         (bankWindowRootAfter ring seed pre e)
         root
         ((bankWindowRootAfter ring seed pre e).1 i).pack.val ∧
       p.heads = bankOriginBinaryValue ring
         (bankWindowRootAfter ring seed pre e).1 o +
         2 ^ ((bankWindowRootAfter ring seed pre e).1 i).pack.val ∧
       bankOriginBinaryValue ring
         (bankWindowRootAfter ring seed pre e).1 o +
         2 ^ ((bankWindowRootAfter ring seed pre e).1 i).pack.val ≤
           (compileAdvice (ceilLogTwo n)).K) ∨
      (((bankWindowRootAfter ring seed pre e).1 i).tok = .AL ∧
       p.heads = bankOriginBinaryValue ring
         (bankWindowRootAfter ring seed pre e).1 o ∧
       bankOriginBinaryValue ring
         (bankWindowRootAfter ring seed pre e).1 o ≤
           (compileAdvice (ceilLogTwo n)).K))) := by
  have houtsideOrigin : Counter.OutsideSites
      (q := ceilLogTwo n) ring o.root e := by
    rw [horoot]
    exact houtside
  have hfree := bankWindowOverlapOutsideGenuineWorkerOffPair
    ring hn hbank seed pre e i p o
    houtsideOrigin hworker horigin
  have hworkerReads := bankWindowExactOffPairAtomicReads ring
    (bankWindowRootBefore ring seed pre) e i hfree.1 hfree.2
  have hrootOutside := houtside 0 (by omega)
  have hrootReads := bankWindowExactOffPairAtomicReads ring
    (bankWindowRootBefore ring seed pre) e root
    (by simpa only [Counter.site] using hrootOutside.1.symm)
    (by simpa only [Counter.site] using hrootOutside.2.symm)
  have hwindow := bankWindowExactOffWindowFrame ring
    (bankWindowRootBefore ring seed pre) root e houtside
  have hpack : bankWindowReadPackPrefix ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) root
      (compileAdvice (ceilLogTwo n)).b := by
    intro k hk
    exact congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
        a.pack.val) (hwindow k hk).1
  have htoks : bankWindowReadDigitTokens ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) root := by
    intro j
    have hj : j.val + 1 ≤
        (compileAdvice (ceilLogTwo n)).b := by
      have hb := j.isLt
      omega
    exact congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
        a.tok) (hwindow (j.val + 1) hj).1
  have hbits : bankWindowReadDigitBits ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) root := by
    intro j
    have hj : j.val + 1 ≤
        (compileAdvice (ceilLogTwo n)).b := by
      have hb := j.isLt
      omega
    exact congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
        a.bit) (hwindow (j.val + 1) hj).1
  have hbitsOrigin : bankWindowReadDigitBits ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) o.root := by
    rw [horoot]
    exact hbits
  exact bankWindowIncrementExactReadTransport ring
    (bankWindowRootBefore ring seed pre)
    (bankWindowRootAfter ring seed pre e)
    root o i p hJ
    ⟨hpack, hrootReads.2.2.2.2.1,
      hrootReads.2.1,
      hrootReads.2.2.2.2.2.2,
      hworkerReads.2.2.2.2.2.1,
      hworkerReads.1, hworkerReads.2.2.1,
      htoks, hbits, hbitsOrigin⟩
    hscope hmode hcontroller hworker horigin horoot

/--
For a genuine comparator whose root differs from both endpoints
of a source PACK-zero service, the old J and actual renewal
step establish all comparator phase fields and compareExact.
This is valid for every root-source BANK mode/return subrow:
RESET launch, RWAIT pending acceptance or inherited return,
ARMED head, IWAIT carry return, CSTART compare launch,
CWAIT negative/success return, timeout, and sanitation.
Consumer: the root-source part of global phase assembly.
-/
theorem bankWindowOverlapRootSourceForeignCurrentPhaseFields {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hx : ((bankWindowRootBefore ring seed pre).1 e).pack.val =
      0)
    (o : RenewalBankOrigin n) (i : Fin n)
    (p : RenewalBankPayload n)
    (hforeign : o.root ≠ e ∧
      o.root ≠ ring.rightNeighbor e)
    (hworker : BankComparatorOriginWorker ring
      (bankWindowRootAfter ring seed pre e) o i p)
    (hmode : ((bankWindowRootAfter ring seed pre e).1
      o.root).mode = .CWAIT)
    (hcontroller : ((bankWindowRootAfter ring seed pre e).2.sites
      o.root).controller = .waiting []) :
    (((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠
        .ARMED ∧
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠
        .CSTART ∧
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠
        .IWAIT) ∧
    Counter.Complete ring
      (bankWindowRootAfter ring seed pre e).1 o.root ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankTrialLiveComparisonToken
        ((bankWindowRootAfter ring seed pre e).1
          (Counter.site ring o.root (j.val + 1))).tok →
      Counter.site ring o.root (j.val + 1) = i) ∧
    ((((bankWindowRootAfter ring seed pre e).1 i).tok = .CR1 →
      bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        ((bankWindowRootAfter ring seed pre e).1 i).pack.val) ∧
     (((bankWindowRootAfter ring seed pre e).1 i).tok = .CR0 →
      ¬ bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        ((bankWindowRootAfter ring seed pre e).1 i).pack.val) ∧
     (((bankWindowRootAfter ring seed pre e).1 i).tok = .CL1 →
      bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        (compileAdvice (ceilLogTwo n)).b) ∧
     (((bankWindowRootAfter ring seed pre e).1 i).tok = .CL0 →
      ¬ bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        (compileAdvice (ceilLogTwo n)).b)) ∧
    (bankWindowOnlyToken ring
      (bankWindowRootAfter ring seed pre e) o.root i ∧
      BankTrialLiveComparisonToken
        ((bankWindowRootAfter ring seed pre e).1 i).tok ∧
      p.heads = bankOriginBinaryValue ring
        (bankWindowRootAfter ring seed pre e).1 o ∧
      bankOriginBinaryValue ring
        (bankWindowRootAfter ring seed pre e).1 o ≤
        (compileAdvice (ceilLogTwo n)).K) := by
  have hphase := bankWindowRootForeignPhaseExcludesOnSource
    ring hn hbank seed pre e hJ hx o i p hforeign hworker
  have hmain := bankWindowRootForeignComparatorStep
    ring hn hbank seed pre e hJ hx
    o i p hforeign hworker hmode
  have hcompare := bankWindowRootForeignCompareExactOnSource
    ring hn hbank seed pre e hJ hx
    o i p hforeign hworker.1 hworker.2.1
    hmode hcontroller
  exact ⟨hphase, hmain.1, hmain.2.1, hmain.2.2, hcompare⟩

/--
A genuine comparator rooted in a continuing incoming
PACK-zero CWAIT responder has every phase field, not only
the four flags. This uses its real post-step source exclusion,
the OLD CWAIT lease row, and the previously checked incoming
worker/read-set package. The grant-free hypothesis is a literal
old BANK row guard, not a post-J premise.
Consumer: the incoming CWAIT branch of global J phase assembly.
-/
theorem bankWindowOverlapIncomingCurrentPhaseFields {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hy : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = 0)
    (hpost : ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).pack.val = 0)
    (hgrant : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).grant = false)
    (hmodeOld : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).mode = .CWAIT)
    (hmode : ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).mode = .CWAIT)
    (o : RenewalBankOrigin n) (i : Fin n)
    (p : RenewalBankPayload n)
    (hroot : o.root = ring.rightNeighbor e)
    (hworker : BankComparatorOriginWorker ring
      (bankWindowRootAfter ring seed pre e) o i p)
    (hcontroller :
      ((bankWindowRootAfter ring seed pre e).2.sites
        o.root).controller = .waiting []) :
    (((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠
        .ARMED ∧
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠
        .CSTART ∧
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠
        .IWAIT) ∧
    Counter.Complete ring
      (bankWindowRootAfter ring seed pre e).1 o.root ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankTrialLiveComparisonToken
        ((bankWindowRootAfter ring seed pre e).1
          (Counter.site ring o.root (j.val + 1))).tok →
      Counter.site ring o.root (j.val + 1) = i) ∧
    ((((bankWindowRootAfter ring seed pre e).1 i).tok = .CR1 →
      bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        ((bankWindowRootAfter ring seed pre e).1 i).pack.val) ∧
     (((bankWindowRootAfter ring seed pre e).1 i).tok = .CR0 →
      ¬ bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        ((bankWindowRootAfter ring seed pre e).1 i).pack.val) ∧
     (((bankWindowRootAfter ring seed pre e).1 i).tok = .CL1 →
      bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        (compileAdvice (ceilLogTwo n)).b) ∧
     (((bankWindowRootAfter ring seed pre e).1 i).tok = .CL0 →
      ¬ bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        (compileAdvice (ceilLogTwo n)).b)) ∧
    (bankWindowOnlyToken ring
      (bankWindowRootAfter ring seed pre e) o.root i ∧
      BankTrialLiveComparisonToken
        ((bankWindowRootAfter ring seed pre e).1 i).tok ∧
      p.heads = bankOriginBinaryValue ring
        (bankWindowRootAfter ring seed pre e).1 o ∧
      bankOriginBinaryValue ring
        (bankWindowRootAfter ring seed pre e).1 o ≤
        (compileAdvice (ceilLogTwo n)).K) := by
  have hpart := bankWindowOverlapIncomingCurrentComparisonFields
    ring hn hbank seed pre e hJ hy hpost
    hgrant hmodeOld hmode o i p hroot hworker hcontroller
  have hmodeAtRoot :
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode =
        .CWAIT := by
    rw [hroot]
    exact hmode
  have hexcludes :
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠
        .ARMED ∧
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠
        .CSTART ∧
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠
        .IWAIT := by
    rw [hmodeAtRoot]
    refine ⟨?_, ?_, ?_⟩
    · intro h
      cases h
    · intro h
      cases h
    · intro h
      cases h
  exact ⟨hexcludes, hpart.1, hpart.2.1,
    hpart.2.2.1, hpart.2.2.2⟩

/--
The phaseExcludes premise is unconditional in the owner's
mode, while phaseComplete, phaseUnique and phaseFlags depend
only on CWAIT, not on a waiting-controller hypothesis. This
is the uniform disjoint-interval branch for all twelve real
RBRow constructors, with genuine-worker provenance eliminating
any extra off-pair premise.
Consumer: the global J.phaseExcludes/phaseComplete/
phaseUnique/phaseFlags fields.
-/
theorem bankWindowOverlapOutsideOriginPhasePackage {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (o : RenewalBankOrigin n) (i : Fin n)
    (p : RenewalBankPayload n)
    (houtside : Counter.OutsideSites (q := ceilLogTwo n)
      ring o.root e)
    (hworker : BankComparatorOriginWorker ring
      (bankWindowRootAfter ring seed pre e) o i p) :
    (((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠
        .ARMED ∧
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠
        .CSTART ∧
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠
        .IWAIT) ∧
    (((bankWindowRootAfter ring seed pre e).1 o.root).mode =
        .CWAIT →
      Counter.Complete ring
        (bankWindowRootAfter ring seed pre e).1 o.root ∧
      (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        BankTrialLiveComparisonToken
          ((bankWindowRootAfter ring seed pre e).1
            (Counter.site ring o.root (j.val + 1))).tok →
        Counter.site ring o.root (j.val + 1) = i) ∧
      ((((bankWindowRootAfter ring seed pre e).1 i).tok = .CR1 →
        bankComparatorPrefixMatched ring
          (bankWindowRootAfter ring seed pre e) o
          ((bankWindowRootAfter ring seed pre e).1 i).pack.val) ∧
       (((bankWindowRootAfter ring seed pre e).1 i).tok = .CR0 →
        ¬ bankComparatorPrefixMatched ring
          (bankWindowRootAfter ring seed pre e) o
          ((bankWindowRootAfter ring seed pre e).1 i).pack.val) ∧
       (((bankWindowRootAfter ring seed pre e).1 i).tok = .CL1 →
        bankComparatorPrefixMatched ring
          (bankWindowRootAfter ring seed pre e) o
          (compileAdvice (ceilLogTwo n)).b) ∧
       (((bankWindowRootAfter ring seed pre e).1 i).tok = .CL0 →
        ¬ bankComparatorPrefixMatched ring
          (bankWindowRootAfter ring seed pre e) o
          (compileAdvice (ceilLogTwo n)).b))) := by
  have hfree := bankWindowOverlapOutsideGenuineWorkerOffPair
    ring hn hbank seed pre e i p o
    houtside hworker.1 hworker.2.1
  have hrootOutside := houtside 0 (by omega)
  have hforeign : o.root ≠ e ∧
      o.root ≠ ring.rightNeighbor e := by
    constructor
    · simpa only [Counter.site] using hrootOutside.1.symm
    · simpa only [Counter.site] using hrootOutside.2.symm
  have hexcludes := bankWindowOverlapOutsideOriginPhaseExcludes
    ring hn hbank seed pre e hJ o i p houtside hworker
  refine ⟨hexcludes, ?_⟩
  intro hmode
  exact bankWindowOverlapForeignComparisonOffWindow
    ring hn seed pre e hJ o i p hforeign hfree
    houtside hworker hmode

/--
An off-window foreign root cannot gain a new first-mismatch
proto obligation at a selected BANK edge: the first bad site
of any POST proto-run has index at most b, so every PACK,
token, bit, worker and root-controller read is unchanged.
This is a real-step statement and does not assume the
stable-interior producer or a post-J hypothesis.
Consumer: PFX/PROTO item 5 in the disjoint geometry branch.
-/
theorem bankWindowOverlapOutsideProtoField {n : Nat}
    (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (houtside : Counter.OutsideSites (q := ceilLogTwo n)
      ring root e)
    (limit : Nat)
    (hproto : BankWindowProtoRun ring
      (bankWindowRootAfter ring seed pre e) root limit) :
    BankWindowRootForeignProtoField ring
      (bankWindowRootAfter ring seed pre e) root limit := by
  have hrootOutside := houtside 0 (by omega)
  have hroot : root ≠ e ∧
      root ≠ ring.rightNeighbor e := by
    constructor
    · simpa only [Counter.site] using hrootOutside.1.symm
    · simpa only [Counter.site] using hrootOutside.2.symm
  have hpackAvoid :
      ∀ k : Nat, k ≤ limit + 1 →
        Counter.site ring root k ≠ e ∧
        Counter.site ring root k ≠ ring.rightNeighbor e := by
    intro k hk
    have hbound : k ≤
        (compileAdvice (ceilLogTwo n)).b := by
      have hlimit := hproto.1
      omega
    have hf := houtside k hbound
    exact ⟨hf.1.symm, hf.2.symm⟩
  have hprefixAvoid :
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        j.val + 1 ≤ limit →
        Counter.site ring root (j.val + 1) ≠ e ∧
        Counter.site ring root (j.val + 1) ≠
          ring.rightNeighbor e := by
    intro j hj
    exact hpackAvoid (j.val + 1) (by omega)
  exact bankWindowExactDisjointProtoStep ring
    (bankWindowRootBefore ring seed pre) e root limit
    hJ hroot hpackAvoid hprefixAvoid hproto


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

/--
The authentic BANK CSTART first-digit issue. The apparent
isRetTok E = true branch in the repair log is impossible:
isRetTok E reduces to false before CSTART is dispatched.
The source therefore becomes CWAIT and emits CR1 or CR0,
while the two bit fields remain fixed.
Consumer: selected source root in J.phaseFlags/compareExact.
-/
theorem bankWindowOverlapCstartComparatorIssueCell
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hb : 1 ≤ b)
    (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false)
    (hm : x.mode = .CSTART)
    (ht : y.tok = .E) :
    (bankPair x y 1 b theta).1.mode = .CWAIT ∧
    (bankPair x y 1 b theta).1.tok = .E ∧
    (bankPair x y 1 b theta).2.tok =
      (if y.bit = theta 0 then .CR1 else .CR0) ∧
    (bankPair x y 1 b theta).1.bit = x.bit ∧
    (bankPair x y 1 b theta).2.bit = y.bit := by
  have hreturn : isRetTok BTok.E = false := rfl
  by_cases hbit : y.bit = theta 0
  · simp [bankPair, hx, hy, hg, hm, ht, hb, hbit,
      isRetTok, isWaitMode, hreturn, Id.run_pure, Id.run_bind] <;>
        repeat (first | rfl | split)
  · simp [bankPair, hx, hy, hg, hm, ht, hb, hbit,
      isRetTok, isWaitMode, hreturn, Id.run_pure, Id.run_bind] <;>
        repeat (first | rfl | split)

/--
Physical projections of the actual masked BANK CSTART issue.
The role equation is solved from positive b, not by opening a
spurious b=0 case; the returned BankCell bit/token fields are
normalized explicitly to the underlying Agent fields.
Consumer: genuinely issued CR phaseFlags and compareExact.
-/
theorem bankWindowOverlapRootCstartComparatorIssuePhysical
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hx : ((bankWindowRootBefore ring seed pre).1 e).pack.val = 0)
    (hy : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = 1)
    (hg : ((bankWindowRootBefore ring seed pre).1 e).grant = false)
    (hm : ((bankWindowRootBefore ring seed pre).1 e).mode = .CSTART)
    (ht : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).tok = .E) :
    ((bankWindowRootAfter ring seed pre e).1 e).mode = .CWAIT ∧
    ((bankWindowRootAfter ring seed pre e).1 e).tok = .E ∧
    ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).tok =
        (if ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).bit =
          (compileAdvice (ceilLogTwo n)).theta 0
         then .CR1 else .CR0) ∧
    ((bankWindowRootAfter ring seed pre e).1 e).bit =
      ((bankWindowRootBefore ring seed pre).1 e).bit ∧
    ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).bit =
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).bit := by
  have hb : 1 ≤ (compileAdvice (ceilLogTwo n)).b := by
    change 1 ≤ (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hpositive : 0 < (compileAdvice (ceilLogTwo n)).b := by
    omega
  have hpackNext :
      packNext 0 1 (compileAdvice (ceilLogTwo n)).b = 1 := by
    simp [packNext, hpositive]
  have hraw := bankWindowOverlapCstartComparatorIssueCell
    (bankCell ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1 e).pack.val)
    (bankCell ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val)
    (compileAdvice (ceilLogTwo n)).b
    (compileAdvice (ceilLogTwo n)).theta hb
    (by change ((bankWindowRootBefore ring seed pre).1 e).pack.val =
      0; exact hx)
    (by change ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = 1; exact hy)
    (by change ((bankWindowRootBefore ring seed pre).1 e).grant =
      false; exact hg)
    (by change ((bankWindowRootBefore ring seed pre).1 e).mode =
      .CSTART; exact hm)
    (by change ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).tok = .E; exact ht)
  have htriple := bankWindowClosureSelectedBankTrip
    ring hn hbank (bankWindowRootBefore ring seed pre) e
  have hmode := congrArg
    (fun t : Mode × Bool × BTok => t.1) htriple.1
  have hsourceTok := congrArg
    (fun t : Mode × Bool × BTok => t.2.2) htriple.1
  have htargetTok := congrArg
    (fun t : Mode × Bool × BTok => t.2.2) htriple.2
  have hsourceBit := congrArg
    (fun t : Mode × Bool × BTok => t.2.1) htriple.1
  have htargetBit := congrArg
    (fun t : Mode × Bool × BTok => t.2.1) htriple.2
  have hrawMode :
      (Counter.resetBankOld
        ((bankWindowRootBefore ring seed pre).1 e)
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e))).1.mode = .CWAIT := by
    simpa only [Counter.resetBankOld, hx, hy, hpackNext]
      using hraw.1
  have hrawSource :
      (Counter.resetBankOld
        ((bankWindowRootBefore ring seed pre).1 e)
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e))).1.tok = .E := by
    simpa only [Counter.resetBankOld, hx, hy, hpackNext]
      using hraw.2.1
  have hrawTarget :
      (Counter.resetBankOld
        ((bankWindowRootBefore ring seed pre).1 e)
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e))).2.tok =
          (if ((bankWindowRootBefore ring seed pre).1
            (ring.rightNeighbor e)).bit =
              (compileAdvice (ceilLogTwo n)).theta 0
           then .CR1 else .CR0) := by
    simpa only [Counter.resetBankOld, hx, hy, hpackNext,
      bankCell] using hraw.2.2.1
  have hrawSourceBit :
      (Counter.resetBankOld
        ((bankWindowRootBefore ring seed pre).1 e)
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e))).1.bit =
          ((bankWindowRootBefore ring seed pre).1 e).bit := by
    simpa only [Counter.resetBankOld, hx, hy, hpackNext,
      bankCell] using hraw.2.2.2.1
  have hrawTargetBit :
      (Counter.resetBankOld
        ((bankWindowRootBefore ring seed pre).1 e)
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e))).2.bit =
          ((bankWindowRootBefore ring seed pre).1
            (ring.rightNeighbor e)).bit := by
    simpa only [Counter.resetBankOld, hx, hy, hpackNext,
      bankCell] using hraw.2.2.2.2
  change ((bankWindowRootAfter ring seed pre e).1 e).mode =
    (Counter.resetBankOld
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).1.mode at hmode
  change ((bankWindowRootAfter ring seed pre e).1 e).tok =
    (Counter.resetBankOld
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).1.tok at hsourceTok
  change ((bankWindowRootAfter ring seed pre e).1
    (ring.rightNeighbor e)).tok =
    (Counter.resetBankOld
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).2.tok at htargetTok
  change ((bankWindowRootAfter ring seed pre e).1 e).bit =
    (Counter.resetBankOld
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).1.bit at hsourceBit
  change ((bankWindowRootAfter ring seed pre e).1
    (ring.rightNeighbor e)).bit =
    (Counter.resetBankOld
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).2.bit at htargetBit
  exact ⟨hmode.trans hrawMode,
    hsourceTok.trans hrawSource,
    htargetTok.trans hrawTarget,
    hsourceBit.trans hrawSourceBit,
    htargetBit.trans hrawTargetBit⟩

/--
Source-root CSTART issuance from the actual pair and OLD J.
The post controller and worker are from the ghost source row;
the comparison token is from the independent physical row.
The origin is the actual old active controller's root.
Consumer: new comparator CWAIT / phase flags / compareExact.
-/
theorem bankWindowOverlapRootCstartIssuedComparatorCore {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hscope : BankWindowScope ring
      (bankWindowRootBefore ring seed pre) e)
    (hmode :
      ((bankWindowRootBefore ring seed pre).1 e).mode = .CSTART)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hactive :
      ((bankWindowRootBefore ring seed pre).2.sites e).controller =
        .active p)
    (horigin : p.origin = some o) :
    Counter.Complete ring
      (bankWindowRootAfter ring seed pre e).1 e ∧
    ((bankWindowRootAfter ring seed pre e).1 e).mode = .CWAIT ∧
    ((bankWindowRootAfter ring seed pre e).2.sites e).controller =
      .waiting [] ∧
    ((bankWindowRootAfter ring seed pre e).2.sites
      (ring.rightNeighbor e)).worker = .payload p ∧
    p.origin = some o ∧
    o.root = e ∧
    ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).tok =
      (if ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).bit =
          (compileAdvice (ceilLogTwo n)).theta 0
       then .CR1 else .CR0) ∧
    p.heads = bankOriginBinaryValue ring
      (bankWindowRootAfter ring seed pre e).1 o ∧
    (∀ z : Fin n,
      ((bankWindowRootAfter ring seed pre e).1 z).bit =
        ((bankWindowRootBefore ring seed pre).1 z).bit) := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hx :
      ((bankWindowRootBefore ring seed pre).1 e).pack.val =
        0 := by
    change ((bankWindowRootBefore ring seed pre).1
      (Counter.site ring e 0)).pack.val = 0
    exact hscope.1 0 (by omega)
  have hy :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val = 1 := by
    change ((bankWindowRootBefore ring seed pre).1
      (Counter.site ring e 1)).pack.val = 1
    exact hscope.1 1 (by omega)
  have htoken :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .E := by
    have hread := (hJ.armedExact e o p hscope
      (Or.inr hmode) hactive horigin).1
      (⟨0, hb⟩ :
        Fin (compileAdvice (ceilLogTwo n)).b)
    change ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).tok = .E at hread
    exact hread
  have hphysical :=
    bankWindowOverlapRootCstartComparatorIssuePhysical
      ring hn hbank seed pre e hx hy hscope.2 hmode htoken
  have hissue := bankWindowClosureCstartIssueGenuine
    ring hn (bankWindowRootBefore ring seed pre)
    e hJ hscope hmode p o hactive horigin
  have hreceiptOld := rbReceiptInvBankWordOfInv ring
    (by omega : 2 ≤ n) seed hbank pre
  have hroot : o.root = e :=
    (hreceiptOld.activeRoot e p o hactive horigin).symm
  have hbitsGlobal := bankWindowOverlapSelectedBitFrame
    ring (bankWindowRootBefore ring seed pre) e
    hphysical.2.2.2.1 hphysical.2.2.2.2
  have hbits : bankWindowReadDigitBits ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) o.root := by
    intro j
    exact hbitsGlobal (Counter.site ring o.root (j.val + 1))
  have hvalue := bankWindowOverlapComparatorBinaryBitTransport
    ring (bankWindowRootBefore ring seed pre)
    (bankWindowRootAfter ring seed pre e) o hbits
  have hheads :
      p.heads = bankOriginBinaryValue ring
        (bankWindowRootAfter ring seed pre e).1 o :=
    hissue.2.2.2.2.1.trans hvalue.symm
  exact ⟨hissue.1, hphysical.1, hissue.2.1,
    hissue.2.2.1, hissue.2.2.2.1, hroot,
    hphysical.2.2.1, hheads, hbitsGlobal⟩


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
/--
The newly issued genuine comparator at a CSTART root owns the
only nonempty token of that root's digit window. OLD J.armedExact
makes every digit token E, the physical BANK row changes only
the selected first digit, and other digits are genuinely off
both selected endpoints by BANK spatial geometry.
Consumer: source-root CSTART compareExact and phaseUnique.
-/
theorem bankWindowOverlapRootCstartIssuedOnlyToken {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hscope : BankWindowScope ring
      (bankWindowRootBefore ring seed pre) e)
    (hmode :
      ((bankWindowRootBefore ring seed pre).1 e).mode = .CSTART)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hactive :
      ((bankWindowRootBefore ring seed pre).2.sites e).controller =
        .active p)
    (horigin : p.origin = some o) :
    bankWindowOnlyToken ring
      (bankWindowRootAfter ring seed pre e)
      o.root (ring.rightNeighbor e) := by
  have hcore := bankWindowOverlapRootCstartIssuedComparatorCore
    ring hn hbank seed pre e hJ hscope hmode p o hactive horigin
  obtain ⟨_, _, _, _, _, hroot, _, _, _⟩ := hcore
  have holdTokens := (hJ.armedExact e o p hscope
    (Or.inr hmode) hactive horigin).1
  intro j hnonempty
  by_cases hfirst : j.val = 0
  · have hsite :
        Counter.site ring o.root (j.val + 1) =
          ring.rightNeighbor e := by
      rw [hroot, hfirst]
      rfl
    exact hsite
  · have hj : j.val + 1 ≤
        (compileAdvice (ceilLogTwo n)).b := by
      have hbound := j.isLt
      omega
    have hsource :
        Counter.site ring o.root (j.val + 1) ≠ e := by
      rw [hroot]
      -- Counter.site at zero is definitionally the root
      -- (Leader/L3/Bank/Counter.lean, definition Counter.site).
      have hzero : Counter.site ring e 0 = e := rfl
      simpa only [hzero] using
        (bankWindowIncidenceSiteDistinct ring hbank
          e 0 (j.val + 1) (by omega) (by omega)).symm
    have htarget :
        Counter.site ring o.root (j.val + 1) ≠
          ring.rightNeighbor e := by
      rw [hroot]
      change
        Counter.site ring e (j.val + 1) ≠
          Counter.site ring e 1
      exact (bankWindowIncidenceSiteDistinct ring hbank
        e 1 (j.val + 1) (by omega) (by omega)).symm
    have hframe := (bankWindowExactOffPairFrame ring
      (bankWindowRootBefore ring seed pre)
      e (Counter.site ring o.root (j.val + 1))
      hsource htarget).1
    have ht := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
      hframe
    have htokenOld :
        ((bankWindowRootBefore ring seed pre).1
          (Counter.site ring o.root (j.val + 1))).tok = .E := by
      rw [hroot]
      exact holdTokens j
    have htokenPost :
        ((bankWindowRootAfter ring seed pre e).1
          (Counter.site ring o.root (j.val + 1))).tok = .E :=
      ht.trans htokenOld
    exact False.elim (hnonempty htokenPost)

/--
The newly issued CSTART comparator satisfies the exact
POST selected-origin phase obligations from OLD J, ReceiptInv,
the physical BANK comparison row, and its real ghost payload.
In particular, CR1 certifies the first bit agreement, CR0 its
negation, and the dormant CL0/CL1 flags are contradictory.
Consumer: source-root comparator-birth branch of R11 group 13.
-/
theorem bankWindowOverlapRootCstartIssuedCurrentFields {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hscope : BankWindowScope ring
      (bankWindowRootBefore ring seed pre) e)
    (hmode :
      ((bankWindowRootBefore ring seed pre).1 e).mode = .CSTART)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hactive :
      ((bankWindowRootBefore ring seed pre).2.sites e).controller =
        .active p)
    (horigin : p.origin = some o) :
    BankComparatorCurrentWorker ring
      (bankWindowRootAfter ring seed pre e)
      o (ring.rightNeighbor e) p ∧
    Counter.Complete ring
      (bankWindowRootAfter ring seed pre e).1 o.root ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankTrialLiveComparisonToken
        ((bankWindowRootAfter ring seed pre e).1
          (Counter.site ring o.root (j.val + 1))).tok →
      Counter.site ring o.root (j.val + 1) =
        ring.rightNeighbor e) ∧
    ((((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).tok = .CR1 →
      bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        ((bankWindowRootAfter ring seed pre e).1
          (ring.rightNeighbor e)).pack.val) ∧
     (((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).tok = .CR0 →
      ¬ bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        ((bankWindowRootAfter ring seed pre e).1
          (ring.rightNeighbor e)).pack.val) ∧
     (((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).tok = .CL1 →
      bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        (compileAdvice (ceilLogTwo n)).b) ∧
     (((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).tok = .CL0 →
      ¬ bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o
        (compileAdvice (ceilLogTwo n)).b)) ∧
    (bankWindowOnlyToken ring
      (bankWindowRootAfter ring seed pre e)
      o.root (ring.rightNeighbor e) ∧
      BankTrialLiveComparisonToken
        ((bankWindowRootAfter ring seed pre e).1
          (ring.rightNeighbor e)).tok ∧
      p.heads = bankOriginBinaryValue ring
        (bankWindowRootAfter ring seed pre e).1 o ∧
      bankOriginBinaryValue ring
        (bankWindowRootAfter ring seed pre e).1 o ≤
          (compileAdvice (ceilLogTwo n)).K) := by
  have hcore := bankWindowOverlapRootCstartIssuedComparatorCore
    ring hn hbank seed pre e hJ hscope hmode p o hactive horigin
  obtain ⟨hcomplete, hmodePost, hwaitPost, hworkerPost,
    hpo, hroot, htoken, hheads, hbitsGlobal⟩ := hcore
  have hmodeOrigin :
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode =
        .CWAIT := by
    rw [hroot]
    exact hmodePost
  have hcompleteOrigin :
      Counter.Complete ring
        (bankWindowRootAfter ring seed pre e).1 o.root := by
    rw [hroot]
    exact hcomplete
  have htokLive :
      BankTrialLiveComparisonToken
        ((bankWindowRootAfter ring seed pre e).1
          (ring.rightNeighbor e)).tok := by
    rw [htoken]
    split <;> simp [BankTrialLiveComparisonToken]
  have hcurrent : BankComparatorCurrentWorker ring
      (bankWindowRootAfter ring seed pre e)
      o (ring.rightNeighbor e) p :=
    ⟨⟨hworkerPost, hpo, htokLive⟩, hmodeOrigin⟩
  have honly := bankWindowOverlapRootCstartIssuedOnlyToken
    ring hn hbank seed pre e hJ hscope hmode p o
    hactive horigin
  have hunique :
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        BankTrialLiveComparisonToken
          ((bankWindowRootAfter ring seed pre e).1
            (Counter.site ring o.root (j.val + 1))).tok →
        Counter.site ring o.root (j.val + 1) =
          ring.rightNeighbor e := by
    intro j htokPost
    apply honly j
    intro hempty
    rw [hempty] at htokPost
    simp [BankTrialLiveComparisonToken] at htokPost
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hx :
      ((bankWindowRootBefore ring seed pre).1 e).pack.val =
        0 := by
    change ((bankWindowRootBefore ring seed pre).1
      (Counter.site ring e 0)).pack.val = 0
    exact hscope.1 0 (by omega)
  have hy :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val = 1 := by
    change ((bankWindowRootBefore ring seed pre).1
      (Counter.site ring e 1)).pack.val = 1
    exact hscope.1 1 (by omega)
  have hpostPack :
      ((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).pack.val = 1 := by
    have hpair := bankWindowExactResponderPack ring
      (bankWindowRootBefore ring seed pre) e
      (clockNeighborDifferent ring (by omega : 2 ≤ n) e)
    rw [hpair, hx, hy]
    simp [packNext, hb]
  have hsite :
      Counter.site ring o.root 1 = ring.rightNeighbor e := by
    rw [hroot]
    rfl
  have hbitNew :
      ((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).bit =
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).bit :=
    hbitsGlobal (ring.rightNeighbor e)
  have hzeroMatch :
      bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o 0 := by
    intro j hj
    have hfalse : False := by omega
    exact False.elim hfalse
  have honeMatch :
      bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o 1 ↔
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).bit =
          (compileAdvice (ceilLogTwo n)).theta 0 := by
    have hext := bankWindowOverlapComparatorPrefixExtension
      ring (bankWindowRootAfter ring seed pre e) o 0 hb
    constructor
    · intro hmatch
      have hlast := (hext.mp hmatch).2
      change
        ((bankWindowRootAfter ring seed pre e).1
          (Counter.site ring o.root 1)).bit =
          (compileAdvice (ceilLogTwo n)).theta 0 at hlast
      rw [hsite, hbitNew] at hlast
      exact hlast
    · intro hbit
      apply hext.mpr
      refine ⟨hzeroMatch, ?_⟩
      change
        ((bankWindowRootAfter ring seed pre e).1
          (Counter.site ring o.root 1)).bit =
            (compileAdvice (ceilLogTwo n)).theta 0
      rw [hsite, hbitNew]
      exact hbit
  have hflags :
      (((bankWindowRootAfter ring seed pre e).1
          (ring.rightNeighbor e)).tok = .CR1 →
        bankComparatorPrefixMatched ring
          (bankWindowRootAfter ring seed pre e) o
          ((bankWindowRootAfter ring seed pre e).1
            (ring.rightNeighbor e)).pack.val) ∧
      (((bankWindowRootAfter ring seed pre e).1
          (ring.rightNeighbor e)).tok = .CR0 →
        ¬ bankComparatorPrefixMatched ring
          (bankWindowRootAfter ring seed pre e) o
          ((bankWindowRootAfter ring seed pre e).1
            (ring.rightNeighbor e)).pack.val) ∧
      (((bankWindowRootAfter ring seed pre e).1
          (ring.rightNeighbor e)).tok = .CL1 →
        bankComparatorPrefixMatched ring
          (bankWindowRootAfter ring seed pre e) o
          (compileAdvice (ceilLogTwo n)).b) ∧
      (((bankWindowRootAfter ring seed pre e).1
          (ring.rightNeighbor e)).tok = .CL0 →
        ¬ bankComparatorPrefixMatched ring
          (bankWindowRootAfter ring seed pre e) o
          (compileAdvice (ceilLogTwo n)).b) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hcr
      have hbit :
          ((bankWindowRootBefore ring seed pre).1
            (ring.rightNeighbor e)).bit =
              (compileAdvice (ceilLogTwo n)).theta 0 := by
        by_cases heq :
            ((bankWindowRootBefore ring seed pre).1
              (ring.rightNeighbor e)).bit =
                (compileAdvice (ceilLogTwo n)).theta 0
        · exact heq
        · have hzero :
              ((bankWindowRootAfter ring seed pre e).1
                (ring.rightNeighbor e)).tok = .CR0 := by
            rw [htoken, if_neg heq]
          rw [hzero] at hcr
          cases hcr
      rw [hpostPack]
      exact honeMatch.mpr hbit
    · intro hcr hmatched
      have hbit :
          ((bankWindowRootBefore ring seed pre).1
            (ring.rightNeighbor e)).bit =
              (compileAdvice (ceilLogTwo n)).theta 0 := by
        apply honeMatch.mp
        rw [hpostPack] at hmatched
        exact hmatched
      have hone :
          ((bankWindowRootAfter ring seed pre e).1
            (ring.rightNeighbor e)).tok = .CR1 := by
        rw [htoken, if_pos hbit]
      rw [hone] at hcr
      cases hcr
    · intro hcl
      rw [htoken] at hcl
      split at hcl <;> cases hcl
    · intro hcl
      rw [htoken] at hcl
      split at hcl <;> cases hcl
  have holdArmed := hJ.armedExact e o p hscope
    (Or.inr hmode) hactive horigin
  have hbits : bankWindowReadDigitBits ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) o.root := by
    intro j
    exact hbitsGlobal (Counter.site ring o.root (j.val + 1))
  have hvalue := bankWindowOverlapComparatorBinaryBitTransport
    ring (bankWindowRootBefore ring seed pre)
    (bankWindowRootAfter ring seed pre e) o hbits
  have hbound :
      bankOriginBinaryValue ring
        (bankWindowRootAfter ring seed pre e).1 o ≤
          (compileAdvice (ceilLogTwo n)).K := by
    rw [hvalue]
    exact holdArmed.2.2.2 hmode
  exact ⟨hcurrent, hcompleteOrigin, hunique,
    hflags, honly, htokLive, hheads, hbound⟩

/--
Every genuine comparator of the CSTART source root just after
issuance is exactly the newly issued first-digit worker. The
real POST workerSite/band certificate places it on a digit,
the only-token field forces the first digit, and the actual
selected ghost worker fixes its payload and origin.
Consumer: universal source-root CSTART phase and compare fields.
-/
theorem bankWindowOverlapRootCstartIssuedComparatorExclusive {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hscope : BankWindowScope ring
      (bankWindowRootBefore ring seed pre) e)
    (hmode :
      ((bankWindowRootBefore ring seed pre).1 e).mode = .CSTART)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hactive :
      ((bankWindowRootBefore ring seed pre).2.sites e).controller =
        .active p)
    (horigin : p.origin = some o)
    (o' : RenewalBankOrigin n) (i : Fin n)
    (q : RenewalBankPayload n)
    (hroot : o'.root = e)
    (hcomp : BankComparatorOriginWorker ring
      (bankWindowRootAfter ring seed pre e) o' i q) :
    i = ring.rightNeighbor e ∧ q = p ∧ o' = o := by
  have hcore := bankWindowOverlapRootCstartIssuedComparatorCore
    ring hn hbank seed pre e hJ hscope hmode p o hactive horigin
  obtain ⟨_, _, _, hworkerPost, hpo, hissuedRoot, _, _, _⟩ :=
    hcore
  have honly := bankWindowOverlapRootCstartIssuedOnlyToken
    ring hn hbank seed pre e hJ hscope hmode p o
    hactive horigin
  have hrun :
      rbRun ring (renewalBankStart ring seed) (pre ++ [e]) =
        bankWindowRootAfter ring seed pre e := by
    rw [rbRunAppend]
    rfl
  have hwordWorker :
      ((rbRun ring (renewalBankStart ring seed)
        (pre ++ [e])).2.sites i).worker = .payload q := by
    rw [hrun]
    exact hcomp.1
  have hband := bankWindowOverlapGenuineWorkerInBand
    ring hn hbank seed (pre ++ [e]) i q o'
    hwordWorker hcomp.2.1
  rw [hrun] at hband
  have hsite := bankWindowGenuineWorkerSiteOfRun
    ring hn hbank seed (pre ++ [e]) i q o'
    hwordWorker hcomp.2.1
  rw [hrun] at hsite
  rw [hroot] at hsite
  have hidx :
      ((bankWindowRootAfter ring seed pre e).1 i).pack.val - 1 <
        (compileAdvice (ceilLogTwo n)).b := by omega
  have hidxSucc :
      ((bankWindowRootAfter ring seed pre e).1 i).pack.val - 1 + 1 =
      ((bankWindowRootAfter ring seed pre e).1 i).pack.val := by
    omega
  have hsiteAt :
      Counter.site ring e
        (((bankWindowRootAfter ring seed pre e).1 i).pack.val -
          1 + 1) = i := by
    rw [hidxSucc]
    exact hsite.symm
  have htokenNotEmpty :
      ((bankWindowRootAfter ring seed pre e).1 i).tok ≠ .E := by
    intro hempty
    have hlive := hcomp.2.2
    rw [hempty] at hlive
    simp [BankTrialLiveComparisonToken] at hlive
  have htokenAt :
      ((bankWindowRootAfter ring seed pre e).1
        (Counter.site ring e
          (((bankWindowRootAfter ring seed pre e).1 i).pack.val -
            1 + 1))).tok ≠ .E := by
    rw [hsiteAt]
    exact htokenNotEmpty
  have honlyAt := honly
    (⟨((bankWindowRootAfter ring seed pre e).1 i).pack.val - 1,
      hidx⟩ : Fin (compileAdvice (ceilLogTwo n)).b)
    (by
      change ((bankWindowRootAfter ring seed pre e).1
        (Counter.site ring o.root
          (((bankWindowRootAfter ring seed pre e).1 i).pack.val -
            1 + 1))).tok ≠ .E
      rw [hissuedRoot]
      exact htokenAt)
  rw [hissuedRoot] at honlyAt
  have hfirst : i = ring.rightNeighbor e :=
    hsiteAt.symm.trans honlyAt
  have hsamePayload : q = p := by
    have hw := hcomp.1
    rw [hfirst] at hw
    have heq : RenewalBankWorker.payload q =
        RenewalBankWorker.payload p := hw.symm.trans hworkerPost
    cases heq
    rfl
  have hsameOrigin : o' = o := by
    have ho : q.origin = some o' := hcomp.2.1
    rw [hsamePayload] at ho
    have heq : some o' = some o := ho.symm.trans hpo
    cases heq
    rfl
  exact ⟨hfirst, hsamePayload, hsameOrigin⟩

/--
Universal CSTART issuance row for an arbitrary genuine POST
comparator of the source root. The actual post-worker uniqueness
identifies it with the issued worker, so every J phase field
and compareExact is inherited from the issued-comparator bundle;
there is no hypothesis naming a particular POST worker.
Consumer: selected-source CSTART branch of group-13 J phase
and comparison assembly.
-/
theorem bankWindowOverlapRootCstartUniversalCurrentFields {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hscope : BankWindowScope ring
      (bankWindowRootBefore ring seed pre) e)
    (hmode :
      ((bankWindowRootBefore ring seed pre).1 e).mode = .CSTART)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hactive :
      ((bankWindowRootBefore ring seed pre).2.sites e).controller =
        .active p)
    (horigin : p.origin = some o)
    (o' : RenewalBankOrigin n) (i : Fin n)
    (q : RenewalBankPayload n)
    (hroot : o'.root = e)
    (hcomp : BankComparatorOriginWorker ring
      (bankWindowRootAfter ring seed pre e) o' i q) :
    (((bankWindowRootAfter ring seed pre e).1 o'.root).mode ≠
        .ARMED ∧
      ((bankWindowRootAfter ring seed pre e).1 o'.root).mode ≠
        .CSTART ∧
      ((bankWindowRootAfter ring seed pre e).1 o'.root).mode ≠
        .IWAIT) ∧
    Counter.Complete ring
      (bankWindowRootAfter ring seed pre e).1 o'.root ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankTrialLiveComparisonToken
        ((bankWindowRootAfter ring seed pre e).1
          (Counter.site ring o'.root (j.val + 1))).tok →
      Counter.site ring o'.root (j.val + 1) = i) ∧
    ((((bankWindowRootAfter ring seed pre e).1 i).tok = .CR1 →
      bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o'
        ((bankWindowRootAfter ring seed pre e).1 i).pack.val) ∧
     (((bankWindowRootAfter ring seed pre e).1 i).tok = .CR0 →
      ¬ bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o'
        ((bankWindowRootAfter ring seed pre e).1 i).pack.val) ∧
     (((bankWindowRootAfter ring seed pre e).1 i).tok = .CL1 →
      bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o'
        (compileAdvice (ceilLogTwo n)).b) ∧
     (((bankWindowRootAfter ring seed pre e).1 i).tok = .CL0 →
      ¬ bankComparatorPrefixMatched ring
        (bankWindowRootAfter ring seed pre e) o'
        (compileAdvice (ceilLogTwo n)).b)) ∧
    (bankWindowOnlyToken ring
      (bankWindowRootAfter ring seed pre e) o'.root i ∧
      BankTrialLiveComparisonToken
        ((bankWindowRootAfter ring seed pre e).1 i).tok ∧
      q.heads = bankOriginBinaryValue ring
        (bankWindowRootAfter ring seed pre e).1 o' ∧
      bankOriginBinaryValue ring
        (bankWindowRootAfter ring seed pre e).1 o' ≤
        (compileAdvice (ceilLogTwo n)).K) := by
  obtain ⟨hi, hq, ho⟩ :=
    bankWindowOverlapRootCstartIssuedComparatorExclusive
      ring hn hbank seed pre e hJ hscope hmode p o
      hactive horigin o' i q hroot hcomp
  subst i
  subst q
  subst o'
  have hfields := bankWindowOverlapRootCstartIssuedCurrentFields
    ring hn hbank seed pre e hJ hscope hmode p o hactive horigin
  have hmodePost := hfields.1.2
  have hexcludes :
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠
        .ARMED ∧
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠
        .CSTART ∧
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠
        .IWAIT := by
    rw [hmodePost]
    refine ⟨?_, ?_, ?_⟩
    · intro hbad
      cases hbad
    · intro hbad
      cases hbad
    · intro hbad
      cases hbad
  exact ⟨hexcludes, hfields.2.1,
    hfields.2.2.1, hfields.2.2.2.1,
    hfields.2.2.2.2⟩

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

/-- A changed BANK responder cannot belong to a window which
is complete both before and after the actual service. This
includes the incoming root and all interior digit responders.
Consumer: M5 TOP-only incidence in BankWindowOverlapJoint. -/
theorem bankWindowOverlapRepairCompleteResponderOutside
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalBankReference n) (e root : Fin n)
    (hbefore : Counter.Complete ring r.1 root)
    (hafter : Counter.Complete ring
      (renewalBankNext ring r e).1 root)
    (hchanged :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
        (r.1 (ring.rightNeighbor e)).pack.val) :
    ∀ k : Nat, k ≤ (compileAdvice (ceilLogTwo n)).b →
      ring.rightNeighbor e ≠ Counter.site ring root k := by
  have hresponder := bankWindowExactResponderPack
    ring r e (clockNeighborDifferent ring (by omega : 2 ≤ n) e)
  intro k hk heq
  have hold :
      (r.1 (ring.rightNeighbor e)).pack.val = k := by
    rw [heq]
    exact hbefore k hk
  have hpost :
      ((renewalBankNext ring r e).1
        (ring.rightNeighbor e)).pack.val = k := by
    rw [heq]
    exact hafter k hk
  have hsame :
      (r.1 (ring.rightNeighbor e)).pack.val =
        ((renewalBankNext ring r e).1
          (ring.rightNeighbor e)).pack.val :=
    hold.trans hpost.symm
  exact hchanged (hresponder.symm.trans hsame.symm)

/-- Complete-before-and-after repair intersects another root's
bounded support only at its TOP source digit. A source interior
digit has its next digit in the unchanged completed interval;
an incoming source has the root as its target, also unchanged.
Consumer: M5 repair-foreign TOP dispatch in BankWindowOverlapJoint. -/
theorem bankWindowOverlapRepairCompleteIncidentTop
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalBankReference n) (e root : Fin n)
    (hbefore : Counter.Complete ring r.1 root)
    (hafter : Counter.Complete ring
      (renewalBankNext ring r e).1 root)
    (hchanged :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
        (r.1 (ring.rightNeighbor e)).pack.val)
    (hincident : Counter.Support (ceilLogTwo n)
      ring root e) :
    e = Counter.site ring root
      (compileAdvice (ceilLogTwo n)).b := by
  have htarget := bankWindowOverlapRepairCompleteResponderOutside
    ring hn r e root hbefore hafter hchanged
  rcases hincident with hincoming | ⟨k, hk, he⟩
  · exact False.elim
      ((htarget 0 (by omega))
        (by simpa only [Counter.site] using hincoming))
  · by_cases htop : k = (compileAdvice (ceilLogTwo n)).b
    · rw [htop] at he
      exact he
    · have hbelow : k < (compileAdvice (ceilLogTwo n)).b := by
        omega
      have hnext :
          ring.rightNeighbor e =
            Counter.site ring root (k + 1) := by
        rw [he]
        rfl
      exact False.elim ((htarget (k + 1) (by omega)) hnext)

/-- A complete-to-complete changed-responder repair on the TOP
source has its responder beyond the completed root's real digit
interval. This is the exact geometric guard for all M5 read
transports, not a claim that the whole ring is partitioned.
Consumer: M5 TOP source/target atomic frame. -/
theorem bankWindowOverlapRepairCompleteTopTargetOutside
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalBankReference n) (e root : Fin n)
    (hbefore : Counter.Complete ring r.1 root)
    (hafter : Counter.Complete ring
      (renewalBankNext ring r e).1 root)
    (hchanged :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
        (r.1 (ring.rightNeighbor e)).pack.val) :
    ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      Counter.site ring root (j.val + 1) ≠
        ring.rightNeighbor e := by
  intro j
  have houtside := bankWindowOverlapRepairCompleteResponderOutside
    ring hn r e root hbefore hafter hchanged
    (j.val + 1) (by have hj := j.isLt; omega)
  exact Ne.symm houtside

/-- The selected TOP digit has nonzero role b on a changed
responder service, so the literal BANK owner returns early
from the changed branch without modifying its bit, token,
or ghost worker. Only its mode/lease may be reset.
Consumer: M5 TOP atomic source-read frame. -/
theorem bankWindowOverlapRepairCompleteTopRaw
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (htop : x.pack.val = c.b)
    (hchanged :
      packNext x.pack.val y.pack.val c.b ≠ y.pack.val) :
    (Counter.resetBankOld x y).1.tok = x.tok ∧
    (Counter.resetBankOld x y).1.bit = x.bit ∧
    (renewalBankPairMemory c m e dest x y).1.worker =
      (m.sites e).worker := by
  have hb : 0 < c.b := by
    change 0 < c.s + 11
    omega
  have hbz : c.b ≠ 0 := by omega
  have hpositive : 1 ≤ x.pack.val := by omega
  have hnonzero : x.pack.val ≠ 0 := by omega
  have hrange : x.pack.val ≤ c.b := by omega
  rw [htop] at hchanged
  constructor
  · simp [Counter.resetBankOld, bankPair, bankCell,
      htop, hchanged, hb, hbz, hpositive, hnonzero,
      hrange, Id.run_pure, Id.run_bind] <;>
      repeat (first | rfl | split)
  constructor
  · simp [Counter.resetBankOld, bankPair, bankCell,
      htop, hchanged, hb, hbz, hpositive, hnonzero,
      hrange, Id.run_pure, Id.run_bind] <;>
      repeat (first | rfl | split)
  · simp [renewalBankPairMemory, bankCell,
      htop, hchanged, hb, hbz, hpositive, hnonzero,
      hrange, Id.run_pure, Id.run_bind] <;>
      repeat (first | rfl | split)

/-- The TOP digit itself retains precisely the four reads
needed by M5's proto/phase/tainted/bit clauses: role,
token, bit, and ghost worker. The source's mode/lease
are NOT claimed to be framed. Consumer: M5 full
completed-window read transport. -/
theorem bankWindowOverlapRepairCompleteTopSourceReads
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (htop :
      (r.1 e).pack.val = (compileAdvice (ceilLogTwo n)).b)
    (hchanged :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
        (r.1 (ring.rightNeighbor e)).pack.val) :
    bankWindowReadPack r (renewalBankNext ring r e) e ∧
    bankWindowReadTok r (renewalBankNext ring r e) e ∧
    bankWindowReadBit r (renewalBankNext ring r e) e ∧
    bankWindowReadWorker r (renewalBankNext ring r e) e := by
  have hpack := bankWindowClosureRepairNonresponderPackFixed
    ring (by omega : 2 ≤ n) r e e
    (clockNeighborDifferent ring (by omega : 2 ≤ n) e).symm
  have hraw := bankWindowOverlapRepairCompleteTopRaw
    (compileAdvice (ceilLogTwo n)) r.2 e
    (ring.rightNeighbor e) (r.1 e)
    (r.1 (ring.rightNeighbor e)) htop hchanged
  have htrip := bankWindowClosureSelectedBankTrip
    ring hn hbank r e
  have htok := congrArg
    (fun t : Mode × Bool × BTok => t.2.2) htrip.1
  have hbit := congrArg
    (fun t : Mode × Bool × BTok => t.2.1) htrip.1
  change ((renewalBankNext ring r e).1 e).tok =
    (Counter.resetBankOld (r.1 e)
      (r.1 (ring.rightNeighbor e))).1.tok at htok
  change ((renewalBankNext ring r e).1 e).bit =
    (Counter.resetBankOld (r.1 e)
      (r.1 (ring.rightNeighbor e))).1.bit at hbit
  have hf := (rbReferenceSelectedPairFrame
    ring (by omega : 2 ≤ n) r e).2.2.1
  have hworker := congrArg
    (fun s : RenewalBankSite n => s.worker) hf
  change ((renewalBankNext ring r e).2.sites e).worker =
    (renewalBankPairMemory
      (compileAdvice (ceilLogTwo n)) r.2
      e (ring.rightNeighbor e)
      (r.1 e) (r.1 (ring.rightNeighbor e))).1.worker at hworker
  exact ⟨hpack, htok.trans hraw.1,
    hbit.trans hraw.2.1, hworker.trans hraw.2.2⟩

/-- The selected repair TOP source and all strictly earlier
digit sites preserve the physical and ghost READ coordinates
of the completed foreign root (except TOP mode/lease).
In particular the root grant, mode, controller, every
digit token/bit/worker and PACK 0..b are identical.
Consumer: all M5 TOP root-indexed read transports. -/
theorem bankWindowOverlapRepairCompleteTopWindowReads
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e root : Fin n)
    (hbefore : Counter.Complete ring r.1 root)
    (htop :
      e = Counter.site ring root
        (compileAdvice (ceilLogTwo n)).b)
    (hchanged :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
        (r.1 (ring.rightNeighbor e)).pack.val) :
    bankWindowReadPackPrefix ring r
      (renewalBankNext ring r e) root
      (compileAdvice (ceilLogTwo n)).b ∧
    bankWindowReadDigitTokens ring r
      (renewalBankNext ring r e) root ∧
    bankWindowReadDigitBits ring r
      (renewalBankNext ring r e) root ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      bankWindowReadWorker r (renewalBankNext ring r e)
        (Counter.site ring root (j.val + 1))) ∧
    bankWindowReadGrant r (renewalBankNext ring r e) root ∧
    bankWindowReadMode r (renewalBankNext ring r e) root ∧
    bankWindowReadController r (renewalBankNext ring r e) root := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hsourceRole :
      (r.1 e).pack.val = (compileAdvice (ceilLogTwo n)).b := by
    rw [htop]
    exact hbefore _ (Nat.le_refl _)
  have htopReads := bankWindowOverlapRepairCompleteTopSourceReads
    ring hn hbank r e hsourceRole hchanged
  have hearlier :
      ∀ t : Nat, t < (compileAdvice (ceilLogTwo n)).b →
        (renewalBankNext ring r e).1
          (Counter.site ring root t) =
            r.1 (Counter.site ring root t) ∧
        (renewalBankNext ring r e).2.sites
          (Counter.site ring root t) =
            r.2.sites (Counter.site ring root t) := by
    intro t ht
    exact bankWindowOverlapRepairEarlierSiteFrame
      ring hbank r e root
      (compileAdvice (ceilLogTwo n)).b t
      htop (Nat.le_refl _) ht
  have hrootFrame := hearlier 0 hb
  have hpack :
      bankWindowReadPackPrefix ring r
        (renewalBankNext ring r e) root
        (compileAdvice (ceilLogTwo n)).b := by
    intro k hk
    by_cases hlt : k < (compileAdvice (ceilLogTwo n)).b
    · exact congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
          a.pack.val) (hearlier k hlt).1
    · have heq : k = (compileAdvice (ceilLogTwo n)).b := by
        omega
      rw [heq, ← htop]
      exact htopReads.1
  have htoks :
      bankWindowReadDigitTokens ring r
        (renewalBankNext ring r e) root := by
    intro j
    by_cases hlt :
        j.val + 1 < (compileAdvice (ceilLogTwo n)).b
    · exact congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
          a.tok) (hearlier (j.val + 1) hlt).1
    · have heq :
          j.val + 1 = (compileAdvice (ceilLogTwo n)).b := by
        have hj := j.isLt
        omega
      rw [heq, ← htop]
      exact htopReads.2.1
  have hbits :
      bankWindowReadDigitBits ring r
        (renewalBankNext ring r e) root := by
    intro j
    by_cases hlt :
        j.val + 1 < (compileAdvice (ceilLogTwo n)).b
    · exact congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
          a.bit) (hearlier (j.val + 1) hlt).1
    · have heq :
          j.val + 1 = (compileAdvice (ceilLogTwo n)).b := by
        have hj := j.isLt
        omega
      rw [heq, ← htop]
      exact htopReads.2.2.1
  have hworkers :
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        bankWindowReadWorker r (renewalBankNext ring r e)
          (Counter.site ring root (j.val + 1)) := by
    intro j
    by_cases hlt :
        j.val + 1 < (compileAdvice (ceilLogTwo n)).b
    · exact congrArg
        (fun a : RenewalBankSite n => a.worker)
        (hearlier (j.val + 1) hlt).2
    · have heq :
          j.val + 1 = (compileAdvice (ceilLogTwo n)).b := by
        have hj := j.isLt
        omega
      rw [heq, ← htop]
      exact htopReads.2.2.2
  exact ⟨hpack, htoks, hbits, hworkers,
    congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
      a.grant) hrootFrame.1,
    congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
      a.mode) hrootFrame.1,
    congrArg (fun a : RenewalBankSite n =>
      a.controller) hrootFrame.2⟩

/-- A genuine POST worker on a TOP repair cannot be the
changed responder (whose ghost was erased). At the top
source its PACK/token/bit/worker are framed by the changed
source row; everywhere else its two physical and worker
slots are off-pair. No POST-J premise is used.
Consumer: all M5 free-worker phase and increment/compare reads. -/
theorem bankWindowOverlapRepairCompleteTopGenuineWorkerReads
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e root i : Fin n)
    (htop :
      e = Counter.site ring root
        (compileAdvice (ceilLogTwo n)).b)
    (hbefore : Counter.Complete ring r.1 root)
    (hchanged :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
        (r.1 (ring.rightNeighbor e)).pack.val)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hworker :
      ((renewalBankNext ring r e).2.sites i).worker =
        .payload p)
    (horigin : p.origin = some o) :
    bankWindowReadPack r (renewalBankNext ring r e) i ∧
    bankWindowReadTok r (renewalBankNext ring r e) i ∧
    bankWindowReadBit r (renewalBankNext ring r e) i ∧
    bankWindowReadWorker r (renewalBankNext ring r e) i := by
  by_cases hsource : i = e
  · subst i
    have hrole :
        (r.1 e).pack.val = (compileAdvice (ceilLogTwo n)).b := by
      rw [htop]
      exact hbefore _ (Nat.le_refl _)
    have ht := bankWindowOverlapRepairCompleteTopSourceReads
      ring hn hbank r e hrole hchanged
    exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2⟩
  · by_cases htarget : i = ring.rightNeighbor e
    · subst i
      have htainted : BankWindowTainted
          (renewalBankNext ring r e)
          (ring.rightNeighbor e) :=
        Or.inr ⟨p, o, hworker, horigin⟩
      have hclean := (bankWindowClosureChangedDigitClean
        ring hn hbank r e hchanged).2.2.2.1
      exact False.elim (hclean htainted)
    · have hf := bankWindowExactOffPairAtomicReads
        ring r e i hsource htarget
      exact ⟨hf.1, hf.2.2.1,
        hf.2.2.2.1, hf.2.2.2.2.2.1⟩

/-- All thirteen OLD-to-POST root-local M5 fields for a
complete-to-complete changed-responder repair whose source
is the foreign root's TOP digit. The repaired responder lies
outside the complete window; the TOP source preserves its
PACK/bit/token/worker and the earlier sites are off-pair.
The scope, provenance, phase and tainted-owner transports
therefore use only OLD BankWindowExact and the actual
ReceiptInv of the extended rbRun. Proto/orphan are excluded
by the authentic POST complete window. Consumer:
BankWindowOverlapJoint M5 and bankWindowExactOfRootFields. -/
theorem bankWindowOverlapRepairCompleteTopRootClauses
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hcompleteOld : Counter.Complete ring
      (bankWindowRootBefore ring seed pre).1 root)
    (hcompletePost : Counter.Complete ring
      (bankWindowRootAfter ring seed pre e).1 root)
    (htop :
      e = Counter.site ring root
        (compileAdvice (ceilLogTwo n)).b)
    (hchanged :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val) :
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    o.root = root → BankComparatorOriginWorker ring (bankWindowRootAfter ring seed pre e) o i p →
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠ .ARMED ∧
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠ .CSTART ∧
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠ .IWAIT) ∧
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    o.root = root → BankComparatorOriginWorker ring (bankWindowRootAfter ring seed pre e) o i p →
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode = .CWAIT →
      Counter.Complete ring (bankWindowRootAfter ring seed pre e).1 o.root) ∧
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    o.root = root → BankComparatorOriginWorker ring (bankWindowRootAfter ring seed pre e) o i p →
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode = .CWAIT →
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        BankTrialLiveComparisonToken
          ((bankWindowRootAfter ring seed pre e).1 (Counter.site ring o.root (j.val + 1))).tok →
        Counter.site ring o.root (j.val + 1) = i) ∧
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    o.root = root → BankComparatorOriginWorker ring (bankWindowRootAfter ring seed pre e) o i p →
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode = .CWAIT →
      (((bankWindowRootAfter ring seed pre e).1 i).tok = .CR1 →
        bankComparatorPrefixMatched ring (bankWindowRootAfter ring seed pre e) o ((bankWindowRootAfter ring seed pre e).1 i).pack.val) ∧
      (((bankWindowRootAfter ring seed pre e).1 i).tok = .CR0 →
        ¬ bankComparatorPrefixMatched ring (bankWindowRootAfter ring seed pre e) o ((bankWindowRootAfter ring seed pre e).1 i).pack.val) ∧
      (((bankWindowRootAfter ring seed pre e).1 i).tok = .CL1 →
        bankComparatorPrefixMatched ring (bankWindowRootAfter ring seed pre e) o
          (compileAdvice (ceilLogTwo n)).b) ∧
      (((bankWindowRootAfter ring seed pre e).1 i).tok = .CL0 →
        ¬ bankComparatorPrefixMatched ring (bankWindowRootAfter ring seed pre e) o
          (compileAdvice (ceilLogTwo n)).b)) ∧
  (BankWindowScope ring (bankWindowRootAfter ring seed pre e) root →
    BankWindowInheritedController (bankWindowRootAfter ring seed pre e) root →
    ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ¬ BankWindowTainted (bankWindowRootAfter ring seed pre e) (Counter.site ring root (j.val + 1))) ∧
  (BankWindowScope ring (bankWindowRootAfter ring seed pre e) root →
    ((bankWindowRootAfter ring seed pre e).1 root).mode = .RWAIT →
    ((bankWindowRootAfter ring seed pre e).2.sites root).controller = .waiting [] →
    ∃ (j : Fin (compileAdvice (ceilLogTwo n)).b)
      (rho : RenewalBankReceipt n),
      ((bankWindowRootAfter ring seed pre e).2.sites (Counter.site ring root (j.val + 1))).worker =
        .pending rho ∧
      (((bankWindowRootAfter ring seed pre e).1 (Counter.site ring root (j.val + 1))).tok = .RR ∨
       ((bankWindowRootAfter ring seed pre e).1 (Counter.site ring root (j.val + 1))).tok = .RL) ∧
      bankWindowZeroPrefix ring (bankWindowRootAfter ring seed pre e) root (j.val + 1) ∧
      (∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
        k.val < j.val →
        ((bankWindowRootAfter ring seed pre e).1 (Counter.site ring root (k.val + 1))).tok = .E) ∧
      (((bankWindowRootAfter ring seed pre e).1 (Counter.site ring root (j.val + 1))).tok = .RL →
        bankWindowOnlyToken ring (bankWindowRootAfter ring seed pre e) root
          (Counter.site ring root (j.val + 1)) ∧
        bankWindowZeroPrefix ring (bankWindowRootAfter ring seed pre e) root
          (compileAdvice (ceilLogTwo n)).b)) ∧
  (∀ (o : RenewalBankOrigin n) (p : RenewalBankPayload n),
    BankWindowScope ring (bankWindowRootAfter ring seed pre e) root →
    (((bankWindowRootAfter ring seed pre e).1 root).mode = .ARMED ∨ ((bankWindowRootAfter ring seed pre e).1 root).mode = .CSTART) →
    ((bankWindowRootAfter ring seed pre e).2.sites root).controller = .active p →
    p.origin = some o →
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ((bankWindowRootAfter ring seed pre e).1 (Counter.site ring root (j.val + 1))).tok = .E) ∧
    p.heads = bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o ∧
    (((bankWindowRootAfter ring seed pre e).1 root).mode = .ARMED →
      bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o <
        (compileAdvice (ceilLogTwo n)).K) ∧
    (((bankWindowRootAfter ring seed pre e).1 root).mode = .CSTART →
      bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o ≤
        (compileAdvice (ceilLogTwo n)).K)) ∧
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    BankWindowScope ring (bankWindowRootAfter ring seed pre e) root →
    ((bankWindowRootAfter ring seed pre e).1 root).mode = .IWAIT →
    ((bankWindowRootAfter ring seed pre e).2.sites root).controller = .waiting [] →
    ((bankWindowRootAfter ring seed pre e).2.sites i).worker = .payload p →
    p.origin = some o → o.root = root →
    bankWindowOnlyToken ring (bankWindowRootAfter ring seed pre e) root i ∧
    ((((bankWindowRootAfter ring seed pre e).1 i).tok = .IR ∧
        bankWindowZeroPrefix ring (bankWindowRootAfter ring seed pre e) root ((bankWindowRootAfter ring seed pre e).1 i).pack.val ∧
        p.heads = bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o +
          2 ^ ((bankWindowRootAfter ring seed pre e).1 i).pack.val ∧
        bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o +
          2 ^ ((bankWindowRootAfter ring seed pre e).1 i).pack.val ≤
            (compileAdvice (ceilLogTwo n)).K) ∨
     (((bankWindowRootAfter ring seed pre e).1 i).tok = .AL ∧
        p.heads = bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o ∧
        bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o ≤
          (compileAdvice (ceilLogTwo n)).K))) ∧
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    o.root = root →
    ((bankWindowRootAfter ring seed pre e).2.sites i).worker = .payload p →
    p.origin = some o →
    ((bankWindowRootAfter ring seed pre e).1 o.root).mode = .CWAIT →
    ((bankWindowRootAfter ring seed pre e).2.sites o.root).controller = .waiting [] →
    bankWindowOnlyToken ring (bankWindowRootAfter ring seed pre e) o.root i ∧
    BankTrialLiveComparisonToken ((bankWindowRootAfter ring seed pre e).1 i).tok ∧
    p.heads = bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o ∧
    bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o ≤
      (compileAdvice (ceilLogTwo n)).K) ∧
  (BankWindowScope ring (bankWindowRootAfter ring seed pre e) root →
    ((bankWindowRootAfter ring seed pre e).1 root).mode = .IWAIT →
    ((bankWindowRootAfter ring seed pre e).2.sites root).controller = .waiting [] →
    ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowTainted (bankWindowRootAfter ring seed pre e) (Counter.site ring root (j.val + 1)) →
      ∃ (o : RenewalBankOrigin n) (p : RenewalBankPayload n),
        ((bankWindowRootAfter ring seed pre e).2.sites (Counter.site ring root (j.val + 1))).worker =
          .payload p ∧ p.origin = some o ∧
        o.root = root ∧
        bankWindowOnlyToken ring (bankWindowRootAfter ring seed pre e) root
          (Counter.site ring root (j.val + 1))) ∧
  (BankWindowScope ring (bankWindowRootAfter ring seed pre e) root →
    ((bankWindowRootAfter ring seed pre e).1 root).mode = .CWAIT →
    ((bankWindowRootAfter ring seed pre e).2.sites root).controller = .waiting [] →
    ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowTainted (bankWindowRootAfter ring seed pre e) (Counter.site ring root (j.val + 1)) →
      ∃ (o : RenewalBankOrigin n) (p : RenewalBankPayload n),
        ((bankWindowRootAfter ring seed pre e).2.sites (Counter.site ring root (j.val + 1))).worker =
          .payload p ∧ p.origin = some o ∧
        o.root = root ∧
        BankTrialLiveComparisonToken
          ((bankWindowRootAfter ring seed pre e).1 (Counter.site ring root (j.val + 1))).tok ∧
        bankWindowOnlyToken ring (bankWindowRootAfter ring seed pre e) root
          (Counter.site ring root (j.val + 1))) ∧
  (∀ limit : Nat, BankWindowProtoRun ring (bankWindowRootAfter ring seed pre e) root limit →
    BankWindowRootForeignProtoField ring (bankWindowRootAfter ring seed pre e) root limit) ∧
  (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
    BankWindowOrphanOwner ring (bankWindowRootAfter ring seed pre e) root j →
    BankWindowTainted (bankWindowRootAfter ring seed pre e) (Counter.site ring root (j.val + 1)) →
    ((bankWindowRootAfter ring seed pre e).1 root).mode = .RESET ∨
      (((bankWindowRootAfter ring seed pre e).1 root).mode = .RWAIT ∧
        ((bankWindowRootAfter ring seed pre e).2.sites root).controller = .waiting [])) := by
  have hreads := bankWindowOverlapRepairCompleteTopWindowReads
    ring hn hbank (bankWindowRootBefore ring seed pre) e root
    hcompleteOld htop hchanged
  have hpack : bankWindowReadPackPrefix ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) root
      (compileAdvice (ceilLogTwo n)).b := hreads.1
  have htoks : bankWindowReadDigitTokens ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) root := hreads.2.1
  have hbits : bankWindowReadDigitBits ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) root := hreads.2.2.1
  have hworkers :
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        bankWindowReadWorker
          (bankWindowRootBefore ring seed pre)
          (bankWindowRootAfter ring seed pre e)
          (Counter.site ring root (j.val + 1)) :=
    hreads.2.2.2.1
  have hgrant : bankWindowReadGrant
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) root :=
    hreads.2.2.2.2.1
  have hmode : bankWindowReadMode
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) root :=
    hreads.2.2.2.2.2.1
  have hcontroller : bankWindowReadController
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) root :=
    hreads.2.2.2.2.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o i p horoot hcomp
    have hi := bankWindowOverlapRepairCompleteTopGenuineWorkerReads
      ring hn hbank (bankWindowRootBefore ring seed pre)
      e root i htop hcompleteOld hchanged
      p o hcomp.1 hcomp.2.1
    have hm : bankWindowReadMode
        (bankWindowRootBefore ring seed pre)
        (bankWindowRootAfter ring seed pre e) o.root := by
      rw [horoot]
      exact hmode
    exact bankWindowPhaseExcludesReadTransport ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e)
      o i p hJ ⟨hi.2.1, hi.2.2.2, hm⟩ hcomp
  · intro o i p horoot hcomp hphase
    rw [horoot]
    exact hcompletePost
  · intro o i p horoot hcomp hphase j htoken
    have hi := bankWindowOverlapRepairCompleteTopGenuineWorkerReads
      ring hn hbank (bankWindowRootBefore ring seed pre)
      e root i htop hcompleteOld hchanged
      p o hcomp.1 hcomp.2.1
    have hm : bankWindowReadMode
        (bankWindowRootBefore ring seed pre)
        (bankWindowRootAfter ring seed pre e) o.root := by
      rw [horoot]
      exact hmode
    have htokenReads : bankWindowReadDigitTokens ring
        (bankWindowRootBefore ring seed pre)
        (bankWindowRootAfter ring seed pre e) o.root := by
      rw [horoot]
      exact htoks
    exact bankWindowPhaseUniqueReadTransport ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e)
      o i p hJ ⟨⟨hi.2.1, hi.2.2.2, hm⟩, htokenReads⟩
      hcomp hphase j htoken
  · intro o i p horoot hcomp hphase
    have hi := bankWindowOverlapRepairCompleteTopGenuineWorkerReads
      ring hn hbank (bankWindowRootBefore ring seed pre)
      e root i htop hcompleteOld hchanged
      p o hcomp.1 hcomp.2.1
    have hm : bankWindowReadMode
        (bankWindowRootBefore ring seed pre)
        (bankWindowRootAfter ring seed pre e) o.root := by
      rw [horoot]
      exact hmode
    have hbitReads : bankWindowReadDigitBits ring
        (bankWindowRootBefore ring seed pre)
        (bankWindowRootAfter ring seed pre e) o.root := by
      rw [horoot]
      exact hbits
    exact bankWindowPhaseFlagsReadTransport ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e)
      o i p hJ ⟨⟨hi.2.1, hi.2.2.2, hm⟩,
        hi.1, hbitReads⟩ hcomp hphase
  · intro hscope hinherited j htainted
    exact bankWindowInheritedCleanReadTransport ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e)
      root j hJ ⟨hpack, hgrant, hcontroller, hworkers j⟩
      hscope hinherited htainted
  · intro hscope hwait hctl
    exact bankWindowResetWaitReadTransport ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e)
      root hJ ⟨hpack, hgrant, hmode, hcontroller,
        hbits, htoks, hworkers⟩ hscope hwait hctl
  · intro o p hscope hphase hactive horigin
    have hrootOrigin := (bankWindowOverlapPostReceipt
      ring hn hbank seed pre e).activeRoot
      root p o hactive horigin
    have hbitsOrigin : bankWindowReadDigitBits ring
        (bankWindowRootBefore ring seed pre)
        (bankWindowRootAfter ring seed pre e) o.root := by
      rw [← hrootOrigin]
      exact hbits
    exact bankWindowArmedExactReadTransport ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e)
      root o p hJ ⟨hpack, hgrant, hmode, hcontroller,
        htoks, hbitsOrigin⟩ hscope hphase hactive horigin
  · intro o i p hscope hphase hctl hworker horigin horoot
    have hi := bankWindowOverlapRepairCompleteTopGenuineWorkerReads
      ring hn hbank (bankWindowRootBefore ring seed pre)
      e root i htop hcompleteOld hchanged
      p o hworker horigin
    have hbitsOrigin : bankWindowReadDigitBits ring
        (bankWindowRootBefore ring seed pre)
        (bankWindowRootAfter ring seed pre e) o.root := by
      rw [horoot]
      exact hbits
    exact bankWindowIncrementExactReadTransport ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e)
      root o i p hJ ⟨hpack, hgrant, hmode, hcontroller,
        hi.2.2.2, hi.1, hi.2.1, htoks, hbits,
        hbitsOrigin⟩ hscope hphase hctl hworker horigin horoot
  · intro o i p horoot hworker horigin hphase hctl
    have hi := bankWindowOverlapRepairCompleteTopGenuineWorkerReads
      ring hn hbank (bankWindowRootBefore ring seed pre)
      e root i htop hcompleteOld hchanged
      p o hworker horigin
    have hmodeOrigin : bankWindowReadMode
        (bankWindowRootBefore ring seed pre)
        (bankWindowRootAfter ring seed pre e) o.root := by
      rw [horoot]
      exact hmode
    have hcontrollerOrigin : bankWindowReadController
        (bankWindowRootBefore ring seed pre)
        (bankWindowRootAfter ring seed pre e) o.root := by
      rw [horoot]
      exact hcontroller
    have htoksOrigin : bankWindowReadDigitTokens ring
        (bankWindowRootBefore ring seed pre)
        (bankWindowRootAfter ring seed pre e) o.root := by
      rw [horoot]
      exact htoks
    have hbitsOrigin : bankWindowReadDigitBits ring
        (bankWindowRootBefore ring seed pre)
        (bankWindowRootAfter ring seed pre e) o.root := by
      rw [horoot]
      exact hbits
    exact bankWindowCompareExactReadTransport ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e)
      o i p hJ
      ⟨hmodeOrigin, hcontrollerOrigin, hi.2.2.2,
        hi.2.1, htoksOrigin, hbitsOrigin⟩
      hworker horigin hphase hctl
  · intro hscope hphase hctl j htainted
    exact bankWindowIwaitTaintedUniqueReadTransport ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e)
      root j hJ
      ⟨hpack, hgrant, hmode, hcontroller, htoks, hworkers j⟩
      hscope hphase hctl htainted
  · intro hscope hphase hctl j htainted
    exact bankWindowCwaitTaintedUniqueReadTransport ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e)
      root j hJ
      ⟨hpack, hgrant, hmode, hcontroller, htoks, hworkers j⟩
      hscope hphase hctl htainted
  · intro limit hproto
    have hwrong := hproto.2.2
    exact False.elim (hwrong
      (hcompletePost (limit + 1)
        (by have hl := hproto.1; omega)))
  · intro j howner htainted
    exact False.elim (howner.2.2
      (by
        intro k hk
        exact hcompletePost k
          (by have hj := j.isLt; omega)))

/-- The directly dispatchable M5 proof. A complete-to-complete
changed-responder repair incident to a foreign root is first
shown to have TOP source geometry, then all thirteen root-local
post clauses are transported from OLD J. This is the same
conjunction that BankWindowRootFieldsAt expects; the latter
is in BankWindowOverlapJoint, which imports this module, so
no cyclic import is introduced here.
Consumer: BankWindowOverlapJoint M5 and bankWindowExactStep. -/
theorem bankWindowOverlapRepairCompleteIncidentRootClauses
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hcompleteOld : Counter.Complete ring
      (bankWindowRootBefore ring seed pre).1 root)
    (hcompletePost : Counter.Complete ring
      (bankWindowRootAfter ring seed pre e).1 root)
    (hchanged :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val)
    (hincident : Counter.Support (ceilLogTwo n)
      ring root e) :
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    o.root = root → BankComparatorOriginWorker ring (bankWindowRootAfter ring seed pre e) o i p →
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠ .ARMED ∧
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠ .CSTART ∧
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠ .IWAIT) ∧
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    o.root = root → BankComparatorOriginWorker ring (bankWindowRootAfter ring seed pre e) o i p →
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode = .CWAIT →
      Counter.Complete ring (bankWindowRootAfter ring seed pre e).1 o.root) ∧
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    o.root = root → BankComparatorOriginWorker ring (bankWindowRootAfter ring seed pre e) o i p →
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode = .CWAIT →
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        BankTrialLiveComparisonToken
          ((bankWindowRootAfter ring seed pre e).1 (Counter.site ring o.root (j.val + 1))).tok →
        Counter.site ring o.root (j.val + 1) = i) ∧
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    o.root = root → BankComparatorOriginWorker ring (bankWindowRootAfter ring seed pre e) o i p →
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode = .CWAIT →
      (((bankWindowRootAfter ring seed pre e).1 i).tok = .CR1 →
        bankComparatorPrefixMatched ring (bankWindowRootAfter ring seed pre e) o ((bankWindowRootAfter ring seed pre e).1 i).pack.val) ∧
      (((bankWindowRootAfter ring seed pre e).1 i).tok = .CR0 →
        ¬ bankComparatorPrefixMatched ring (bankWindowRootAfter ring seed pre e) o ((bankWindowRootAfter ring seed pre e).1 i).pack.val) ∧
      (((bankWindowRootAfter ring seed pre e).1 i).tok = .CL1 →
        bankComparatorPrefixMatched ring (bankWindowRootAfter ring seed pre e) o
          (compileAdvice (ceilLogTwo n)).b) ∧
      (((bankWindowRootAfter ring seed pre e).1 i).tok = .CL0 →
        ¬ bankComparatorPrefixMatched ring (bankWindowRootAfter ring seed pre e) o
          (compileAdvice (ceilLogTwo n)).b)) ∧
  (BankWindowScope ring (bankWindowRootAfter ring seed pre e) root →
    BankWindowInheritedController (bankWindowRootAfter ring seed pre e) root →
    ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ¬ BankWindowTainted (bankWindowRootAfter ring seed pre e) (Counter.site ring root (j.val + 1))) ∧
  (BankWindowScope ring (bankWindowRootAfter ring seed pre e) root →
    ((bankWindowRootAfter ring seed pre e).1 root).mode = .RWAIT →
    ((bankWindowRootAfter ring seed pre e).2.sites root).controller = .waiting [] →
    ∃ (j : Fin (compileAdvice (ceilLogTwo n)).b)
      (rho : RenewalBankReceipt n),
      ((bankWindowRootAfter ring seed pre e).2.sites (Counter.site ring root (j.val + 1))).worker =
        .pending rho ∧
      (((bankWindowRootAfter ring seed pre e).1 (Counter.site ring root (j.val + 1))).tok = .RR ∨
       ((bankWindowRootAfter ring seed pre e).1 (Counter.site ring root (j.val + 1))).tok = .RL) ∧
      bankWindowZeroPrefix ring (bankWindowRootAfter ring seed pre e) root (j.val + 1) ∧
      (∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
        k.val < j.val →
        ((bankWindowRootAfter ring seed pre e).1 (Counter.site ring root (k.val + 1))).tok = .E) ∧
      (((bankWindowRootAfter ring seed pre e).1 (Counter.site ring root (j.val + 1))).tok = .RL →
        bankWindowOnlyToken ring (bankWindowRootAfter ring seed pre e) root
          (Counter.site ring root (j.val + 1)) ∧
        bankWindowZeroPrefix ring (bankWindowRootAfter ring seed pre e) root
          (compileAdvice (ceilLogTwo n)).b)) ∧
  (∀ (o : RenewalBankOrigin n) (p : RenewalBankPayload n),
    BankWindowScope ring (bankWindowRootAfter ring seed pre e) root →
    (((bankWindowRootAfter ring seed pre e).1 root).mode = .ARMED ∨ ((bankWindowRootAfter ring seed pre e).1 root).mode = .CSTART) →
    ((bankWindowRootAfter ring seed pre e).2.sites root).controller = .active p →
    p.origin = some o →
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ((bankWindowRootAfter ring seed pre e).1 (Counter.site ring root (j.val + 1))).tok = .E) ∧
    p.heads = bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o ∧
    (((bankWindowRootAfter ring seed pre e).1 root).mode = .ARMED →
      bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o <
        (compileAdvice (ceilLogTwo n)).K) ∧
    (((bankWindowRootAfter ring seed pre e).1 root).mode = .CSTART →
      bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o ≤
        (compileAdvice (ceilLogTwo n)).K)) ∧
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    BankWindowScope ring (bankWindowRootAfter ring seed pre e) root →
    ((bankWindowRootAfter ring seed pre e).1 root).mode = .IWAIT →
    ((bankWindowRootAfter ring seed pre e).2.sites root).controller = .waiting [] →
    ((bankWindowRootAfter ring seed pre e).2.sites i).worker = .payload p →
    p.origin = some o → o.root = root →
    bankWindowOnlyToken ring (bankWindowRootAfter ring seed pre e) root i ∧
    ((((bankWindowRootAfter ring seed pre e).1 i).tok = .IR ∧
        bankWindowZeroPrefix ring (bankWindowRootAfter ring seed pre e) root ((bankWindowRootAfter ring seed pre e).1 i).pack.val ∧
        p.heads = bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o +
          2 ^ ((bankWindowRootAfter ring seed pre e).1 i).pack.val ∧
        bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o +
          2 ^ ((bankWindowRootAfter ring seed pre e).1 i).pack.val ≤
            (compileAdvice (ceilLogTwo n)).K) ∨
     (((bankWindowRootAfter ring seed pre e).1 i).tok = .AL ∧
        p.heads = bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o ∧
        bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o ≤
          (compileAdvice (ceilLogTwo n)).K))) ∧
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    o.root = root →
    ((bankWindowRootAfter ring seed pre e).2.sites i).worker = .payload p →
    p.origin = some o →
    ((bankWindowRootAfter ring seed pre e).1 o.root).mode = .CWAIT →
    ((bankWindowRootAfter ring seed pre e).2.sites o.root).controller = .waiting [] →
    bankWindowOnlyToken ring (bankWindowRootAfter ring seed pre e) o.root i ∧
    BankTrialLiveComparisonToken ((bankWindowRootAfter ring seed pre e).1 i).tok ∧
    p.heads = bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o ∧
    bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o ≤
      (compileAdvice (ceilLogTwo n)).K) ∧
  (BankWindowScope ring (bankWindowRootAfter ring seed pre e) root →
    ((bankWindowRootAfter ring seed pre e).1 root).mode = .IWAIT →
    ((bankWindowRootAfter ring seed pre e).2.sites root).controller = .waiting [] →
    ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowTainted (bankWindowRootAfter ring seed pre e) (Counter.site ring root (j.val + 1)) →
      ∃ (o : RenewalBankOrigin n) (p : RenewalBankPayload n),
        ((bankWindowRootAfter ring seed pre e).2.sites (Counter.site ring root (j.val + 1))).worker =
          .payload p ∧ p.origin = some o ∧
        o.root = root ∧
        bankWindowOnlyToken ring (bankWindowRootAfter ring seed pre e) root
          (Counter.site ring root (j.val + 1))) ∧
  (BankWindowScope ring (bankWindowRootAfter ring seed pre e) root →
    ((bankWindowRootAfter ring seed pre e).1 root).mode = .CWAIT →
    ((bankWindowRootAfter ring seed pre e).2.sites root).controller = .waiting [] →
    ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowTainted (bankWindowRootAfter ring seed pre e) (Counter.site ring root (j.val + 1)) →
      ∃ (o : RenewalBankOrigin n) (p : RenewalBankPayload n),
        ((bankWindowRootAfter ring seed pre e).2.sites (Counter.site ring root (j.val + 1))).worker =
          .payload p ∧ p.origin = some o ∧
        o.root = root ∧
        BankTrialLiveComparisonToken
          ((bankWindowRootAfter ring seed pre e).1 (Counter.site ring root (j.val + 1))).tok ∧
        bankWindowOnlyToken ring (bankWindowRootAfter ring seed pre e) root
          (Counter.site ring root (j.val + 1))) ∧
  (∀ limit : Nat, BankWindowProtoRun ring (bankWindowRootAfter ring seed pre e) root limit →
    BankWindowRootForeignProtoField ring (bankWindowRootAfter ring seed pre e) root limit) ∧
  (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
    BankWindowOrphanOwner ring (bankWindowRootAfter ring seed pre e) root j →
    BankWindowTainted (bankWindowRootAfter ring seed pre e) (Counter.site ring root (j.val + 1)) →
    ((bankWindowRootAfter ring seed pre e).1 root).mode = .RESET ∨
      (((bankWindowRootAfter ring seed pre e).1 root).mode = .RWAIT ∧
        ((bankWindowRootAfter ring seed pre e).2.sites root).controller = .waiting [])) := by
  have htop := bankWindowOverlapRepairCompleteIncidentTop
    ring hn (bankWindowRootBefore ring seed pre)
    e root hcompleteOld hcompletePost hchanged hincident
  exact bankWindowOverlapRepairCompleteTopRootClauses
    ring hn hbank seed pre e root hJ
    hcompleteOld hcompletePost htop hchanged

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

/-- Eleven root-indexed J clauses in the exact order of the corresponding
non-proto/non-orphan fields in BankWindowRootFieldsAt. Kept here because
BankWindowOverlapJoint imports this module, not conversely.
Consumer: BankWindowOverlapJoint, class SRC. -/
def bankWindowOverlapSourceOwnClauses {n : Nat} (ring : DirectedRing n)
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
          (Counter.site ring root (j.val + 1)))

/-!
A protocol root in .RESET with its corresponding non-inherited
controller discharges the guarded source-owned J clauses.
Consumer: BankWindowOverlapJoint, SRC source root.
-/
theorem bankWindowOverlapSourceOwnResetModeClauses {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (root : Fin n)
    (hmode : (r.1 root).mode = .RESET)
    (hcontroller : (r.2.sites root).controller = .empty) :
    bankWindowOverlapSourceOwnClauses ring r root := by
  unfold bankWindowOverlapSourceOwnClauses
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o i p ho _
    have hm : (r.1 o.root).mode = .RESET := by
      rw [ho]
      exact hmode
    rw [hm]
    refine ⟨?_, ?_, ?_⟩ <;> intro hbad <;> cases hbad
  · intro o i p ho _ hm
    rw [ho, hmode] at hm
    cases hm
  · intro o i p ho _ hm
    rw [ho, hmode] at hm
    cases hm
  · intro o i p ho _ hm
    rw [ho, hmode] at hm
    cases hm
  · intro _ hi _ _
    rcases hi with ⟨atoms, hc, _⟩ | ⟨p, hc, _⟩
    · rw [hcontroller] at hc
      cases hc
    · rw [hcontroller] at hc
      cases hc
  · intro _ hm
    rw [hmode] at hm
    cases hm
  · intro o p _ hm
    rcases hm with ha | hc
    · rw [hmode] at ha
      cases ha
    · rw [hmode] at hc
      cases hc
  · intro o i p _ hm
    rw [hmode] at hm
    cases hm
  · intro o i p ho _ _ hm
    rw [ho, hmode] at hm
    cases hm
  · intro _ hm
    rw [hmode] at hm
    cases hm
  · intro _ hm
    rw [hmode] at hm
    cases hm

/-!
A protocol root in .RWAIT with its corresponding non-inherited
controller discharges the guarded source-owned J clauses.
Consumer: BankWindowOverlapJoint, SRC source root.
-/
theorem bankWindowOverlapSourceOwnRwaitModeClauses {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (root : Fin n)
    (hmode : (r.1 root).mode = .RWAIT)
    (hcontroller : (r.2.sites root).controller = .waiting [])
    (hreset : (BankWindowScope ring r root →
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
          (compileAdvice (ceilLogTwo n)).b))) :
    bankWindowOverlapSourceOwnClauses ring r root := by
  unfold bankWindowOverlapSourceOwnClauses
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o i p ho _
    have hm : (r.1 o.root).mode = .RWAIT := by
      rw [ho]
      exact hmode
    rw [hm]
    refine ⟨?_, ?_, ?_⟩ <;> intro hbad <;> cases hbad
  · intro o i p ho _ hm
    rw [ho, hmode] at hm
    cases hm
  · intro o i p ho _ hm
    rw [ho, hmode] at hm
    cases hm
  · intro o i p ho _ hm
    rw [ho, hmode] at hm
    cases hm
  · intro _ hi _ _
    rcases hi with ⟨atoms, hc, hn⟩ | ⟨p, hc, _⟩
    · rw [hcontroller] at hc
      cases hc
      exact hn rfl
    · rw [hcontroller] at hc
      cases hc
  · exact hreset
  · intro o p _ hm
    rcases hm with ha | hc
    · rw [hmode] at ha
      cases ha
    · rw [hmode] at hc
      cases hc
  · intro o i p _ hm
    rw [hmode] at hm
    cases hm
  · intro o i p ho _ _ hm
    rw [ho, hmode] at hm
    cases hm
  · intro _ hm
    rw [hmode] at hm
    cases hm
  · intro _ hm
    rw [hmode] at hm
    cases hm

/-- The authentic complete RESET source launches RWAIT and its first
pending RR witness. All eleven SRC clauses follow, without a post-J
assumption. Consumer: BankWindowOverlapJoint SRC RESET launch. -/
theorem bankWindowOverlapSourceOwnResetLaunch {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring (bankWindowRootBefore ring seed pre))
    (hscope : BankWindowScope ring (bankWindowRootBefore ring seed pre) e)
    (hreset : ((bankWindowRootBefore ring seed pre).1 e).mode = .RESET) :
    bankWindowOverlapSourceOwnClauses ring
      (bankWindowRootAfter ring seed pre e) e := by
  have hrow := bankWindowClosureResetLaunchWaitWitness
    ring hn hbank (bankWindowRootBefore ring seed pre)
    e hscope.1 hscope.2 hreset
  exact bankWindowOverlapSourceOwnRwaitModeClauses
    ring (bankWindowRootAfter ring seed pre e) e
    hrow.2.1 hrow.2.2.1 (fun _ _ _ => hrow.2.2.2)

/-- Expiring RWAIT on an actual non-return E edge enters RESET with
empty controller; the eleven SRC clauses, including guarded phase
fields, follow. Consumer: BankWindowOverlapJoint SRC timeout case. -/
theorem bankWindowOverlapSourceOwnRwaitNonreturnExpiry {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring (bankWindowRootBefore ring seed pre))
    (hscope : BankWindowScope ring (bankWindowRootBefore ring seed pre) e)
    (hmode : ((bankWindowRootBefore ring seed pre).1 e).mode = .RWAIT)
    (htok : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).tok = .E)
    (hlease : ((bankWindowRootBefore ring seed pre).1 e).lease.val ≤ 1) :
    bankWindowOverlapSourceOwnClauses ring
      (bankWindowRootAfter ring seed pre e) e := by
  have hrow := bankWindowClosureRootWaitTimeout
    ring hn hbank (bankWindowRootBefore ring seed pre)
    e hscope.1 hscope.2 hmode htok hlease
  exact bankWindowOverlapSourceOwnResetModeClauses
    ring (bankWindowRootAfter ring seed pre e) e
    hrow.2.1 hrow.2.2

/-- A genuine RWAIT/pending-RL birth has an actual complete ARMED
source and a new genuine zero-headed controller, with the OLD
window's sole RL token and fully cleared digit bits. This is the
physical/ghost preparation for the still-open SRC birth armedExact
and phaseExcludes clauses of BankWindowOverlapJoint. -/
theorem bankWindowOverlapSourceOwnRwaitBirthCertificate {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n) (o : RenewalBankOrigin n)
    (hJ : BankWindowExact ring (bankWindowRootBefore ring seed pre))
    (hbirth : renewalBankBirth ring
      (bankWindowRootBefore ring seed pre).1
      (bankWindowRootBefore ring seed pre).2 e = some o) :
    Counter.Complete ring (bankWindowRootAfter ring seed pre e).1 e ∧
    ((bankWindowRootAfter ring seed pre e).1 e).mode = .ARMED ∧
    (∃ p : RenewalBankPayload n,
      ((bankWindowRootAfter ring seed pre e).2.sites e).controller =
        .active p ∧ p.origin = some o ∧ p.heads = 0) ∧
    bankWindowOnlyToken ring (bankWindowRootBefore ring seed pre)
      e (ring.rightNeighbor e) ∧
    bankWindowZeroPrefix ring (bankWindowRootBefore ring seed pre)
      e (compileAdvice (ceilLogTwo n)).b := by
  have hpost := bankWindowClosureBirthCompletePost
    ring hn hbank (bankWindowRootBefore ring seed pre)
    e o hJ hbirth
  have hcleared := bankWindowClosureBirthClearedWindow
    ring (bankWindowRootBefore ring seed pre) e o hJ hbirth
  exact ⟨hpost.1, hpost.2.1, hpost.2.2,
    hcleared.2.1, hcleared.2.2⟩

/-- The genuine RWAIT/RL physical bank row promotes the source
to ARMED and retains its complete PACK window, independently of
whether the responder holds a pending birth receipt. The inherited
(no-pending) subcase uses this result in BankWindowOverlapJoint SRC;
its ghost and eleven-clause bundle remain to be assembled. -/
theorem bankWindowOverlapSourceOwnRwaitInheritedRlPhysical {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring (bankWindowRootBefore ring seed pre))
    (hscope : BankWindowScope ring (bankWindowRootBefore ring seed pre) e)
    (hmode : ((bankWindowRootBefore ring seed pre).1 e).mode = .RWAIT)
    (htok : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).tok = .RL)
    (hnoPending : ∀ rho : RenewalBankReceipt n,
      ((bankWindowRootBefore ring seed pre).2.sites
        (ring.rightNeighbor e)).worker ≠ .pending rho) :
    Counter.Complete ring (bankWindowRootAfter ring seed pre e).1 e ∧
    ((bankWindowRootAfter ring seed pre e).1 e).mode = .ARMED := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hx :
      ((bankWindowRootBefore ring seed pre).1 e).pack.val = 0 := by
    change ((bankWindowRootBefore ring seed pre).1
      (Counter.site ring e 0)).pack.val = 0
    exact hscope.1 0 (by omega)
  have hy :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val = 1 := by
    change ((bankWindowRootBefore ring seed pre).1
      (Counter.site ring e 1)).pack.val = 1
    exact hscope.1 1 (by omega)
  have hpack : packNext 0 1 (compileAdvice (ceilLogTwo n)).b =
      1 := by
    simp [packNext, hb]
  have hraw :
      (Counter.resetBankOld
        ((bankWindowRootBefore ring seed pre).1 e)
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e))).1.mode = .ARMED := by
    have hb0 : (compileAdvice (ceilLogTwo n)).b ≠ 0 := by omega
    simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hscope.2, hy, hmode, htok, hb0, hpack, isRetTok]
  have htrip :=
    (bankWindowClosureSelectedBankTrip ring hn hbank
      (bankWindowRootBefore ring seed pre) e).1
  have hphysical := congrArg
    (fun t : Mode × Bool × BTok => t.1) htrip
  change ((bankWindowRootAfter ring seed pre e).1 e).mode =
    (Counter.resetBankOld
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).1.mode at hphysical
  have hcomplete := bankWindowClosureCompleteInternalPack
    ring hn (bankWindowRootBefore ring seed pre)
    e hscope.1 0 hb
  exact ⟨hcomplete, hphysical.trans hraw⟩

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

/-- The eleven root-local R11 fields in the exact order of
BankWindowRootFieldsAt, excluding its separately assembled
proto and orphan fields. This is an abbreviation over the
actual physical and ghost reference, not a new invariant.
Consumer: BankWindowOverlapJoint SRC ARMED and CSTART rows. -/
def bankWindowOverlapSourceActiveOwnerFields {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (root : Fin n) : Prop :=
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
          (Counter.site ring root (j.val + 1)))

/-- Any actual RESET owner with no inherited controller satisfies
the eleven non-proto/non-orphan root fields. All positive-mode
consequents and their comparator witnesses are excluded by
the literal RESET mode; inheritedClean is vacuous.
Consumer: BankWindowOverlapJoint SRC ARMED/CSTART collision. -/
theorem bankWindowOverlapSourceActiveResetFields
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n)
    (hmode : (r.1 root).mode = .RESET)
    (hinherited : ¬ BankWindowInheritedController r root) :
    bankWindowOverlapSourceActiveOwnerFields ring r root := by
  unfold bankWindowOverlapSourceActiveOwnerFields
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

/-- A role-zero BANK source in ARMED or CSTART paired with PACK
one, grant-free, and a nonempty nonreturn responder token enters
RESET on the genuine first-match collision row. A return token
would have been consumed by the preceding return guard and is
not silently included. Consumer: M2 SRC ARMED collision. -/
theorem bankWindowOverlapSourceActiveCollisionPhysical
    {c : Compiled} (x y : Agent c)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hphase : x.mode = .ARMED ∨ x.mode = .CSTART)
    (hret : isRetTok y.tok = false)
    (htok : y.tok ≠ .E) :
    (Counter.resetBankOld x y).1.mode = .RESET := by
  have hb : 0 < c.b := by
    change 0 < c.s + 11
    omega
  have hbz : c.b ≠ 0 := by omega
  have hnext : packNext x.pack.val y.pack.val c.b = 1 := by
    rw [hx, hy]
    simp [packNext, hb]
  unfold Counter.resetBankOld
  rw [hnext]
  rcases hphase with hm | hm <;>
    cases ht : y.tok <;>
    simp [isRetTok, ht] at hret htok <;>
    simp [bankPair, bankCell, hx, hy, hg, hm, ht, hb, hbz,
      hnext, isRetTok, Id.run_pure, Id.run_bind] <;>
      repeat (first | rfl | split)

/-- The actual selected ARMED/CSTART collision root leaves PACK
zero and enters RESET with empty ghost controller. Its eleven
POST root fields are proved from the OLD exact-J frame, the
masked physical BANK trip, and the RESET owner consequence;
no POST-J or global step theorem is assumed.
Consumer: BankWindowOverlapJoint, class SRC ARMED collision. -/
theorem bankWindowOverlapSourceActiveCollisionFields
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hx : ((bankWindowRootBefore ring seed pre).1 e).pack.val = 0)
    (hy : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = 1)
    (hg : ((bankWindowRootBefore ring seed pre).1 e).grant = false)
    (hphase :
      ((bankWindowRootBefore ring seed pre).1 e).mode = .ARMED ∨
      ((bankWindowRootBefore ring seed pre).1 e).mode = .CSTART)
    (hret : isRetTok ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).tok = false)
    (htok : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).tok ≠ .E) :
    bankWindowOverlapSourceActiveOwnerFields ring
      (bankWindowRootAfter ring seed pre e) e := by
  have hraw := bankWindowOverlapSourceActiveCollisionPhysical
    ((bankWindowRootBefore ring seed pre).1 e)
    ((bankWindowRootBefore ring seed pre).1 (ring.rightNeighbor e))
    hx hy hg hphase hret htok
  have htrip := (bankWindowClosureSelectedBankTrip
    ring hn hbank (bankWindowRootBefore ring seed pre) e).1
  have hmode := congrArg
    (fun t : Mode × Bool × BTok => t.1) htrip
  change ((bankWindowRootAfter ring seed pre e).1 e).mode =
    (Counter.resetBankOld
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).1.mode at hmode
  have hreset :
      ((bankWindowRootAfter ring seed pre e).1 e).mode = .RESET :=
    hmode.trans hraw
  have hpostPack : ((bankWindowRootAfter ring seed pre e).1 e).pack.val = 0 :=
    (bankWindowRootSourceRoles ring hn
      (bankWindowRootBefore ring seed pre) e hx).1
  have hframe := bankWindowExactFrameStep
    ring hn hbank seed pre e hJ
  have hfields := bankWindowIncomingResetOwnerFields
    ring (bankWindowRootBefore ring seed pre) e e
    hpostPack hreset hframe
  exact bankWindowOverlapSourceActiveResetFields
    ring (bankWindowRootAfter ring seed pre e) e
    hreset hfields.2.1

/-- In an OLD scoped ARMED/CSTART source with an active
genuine controller, every digit strictly beyond the first
already has token E and an empty worker. Such digits are
off the selected source edge, so both reads stay unchanged.
Consumer: BankWindowOverlapJoint SRC A0/A1/S0/S1 tainted
uniqueness, issued-worker exclusivity, and field bundles. -/
theorem bankWindowOverlapSourceActiveOuterDigitsClean
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hscope : BankWindowScope ring
      (bankWindowRootBefore ring seed pre) e)
    (hphase :
      ((bankWindowRootBefore ring seed pre).1 e).mode = .ARMED ∨
      ((bankWindowRootBefore ring seed pre).1 e).mode = .CSTART)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hactive :
      ((bankWindowRootBefore ring seed pre).2.sites e).controller =
        .active p)
    (ho : p.origin = some o) :
    ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      0 < j.val →
      ((bankWindowRootAfter ring seed pre e).2.sites
        (Counter.site ring e (j.val + 1))).worker = .empty ∧
      ((bankWindowRootAfter ring seed pre e).1
        (Counter.site ring e (j.val + 1))).tok = .E := by
  have hclean := (hJ.armedExact e o p
    hscope hphase hactive ho).1
  intro j hj
  have hbound : j.val + 1 ≤
      (compileAdvice (ceilLogTwo n)).b := by
    have hlt := j.isLt
    omega
  have hsource :
      Counter.site ring e (j.val + 1) ≠ e := by
    have hh := bankWindowIncidenceSiteDistinct ring hbank
      e 0 (j.val + 1) (by omega) (by omega)
    change e ≠ Counter.site ring e (j.val + 1) at hh
    exact hh.symm
  have htarget :
      Counter.site ring e (j.val + 1) ≠
        ring.rightNeighbor e := by
    have hh := bankWindowIncidenceSiteDistinct ring hbank
      e 1 (j.val + 1) (by omega) (by omega)
    change ring.rightNeighbor e ≠
      Counter.site ring e (j.val + 1) at hh
    exact hh.symm
  have hf := bankWindowExactOffPairFrame ring
    (bankWindowRootBefore ring seed pre) e
    (Counter.site ring e (j.val + 1)) hsource htarget
  have htokOld :
      ((bankWindowRootBefore ring seed pre).1
        (Counter.site ring e (j.val + 1))).tok = .E :=
    hclean j
  have hworkerOld :
      ((bankWindowRootBefore ring seed pre).2.sites
        (Counter.site ring e (j.val + 1))).worker = .empty := by
    have hh := (hJ.frame
      (Counter.site ring e (j.val + 1))).2
    rw [htokOld] at hh
    change ((bankWindowRootBefore ring seed pre).2.sites
      (Counter.site ring e (j.val + 1))).worker = .empty at hh
    exact hh
  exact ⟨(congrArg
    (fun a : RenewalBankSite n => a.worker) hf.2).trans hworkerOld,
    (congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
      hf.1).trans htokOld⟩

/-- Any actual genuine POST worker of this source root is the
selected first-digit worker if all other local digit workers
are empty. The authenticated extended rbRun workerSite
identifies its physical offset. The result includes the
identical payload, not merely a matching origin.
Consumer: SRC ARMED A1 incrementExact and CSTART S0/S1
compareExact, phaseUnique and cwaitTaintedUnique. -/
theorem bankWindowOverlapSourceActiveIssuedWorkerExclusive
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n) (issued : RenewalBankPayload n)
    (hfirst :
      ((bankWindowRootAfter ring seed pre e).2.sites
        (ring.rightNeighbor e)).worker = .payload issued)
    (houter :
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        0 < j.val →
        ((bankWindowRootAfter ring seed pre e).2.sites
          (Counter.site ring e (j.val + 1))).worker = .empty)
    (i : Fin n) (q : RenewalBankPayload n)
    (o : RenewalBankOrigin n)
    (hroot : o.root = e)
    (hworker :
      ((bankWindowRootAfter ring seed pre e).2.sites i).worker =
        .payload q)
    (horigin : q.origin = some o) :
    i = ring.rightNeighbor e ∧ q = issued := by
  have hrun :
      rbRun ring (renewalBankStart ring seed) (pre ++ [e]) =
        bankWindowRootAfter ring seed pre e := by
    rw [rbRunAppend]
    rfl
  have hworkerRun :
      ((rbRun ring (renewalBankStart ring seed)
        (pre ++ [e])).2.sites i).worker = .payload q := by
    rw [hrun]
    exact hworker
  have hband := bankWindowOverlapGenuineWorkerInBand
    ring hn hbank seed (pre ++ [e]) i q o
    hworkerRun horigin
  have hsite := bankWindowGenuineWorkerSiteOfRun
    ring hn hbank seed (pre ++ [e]) i q o
    hworkerRun horigin
  rw [hrun] at hband hsite
  rw [hroot] at hsite
  have hindex :
      ((bankWindowRootAfter ring seed pre e).1 i).pack.val - 1 <
        (compileAdvice (ceilLogTwo n)).b := by omega
  have hindexSucc :
      ((bankWindowRootAfter ring seed pre e).1 i).pack.val - 1 + 1 =
        ((bankWindowRootAfter ring seed pre e).1 i).pack.val := by
    omega
  have hsiteAt :
      Counter.site ring e
        (((bankWindowRootAfter ring seed pre e).1 i).pack.val - 1 + 1) =
          i := by
    rw [hindexSucc]
    exact hsite.symm
  by_cases hfirstIndex :
      ((bankWindowRootAfter ring seed pre e).1 i).pack.val - 1 = 0
  · have hlocation : i = ring.rightNeighbor e := by
      have hh : Counter.site ring e
          (((bankWindowRootAfter ring seed pre e).1 i).pack.val - 1 + 1) =
            ring.rightNeighbor e := by
        rw [hfirstIndex]
        rfl
      exact hsiteAt.symm.trans hh
    have hpair :
        RenewalBankWorker.payload q = .payload issued := by
      have hw := hworker
      rw [hlocation] at hw
      exact hw.symm.trans hfirst
    cases hpair
    exact ⟨hlocation, rfl⟩
  · have hempty := houter
      (⟨((bankWindowRootAfter ring seed pre e).1 i).pack.val - 1,
        hindex⟩ : Fin (compileAdvice (ceilLogTwo n)).b)
      (by change 0 < ((bankWindowRootAfter ring seed pre e).1 i).pack.val - 1; omega)
    change ((bankWindowRootAfter ring seed pre e).2.sites
      (Counter.site ring e
        (((bankWindowRootAfter ring seed pre e).1 i).pack.val - 1 + 1))).worker = .empty at hempty
    rw [hsiteAt] at hempty
    rw [hempty] at hworker
    cases hworker

theorem bankWindowOverlapSourceActiveFirstWeightSum
    (b : Nat) (hb : 0 < b)
    (oldWeight newWeight : Fin b → Nat)
    (hfirst :
      newWeight (⟨0, hb⟩ : Fin b) =
        oldWeight (⟨0, hb⟩ : Fin b) + 1)
    (hrest :
      ∀ j : Fin b, 0 < j.val →
        newWeight j = oldWeight j) :
    (List.ofFn newWeight).sum =
      (List.ofFn oldWeight).sum + 1 := by
  cases b with
  | zero => cases hb
  | succ m =>
      have hhead :
          newWeight (0 : Fin (m + 1)) =
            oldWeight (0 : Fin (m + 1)) + 1 := hfirst
      have htail :
          (fun j : Fin m => newWeight j.succ) =
            (fun j : Fin m => oldWeight j.succ) := by
        funext j
        exact hrest j.succ (by change 0 < j.val + 1; omega)
      simp only [List.ofFn_succ, List.sum_cons]
      rw [htail, hhead]
      omega

/-- A selected source-root edge frames every physical
digit bit strictly beyond the first. Consumer: M2 SRC
ARMED A0/A1 exact binary-value step. -/
theorem bankWindowOverlapSourceActiveOtherBits
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (hj : 0 < j.val) :
    ((renewalBankNext ring r e).1
      (Counter.site ring e (j.val + 1))).bit =
      (r.1 (Counter.site ring e (j.val + 1))).bit := by
  have hbound : j.val + 1 ≤
      (compileAdvice (ceilLogTwo n)).b + 1 := by
    have hh := j.isLt
    omega
  have hsource :
      Counter.site ring e (j.val + 1) ≠ e := by
    have hh := bankWindowIncidenceSiteDistinct ring hbank
      e 0 (j.val + 1) (by omega) hbound
    change e ≠ Counter.site ring e (j.val + 1) at hh
    exact hh.symm
  have htarget :
      Counter.site ring e (j.val + 1) ≠
        ring.rightNeighbor e := by
    have hh := bankWindowIncidenceSiteDistinct ring hbank
      e 1 (j.val + 1) (by omega) hbound
    change ring.rightNeighbor e ≠
      Counter.site ring e (j.val + 1) at hh
    exact hh.symm
  exact congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.bit)
    (bankWindowExactOffPairFrame ring r e
      (Counter.site ring e (j.val + 1)) hsource htarget).1

/-- A0 physical first bit false to true increases the
actual origin's binary value by one; all other bits frame.
Consumer: SRC ARMED A0 exact active-head count. -/
theorem bankWindowOverlapSourceActiveBitSetValue
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (o : RenewalBankOrigin n) (hroot : o.root = e)
    (hbefore : (r.1 (ring.rightNeighbor e)).bit = false)
    (hafter :
      ((renewalBankNext ring r e).1
        (ring.rightNeighbor e)).bit = true) :
    bankOriginBinaryValue ring (renewalBankNext ring r e).1 o =
      bankOriginBinaryValue ring r.1 o + 1 := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hhead :
      (if ((renewalBankNext ring r e).1
          (Counter.site ring o.root (0 + 1))).bit
        then 2 ^ (0 : Nat) else 0) =
        (if (r.1 (Counter.site ring o.root (0 + 1))).bit
          then 2 ^ (0 : Nat) else 0) + 1 := by
    rw [hroot]
    change (if ((renewalBankNext ring r e).1
      (ring.rightNeighbor e)).bit then 1 else 0) =
      (if (r.1 (ring.rightNeighbor e)).bit then 1 else 0) + 1
    rw [hbefore, hafter]
    rfl
  have hrest :
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        0 < j.val →
        (if ((renewalBankNext ring r e).1
          (Counter.site ring o.root (j.val + 1))).bit
          then 2 ^ j.val else 0) =
        (if (r.1 (Counter.site ring o.root (j.val + 1))).bit
          then 2 ^ j.val else 0) := by
    intro j hj
    rw [hroot, bankWindowOverlapSourceActiveOtherBits
      ring hbank r e j hj]
  unfold bankOriginBinaryValue
  exact bankWindowOverlapSourceActiveFirstWeightSum
    (compileAdvice (ceilLogTwo n)).b hb
    (fun j : Fin (compileAdvice (ceilLogTwo n)).b =>
      if (r.1 (Counter.site ring o.root (j.val + 1))).bit
      then 2 ^ j.val else 0)
    (fun j : Fin (compileAdvice (ceilLogTwo n)).b =>
      if ((renewalBankNext ring r e).1
        (Counter.site ring o.root (j.val + 1))).bit
      then 2 ^ j.val else 0)
    hhead hrest

/-- A1 first bit true to false consumes one unit of the
actual origin binary value into the IR worker. Consumer:
SRC ARMED A1 incrementExact. -/
theorem bankWindowOverlapSourceActiveBitClearValue
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (o : RenewalBankOrigin n) (hroot : o.root = e)
    (hbefore : (r.1 (ring.rightNeighbor e)).bit = true)
    (hafter :
      ((renewalBankNext ring r e).1
        (ring.rightNeighbor e)).bit = false) :
    bankOriginBinaryValue ring r.1 o =
      bankOriginBinaryValue ring (renewalBankNext ring r e).1 o + 1 := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hhead :
      (if (r.1 (Counter.site ring o.root (0 + 1))).bit
        then 2 ^ (0 : Nat) else 0) =
        (if ((renewalBankNext ring r e).1
          (Counter.site ring o.root (0 + 1))).bit
          then 2 ^ (0 : Nat) else 0) + 1 := by
    rw [hroot]
    change (if (r.1 (ring.rightNeighbor e)).bit then 1 else 0) =
      (if ((renewalBankNext ring r e).1
        (ring.rightNeighbor e)).bit then 1 else 0) + 1
    rw [hbefore, hafter]
    rfl
  have hrest :
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        0 < j.val →
        (if (r.1 (Counter.site ring o.root (j.val + 1))).bit
          then 2 ^ j.val else 0) =
        (if ((renewalBankNext ring r e).1
          (Counter.site ring o.root (j.val + 1))).bit
          then 2 ^ j.val else 0) := by
    intro j hj
    rw [hroot, bankWindowOverlapSourceActiveOtherBits
      ring hbank r e j hj]
  unfold bankOriginBinaryValue
  exact bankWindowOverlapSourceActiveFirstWeightSum
    (compileAdvice (ceilLogTwo n)).b hb
    (fun j : Fin (compileAdvice (ceilLogTwo n)).b =>
      if ((renewalBankNext ring r e).1
        (Counter.site ring o.root (j.val + 1))).bit
      then 2 ^ j.val else 0)
    (fun j : Fin (compileAdvice (ceilLogTwo n)).b =>
      if (r.1 (Counter.site ring o.root (j.val + 1))).bit
      then 2 ^ j.val else 0)
    hhead hrest

/-- Genuine OLD ARMED/E first-match BANK row: zero bit
sets CSTART and bit one issues IR, with the first bit
toggled. The return guard is false because isRetTok E
reduces to false. Consumer: M2 SRC A0 and A1. -/
theorem bankWindowOverlapSourceActiveArmedCell
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hb : 1 ≤ b)
    (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false)
    (hm : x.mode = .ARMED) (ht : y.tok = .E) :
    (bankPair x y 1 b theta).1.mode =
      (if y.bit then .IWAIT else .CSTART) ∧
    (bankPair x y 1 b theta).2.tok =
      (if y.bit then .IR else .E) ∧
    (bankPair x y 1 b theta).2.bit = !y.bit := by
  have hreturn : isRetTok BTok.E = false := rfl
  cases hbit : y.bit <;>
    simp [bankPair, hx, hy, hg, hm, ht, hb, hbit,
      isRetTok, isWaitMode, hreturn,
      Id.run_pure, Id.run_bind] <;>
      repeat (first | rfl | split)

/-- The actual selected source-root BANK physical output for
ARMED/E; no separate ghost transition is substituted.
Consumer: BankWindowOverlapJoint SRC A0/A1 owner fields. -/
theorem bankWindowOverlapSourceActiveArmedPhysical
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hx : (r.1 e).pack.val = 0)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 1)
    (hg : (r.1 e).grant = false)
    (hm : (r.1 e).mode = .ARMED)
    (ht : (r.1 (ring.rightNeighbor e)).tok = .E) :
    ((renewalBankNext ring r e).1 e).mode =
      (if (r.1 (ring.rightNeighbor e)).bit then .IWAIT else .CSTART) ∧
    ((renewalBankNext ring r e).1 (ring.rightNeighbor e)).tok =
      (if (r.1 (ring.rightNeighbor e)).bit then .IR else .E) ∧
    ((renewalBankNext ring r e).1 (ring.rightNeighbor e)).bit =
      !(r.1 (ring.rightNeighbor e)).bit := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hp :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b = 1 := by
    rw [hx, hy]
    simp [packNext, hb]
  have hcell := bankWindowOverlapSourceActiveArmedCell
    (bankCell (r.1 e) (r.1 e).pack.val)
    (bankCell (r.1 (ring.rightNeighbor e))
      (r.1 (ring.rightNeighbor e)).pack.val)
    (compileAdvice (ceilLogTwo n)).b
    (compileAdvice (ceilLogTwo n)).theta
    (by omega)
    (by change (r.1 e).pack.val = 0; exact hx)
    (by change (r.1 (ring.rightNeighbor e)).pack.val = 1; exact hy)
    (by change (r.1 e).grant = false; exact hg)
    (by change (r.1 e).mode = .ARMED; exact hm)
    (by change (r.1 (ring.rightNeighbor e)).tok = .E; exact ht)
  have hraw :
      (Counter.resetBankOld (r.1 e)
        (r.1 (ring.rightNeighbor e))).1.mode =
          (if (r.1 (ring.rightNeighbor e)).bit
            then .IWAIT else .CSTART) ∧
      (Counter.resetBankOld (r.1 e)
        (r.1 (ring.rightNeighbor e))).2.tok =
          (if (r.1 (ring.rightNeighbor e)).bit
            then .IR else .E) ∧
      (Counter.resetBankOld (r.1 e)
        (r.1 (ring.rightNeighbor e))).2.bit =
          !(r.1 (ring.rightNeighbor e)).bit := by
    unfold Counter.resetBankOld
    rw [hp]
    exact hcell
  have htrip := bankWindowClosureSelectedBankTrip
    ring hn hbank r e
  have hsource := congrArg
    (fun t : Mode × Bool × BTok => t.1) htrip.1
  have htargetTok := congrArg
    (fun t : Mode × Bool × BTok => t.2.2) htrip.2
  have htargetBit := congrArg
    (fun t : Mode × Bool × BTok => t.2.1) htrip.2
  change ((renewalBankNext ring r e).1 e).mode =
    (Counter.resetBankOld (r.1 e)
      (r.1 (ring.rightNeighbor e))).1.mode at hsource
  change ((renewalBankNext ring r e).1
    (ring.rightNeighbor e)).tok =
    (Counter.resetBankOld (r.1 e)
      (r.1 (ring.rightNeighbor e))).2.tok at htargetTok
  change ((renewalBankNext ring r e).1
    (ring.rightNeighbor e)).bit =
    (Counter.resetBankOld (r.1 e)
      (r.1 (ring.rightNeighbor e))).2.bit at htargetBit
  exact ⟨hsource.trans hraw.1,
    htargetTok.trans hraw.2.1,
    htargetBit.trans hraw.2.2⟩

/-- A genuine origin rooted at an actual source e cannot have
a POST worker when every digit worker of e's interval is
empty. The extended-run workerSite field places it on one
such digit, rather than allowing an unlocated ghost payload.
Consumer: M2 SRC ARMED A0 phase/compare/increment exclusions. -/
theorem bankWindowOverlapSourceActiveNoOriginWorker
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hclean :
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ((bankWindowRootAfter ring seed pre e).2.sites
        (Counter.site ring e (j.val + 1))).worker = .empty)
    (i : Fin n) (p : RenewalBankPayload n)
    (o : RenewalBankOrigin n)
    (hroot : o.root = e)
    (hworker :
      ((bankWindowRootAfter ring seed pre e).2.sites i).worker =
        .payload p)
    (horigin : p.origin = some o) : False := by
  have hrun :
      rbRun ring (renewalBankStart ring seed) (pre ++ [e]) =
        bankWindowRootAfter ring seed pre e := by
    rw [rbRunAppend]
    rfl
  have hworkerRun :
      ((rbRun ring (renewalBankStart ring seed)
        (pre ++ [e])).2.sites i).worker = .payload p := by
    rw [hrun]
    exact hworker
  have hband := bankWindowOverlapGenuineWorkerInBand
    ring hn hbank seed (pre ++ [e]) i p o hworkerRun horigin
  have hsite := bankWindowGenuineWorkerSiteOfRun
    ring hn hbank seed (pre ++ [e]) i p o hworkerRun horigin
  rw [hrun] at hband hsite
  rw [hroot] at hsite
  have hindex :
      ((bankWindowRootAfter ring seed pre e).1 i).pack.val - 1 <
        (compileAdvice (ceilLogTwo n)).b := by omega
  have hindexSucc :
      ((bankWindowRootAfter ring seed pre e).1 i).pack.val - 1 + 1 =
        ((bankWindowRootAfter ring seed pre e).1 i).pack.val := by
    omega
  have hsiteAt :
      Counter.site ring e
        (((bankWindowRootAfter ring seed pre e).1 i).pack.val - 1 + 1) =
          i := by
    rw [hindexSucc]
    exact hsite.symm
  have hempty := hclean
    (⟨((bankWindowRootAfter ring seed pre e).1 i).pack.val - 1,
      hindex⟩ : Fin (compileAdvice (ceilLogTwo n)).b)
  change ((bankWindowRootAfter ring seed pre e).2.sites
    (Counter.site ring e
      (((bankWindowRootAfter ring seed pre e).1 i).pack.val - 1 + 1))).worker = .empty
    at hempty
  rw [hsiteAt] at hempty
  rw [hempty] at hworker
  cases hworker

/-- The actual POST shape frame turns an E token into an
empty worker; thus a physically E-token completed window
contains no tainted digit, pending or genuine.
Consumer: M2 SRC ARMED A0 inheritedClean and idle-head fields. -/
theorem bankWindowOverlapSourceActiveEmptyTokensClean
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n)
    (hframe : BankInFlightAligned ring r)
    (htokens :
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        (r.1 (Counter.site ring root (j.val + 1))).tok = .E) :
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      (r.2.sites (Counter.site ring root (j.val + 1))).worker =
        .empty) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ¬ BankWindowTainted r
        (Counter.site ring root (j.val + 1))) := by
  have hempty :
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        (r.2.sites (Counter.site ring root (j.val + 1))).worker =
          .empty := by
    intro j
    have hh := (hframe (Counter.site ring root (j.val + 1))).2
    rw [htokens j] at hh
    change (r.2.sites (Counter.site ring root (j.val + 1))).worker =
      .empty at hh
    exact hh
  refine ⟨hempty, ?_⟩
  intro j ht
  unfold BankWindowTainted at ht
  rw [hempty j] at ht
  rcases ht with ⟨rho, h⟩ | ⟨p, o, h, _⟩ <;> cases h

/-- Genuine ARMED A0: OLD first bit zero, NEW first bit one
and root CSTART. The active controller is renewalBankHead p,
whose exact heads and new physical binary value both equal
the OLD value plus one. Every post digit token is E, so the
real frame leaves every digit worker empty and every
phase/compare worker antecedent of this root is false.
Consumer: BankWindowOverlapJoint, M2 SRC ARMED A0, all
eleven clauses except proto/orphan. -/
theorem bankWindowOverlapSourceActiveArmedSetFields
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hscope : BankWindowScope ring
      (bankWindowRootBefore ring seed pre) e)
    (hm :
      ((bankWindowRootBefore ring seed pre).1 e).mode = .ARMED)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hactive :
      ((bankWindowRootBefore ring seed pre).2.sites e).controller =
        .active p)
    (horigin : p.origin = some o)
    (hbit :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).bit = false) :
    bankWindowOverlapSourceActiveOwnerFields ring
      (bankWindowRootAfter ring seed pre e) e := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hx :
      ((bankWindowRootBefore ring seed pre).1 e).pack.val = 0 := by
    change ((bankWindowRootBefore ring seed pre).1
      (Counter.site ring e 0)).pack.val = 0
    exact hscope.1 0 (by omega)
  have hy :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val = 1 := by
    change ((bankWindowRootBefore ring seed pre).1
      (Counter.site ring e 1)).pack.val = 1
    exact hscope.1 1 (by omega)
  have hbeforeArmed := hJ.armedExact e o p hscope
    (Or.inl hm) hactive horigin
  have ht :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .E := by
    have hfirst := hbeforeArmed.1
      (⟨0, hb⟩ : Fin (compileAdvice (ceilLogTwo n)).b)
    change ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).tok = .E at hfirst
    exact hfirst
  have hphysical := bankWindowOverlapSourceActiveArmedPhysical
    ring hn hbank (bankWindowRootBefore ring seed pre)
    e hx hy hscope.2 hm ht
  have hpostMode :
      ((bankWindowRootAfter ring seed pre e).1 e).mode = .CSTART := by
    have hh := hphysical.1
    rw [hbit] at hh
    exact hh
  have hpostTok :
      ((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).tok = .E := by
    have hh := hphysical.2.1
    rw [hbit] at hh
    exact hh
  have hpostBit :
      ((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).bit = true := by
    have hh := hphysical.2.2
    rw [hbit] at hh
    exact hh
  have hcore := bankWindowClosureArmedSetGenuine
    ring hn (bankWindowRootBefore ring seed pre) e
    hJ hscope hm p o hactive horigin hbit
  have hpostController := hcore.2.1
  have hpostOrigin := hcore.2.2.1
  have hpostHeads := hcore.2.2.2
  have hrootOrigin : o.root = e := by
    have hi := rbReceiptInvBankWordOfInv
      ring (by omega : 2 ≤ n) seed hbank pre
    exact (hi.activeRoot e p o hactive horigin).symm
  have hnewValue := bankWindowOverlapSourceActiveBitSetValue
    ring hbank (bankWindowRootBefore ring seed pre) e
    o hrootOrigin hbit hpostBit
  have hnewHeads :
      (renewalBankHead p).heads =
        bankOriginBinaryValue ring
          (bankWindowRootAfter ring seed pre e).1 o := by
    rw [hnewValue]
    exact hpostHeads
  have hnewBound :
      bankOriginBinaryValue ring
        (bankWindowRootAfter ring seed pre e).1 o ≤
          (compileAdvice (ceilLogTwo n)).K := by
    rw [hnewValue]
    have hstrict := hbeforeArmed.2.2.1 hm
    omega
  have houter := bankWindowOverlapSourceActiveOuterDigitsClean
    ring hn hbank seed pre e hJ hscope
    (Or.inl hm) p o hactive horigin
  have hpostTokens :
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        ((bankWindowRootAfter ring seed pre e).1
          (Counter.site ring e (j.val + 1))).tok = .E := by
    intro j
    by_cases hz : j.val = 0
    · rw [hz]
      change ((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).tok = .E
      exact hpostTok
    · exact (houter j (by omega)).2
  have hframe := bankWindowExactFrameStep
    ring hn hbank seed pre e hJ
  have hclean := bankWindowOverlapSourceActiveEmptyTokensClean
    ring (bankWindowRootAfter ring seed pre e) e
    hframe hpostTokens
  have hnoWorker :
      ∀ (o' : RenewalBankOrigin n) (i : Fin n)
        (q : RenewalBankPayload n),
        o'.root = e →
        ((bankWindowRootAfter ring seed pre e).2.sites i).worker =
          .payload q → q.origin = some o' → False := by
    intro o' i q hroot hw hq
    exact bankWindowOverlapSourceActiveNoOriginWorker
      ring hn hbank seed pre e hclean.1
      i q o' hroot hw hq
  have hnoInherited :
      ¬ BankWindowInheritedController
        (bankWindowRootAfter ring seed pre e) e := by
    intro hi
    rcases hi with ⟨atoms, hw, _⟩ | ⟨q, hw, hnone⟩
    · rw [hpostController] at hw
      cases hw
    · rw [hpostController] at hw
      cases hw
      rw [hpostOrigin] at hnone
      cases hnone
  unfold bankWindowOverlapSourceActiveOwnerFields
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o' i q hr hcomp
    exact False.elim (hnoWorker o' i q hr hcomp.1 hcomp.2.1)
  · intro o' i q hr hcomp _
    exact False.elim (hnoWorker o' i q hr hcomp.1 hcomp.2.1)
  · intro o' i q hr hcomp _ _
    exact False.elim (hnoWorker o' i q hr hcomp.1 hcomp.2.1)
  · intro o' i q hr hcomp _
    exact False.elim (hnoWorker o' i q hr hcomp.1 hcomp.2.1)
  · intro _ hi
    exact False.elim (hnoInherited hi)
  · intro _ hw
    rw [hpostMode] at hw
    cases hw
  · intro o' q _ hphasePost hq hqOrigin
    have heq : q = renewalBankHead p := by
      rw [hpostController] at hq
      cases hq
      rfl
    rw [heq] at hqOrigin
    have ho : o' = o := by
      have hh : some o' = some o := hqOrigin.symm.trans hpostOrigin
      exact Option.some.inj hh
    subst o'
    rw [heq]
    refine ⟨hpostTokens, hnewHeads, ?_, ?_⟩
    · intro hw
      rw [hpostMode] at hw
      cases hw
    · intro _
      exact hnewBound
  · intro o' i q _ hw _ _ _ _
    rw [hpostMode] at hw
    cases hw
  · intro o' i q hr hw hq _ _
    exact False.elim (hnoWorker o' i q hr hw hq)
  · intro _ hw
    rw [hpostMode] at hw
    cases hw
  · intro _ hw
    rw [hpostMode] at hw
    cases hw

theorem bankWindowOverlapSourceActiveIncompleteProto
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n)
    (hx : (r.1 e).pack.val = 0)
    (hnot : ¬ Counter.Complete ring r.1 e) :
    ∃ limit : Nat, BankWindowProtoRun ring r e limit := by
  have hchain :
      ∀ k : Nat, k ≤ (compileAdvice (ceilLogTwo n)).b →
        (∀ t : Nat, t ≤ k →
          (r.1 (Counter.site ring e t)).pack.val = t) ∨
        ∃ limit : Nat, limit < k ∧
          (∀ t : Nat, t ≤ limit →
            (r.1 (Counter.site ring e t)).pack.val = t) ∧
          (r.1 (Counter.site ring e (limit + 1))).pack.val ≠
            limit + 1 := by
    intro k
    induction k with
    | zero =>
        intro _
        left
        intro t ht
        have hz : t = 0 := by omega
        rw [hz]
        change (r.1 e).pack.val = 0
        exact hx
    | succ k ih =>
        intro hk
        rcases ih (by omega) with hall | ⟨limit, hlt, hgood, hbad⟩
        · by_cases hnext :
            (r.1 (Counter.site ring e (k + 1))).pack.val =
              k + 1
          · left
            intro t ht
            by_cases hlast : t = k + 1
            · rw [hlast]
              exact hnext
            · exact hall t (by omega)
          · right
            exact ⟨k, by omega, hall, hnext⟩
        · right
          exact ⟨limit, by omega, hgood, hbad⟩
  rcases hchain (compileAdvice (ceilLogTwo n)).b
      (Nat.le_refl _) with hall | ⟨limit, hlt, hgood, hbad⟩
  · exact False.elim (hnot hall)
  · exact ⟨limit, hlt, hgood, hbad⟩

/-- An authentic OLD ARMED or CSTART genuine active controller
at a PACK-zero source forces the entire physical digit
window to be complete. Otherwise OLD J.proto at its first
mismatch forbids that genuine active controller.
Consumer: M2 SRC A0/A1/S0/S1 genuine-source dispatch
without an extra completeness premise. -/
theorem bankWindowOverlapSourceActiveGenuineComplete
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n)
    (hJ : BankWindowExact ring r)
    (hx : (r.1 e).pack.val = 0)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hactive : (r.2.sites e).controller = .active p)
    (horigin : p.origin = some o) :
    Counter.Complete ring r.1 e := by
  by_cases hcomplete : Counter.Complete ring r.1 e
  · exact hcomplete
  · obtain ⟨limit, hproto⟩ :=
      bankWindowOverlapSourceActiveIncompleteProto
        ring r e hx hcomplete
    exact False.elim ((hJ.proto e limit hproto).1
      p o hactive horigin)

/-- ARMED A0 for every genuine OLD active controller at a
PACK-zero, grant-free source, without assuming completeness:
OLD J.proto derives it. The complete ARMED-set row then
supplies all eleven POST root clauses. Consumer:
BankWindowOverlapJoint M2 SRC ARMED A0 dispatch. -/
theorem bankWindowOverlapSourceActiveArmedSetGenuineFields
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hx : ((bankWindowRootBefore ring seed pre).1 e).pack.val = 0)
    (hg : ((bankWindowRootBefore ring seed pre).1 e).grant = false)
    (hm : ((bankWindowRootBefore ring seed pre).1 e).mode = .ARMED)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hactive :
      ((bankWindowRootBefore ring seed pre).2.sites e).controller =
        .active p)
    (horigin : p.origin = some o)
    (hbit :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).bit = false) :
    bankWindowOverlapSourceActiveOwnerFields ring
      (bankWindowRootAfter ring seed pre e) e := by
  have hscope : BankWindowScope ring
      (bankWindowRootBefore ring seed pre) e :=
    ⟨bankWindowOverlapSourceActiveGenuineComplete
      ring (bankWindowRootBefore ring seed pre)
      e hJ hx p o hactive horigin, hg⟩
  exact bankWindowOverlapSourceActiveArmedSetFields
    ring hn hbank seed pre e hJ hscope hm p o
    hactive horigin hbit

theorem bankWindowOverlapSourceActiveInheritedOldClean
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n)
    (hJ : BankWindowExact ring r)
    (hx : (r.1 e).pack.val = 0)
    (hg : (r.1 e).grant = false)
    (hm : (r.1 e).mode = .ARMED ∨
      (r.1 e).mode = .CSTART)
    (p : RenewalBankPayload n)
    (hactive : (r.2.sites e).controller = .active p)
    (hnone : p.origin = none)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (haligned :
      (r.1 (Counter.site ring e (j.val + 1))).pack.val =
        j.val + 1) :
    ¬ BankWindowTainted r
      (Counter.site ring e (j.val + 1)) := by
  have hinherited : BankWindowInheritedController r e :=
    Or.inr ⟨p, hactive, hnone⟩
  by_cases hcomplete : Counter.Complete ring r.1 e
  · exact hJ.inheritedClean e ⟨hcomplete, hg⟩
      hinherited j
  · obtain ⟨limit, hproto⟩ :=
      bankWindowOverlapSourceActiveIncompleteProto
        ring r e hx hcomplete
    have hnotReset : (r.1 e).mode ≠ .RESET := by
      rcases hm with hh | hh <;>
        (intro h; rw [hh] at h; cases h)
    have hnotRwait : (r.1 e).mode ≠ .RWAIT := by
      rcases hm with hh | hh <;>
        (intro h; rw [hh] at h; cases h)
    intro htainted
    by_cases hbefore : j.val + 1 ≤ limit
    · exact ((hJ.proto e limit hproto).2.1
        hinherited j hbefore) htainted
    · have howner : BankWindowOrphanOwner ring r e j := by
        refine ⟨hx, haligned, ?_⟩
        intro hall
        exact hproto.2.2
          (hall (limit + 1) (by omega))
      rcases hJ.orphan e j howner htainted with
        hreset | ⟨hwait, _⟩
      · exact hnotReset hreset
      · exact hnotRwait hwait

/-- A real post genuine worker of origin root e creates a
tainted physical digit of e, by the authenticated workerSite
certificate. If every post digit is untainted, such a worker
cannot exist anywhere. Consumer: M2 inherited ARMED/CSTART
phaseExcludes, compareExact and incrementExact. -/
theorem bankWindowOverlapSourceActiveNoOwnGenuineFromClean
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hclean :
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        ¬ BankWindowTainted
          (bankWindowRootAfter ring seed pre e)
          (Counter.site ring e (j.val + 1)))
    (i : Fin n) (q : RenewalBankPayload n)
    (o : RenewalBankOrigin n)
    (hroot : o.root = e)
    (hworker :
      ((bankWindowRootAfter ring seed pre e).2.sites i).worker =
        .payload q)
    (horigin : q.origin = some o) : False := by
  have hrun :
      rbRun ring (renewalBankStart ring seed) (pre ++ [e]) =
        bankWindowRootAfter ring seed pre e := by
    rw [rbRunAppend]
    rfl
  have hworkerRun :
      ((rbRun ring (renewalBankStart ring seed)
        (pre ++ [e])).2.sites i).worker = .payload q := by
    rw [hrun]
    exact hworker
  have hband := bankWindowOverlapGenuineWorkerInBand
    ring hn hbank seed (pre ++ [e]) i q o hworkerRun horigin
  have hsite := bankWindowGenuineWorkerSiteOfRun
    ring hn hbank seed (pre ++ [e]) i q o hworkerRun horigin
  rw [hrun] at hband hsite
  rw [hroot] at hsite
  have hindex :
      ((bankWindowRootAfter ring seed pre e).1 i).pack.val - 1 <
        (compileAdvice (ceilLogTwo n)).b := by omega
  have hindexSucc :
      ((bankWindowRootAfter ring seed pre e).1 i).pack.val - 1 + 1 =
        ((bankWindowRootAfter ring seed pre e).1 i).pack.val := by
    omega
  have hsiteAt :
      Counter.site ring e
        (((bankWindowRootAfter ring seed pre e).1 i).pack.val - 1 + 1) =
          i := by
    rw [hindexSucc]
    exact hsite.symm
  have hcontra := hclean
    (⟨((bankWindowRootAfter ring seed pre e).1 i).pack.val - 1,
      hindex⟩ : Fin (compileAdvice (ceilLogTwo n)).b)
  change ¬ BankWindowTainted
    (bankWindowRootAfter ring seed pre e)
    (Counter.site ring e
      (((bankWindowRootAfter ring seed pre e).1 i).pack.val - 1 + 1))
    at hcontra
  rw [hsiteAt] at hcontra
  exact hcontra (Or.inr ⟨q, o, hworker, horigin⟩)

/-- A reachable source-root successor with no tainted digit
workers and no genuine active controller satisfies all eleven
non-PFX/ORPH fields in modes CSTART, IWAIT or CWAIT.
The real POST workerSite rules out unlocated genuine worker
antecedents; inheritedClean and tainted-unique are discharged
by actual worker cleanliness, not by a hypothetical POST J.
Consumer: BankWindowOverlapJoint M2 inherited active rows. -/
theorem bankWindowOverlapSourceActiveCleanOwnerFields
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hphase :
      ((bankWindowRootAfter ring seed pre e).1 e).mode = .CSTART ∨
      ((bankWindowRootAfter ring seed pre e).1 e).mode = .IWAIT ∨
      ((bankWindowRootAfter ring seed pre e).1 e).mode = .CWAIT)
    (hclean :
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        ¬ BankWindowTainted
          (bankWindowRootAfter ring seed pre e)
          (Counter.site ring e (j.val + 1)))
    (hnoActive :
      ∀ (q : RenewalBankPayload n) (o : RenewalBankOrigin n),
        ((bankWindowRootAfter ring seed pre e).2.sites e).controller =
          .active q → q.origin = some o → False) :
    bankWindowOverlapSourceActiveOwnerFields ring
      (bankWindowRootAfter ring seed pre e) e := by
  have hnoWorker :
      ∀ (o : RenewalBankOrigin n) (i : Fin n)
        (q : RenewalBankPayload n),
        o.root = e →
        ((bankWindowRootAfter ring seed pre e).2.sites i).worker =
          .payload q → q.origin = some o → False := by
    intro o i q hroot hw ho
    exact bankWindowOverlapSourceActiveNoOwnGenuineFromClean
      ring hn hbank seed pre e hclean i q o hroot hw ho
  have hnotRwait :
      ((bankWindowRootAfter ring seed pre e).1 e).mode ≠ .RWAIT := by
    intro hm
    rcases hphase with hh | hh | hh <;>
      (rw [hh] at hm; cases hm)
  unfold bankWindowOverlapSourceActiveOwnerFields
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o i q hroot hcomp
    exact False.elim (hnoWorker o i q hroot hcomp.1 hcomp.2.1)
  · intro o i q hroot hcomp _
    exact False.elim (hnoWorker o i q hroot hcomp.1 hcomp.2.1)
  · intro o i q hroot hcomp _ _
    exact False.elim (hnoWorker o i q hroot hcomp.1 hcomp.2.1)
  · intro o i q hroot hcomp _
    exact False.elim (hnoWorker o i q hroot hcomp.1 hcomp.2.1)
  · intro _ _ j
    exact hclean j
  · intro _ hm
    exact False.elim (hnotRwait hm)
  · intro o q _ _ hctl ho
    exact False.elim (hnoActive q o hctl ho)
  · intro o i q _ _ _ hw ho hroot
    exact False.elim (hnoWorker o i q hroot hw ho)
  · intro o i q hroot hw ho _ _
    exact False.elim (hnoWorker o i q hroot hw ho)
  · intro _ _ _ j ht
    exact False.elim (hclean j ht)
  · intro _ _ _ j ht
    exact False.elim (hclean j ht)

theorem bankWindowOverlapSourceActiveInheritedCstartMemory
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hm : x.mode = .CSTART) (ht : y.tok = .E)
    (p : RenewalBankPayload n)
    (hactive : (m.sites e).controller = .active p)
    (hnone : p.origin = none) :
    (renewalBankPairMemory c m e dest x y).1.controller =
      .waiting [] ∧
    (renewalBankPairMemory c m e dest x y).2.worker =
      .payload p ∧ p.origin = none := by
  have hrow := rbRootCstartMemoryExact
    c m e dest x y hb hx hy hg hm ht
  rw [hrow]
  simp [rbRootCstartPair, renewalBankActivePayload, hactive,
    hnone]

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

/-- The exact eleven root-indexed BankWindowExact clauses excluding
proto and orphan. They are the first eleven conjunction components
of Joint.BankWindowRootFieldsAt, but defined in the Root module
to avoid importing Joint (which imports Root).
Consumer: M2 source counting row transitions in BankWindowOverlapJoint. -/
def bankWindowOverlapSourceCountingOwnFields {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (root : Fin n) : Prop :=
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
          (Counter.site ring root (j.val + 1)))

/-- A RESET source root with empty real controller meets all eleven
root-indexed clause obligations. This is a consequence of the actual
POST mode and ghost-controller fields, not a POST J assumption.
Consumer: source CWAIT CL1 and IWAIT/CWAIT timeout rows, M2. -/
theorem bankWindowOverlapSourceCountingResetOwnFields
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n)
    (hmode : (r.1 root).mode = .RESET)
    (hctl : (r.2.sites root).controller = .empty) :
    bankWindowOverlapSourceCountingOwnFields ring r root := by
  unfold bankWindowOverlapSourceCountingOwnFields
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o i p ho _
    have hm : (r.1 o.root).mode = .RESET := by
      rw [ho]
      exact hmode
    rw [hm]
    exact ⟨(by intro h; cases h), (by intro h; cases h),
      (by intro h; cases h)⟩
  · intro o i p ho _ hm
    rw [ho, hmode] at hm
    cases hm
  · intro o i p ho _ hm
    rw [ho, hmode] at hm
    cases hm
  · intro o i p ho _ hm
    rw [ho, hmode] at hm
    cases hm
  · intro _ hi
    unfold BankWindowInheritedController at hi
    rcases hi with ⟨atoms, hw, _⟩ | ⟨p, hw, _⟩
    · rw [hctl] at hw
      cases hw
    · rw [hctl] at hw
      cases hw
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
    rw [ho, hmode] at hm
    cases hm
  · intro _ hm
    rw [hmode] at hm
    cases hm
  · intro _ hm
    rw [hmode] at hm
    cases hm


/-- CWAIT/CL1 consumes the first-digit return, resets the source
and clears its ghost root controller. Consequently all eleven
source-root phase, inherited, resetWait, armed, increment, compare
and tainted-uniqueness clauses follow. Consumer: M2 SRC CWAIT CL1
in BankWindowOverlapJoint. -/
theorem bankWindowOverlapSourceCountingCwaitClOneOwnFields
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hscope : BankWindowScope ring
      (bankWindowRootBefore ring seed pre) e)
    (hm : ((bankWindowRootBefore ring seed pre).1 e).mode = .CWAIT)
    (ht : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).tok = .CL1) :
    bankWindowOverlapSourceCountingOwnFields ring
      (bankWindowRootAfter ring seed pre e) e := by
  have hrow :=
    bankWindowClosureClOneReturnClears ring hn hbank
      (bankWindowRootBefore ring seed pre) e
      hscope.1 hscope.2 hm ht
  exact bankWindowOverlapSourceCountingResetOwnFields
    ring (bankWindowRootAfter ring seed pre e) e
    hrow.2.1 hrow.2.2.1

/-- Exact selected 0-to-1 row with an expired IWAIT/CWAIT
and nonreturn first-digit token E. Unlike a theorem quantified
over arbitrary return tokens, this proves the actual timeout
branch's physical RESET and empty root controller.
Consumer: M2 SRC IWAIT I1 timeout and CWAIT timeout. -/
theorem bankWindowOverlapSourceCountingTimedOutPair
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b) (hwide : c.b ≠ 1)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hm : x.mode = .IWAIT ∨ x.mode = .CWAIT)
    (ht : y.tok = .E)
    (hl : x.lease.val ≤ 1) :
    (Counter.resetBankOld x y).1.mode = .RESET ∧
    (renewalBankPairMemory c m e dest x y).1.controller =
      .empty := by
  have hbz : c.b ≠ 0 := by omega
  have hp : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  have hno : ¬ 1 < x.lease.val := by omega
  rcases hm with hm | hm <;> constructor
  · simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hg, hm, ht, hb, hbz, hp, hwide,
      hno, isRetTok, isWaitMode, Id.run_pure, Id.run_bind]
  · simp [renewalBankPairMemory, renewalBankWaitSlot,
      bankCell, hx, hy, hg, hm, ht, hb, hbz, hp,
      hwide, hno, isRetTok, isWaitMode,
      Id.run_pure, Id.run_bind]
  · simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hg, hm, ht, hb, hbz, hp, hwide,
      hno, isRetTok, isWaitMode, Id.run_pure, Id.run_bind]
  · simp [renewalBankPairMemory, renewalBankWaitSlot,
      bankCell, hx, hy, hg, hm, ht, hb, hbz, hp,
      hwide, hno, isRetTok, isWaitMode,
      Id.run_pure, Id.run_bind]

/-- The complete real source window in an IWAIT/CWAIT timeout
has RESET mode and empty controller, and hence all eleven
root clauses. Nonreturn token E and lease <= 1 select the
literal timeout row. Consumer: M2 SRC waiting expiration. -/
theorem bankWindowOverlapSourceCountingTimedOutOwnFields
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hscope : BankWindowScope ring
      (bankWindowRootBefore ring seed pre) e)
    (hm :
      ((bankWindowRootBefore ring seed pre).1 e).mode = .IWAIT ∨
      ((bankWindowRootBefore ring seed pre).1 e).mode = .CWAIT)
    (ht :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .E)
    (hl : ((bankWindowRootBefore ring seed pre).1 e).lease.val ≤ 1) :
    bankWindowOverlapSourceCountingOwnFields ring
      (bankWindowRootAfter ring seed pre e) e := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hwide : (compileAdvice (ceilLogTwo n)).b ≠ 1 := by
    change (compileAdvice (ceilLogTwo n)).s + 11 ≠ 1
    omega
  have hx :
      ((bankWindowRootBefore ring seed pre).1 e).pack.val = 0 := by
    change ((bankWindowRootBefore ring seed pre).1
      (Counter.site ring e 0)).pack.val = 0
    exact hscope.1 0 (by omega)
  have hy :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val = 1 := by
    change ((bankWindowRootBefore ring seed pre).1
      (Counter.site ring e 1)).pack.val = 1
    exact hscope.1 1 (by omega)
  have hraw := bankWindowOverlapSourceCountingTimedOutPair
    (compileAdvice (ceilLogTwo n))
    (bankWindowRootBefore ring seed pre).2
    e (ring.rightNeighbor e)
    ((bankWindowRootBefore ring seed pre).1 e)
    ((bankWindowRootBefore ring seed pre).1 (ring.rightNeighbor e))
    hb hwide hx hy hscope.2 hm ht hl
  have htrip := (bankWindowClosureSelectedBankTrip
    ring hn hbank (bankWindowRootBefore ring seed pre) e).1
  have hmode := congrArg
    (fun t : Mode × Bool × BTok => t.1) htrip
  change ((bankWindowRootAfter ring seed pre e).1 e).mode =
    (Counter.resetBankOld
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).1.mode at hmode
  have hmodePost :
      ((bankWindowRootAfter ring seed pre e).1 e).mode =
        .RESET := hmode.trans hraw.1
  have hframe := (rbReferenceSelectedPairFrame ring
    (by omega : 2 ≤ n) (bankWindowRootBefore ring seed pre) e).2.2.1
  have hctl := congrArg
    (fun q : RenewalBankSite n => q.controller) hframe
  change ((bankWindowRootAfter ring seed pre e).2.sites e).controller =
    (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
      (bankWindowRootBefore ring seed pre).2
      e (ring.rightNeighbor e)
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).1.controller at hctl
  have hctlPost :
      ((bankWindowRootAfter ring seed pre e).2.sites e).controller =
        .empty := hctl.trans hraw.2
  exact bankWindowOverlapSourceCountingResetOwnFields
    ring (bankWindowRootAfter ring seed pre e) e
    hmodePost hctlPost


/-- The exhausted IWAIT nonreturn-E subcase of source I1
has every post-root clause, because the literal old BANK
pair resets the root and clears the controller.
Consumer: M2 SRC IWAIT I1 timeout in BankWindowOverlapJoint. -/
theorem bankWindowOverlapSourceCountingIwaitExpiredOwnFields
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hscope : BankWindowScope ring
      (bankWindowRootBefore ring seed pre) e)
    (hm : ((bankWindowRootBefore ring seed pre).1 e).mode = .IWAIT)
    (ht : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).tok = .E)
    (hl : ((bankWindowRootBefore ring seed pre).1 e).lease.val ≤ 1) :
    bankWindowOverlapSourceCountingOwnFields ring
      (bankWindowRootAfter ring seed pre e) e := by
  exact bankWindowOverlapSourceCountingTimedOutOwnFields
    ring hn hbank seed pre e hJ hscope (Or.inl hm) ht hl

/-- The exhausted CWAIT nonreturn-E subcase has all eleven
POST root clauses. The still-live CWAIT/CL0 and long-lease
CWAIT rows are separate and are not assumed by this theorem.
Consumer: M2 SRC CWAIT timeout in BankWindowOverlapJoint. -/
theorem bankWindowOverlapSourceCountingCwaitExpiredOwnFields
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hscope : BankWindowScope ring
      (bankWindowRootBefore ring seed pre) e)
    (hm : ((bankWindowRootBefore ring seed pre).1 e).mode = .CWAIT)
    (ht : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).tok = .E)
    (hl : ((bankWindowRootBefore ring seed pre).1 e).lease.val ≤ 1) :
    bankWindowOverlapSourceCountingOwnFields ring
      (bankWindowRootAfter ring seed pre e) e := by
  exact bankWindowOverlapSourceCountingTimedOutOwnFields
    ring hn hbank seed pre e hJ hscope (Or.inr hm) ht hl


theorem bankWindowOverlapSourceCountingNonexpiredPair
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b) (hwide : c.b ≠ 1)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hm : x.mode = .IWAIT ∨ x.mode = .CWAIT)
    (ht : y.tok = .E)
    (hl : 1 < x.lease.val) :
    (Counter.resetBankOld x y).1.mode = x.mode ∧
    (renewalBankPairMemory c m e dest x y).1.controller =
      (m.sites e).controller := by
  have hbz : c.b ≠ 0 := by omega
  have hp : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  rcases hm with hm | hm <;> constructor
  · simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hg, hm, ht, hb, hbz, hp, hwide,
      hl, isRetTok, isWaitMode, Id.run_pure, Id.run_bind]
  · simp [renewalBankPairMemory, renewalBankWaitSlot,
      bankCell, hx, hy, hg, hm, ht, hb, hbz, hp,
      hwide, hl, isRetTok, isWaitMode,
      Id.run_pure, Id.run_bind]
  · simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hg, hm, ht, hb, hbz, hp, hwide,
      hl, isRetTok, isWaitMode, Id.run_pure, Id.run_bind]
  · simp [renewalBankPairMemory, renewalBankWaitSlot,
      bankCell, hx, hy, hg, hm, ht, hb, hbz, hp,
      hwide, hl, isRetTok, isWaitMode,
      Id.run_pure, Id.run_bind]

/-- Transport the nonexpired idle IWAIT/CWAIT source row from
the literal BANK pair to the real masked reference step.
Consumer: BankWindowOverlapJoint SRC IWAIT I1 and continuing
CWAIT classification. -/
theorem bankWindowOverlapSourceCountingNonexpiredReal
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hscope : BankWindowScope ring
      (bankWindowRootBefore ring seed pre) e)
    (hm :
      ((bankWindowRootBefore ring seed pre).1 e).mode = .IWAIT ∨
      ((bankWindowRootBefore ring seed pre).1 e).mode = .CWAIT)
    (ht : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).tok = .E)
    (hl : 1 < ((bankWindowRootBefore ring seed pre).1 e).lease.val) :
    ((bankWindowRootAfter ring seed pre e).1 e).mode =
      ((bankWindowRootBefore ring seed pre).1 e).mode ∧
    ((bankWindowRootAfter ring seed pre e).2.sites e).controller =
      ((bankWindowRootBefore ring seed pre).2.sites e).controller := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hwide : (compileAdvice (ceilLogTwo n)).b ≠ 1 := by
    change (compileAdvice (ceilLogTwo n)).s + 11 ≠ 1
    omega
  have hx :
      ((bankWindowRootBefore ring seed pre).1 e).pack.val = 0 := by
    change ((bankWindowRootBefore ring seed pre).1
      (Counter.site ring e 0)).pack.val = 0
    exact hscope.1 0 (by omega)
  have hy :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val = 1 := by
    change ((bankWindowRootBefore ring seed pre).1
      (Counter.site ring e 1)).pack.val = 1
    exact hscope.1 1 (by omega)
  have hraw := bankWindowOverlapSourceCountingNonexpiredPair
    (compileAdvice (ceilLogTwo n))
    (bankWindowRootBefore ring seed pre).2
    e (ring.rightNeighbor e)
    ((bankWindowRootBefore ring seed pre).1 e)
    ((bankWindowRootBefore ring seed pre).1 (ring.rightNeighbor e))
    hb hwide hx hy hscope.2 hm ht hl
  have htrip := (bankWindowClosureSelectedBankTrip
    ring hn hbank (bankWindowRootBefore ring seed pre) e).1
  have hmode := congrArg
    (fun t : Mode × Bool × BTok => t.1) htrip
  change ((bankWindowRootAfter ring seed pre e).1 e).mode =
    (Counter.resetBankOld
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).1.mode at hmode
  have hframe := (rbReferenceSelectedPairFrame ring
    (by omega : 2 ≤ n) (bankWindowRootBefore ring seed pre) e).2.2.1
  have hctl := congrArg
    (fun q : RenewalBankSite n => q.controller) hframe
  change ((bankWindowRootAfter ring seed pre e).2.sites e).controller =
    (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
      (bankWindowRootBefore ring seed pre).2
      e (ring.rightNeighbor e)
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).1.controller at hctl
  exact ⟨hmode.trans hraw.1, hctl.trans hraw.2⟩


theorem bankWindowOverlapSourceCountingCstartOwnFieldsFromReturn
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hmode : (r.1 root).mode = .CSTART)
    (hactive : (r.2.sites root).controller = .active p)
    (horigin : p.origin = some o)
    (hnoComparator :
      ∀ (o' : RenewalBankOrigin n) (i : Fin n)
        (q : RenewalBankPayload n),
        o'.root = root →
        BankComparatorOriginWorker ring r o' i q → False)
    (htokens :
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        (r.1 (Counter.site ring root (j.val + 1))).tok = .E)
    (hheads : p.heads = bankOriginBinaryValue ring r.1 o)
    (hcredit :
      bankOriginBinaryValue ring r.1 o ≤
        (compileAdvice (ceilLogTwo n)).K) :
    bankWindowOverlapSourceCountingOwnFields ring r root := by
  unfold bankWindowOverlapSourceCountingOwnFields
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
  · intro o' q _ hm hctl hqorigin
    have hq : q = p := by
      rw [hactive] at hctl
      cases hctl
      rfl
    subst q
    have ho : o' = o := by
      exact Option.some.inj (hqorigin.symm.trans horigin)
    subst o'
    refine ⟨htokens, hheads, ?_, ?_⟩
    · intro h
      rw [hmode] at h
      cases h
    · intro _
      exact hcredit
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


theorem bankWindowOverlapSourceCountingCwaitClZeroMismatch
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n)
    (hJ : BankWindowExact ring r)
    (hm : (r.1 root).mode = .CWAIT)
    (hwait : (r.2.sites root).controller = .waiting [])
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hw : (r.2.sites (ring.rightNeighbor root)).worker =
      .payload p)
    (ho : p.origin = some o)
    (hroot : o.root = root)
    (ht : (r.1 (ring.rightNeighbor root)).tok = .CL0) :
    ¬ bankComparatorPrefixMatched ring r o
      (compileAdvice (ceilLogTwo n)).b ∧
    bankOriginBinaryValue ring r.1 o ≤
      (compileAdvice (ceilLogTwo n)).K := by
  have htoken :
      BankTrialLiveComparisonToken
        (r.1 (ring.rightNeighbor root)).tok := by
    rw [ht]
    simp [BankTrialLiveComparisonToken]
  have hcomp : BankComparatorOriginWorker ring
      r o (ring.rightNeighbor root) p := ⟨hw, ho, htoken⟩
  have hflags := hJ.phaseFlags o
    (ring.rightNeighbor root) p hcomp
    (by rw [hroot]; exact hm)
  have hcredit := hJ.compareExact o
    (ring.rightNeighbor root) p hw ho
    (by rw [hroot]; exact hm)
    (by rw [hroot]; exact hwait)
  exact ⟨hflags.2.2.2 ht, hcredit.2.2.2⟩

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

/-- At a stable TOP source (role b), the ghost BANK pair has one
possible deletion: the source IR erasure row deletes its worker.
Every other source token retains the OLD source worker, and no
responder token can copy a worker backwards from the exterior.
The responder worker is always erased.
Consumer: BankWindowOverlapJoint M6-T TOP field transport. -/
theorem bankWindowOverlapTopGhostStablePairRaw {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (htop : x.pack.val = c.b)
    (hstable : packNext x.pack.val y.pack.val c.b = y.pack.val) :
    (renewalBankPairMemory c m e dest x y).1.worker =
      (if x.tok = .IR then .empty else (m.sites e).worker) ∧
    (renewalBankPairMemory c m e dest x y).2.worker =
      .empty := by
  have hb : 0 < c.b := by
    change 0 < c.s + 11
    omega
  have hbz : c.b ≠ 0 := by omega
  -- The source is nonroot (TOP): only the worker rows of the ghost memory run.
  have hxn : x.pack.val ≠ 0 := by omega
  have hW := L3.HeadlineRenewal.renewalBankPairMemory_nonroot_workers c m e dest x y hxn
  rw [hW.1, hW.2]
  by_cases hyzero : y.pack.val = 0
  · have hp : packNext c.b 0 c.b = 0 := by
      simp [packNext]
    by_cases hir : x.tok = .IR
    · by_cases hyt : y.tok = .IR <;>
        simp [L3.HeadlineRenewal.bankMemoryNRW, bankCell,
          htop, hyzero, hb, hbz, hp, hir, hyt]
    · by_cases hyt : y.tok = .IR <;>
        simp [L3.HeadlineRenewal.bankMemoryNRW, bankCell,
          htop, hyzero, hb, hbz, hp, hir, hyt]
  · have hpost : packNext c.b y.pack.val c.b = c.b + 1 := by
      simp [packNext, hyzero]
    have hy : y.pack.val = c.b + 1 := by
      have hs := hstable
      rw [htop, hpost] at hs
      exact hs.symm
    have houtside : ¬ c.b + 1 ≤ c.b := by omega
    have hp : packNext c.b (c.b + 1) c.b = c.b + 1 := by
      simp [packNext]
    by_cases hir : x.tok = .IR
    · by_cases hyt : y.tok = .IR <;>
        simp [L3.HeadlineRenewal.bankMemoryNRW, bankCell,
          htop, hy, hb, hbz, houtside, hp, hir, hyt]
    · by_cases hyt : y.tok = .IR <;>
        simp [L3.HeadlineRenewal.bankMemoryNRW, bankCell,
          htop, hy, hb, hbz, houtside, hp, hir, hyt]

theorem bankWindowOverlapTopGhostStableTaintPreimage {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (htop : (r.1 e).pack.val = (compileAdvice (ceilLogTwo n)).b)
    (hstable :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
        (r.1 (ring.rightNeighbor e)).pack.val) :
    (BankWindowTainted (renewalBankNext ring r e) e →
      BankWindowTainted r e) ∧
    ¬ BankWindowTainted (renewalBankNext ring r e)
      (ring.rightNeighbor e) := by
  have hrow := bankWindowOverlapTopGhostStablePairRaw
    (compileAdvice (ceilLogTwo n)) r.2 e
    (ring.rightNeighbor e) (r.1 e)
    (r.1 (ring.rightNeighbor e)) htop hstable
  have hf := (rbReferenceSelectedPairFrame
    ring (by omega : 2 ≤ n) r e).2.2
  have hs := congrArg
    (fun z : RenewalBankSite n => z.worker) hf.1
  have hd := congrArg
    (fun z : RenewalBankSite n => z.worker) hf.2
  change ((renewalBankNext ring r e).2.sites e).worker =
    (renewalBankPairMemory
      (compileAdvice (ceilLogTwo n)) r.2 e
      (ring.rightNeighbor e) (r.1 e)
      (r.1 (ring.rightNeighbor e))).1.worker at hs
  change ((renewalBankNext ring r e).2.sites
    (ring.rightNeighbor e)).worker =
    (renewalBankPairMemory
      (compileAdvice (ceilLogTwo n)) r.2 e
      (ring.rightNeighbor e) (r.1 e)
      (r.1 (ring.rightNeighbor e))).2.worker at hd
  have hsrc := hs.trans hrow.1
  have hdst := hd.trans hrow.2
  constructor
  · intro ht
    by_cases hir : (r.1 e).tok = .IR
    · have hzero :
        ((renewalBankNext ring r e).2.sites e).worker = .empty := by
        rw [if_pos hir] at hsrc
        exact hsrc
      rcases ht with ⟨rho, hw⟩ | ⟨p, o, hw, ho⟩
      · rw [hzero] at hw
        cases hw
      · rw [hzero] at hw
        cases hw
    · have hkeep :
        ((renewalBankNext ring r e).2.sites e).worker =
          (r.2.sites e).worker := by
        rw [if_neg hir] at hsrc
        exact hsrc
      rcases ht with ⟨rho, hw⟩ | ⟨p, o, hw, ho⟩
      · exact Or.inl ⟨rho, hkeep.symm.trans hw⟩
      · exact Or.inr ⟨p, o, hkeep.symm.trans hw, ho⟩
  · intro ht
    rcases ht with ⟨rho, hw⟩ | ⟨p, o, hw, ho⟩
    · rw [hdst] at hw
      cases hw
    · rw [hdst] at hw
      cases hw

/-- Non-IR stable TOP source: physical TOP bits and token and its
ghost worker are all framed. The sole exceptional top source
row is IR-erasure. Consumer: M6-T digit-read transport. -/
theorem bankWindowOverlapTopGhostStableSourceReads {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (htop : (r.1 e).pack.val = (compileAdvice (ceilLogTwo n)).b)
    (hstable :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
        (r.1 (ring.rightNeighbor e)).pack.val)
    (hnoIR : (r.1 e).tok ≠ .IR) :
    bankWindowReadPack r (renewalBankNext ring r e) e ∧
    bankWindowReadTok r (renewalBankNext ring r e) e ∧
    bankWindowReadBit r (renewalBankNext ring r e) e ∧
    bankWindowReadWorker r (renewalBankNext ring r e) e := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hpack := bankWindowClosureRepairNonresponderPackFixed
    ring (by omega : 2 ≤ n) r e e
    (clockNeighborDifferent ring (by omega : 2 ≤ n) e).symm
  have hraw :
      (Counter.resetBankOld (r.1 e)
        (r.1 (ring.rightNeighbor e))).1.bit = (r.1 e).bit ∧
      (Counter.resetBankOld (r.1 e)
        (r.1 (ring.rightNeighbor e))).1.tok = (r.1 e).tok := by
    exact Counter.resetTrialBankTopSourceNoIR
      (bankCell (r.1 e) (r.1 e).pack.val)
      (bankCell (r.1 (ring.rightNeighbor e))
        (r.1 (ring.rightNeighbor e)).pack.val)
      (compileAdvice (ceilLogTwo n)).b
      (compileAdvice (ceilLogTwo n)).theta htop hb hnoIR
  have hghost := bankWindowOverlapTopGhostStablePairRaw
    (compileAdvice (ceilLogTwo n)) r.2
    e (ring.rightNeighbor e) (r.1 e)
    (r.1 (ring.rightNeighbor e)) htop hstable
  have hrawWorker :
      (renewalBankPairMemory
        (compileAdvice (ceilLogTwo n)) r.2 e
        (ring.rightNeighbor e) (r.1 e)
        (r.1 (ring.rightNeighbor e))).1.worker =
          (r.2.sites e).worker := by
    have hw := hghost.1
    rw [if_neg hnoIR] at hw
    exact hw
  have htrip := bankWindowClosureSelectedBankTrip
    ring hn hbank r e
  have htok := congrArg
    (fun t : Mode × Bool × BTok => t.2.2) htrip.1
  have hbit := congrArg
    (fun t : Mode × Bool × BTok => t.2.1) htrip.1
  change ((renewalBankNext ring r e).1 e).tok =
    (Counter.resetBankOld (r.1 e)
      (r.1 (ring.rightNeighbor e))).1.tok at htok
  change ((renewalBankNext ring r e).1 e).bit =
    (Counter.resetBankOld (r.1 e)
      (r.1 (ring.rightNeighbor e))).1.bit at hbit
  have hf := (rbReferenceSelectedPairFrame
    ring (by omega : 2 ≤ n) r e).2.2.1
  have hworker := congrArg
    (fun s : RenewalBankSite n => s.worker) hf
  change ((renewalBankNext ring r e).2.sites e).worker =
    (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
      r.2 e (ring.rightNeighbor e)
      (r.1 e) (r.1 (ring.rightNeighbor e))).1.worker
    at hworker
  exact ⟨hpack, htok.trans hraw.2,
    hbit.trans hraw.1, hworker.trans hrawWorker⟩

/-- Stable non-IR TOP service preserves all window digit read
coordinates through b; all earlier digits and the root are off pair.
Consumer: BankWindowOverlapJoint M6-T top field transport. -/
theorem bankWindowOverlapTopGhostStableWindowReads {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e root : Fin n)
    (hbefore : Counter.Complete ring r.1 root)
    (htop :
      e = Counter.site ring root
        (compileAdvice (ceilLogTwo n)).b)
    (hstable :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
        (r.1 (ring.rightNeighbor e)).pack.val)
    (hnoIR : (r.1 e).tok ≠ .IR) :
    bankWindowReadPackPrefix ring r
      (renewalBankNext ring r e) root
      (compileAdvice (ceilLogTwo n)).b ∧
    bankWindowReadDigitTokens ring r
      (renewalBankNext ring r e) root ∧
    bankWindowReadDigitBits ring r
      (renewalBankNext ring r e) root ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      bankWindowReadWorker r (renewalBankNext ring r e)
        (Counter.site ring root (j.val + 1))) ∧
    bankWindowReadGrant r (renewalBankNext ring r e) root ∧
    bankWindowReadMode r (renewalBankNext ring r e) root ∧
    bankWindowReadController r (renewalBankNext ring r e) root := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hsourceRole :
      (r.1 e).pack.val = (compileAdvice (ceilLogTwo n)).b := by
    rw [htop]
    exact hbefore _ (Nat.le_refl _)
  have htopReads := bankWindowOverlapTopGhostStableSourceReads
    ring hn hbank r e hsourceRole hstable hnoIR
  have hearlier :
      ∀ t : Nat, t < (compileAdvice (ceilLogTwo n)).b →
        (renewalBankNext ring r e).1
          (Counter.site ring root t) =
            r.1 (Counter.site ring root t) ∧
        (renewalBankNext ring r e).2.sites
          (Counter.site ring root t) =
            r.2.sites (Counter.site ring root t) := by
    intro t ht
    exact bankWindowOverlapRepairEarlierSiteFrame
      ring hbank r e root
      (compileAdvice (ceilLogTwo n)).b t
      htop (Nat.le_refl _) ht
  have hrootFrame := hearlier 0 hb
  have hpack :
      bankWindowReadPackPrefix ring r
        (renewalBankNext ring r e) root
        (compileAdvice (ceilLogTwo n)).b := by
    intro k hk
    by_cases hlt : k < (compileAdvice (ceilLogTwo n)).b
    · exact congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
          a.pack.val) (hearlier k hlt).1
    · have heq : k = (compileAdvice (ceilLogTwo n)).b := by
        omega
      rw [heq, ← htop]
      exact htopReads.1
  have htoks :
      bankWindowReadDigitTokens ring r
        (renewalBankNext ring r e) root := by
    intro j
    by_cases hlt :
        j.val + 1 < (compileAdvice (ceilLogTwo n)).b
    · exact congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
          a.tok) (hearlier (j.val + 1) hlt).1
    · have heq :
          j.val + 1 = (compileAdvice (ceilLogTwo n)).b := by
        have hj := j.isLt
        omega
      rw [heq, ← htop]
      exact htopReads.2.1
  have hbits :
      bankWindowReadDigitBits ring r
        (renewalBankNext ring r e) root := by
    intro j
    by_cases hlt :
        j.val + 1 < (compileAdvice (ceilLogTwo n)).b
    · exact congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
          a.bit) (hearlier (j.val + 1) hlt).1
    · have heq :
          j.val + 1 = (compileAdvice (ceilLogTwo n)).b := by
        have hj := j.isLt
        omega
      rw [heq, ← htop]
      exact htopReads.2.2.1
  have hworkers :
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        bankWindowReadWorker r (renewalBankNext ring r e)
          (Counter.site ring root (j.val + 1)) := by
    intro j
    by_cases hlt :
        j.val + 1 < (compileAdvice (ceilLogTwo n)).b
    · exact congrArg
        (fun a : RenewalBankSite n => a.worker)
        (hearlier (j.val + 1) hlt).2
    · have heq :
          j.val + 1 = (compileAdvice (ceilLogTwo n)).b := by
        have hj := j.isLt
        omega
      rw [heq, ← htop]
      exact htopReads.2.2.2
  exact ⟨hpack, htoks, hbits, hworkers,
    congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
      a.grant) hrootFrame.1,
    congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
      a.mode) hrootFrame.1,
    congrArg (fun a : RenewalBankSite n =>
      a.controller) hrootFrame.2⟩


/-- A POST genuine comparator rooted at a stable TOP foreign
window cannot be newly copied from its exterior responder.
Every such worker that survives keeps its OLD PACK/token/bit/worker
read coordinates. Consumer: M6-T phaseFlags and compareExact. -/
theorem bankWindowOverlapTopGhostStableGenuineWorkerReads
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e root i : Fin n)
    (htop :
      e = Counter.site ring root
        (compileAdvice (ceilLogTwo n)).b)
    (hbefore : Counter.Complete ring r.1 root)
    (hstable :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
        (r.1 (ring.rightNeighbor e)).pack.val)
    (hnoIR : (r.1 e).tok ≠ .IR)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hworker :
      ((renewalBankNext ring r e).2.sites i).worker =
        .payload p)
    (horigin : p.origin = some o) :
    bankWindowReadPack r (renewalBankNext ring r e) i ∧
    bankWindowReadTok r (renewalBankNext ring r e) i ∧
    bankWindowReadBit r (renewalBankNext ring r e) i ∧
    bankWindowReadWorker r (renewalBankNext ring r e) i := by
  by_cases hsource : i = e
  · subst i
    have hrole :
        (r.1 e).pack.val = (compileAdvice (ceilLogTwo n)).b := by
      rw [htop]
      exact hbefore _ (Nat.le_refl _)
    have ht := bankWindowOverlapTopGhostStableSourceReads
      ring hn hbank r e hrole hstable hnoIR
    exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2⟩
  · by_cases htarget : i = ring.rightNeighbor e
    · subst i
      have hrole :
          (r.1 e).pack.val = (compileAdvice (ceilLogTwo n)).b := by
        rw [htop]
        exact hbefore _ (Nat.le_refl _)
      have hghost := bankWindowOverlapTopGhostStablePairRaw
        (compileAdvice (ceilLogTwo n)) r.2 e
        (ring.rightNeighbor e) (r.1 e)
        (r.1 (ring.rightNeighbor e)) hrole hstable
      have hf := (rbReferenceSelectedPairFrame
        ring (by omega : 2 ≤ n) r e).2.2.2
      have hworkerDest := congrArg
        (fun s : RenewalBankSite n => s.worker) hf
      change ((renewalBankNext ring r e).2.sites
        (ring.rightNeighbor e)).worker =
          (renewalBankPairMemory
            (compileAdvice (ceilLogTwo n)) r.2 e
            (ring.rightNeighbor e) (r.1 e)
            (r.1 (ring.rightNeighbor e))).2.worker at hworkerDest
      have hempty := hworkerDest.trans hghost.2
      rw [hempty] at hworker
      cases hworker
    · have hf := bankWindowExactOffPairAtomicReads
        ring r e i hsource htarget
      exact ⟨hf.1, hf.2.2.1,
        hf.2.2.2.1, hf.2.2.2.2.2.1⟩


/-- M6-T non-IR branch: all thirteen POST root-indexed
BankWindowRootFieldsAt clauses for a stable TOP edge, without
importing BankWindowOverlapJoint. The selected TOP source is
not an IR erasure, and genuine workers cannot arrive from the
exterior responder. Consumer: BankWindowOverlapJoint, TOP M6-T. -/
theorem bankWindowOverlapTopGhostStableNonIrRootClauses
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hcompleteOld : Counter.Complete ring
      (bankWindowRootBefore ring seed pre).1 root)
    (htop :
      e = Counter.site ring root
        (compileAdvice (ceilLogTwo n)).b)
    (hstable :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val)
    (hnoIR : ((bankWindowRootBefore ring seed pre).1 e).tok ≠ .IR) :
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    o.root = root → BankComparatorOriginWorker ring (bankWindowRootAfter ring seed pre e) o i p →
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠ .ARMED ∧
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠ .CSTART ∧
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠ .IWAIT) ∧
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    o.root = root → BankComparatorOriginWorker ring (bankWindowRootAfter ring seed pre e) o i p →
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode = .CWAIT →
      Counter.Complete ring (bankWindowRootAfter ring seed pre e).1 o.root) ∧
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    o.root = root → BankComparatorOriginWorker ring (bankWindowRootAfter ring seed pre e) o i p →
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode = .CWAIT →
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        BankTrialLiveComparisonToken
          ((bankWindowRootAfter ring seed pre e).1 (Counter.site ring o.root (j.val + 1))).tok →
        Counter.site ring o.root (j.val + 1) = i) ∧
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    o.root = root → BankComparatorOriginWorker ring (bankWindowRootAfter ring seed pre e) o i p →
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode = .CWAIT →
      (((bankWindowRootAfter ring seed pre e).1 i).tok = .CR1 →
        bankComparatorPrefixMatched ring (bankWindowRootAfter ring seed pre e) o ((bankWindowRootAfter ring seed pre e).1 i).pack.val) ∧
      (((bankWindowRootAfter ring seed pre e).1 i).tok = .CR0 →
        ¬ bankComparatorPrefixMatched ring (bankWindowRootAfter ring seed pre e) o ((bankWindowRootAfter ring seed pre e).1 i).pack.val) ∧
      (((bankWindowRootAfter ring seed pre e).1 i).tok = .CL1 →
        bankComparatorPrefixMatched ring (bankWindowRootAfter ring seed pre e) o
          (compileAdvice (ceilLogTwo n)).b) ∧
      (((bankWindowRootAfter ring seed pre e).1 i).tok = .CL0 →
        ¬ bankComparatorPrefixMatched ring (bankWindowRootAfter ring seed pre e) o
          (compileAdvice (ceilLogTwo n)).b)) ∧
  (BankWindowScope ring (bankWindowRootAfter ring seed pre e) root →
    BankWindowInheritedController (bankWindowRootAfter ring seed pre e) root →
    ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ¬ BankWindowTainted (bankWindowRootAfter ring seed pre e) (Counter.site ring root (j.val + 1))) ∧
  (BankWindowScope ring (bankWindowRootAfter ring seed pre e) root →
    ((bankWindowRootAfter ring seed pre e).1 root).mode = .RWAIT →
    ((bankWindowRootAfter ring seed pre e).2.sites root).controller = .waiting [] →
    ∃ (j : Fin (compileAdvice (ceilLogTwo n)).b)
      (rho : RenewalBankReceipt n),
      ((bankWindowRootAfter ring seed pre e).2.sites (Counter.site ring root (j.val + 1))).worker =
        .pending rho ∧
      (((bankWindowRootAfter ring seed pre e).1 (Counter.site ring root (j.val + 1))).tok = .RR ∨
       ((bankWindowRootAfter ring seed pre e).1 (Counter.site ring root (j.val + 1))).tok = .RL) ∧
      bankWindowZeroPrefix ring (bankWindowRootAfter ring seed pre e) root (j.val + 1) ∧
      (∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
        k.val < j.val →
        ((bankWindowRootAfter ring seed pre e).1 (Counter.site ring root (k.val + 1))).tok = .E) ∧
      (((bankWindowRootAfter ring seed pre e).1 (Counter.site ring root (j.val + 1))).tok = .RL →
        bankWindowOnlyToken ring (bankWindowRootAfter ring seed pre e) root
          (Counter.site ring root (j.val + 1)) ∧
        bankWindowZeroPrefix ring (bankWindowRootAfter ring seed pre e) root
          (compileAdvice (ceilLogTwo n)).b)) ∧
  (∀ (o : RenewalBankOrigin n) (p : RenewalBankPayload n),
    BankWindowScope ring (bankWindowRootAfter ring seed pre e) root →
    (((bankWindowRootAfter ring seed pre e).1 root).mode = .ARMED ∨ ((bankWindowRootAfter ring seed pre e).1 root).mode = .CSTART) →
    ((bankWindowRootAfter ring seed pre e).2.sites root).controller = .active p →
    p.origin = some o →
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ((bankWindowRootAfter ring seed pre e).1 (Counter.site ring root (j.val + 1))).tok = .E) ∧
    p.heads = bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o ∧
    (((bankWindowRootAfter ring seed pre e).1 root).mode = .ARMED →
      bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o <
        (compileAdvice (ceilLogTwo n)).K) ∧
    (((bankWindowRootAfter ring seed pre e).1 root).mode = .CSTART →
      bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o ≤
        (compileAdvice (ceilLogTwo n)).K)) ∧
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    BankWindowScope ring (bankWindowRootAfter ring seed pre e) root →
    ((bankWindowRootAfter ring seed pre e).1 root).mode = .IWAIT →
    ((bankWindowRootAfter ring seed pre e).2.sites root).controller = .waiting [] →
    ((bankWindowRootAfter ring seed pre e).2.sites i).worker = .payload p →
    p.origin = some o → o.root = root →
    bankWindowOnlyToken ring (bankWindowRootAfter ring seed pre e) root i ∧
    ((((bankWindowRootAfter ring seed pre e).1 i).tok = .IR ∧
        bankWindowZeroPrefix ring (bankWindowRootAfter ring seed pre e) root ((bankWindowRootAfter ring seed pre e).1 i).pack.val ∧
        p.heads = bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o +
          2 ^ ((bankWindowRootAfter ring seed pre e).1 i).pack.val ∧
        bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o +
          2 ^ ((bankWindowRootAfter ring seed pre e).1 i).pack.val ≤
            (compileAdvice (ceilLogTwo n)).K) ∨
     (((bankWindowRootAfter ring seed pre e).1 i).tok = .AL ∧
        p.heads = bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o ∧
        bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o ≤
          (compileAdvice (ceilLogTwo n)).K))) ∧
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    o.root = root →
    ((bankWindowRootAfter ring seed pre e).2.sites i).worker = .payload p →
    p.origin = some o →
    ((bankWindowRootAfter ring seed pre e).1 o.root).mode = .CWAIT →
    ((bankWindowRootAfter ring seed pre e).2.sites o.root).controller = .waiting [] →
    bankWindowOnlyToken ring (bankWindowRootAfter ring seed pre e) o.root i ∧
    BankTrialLiveComparisonToken ((bankWindowRootAfter ring seed pre e).1 i).tok ∧
    p.heads = bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o ∧
    bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o ≤
      (compileAdvice (ceilLogTwo n)).K) ∧
  (BankWindowScope ring (bankWindowRootAfter ring seed pre e) root →
    ((bankWindowRootAfter ring seed pre e).1 root).mode = .IWAIT →
    ((bankWindowRootAfter ring seed pre e).2.sites root).controller = .waiting [] →
    ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowTainted (bankWindowRootAfter ring seed pre e) (Counter.site ring root (j.val + 1)) →
      ∃ (o : RenewalBankOrigin n) (p : RenewalBankPayload n),
        ((bankWindowRootAfter ring seed pre e).2.sites (Counter.site ring root (j.val + 1))).worker =
          .payload p ∧ p.origin = some o ∧
        o.root = root ∧
        bankWindowOnlyToken ring (bankWindowRootAfter ring seed pre e) root
          (Counter.site ring root (j.val + 1))) ∧
  (BankWindowScope ring (bankWindowRootAfter ring seed pre e) root →
    ((bankWindowRootAfter ring seed pre e).1 root).mode = .CWAIT →
    ((bankWindowRootAfter ring seed pre e).2.sites root).controller = .waiting [] →
    ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowTainted (bankWindowRootAfter ring seed pre e) (Counter.site ring root (j.val + 1)) →
      ∃ (o : RenewalBankOrigin n) (p : RenewalBankPayload n),
        ((bankWindowRootAfter ring seed pre e).2.sites (Counter.site ring root (j.val + 1))).worker =
          .payload p ∧ p.origin = some o ∧
        o.root = root ∧
        BankTrialLiveComparisonToken
          ((bankWindowRootAfter ring seed pre e).1 (Counter.site ring root (j.val + 1))).tok ∧
        bankWindowOnlyToken ring (bankWindowRootAfter ring seed pre e) root
          (Counter.site ring root (j.val + 1))) ∧
  (∀ limit : Nat, BankWindowProtoRun ring (bankWindowRootAfter ring seed pre e) root limit →
    BankWindowRootForeignProtoField ring (bankWindowRootAfter ring seed pre e) root limit) ∧
  (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
    BankWindowOrphanOwner ring (bankWindowRootAfter ring seed pre e) root j →
    BankWindowTainted (bankWindowRootAfter ring seed pre e) (Counter.site ring root (j.val + 1)) →
    ((bankWindowRootAfter ring seed pre e).1 root).mode = .RESET ∨
      (((bankWindowRootAfter ring seed pre e).1 root).mode = .RWAIT ∧
        ((bankWindowRootAfter ring seed pre e).2.sites root).controller = .waiting [])) := by
  have hstablePack :=
    bankWindowOverlapStablePackFrame ring hn seed pre e hstable
  have hcompletePost : Counter.Complete ring
      (bankWindowRootAfter ring seed pre e).1 root := by
    intro k hk
    exact (hstablePack (Counter.site ring root k)).trans
      (hcompleteOld k hk)
  have hreads := bankWindowOverlapTopGhostStableWindowReads
    ring hn hbank (bankWindowRootBefore ring seed pre) e root
    hcompleteOld htop hstable hnoIR
  have hpack : bankWindowReadPackPrefix ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) root
      (compileAdvice (ceilLogTwo n)).b := hreads.1
  have htoks : bankWindowReadDigitTokens ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) root := hreads.2.1
  have hbits : bankWindowReadDigitBits ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) root := hreads.2.2.1
  have hworkers :
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        bankWindowReadWorker
          (bankWindowRootBefore ring seed pre)
          (bankWindowRootAfter ring seed pre e)
          (Counter.site ring root (j.val + 1)) :=
    hreads.2.2.2.1
  have hgrant : bankWindowReadGrant
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) root :=
    hreads.2.2.2.2.1
  have hmode : bankWindowReadMode
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) root :=
    hreads.2.2.2.2.2.1
  have hcontroller : bankWindowReadController
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) root :=
    hreads.2.2.2.2.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o i p horoot hcomp
    have hi := bankWindowOverlapTopGhostStableGenuineWorkerReads
      ring hn hbank (bankWindowRootBefore ring seed pre)
      e root i htop hcompleteOld hstable hnoIR
      p o hcomp.1 hcomp.2.1
    have hm : bankWindowReadMode
        (bankWindowRootBefore ring seed pre)
        (bankWindowRootAfter ring seed pre e) o.root := by
      rw [horoot]
      exact hmode
    exact bankWindowPhaseExcludesReadTransport ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e)
      o i p hJ ⟨hi.2.1, hi.2.2.2, hm⟩ hcomp
  · intro o i p horoot hcomp hphase
    rw [horoot]
    exact hcompletePost
  · intro o i p horoot hcomp hphase j htoken
    have hi := bankWindowOverlapTopGhostStableGenuineWorkerReads
      ring hn hbank (bankWindowRootBefore ring seed pre)
      e root i htop hcompleteOld hstable hnoIR
      p o hcomp.1 hcomp.2.1
    have hm : bankWindowReadMode
        (bankWindowRootBefore ring seed pre)
        (bankWindowRootAfter ring seed pre e) o.root := by
      rw [horoot]
      exact hmode
    have htokenReads : bankWindowReadDigitTokens ring
        (bankWindowRootBefore ring seed pre)
        (bankWindowRootAfter ring seed pre e) o.root := by
      rw [horoot]
      exact htoks
    exact bankWindowPhaseUniqueReadTransport ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e)
      o i p hJ ⟨⟨hi.2.1, hi.2.2.2, hm⟩, htokenReads⟩
      hcomp hphase j htoken
  · intro o i p horoot hcomp hphase
    have hi := bankWindowOverlapTopGhostStableGenuineWorkerReads
      ring hn hbank (bankWindowRootBefore ring seed pre)
      e root i htop hcompleteOld hstable hnoIR
      p o hcomp.1 hcomp.2.1
    have hm : bankWindowReadMode
        (bankWindowRootBefore ring seed pre)
        (bankWindowRootAfter ring seed pre e) o.root := by
      rw [horoot]
      exact hmode
    have hbitReads : bankWindowReadDigitBits ring
        (bankWindowRootBefore ring seed pre)
        (bankWindowRootAfter ring seed pre e) o.root := by
      rw [horoot]
      exact hbits
    exact bankWindowPhaseFlagsReadTransport ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e)
      o i p hJ ⟨⟨hi.2.1, hi.2.2.2, hm⟩,
        hi.1, hbitReads⟩ hcomp hphase
  · intro hscope hinherited j htainted
    exact bankWindowInheritedCleanReadTransport ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e)
      root j hJ ⟨hpack, hgrant, hcontroller, hworkers j⟩
      hscope hinherited htainted
  · intro hscope hwait hctl
    exact bankWindowResetWaitReadTransport ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e)
      root hJ ⟨hpack, hgrant, hmode, hcontroller,
        hbits, htoks, hworkers⟩ hscope hwait hctl
  · intro o p hscope hphase hactive horigin
    have hrootOrigin := (bankWindowOverlapPostReceipt
      ring hn hbank seed pre e).activeRoot
      root p o hactive horigin
    have hbitsOrigin : bankWindowReadDigitBits ring
        (bankWindowRootBefore ring seed pre)
        (bankWindowRootAfter ring seed pre e) o.root := by
      rw [← hrootOrigin]
      exact hbits
    exact bankWindowArmedExactReadTransport ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e)
      root o p hJ ⟨hpack, hgrant, hmode, hcontroller,
        htoks, hbitsOrigin⟩ hscope hphase hactive horigin
  · intro o i p hscope hphase hctl hworker horigin horoot
    have hi := bankWindowOverlapTopGhostStableGenuineWorkerReads
      ring hn hbank (bankWindowRootBefore ring seed pre)
      e root i htop hcompleteOld hstable hnoIR
      p o hworker horigin
    have hbitsOrigin : bankWindowReadDigitBits ring
        (bankWindowRootBefore ring seed pre)
        (bankWindowRootAfter ring seed pre e) o.root := by
      rw [horoot]
      exact hbits
    exact bankWindowIncrementExactReadTransport ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e)
      root o i p hJ ⟨hpack, hgrant, hmode, hcontroller,
        hi.2.2.2, hi.1, hi.2.1, htoks, hbits,
        hbitsOrigin⟩ hscope hphase hctl hworker horigin horoot
  · intro o i p horoot hworker horigin hphase hctl
    have hi := bankWindowOverlapTopGhostStableGenuineWorkerReads
      ring hn hbank (bankWindowRootBefore ring seed pre)
      e root i htop hcompleteOld hstable hnoIR
      p o hworker horigin
    have hmodeOrigin : bankWindowReadMode
        (bankWindowRootBefore ring seed pre)
        (bankWindowRootAfter ring seed pre e) o.root := by
      rw [horoot]
      exact hmode
    have hcontrollerOrigin : bankWindowReadController
        (bankWindowRootBefore ring seed pre)
        (bankWindowRootAfter ring seed pre e) o.root := by
      rw [horoot]
      exact hcontroller
    have htoksOrigin : bankWindowReadDigitTokens ring
        (bankWindowRootBefore ring seed pre)
        (bankWindowRootAfter ring seed pre e) o.root := by
      rw [horoot]
      exact htoks
    have hbitsOrigin : bankWindowReadDigitBits ring
        (bankWindowRootBefore ring seed pre)
        (bankWindowRootAfter ring seed pre e) o.root := by
      rw [horoot]
      exact hbits
    exact bankWindowCompareExactReadTransport ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e)
      o i p hJ
      ⟨hmodeOrigin, hcontrollerOrigin, hi.2.2.2,
        hi.2.1, htoksOrigin, hbitsOrigin⟩
      hworker horigin hphase hctl
  · intro hscope hphase hctl j htainted
    exact bankWindowIwaitTaintedUniqueReadTransport ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e)
      root j hJ
      ⟨hpack, hgrant, hmode, hcontroller, htoks, hworkers j⟩
      hscope hphase hctl htainted
  · intro hscope hphase hctl j htainted
    exact bankWindowCwaitTaintedUniqueReadTransport ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e)
      root j hJ
      ⟨hpack, hgrant, hmode, hcontroller, htoks, hworkers j⟩
      hscope hphase hctl htainted
  · intro limit hproto
    have hwrong := hproto.2.2
    exact False.elim (hwrong
      (hcompletePost (limit + 1)
        (by have hl := hproto.1; omega)))
  · intro j howner htainted
    exact False.elim (howner.2.2
      (by
        intro k hk
        exact hcompletePost k
          (by have hj := j.isLt; omega)))


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

/-- The matched IWAIT/AL source action reactivates the returned genuine worker and enters CSTART. Consumer: M2 SRC IWAIT I0, BankWindowOverlapJoint. -/
theorem bankWindowOverlapSourceCountingIwaitAlReturnFields
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hscope : BankWindowScope ring
      (bankWindowRootBefore ring seed pre) e)
    (hm : ((bankWindowRootBefore ring seed pre).1 e).mode = .IWAIT)
    (hwait :
      ((bankWindowRootBefore ring seed pre).2.sites e).controller =
        .waiting [])
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hw : ((bankWindowRootBefore ring seed pre).2.sites
      (ring.rightNeighbor e)).worker = .payload p)
    (ho : p.origin = some o)
    (hroot : o.root = e)
    (ht : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).tok = .AL) :
    ((bankWindowRootAfter ring seed pre e).1 e).mode = .CSTART ∧
    Counter.Complete ring
      (bankWindowRootAfter ring seed pre e).1 e ∧
    ∃ q : RenewalBankPayload n,
      ((bankWindowRootAfter ring seed pre e).2.sites e).controller =
        .active q ∧
      ((bankWindowRootAfter ring seed pre e).2.sites
        (ring.rightNeighbor e)).worker = .empty ∧
      q.origin = some o ∧
      q.heads = bankOriginBinaryValue ring
        (bankWindowRootBefore ring seed pre).1 o ∧
      q.atoms = [] := by
  have hghost :=
    bankWindowClosureIncrementReturnExactGhost ring hn
      (bankWindowRootBefore ring seed pre) e
      hJ hscope hm hwait p o hw ho hroot ht
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hx :
      ((bankWindowRootBefore ring seed pre).1 e).pack.val = 0 := by
    change ((bankWindowRootBefore ring seed pre).1
      (Counter.site ring e 0)).pack.val = 0
    exact hscope.1 0 (by omega)
  have hy :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val = 1 := by
    change ((bankWindowRootBefore ring seed pre).1
      (Counter.site ring e 1)).pack.val = 1
    exact hscope.1 1 (by omega)
  have hp : packNext 0 1
      (compileAdvice (ceilLogTwo n)).b = 1 := by
    simp [packNext, hb]
  have hbz : (compileAdvice (ceilLogTwo n)).b ≠ 0 := by
    omega
  have hraw :
      (Counter.resetBankOld
        ((bankWindowRootBefore ring seed pre).1 e)
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e))).1.mode = .CSTART := by
    simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hscope.2, hm, ht, hp, hbz,
      hb, isRetTok, Id.run_pure, Id.run_bind]
  have htrip := (bankWindowClosureSelectedBankTrip
    ring hn hbank (bankWindowRootBefore ring seed pre) e).1
  have hmode := congrArg
    (fun t : Mode × Bool × BTok => t.1) htrip
  change ((bankWindowRootAfter ring seed pre e).1 e).mode =
    (Counter.resetBankOld
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).1.mode at hmode
  exact ⟨hmode.trans hraw, hghost⟩

/-- The matched CWAIT/CL0 action reactivates the comparison worker in ARMED with its genuine origin and exact head value. Consumer: M2 SRC CWAIT CL0, BankWindowOverlapJoint. -/
theorem bankWindowOverlapSourceCountingCwaitClZeroReturnFields
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hscope : BankWindowScope ring
      (bankWindowRootBefore ring seed pre) e)
    (hm : ((bankWindowRootBefore ring seed pre).1 e).mode = .CWAIT)
    (hwait :
      ((bankWindowRootBefore ring seed pre).2.sites e).controller =
        .waiting [])
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hw : ((bankWindowRootBefore ring seed pre).2.sites
      (ring.rightNeighbor e)).worker = .payload p)
    (ho : p.origin = some o)
    (hroot : o.root = e)
    (ht : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).tok = .CL0) :
    ((bankWindowRootAfter ring seed pre e).1 e).mode = .ARMED ∧
    Counter.Complete ring
      (bankWindowRootAfter ring seed pre e).1 e ∧
    ∃ q : RenewalBankPayload n,
      ((bankWindowRootAfter ring seed pre e).2.sites e).controller =
        .active q ∧
      ((bankWindowRootAfter ring seed pre e).2.sites
        (ring.rightNeighbor e)).worker = .empty ∧
      q.origin = some o ∧
      q.heads = bankOriginBinaryValue ring
        (bankWindowRootBefore ring seed pre).1 o ∧
      q.atoms = [] := by
  have hghost :=
    bankWindowClosureCompareReturnExactGhost ring hn
      (bankWindowRootBefore ring seed pre) e
      hJ hscope hm hwait p o hw ho hroot ht
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hx :
      ((bankWindowRootBefore ring seed pre).1 e).pack.val = 0 := by
    change ((bankWindowRootBefore ring seed pre).1
      (Counter.site ring e 0)).pack.val = 0
    exact hscope.1 0 (by omega)
  have hy :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val = 1 := by
    change ((bankWindowRootBefore ring seed pre).1
      (Counter.site ring e 1)).pack.val = 1
    exact hscope.1 1 (by omega)
  have hp : packNext 0 1
      (compileAdvice (ceilLogTwo n)).b = 1 := by
    simp [packNext, hb]
  have hbz : (compileAdvice (ceilLogTwo n)).b ≠ 0 := by
    omega
  have hraw :
      (Counter.resetBankOld
        ((bankWindowRootBefore ring seed pre).1 e)
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e))).1.mode = .ARMED := by
    simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hscope.2, hm, ht, hp, hbz,
      hb, isRetTok, Id.run_pure, Id.run_bind]
  have htrip := (bankWindowClosureSelectedBankTrip
    ring hn hbank (bankWindowRootBefore ring seed pre) e).1
  have hmode := congrArg
    (fun t : Mode × Bool × BTok => t.1) htrip
  change ((bankWindowRootAfter ring seed pre e).1 e).mode =
    (Counter.resetBankOld
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).1.mode at hmode
  exact ⟨hmode.trans hraw, hghost⟩

/-- The source IWAIT/AL return excludes every POST comparator belonging to this origin by source ownership, responder erasure and OLD phaseExcludes. Consumer: M2 IWAIT I0 source counting. -/
theorem bankWindowOverlapSourceCountingIwaitNoPostComparator
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hscope : BankWindowScope ring
      (bankWindowRootBefore ring seed pre) e)
    (hm : ((bankWindowRootBefore ring seed pre).1 e).mode = .IWAIT)
    (hclear :
      ((bankWindowRootAfter ring seed pre e).2.sites
        (ring.rightNeighbor e)).worker = .empty) :
    ∀ (o : RenewalBankOrigin n) (i : Fin n)
      (p : RenewalBankPayload n),
      o.root = e →
      BankComparatorOriginWorker ring
        (bankWindowRootAfter ring seed pre e) o i p →
      False := by
  have hx : ((bankWindowRootBefore ring seed pre).1 e).pack.val =
      0 := by
    change ((bankWindowRootBefore ring seed pre).1
      (Counter.site ring e 0)).pack.val = 0
    exact hscope.1 0 (by omega)
  have hselected :=
    bankWindowRootSelectedCarrierOwnership
      ring hn hbank seed pre e hJ hx
  intro o i p hroot hcomp
  by_cases hsource : i = e
  · subst i
    exact hselected.2.2.1 p o hcomp.1 hcomp.2.1
  · by_cases hdest : i = ring.rightNeighbor e
    · subst i
      have hw := hcomp.1
      rw [hclear] at hw
      cases hw
    · have hf := bankWindowExactOffPairFrame
        ring (bankWindowRootBefore ring seed pre) e i
        hsource hdest
      have hworkerFrame :
          ((bankWindowRootAfter ring seed pre e).2.sites i).worker =
            ((bankWindowRootBefore ring seed pre).2.sites i).worker :=
        congrArg (fun site : RenewalBankSite n => site.worker) hf.2
      have holdWorker :
          ((bankWindowRootBefore ring seed pre).2.sites i).worker =
            .payload p := hworkerFrame.symm.trans hcomp.1
      have holdTok :
          BankTrialLiveComparisonToken
            ((bankWindowRootBefore ring seed pre).1 i).tok := by
        have ht := congrArg
          (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
          hf.1
        rw [← ht]
        exact hcomp.2.2
      have holdComp : BankComparatorOriginWorker ring
          (bankWindowRootBefore ring seed pre) o i p :=
        ⟨holdWorker, hcomp.2.1, holdTok⟩
      have hforbid := (hJ.phaseExcludes o i p holdComp).2.2
      have hmodeOld :
          ((bankWindowRootBefore ring seed pre).1 o.root).mode =
            .IWAIT := by
        rw [hroot]
        exact hm
      exact hforbid hmodeOld

/-- The selected IWAIT/AL return preserves both physical bits and erases the first-digit AL token. Consumer: M2 IWAIT I0 bit/token transport. -/
theorem bankWindowOverlapSourceCountingIwaitAlEndpointReads
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hscope : BankWindowScope ring
      (bankWindowRootBefore ring seed pre) e)
    (hm : ((bankWindowRootBefore ring seed pre).1 e).mode = .IWAIT)
    (ht : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).tok = .AL) :
    ((bankWindowRootAfter ring seed pre e).1 e).bit =
      ((bankWindowRootBefore ring seed pre).1 e).bit ∧
    ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).bit =
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).bit ∧
    ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).tok = .E := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hx :
      ((bankWindowRootBefore ring seed pre).1 e).pack.val = 0 := by
    change ((bankWindowRootBefore ring seed pre).1
      (Counter.site ring e 0)).pack.val = 0
    exact hscope.1 0 (by omega)
  have hy :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val = 1 := by
    change ((bankWindowRootBefore ring seed pre).1
      (Counter.site ring e 1)).pack.val = 1
    exact hscope.1 1 (by omega)
  have hp : packNext 0 1
      (compileAdvice (ceilLogTwo n)).b = 1 := by
    simp [packNext, hb]
  have hbz : (compileAdvice (ceilLogTwo n)).b ≠ 0 := by
    omega
  have hraw :
      (Counter.resetBankOld
        ((bankWindowRootBefore ring seed pre).1 e)
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e))).1.bit =
        ((bankWindowRootBefore ring seed pre).1 e).bit ∧
      (Counter.resetBankOld
        ((bankWindowRootBefore ring seed pre).1 e)
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e))).2.bit =
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).bit ∧
      (Counter.resetBankOld
        ((bankWindowRootBefore ring seed pre).1 e)
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e))).2.tok = .E := by
    simp [Counter.resetBankOld, bankPair, bankCell,
      hx, hy, hscope.2, hm, ht, hp, hbz, hb, isRetTok,
      Id.run_pure, Id.run_bind]
  have htrip := bankWindowClosureSelectedBankTrip ring
    hn hbank (bankWindowRootBefore ring seed pre) e
  have hsrc := congrArg
    (fun t : Mode × Bool × BTok => t.2.1) htrip.1
  have hdst := congrArg
    (fun t : Mode × Bool × BTok => t.2.1) htrip.2
  have htok := congrArg
    (fun t : Mode × Bool × BTok => t.2.2) htrip.2
  change ((bankWindowRootAfter ring seed pre e).1 e).bit =
    (Counter.resetBankOld
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).1.bit at hsrc
  change ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).bit =
    (Counter.resetBankOld
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).2.bit at hdst
  change ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).tok =
    (Counter.resetBankOld
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).2.tok at htok
  exact ⟨hsrc.trans hraw.1,
    hdst.trans hraw.2.1,
    htok.trans hraw.2.2⟩

/-- The source IWAIT/AL return removes the unique AL and preserves the bounded origin binary count by a real bit frame. Consumer: M2 IWAIT I0 armedExact. -/
theorem bankWindowOverlapSourceCountingIwaitAlDigitCredit
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hscope : BankWindowScope ring
      (bankWindowRootBefore ring seed pre) e)
    (hm : ((bankWindowRootBefore ring seed pre).1 e).mode = .IWAIT)
    (hwait :
      ((bankWindowRootBefore ring seed pre).2.sites e).controller =
        .waiting [])
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hw : ((bankWindowRootBefore ring seed pre).2.sites
      (ring.rightNeighbor e)).worker = .payload p)
    (ho : p.origin = some o)
    (hroot : o.root = e)
    (ht : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).tok = .AL) :
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ((bankWindowRootAfter ring seed pre e).1
        (Counter.site ring e (j.val + 1))).tok = .E) ∧
    bankOriginBinaryValue ring
      (bankWindowRootAfter ring seed pre e).1 o =
      bankOriginBinaryValue ring
        (bankWindowRootBefore ring seed pre).1 o ∧
    bankOriginBinaryValue ring
      (bankWindowRootAfter ring seed pre e).1 o ≤
        (compileAdvice (ceilLogTwo n)).K := by
  have hinc := hJ.incrementExact e o
    (ring.rightNeighbor e) p hscope hm hwait hw ho hroot
  have holdOnly := hinc.1
  have hcapOld :
      bankOriginBinaryValue ring
        (bankWindowRootBefore ring seed pre).1 o ≤
          (compileAdvice (ceilLogTwo n)).K := by
    rcases hinc.2 with hir | hal
    · have hbad : BTok.IR = BTok.AL :=
        hir.1.symm.trans ht
      cases hbad
    · exact hal.2.2
  have hreads := bankWindowOverlapSourceCountingIwaitAlEndpointReads
    ring hn hbank seed pre e hscope hm ht
  have hallBits := bankWindowOverlapSelectedBitFrame
    ring (bankWindowRootBefore ring seed pre) e
    hreads.1 hreads.2.1
  have hbits : bankWindowReadDigitBits ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) o.root := by
    intro j
    exact hallBits (Counter.site ring o.root (j.val + 1))
  have hvalue := bankWindowOverlapComparatorBinaryBitTransport
    ring (bankWindowRootBefore ring seed pre)
    (bankWindowRootAfter ring seed pre e) o hbits
  refine ⟨?_, hvalue, ?_⟩
  · intro j
    by_cases hfirst : j.val = 0
    · have hsite : Counter.site ring e (j.val + 1) =
          ring.rightNeighbor e := by
        rw [hfirst]
        rfl
      rw [hsite]
      exact hreads.2.2
    · have hlimit : j.val + 1 ≤
          (compileAdvice (ceilLogTwo n)).b + 1 := by
        have hj := j.isLt
        omega
      have hsrc :
          Counter.site ring e (j.val + 1) ≠ e := by
        have hd := bankWindowIncidenceSiteDistinct
          ring hbank e 0 (j.val + 1)
          (by omega) hlimit
        change e ≠ Counter.site ring e (j.val + 1) at hd
        exact hd.symm
      have hdst :
          Counter.site ring e (j.val + 1) ≠
            ring.rightNeighbor e := by
        have hd := bankWindowIncidenceSiteDistinct
          ring hbank e 1 (j.val + 1)
          (by omega) hlimit
        change ring.rightNeighbor e ≠
          Counter.site ring e (j.val + 1) at hd
        exact hd.symm
      have hf := (bankWindowExactOffPairFrame ring
        (bankWindowRootBefore ring seed pre) e
        (Counter.site ring e (j.val + 1)) hsrc hdst).1
      have htokOld :
          ((bankWindowRootBefore ring seed pre).1
            (Counter.site ring e (j.val + 1))).tok = .E := by
        by_cases he :
            ((bankWindowRootBefore ring seed pre).1
              (Counter.site ring e (j.val + 1))).tok = .E
        · exact he
        · exact False.elim (hdst (holdOnly j he))
      have htokFrame := congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
        hf
      exact htokFrame.trans htokOld
  · rw [hvalue]
    exact hcapOld

/-- Bundle all eleven POST source-counting clauses for IWAIT/AL via the physical, ghost, and token rows. Consumer: R11 M2 SRC in BankWindowOverlapJoint. -/
theorem bankWindowOverlapSourceCountingIwaitAlOwnFields
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hscope : BankWindowScope ring
      (bankWindowRootBefore ring seed pre) e)
    (hm : ((bankWindowRootBefore ring seed pre).1 e).mode = .IWAIT)
    (hwait :
      ((bankWindowRootBefore ring seed pre).2.sites e).controller =
        .waiting [])
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hw : ((bankWindowRootBefore ring seed pre).2.sites
      (ring.rightNeighbor e)).worker = .payload p)
    (ho : p.origin = some o)
    (hroot : o.root = e)
    (ht : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).tok = .AL) :
    bankWindowOverlapSourceCountingOwnFields ring
      (bankWindowRootAfter ring seed pre e) e := by
  obtain ⟨hmodePost, hcompletePost,
    q, hactive, hclear, hqorigin, hqheads, hqatoms⟩ :=
      bankWindowOverlapSourceCountingIwaitAlReturnFields
        ring hn hbank seed pre e hJ hscope hm hwait
        p o hw ho hroot ht
  have hread := bankWindowOverlapSourceCountingIwaitAlDigitCredit
    ring hn hbank seed pre e hJ hscope hm hwait
    p o hw ho hroot ht
  have hno := bankWindowOverlapSourceCountingIwaitNoPostComparator
    ring hn hbank seed pre e hJ hscope hm hclear
  have hpostHeads :
      q.heads = bankOriginBinaryValue ring
        (bankWindowRootAfter ring seed pre e).1 o :=
    hqheads.trans hread.2.1.symm
  exact bankWindowOverlapSourceCountingCstartOwnFieldsFromReturn
    ring (bankWindowRootAfter ring seed pre e) e
    q o hmodePost hactive hqorigin
    hno hread.1 hpostHeads hread.2.2

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

/-- A stable TOP service whose source carries IR executes the
physical top-IR erasure row, not an interior transfer.
Both selected ghost worker slots are erased as well.
Consumer: the remaining M6-T TOP IR branch of BankWindowOverlapJoint. -/
theorem bankWindowOverlapTopGhostStableIrErasure {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (htop : (r.1 e).pack.val = (compileAdvice (ceilLogTwo n)).b)
    (hstable :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
        (r.1 (ring.rightNeighbor e)).pack.val)
    (hir : (r.1 e).tok = .IR) :
    ((renewalBankNext ring r e).1 e).tok = .E ∧
    ((renewalBankNext ring r e).2.sites e).worker = .empty ∧
    ((renewalBankNext ring r e).2.sites
      (ring.rightNeighbor e)).worker = .empty := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hbz : (compileAdvice (ceilLogTwo n)).b ≠ 0 := by omega
  have hraw :
      (Counter.resetBankOld (r.1 e)
        (r.1 (ring.rightNeighbor e))).1.tok = .E := by
    -- The source is nonroot (TOP): only the token rows of `bankPair` run.
    have hxn : (r.1 e).pack.val ≠ 0 := by omega
    unfold Counter.resetBankOld
    rw [L3.bankPair_nonroot _ _ _ _ _ hxn]
    by_cases hyzero :
        (r.1 (ring.rightNeighbor e)).pack.val = 0
    · have hp :
        packNext (compileAdvice (ceilLogTwo n)).b 0
          (compileAdvice (ceilLogTwo n)).b = 0 := by
          simp [packNext]
      by_cases hyt : (r.1 (ring.rightNeighbor e)).tok = .IR <;>
        simp [L3.bankPairNR, bankCell,
          htop, hyzero, hb, hbz, hp, hir, hyt,
          Id.run_pure, Id.run_bind] <;>
        repeat (first | rfl | split)
    · have hp :
        packNext (compileAdvice (ceilLogTwo n)).b
          (r.1 (ring.rightNeighbor e)).pack.val
          (compileAdvice (ceilLogTwo n)).b =
            (compileAdvice (ceilLogTwo n)).b + 1 := by
          simp [packNext, hyzero]
      have hy :
          (r.1 (ring.rightNeighbor e)).pack.val =
            (compileAdvice (ceilLogTwo n)).b + 1 := by
        have hs := hstable
        rw [htop, hp] at hs
        exact hs.symm
      have houtside :
          ¬ (compileAdvice (ceilLogTwo n)).b + 1 ≤
            (compileAdvice (ceilLogTwo n)).b := by omega
      have hnext :
          packNext (compileAdvice (ceilLogTwo n)).b
            ((compileAdvice (ceilLogTwo n)).b + 1)
            (compileAdvice (ceilLogTwo n)).b =
              (compileAdvice (ceilLogTwo n)).b + 1 := by
        simp [packNext]
      have hnextNonzero :
          packNext (compileAdvice (ceilLogTwo n)).b
            ((compileAdvice (ceilLogTwo n)).b + 1)
            (compileAdvice (ceilLogTwo n)).b ≠ 0 := by
        rw [hnext]
        omega
      have hnextOutside :
          (compileAdvice (ceilLogTwo n)).b <
            packNext (compileAdvice (ceilLogTwo n)).b
              ((compileAdvice (ceilLogTwo n)).b + 1)
              (compileAdvice (ceilLogTwo n)).b := by
        rw [hnext]
        omega
      by_cases hyt : (r.1 (ring.rightNeighbor e)).tok = .IR <;>
        simp [L3.bankPairNR, bankCell,
          htop, hy, hbz, hnext, hnextNonzero, hnextOutside,
          houtside, hir, hyt, packNext,
          Id.run_pure, Id.run_bind] <;>
        repeat (first | rfl | split)
  have htrip := (bankWindowClosureSelectedBankTrip
    ring hn hbank r e).1
  have htok := congrArg
    (fun t : Mode × Bool × BTok => t.2.2) htrip
  change ((renewalBankNext ring r e).1 e).tok =
    (Counter.resetBankOld (r.1 e)
      (r.1 (ring.rightNeighbor e))).1.tok at htok
  have hghost := bankWindowOverlapTopGhostStablePairRaw
    (compileAdvice (ceilLogTwo n)) r.2 e
    (ring.rightNeighbor e) (r.1 e)
    (r.1 (ring.rightNeighbor e)) htop hstable
  have hsourceGhost := congrArg
    (fun z : RenewalBankSite n => z.worker)
    (rbReferenceSelectedPairFrame
      ring (by omega : 2 ≤ n) r e).2.2.1
  have htargetGhost := congrArg
    (fun z : RenewalBankSite n => z.worker)
    (rbReferenceSelectedPairFrame
      ring (by omega : 2 ≤ n) r e).2.2.2
  change ((renewalBankNext ring r e).2.sites e).worker =
    (renewalBankPairMemory
      (compileAdvice (ceilLogTwo n)) r.2 e
      (ring.rightNeighbor e) (r.1 e)
      (r.1 (ring.rightNeighbor e))).1.worker at hsourceGhost
  change ((renewalBankNext ring r e).2.sites
    (ring.rightNeighbor e)).worker =
    (renewalBankPairMemory
      (compileAdvice (ceilLogTwo n)) r.2 e
      (ring.rightNeighbor e) (r.1 e)
      (r.1 (ring.rightNeighbor e))).2.worker at htargetGhost
  have hsrc := hsourceGhost.trans hghost.1
  rw [if_pos hir] at hsrc
  exact ⟨htok.trans hraw, hsrc, htargetGhost.trans hghost.2⟩




/-- M6-T TOP IR erasure on the authentic stable edge. The source
IR is retired and its worker erased, with every earlier digit framed.
All thirteen root-indexed J clauses of BankWindowRootFieldsAt hold
without importing the later BankWindowOverlapJoint module.
Consumer: BankWindowOverlapJoint M6-T top-IR branch. -/
theorem bankWindowOverlapTopGhostStableIrRootClauses
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hcompleteOld : Counter.Complete ring
      (bankWindowRootBefore ring seed pre).1 root)
    (htop :
      e = Counter.site ring root
        (compileAdvice (ceilLogTwo n)).b)
    (hstable :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val)
    (hir : ((bankWindowRootBefore ring seed pre).1 e).tok = .IR) :
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    o.root = root → BankComparatorOriginWorker ring (bankWindowRootAfter ring seed pre e) o i p →
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠ .ARMED ∧
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠ .CSTART ∧
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠ .IWAIT) ∧
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    o.root = root → BankComparatorOriginWorker ring (bankWindowRootAfter ring seed pre e) o i p →
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode = .CWAIT →
      Counter.Complete ring (bankWindowRootAfter ring seed pre e).1 o.root) ∧
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    o.root = root → BankComparatorOriginWorker ring (bankWindowRootAfter ring seed pre e) o i p →
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode = .CWAIT →
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        BankTrialLiveComparisonToken
          ((bankWindowRootAfter ring seed pre e).1 (Counter.site ring o.root (j.val + 1))).tok →
        Counter.site ring o.root (j.val + 1) = i) ∧
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    o.root = root → BankComparatorOriginWorker ring (bankWindowRootAfter ring seed pre e) o i p →
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode = .CWAIT →
      (((bankWindowRootAfter ring seed pre e).1 i).tok = .CR1 →
        bankComparatorPrefixMatched ring (bankWindowRootAfter ring seed pre e) o ((bankWindowRootAfter ring seed pre e).1 i).pack.val) ∧
      (((bankWindowRootAfter ring seed pre e).1 i).tok = .CR0 →
        ¬ bankComparatorPrefixMatched ring (bankWindowRootAfter ring seed pre e) o ((bankWindowRootAfter ring seed pre e).1 i).pack.val) ∧
      (((bankWindowRootAfter ring seed pre e).1 i).tok = .CL1 →
        bankComparatorPrefixMatched ring (bankWindowRootAfter ring seed pre e) o
          (compileAdvice (ceilLogTwo n)).b) ∧
      (((bankWindowRootAfter ring seed pre e).1 i).tok = .CL0 →
        ¬ bankComparatorPrefixMatched ring (bankWindowRootAfter ring seed pre e) o
          (compileAdvice (ceilLogTwo n)).b)) ∧
  (BankWindowScope ring (bankWindowRootAfter ring seed pre e) root →
    BankWindowInheritedController (bankWindowRootAfter ring seed pre e) root →
    ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ¬ BankWindowTainted (bankWindowRootAfter ring seed pre e) (Counter.site ring root (j.val + 1))) ∧
  (BankWindowScope ring (bankWindowRootAfter ring seed pre e) root →
    ((bankWindowRootAfter ring seed pre e).1 root).mode = .RWAIT →
    ((bankWindowRootAfter ring seed pre e).2.sites root).controller = .waiting [] →
    ∃ (j : Fin (compileAdvice (ceilLogTwo n)).b)
      (rho : RenewalBankReceipt n),
      ((bankWindowRootAfter ring seed pre e).2.sites (Counter.site ring root (j.val + 1))).worker =
        .pending rho ∧
      (((bankWindowRootAfter ring seed pre e).1 (Counter.site ring root (j.val + 1))).tok = .RR ∨
       ((bankWindowRootAfter ring seed pre e).1 (Counter.site ring root (j.val + 1))).tok = .RL) ∧
      bankWindowZeroPrefix ring (bankWindowRootAfter ring seed pre e) root (j.val + 1) ∧
      (∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
        k.val < j.val →
        ((bankWindowRootAfter ring seed pre e).1 (Counter.site ring root (k.val + 1))).tok = .E) ∧
      (((bankWindowRootAfter ring seed pre e).1 (Counter.site ring root (j.val + 1))).tok = .RL →
        bankWindowOnlyToken ring (bankWindowRootAfter ring seed pre e) root
          (Counter.site ring root (j.val + 1)) ∧
        bankWindowZeroPrefix ring (bankWindowRootAfter ring seed pre e) root
          (compileAdvice (ceilLogTwo n)).b)) ∧
  (∀ (o : RenewalBankOrigin n) (p : RenewalBankPayload n),
    BankWindowScope ring (bankWindowRootAfter ring seed pre e) root →
    (((bankWindowRootAfter ring seed pre e).1 root).mode = .ARMED ∨ ((bankWindowRootAfter ring seed pre e).1 root).mode = .CSTART) →
    ((bankWindowRootAfter ring seed pre e).2.sites root).controller = .active p →
    p.origin = some o →
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ((bankWindowRootAfter ring seed pre e).1 (Counter.site ring root (j.val + 1))).tok = .E) ∧
    p.heads = bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o ∧
    (((bankWindowRootAfter ring seed pre e).1 root).mode = .ARMED →
      bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o <
        (compileAdvice (ceilLogTwo n)).K) ∧
    (((bankWindowRootAfter ring seed pre e).1 root).mode = .CSTART →
      bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o ≤
        (compileAdvice (ceilLogTwo n)).K)) ∧
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    BankWindowScope ring (bankWindowRootAfter ring seed pre e) root →
    ((bankWindowRootAfter ring seed pre e).1 root).mode = .IWAIT →
    ((bankWindowRootAfter ring seed pre e).2.sites root).controller = .waiting [] →
    ((bankWindowRootAfter ring seed pre e).2.sites i).worker = .payload p →
    p.origin = some o → o.root = root →
    bankWindowOnlyToken ring (bankWindowRootAfter ring seed pre e) root i ∧
    ((((bankWindowRootAfter ring seed pre e).1 i).tok = .IR ∧
        bankWindowZeroPrefix ring (bankWindowRootAfter ring seed pre e) root ((bankWindowRootAfter ring seed pre e).1 i).pack.val ∧
        p.heads = bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o +
          2 ^ ((bankWindowRootAfter ring seed pre e).1 i).pack.val ∧
        bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o +
          2 ^ ((bankWindowRootAfter ring seed pre e).1 i).pack.val ≤
            (compileAdvice (ceilLogTwo n)).K) ∨
     (((bankWindowRootAfter ring seed pre e).1 i).tok = .AL ∧
        p.heads = bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o ∧
        bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o ≤
          (compileAdvice (ceilLogTwo n)).K))) ∧
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    o.root = root →
    ((bankWindowRootAfter ring seed pre e).2.sites i).worker = .payload p →
    p.origin = some o →
    ((bankWindowRootAfter ring seed pre e).1 o.root).mode = .CWAIT →
    ((bankWindowRootAfter ring seed pre e).2.sites o.root).controller = .waiting [] →
    bankWindowOnlyToken ring (bankWindowRootAfter ring seed pre e) o.root i ∧
    BankTrialLiveComparisonToken ((bankWindowRootAfter ring seed pre e).1 i).tok ∧
    p.heads = bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o ∧
    bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o ≤
      (compileAdvice (ceilLogTwo n)).K) ∧
  (BankWindowScope ring (bankWindowRootAfter ring seed pre e) root →
    ((bankWindowRootAfter ring seed pre e).1 root).mode = .IWAIT →
    ((bankWindowRootAfter ring seed pre e).2.sites root).controller = .waiting [] →
    ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowTainted (bankWindowRootAfter ring seed pre e) (Counter.site ring root (j.val + 1)) →
      ∃ (o : RenewalBankOrigin n) (p : RenewalBankPayload n),
        ((bankWindowRootAfter ring seed pre e).2.sites (Counter.site ring root (j.val + 1))).worker =
          .payload p ∧ p.origin = some o ∧
        o.root = root ∧
        bankWindowOnlyToken ring (bankWindowRootAfter ring seed pre e) root
          (Counter.site ring root (j.val + 1))) ∧
  (BankWindowScope ring (bankWindowRootAfter ring seed pre e) root →
    ((bankWindowRootAfter ring seed pre e).1 root).mode = .CWAIT →
    ((bankWindowRootAfter ring seed pre e).2.sites root).controller = .waiting [] →
    ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowTainted (bankWindowRootAfter ring seed pre e) (Counter.site ring root (j.val + 1)) →
      ∃ (o : RenewalBankOrigin n) (p : RenewalBankPayload n),
        ((bankWindowRootAfter ring seed pre e).2.sites (Counter.site ring root (j.val + 1))).worker =
          .payload p ∧ p.origin = some o ∧
        o.root = root ∧
        BankTrialLiveComparisonToken
          ((bankWindowRootAfter ring seed pre e).1 (Counter.site ring root (j.val + 1))).tok ∧
        bankWindowOnlyToken ring (bankWindowRootAfter ring seed pre e) root
          (Counter.site ring root (j.val + 1))) ∧
  (∀ limit : Nat, BankWindowProtoRun ring (bankWindowRootAfter ring seed pre e) root limit →
    BankWindowRootForeignProtoField ring (bankWindowRootAfter ring seed pre e) root limit) ∧
  (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
    BankWindowOrphanOwner ring (bankWindowRootAfter ring seed pre e) root j →
    BankWindowTainted (bankWindowRootAfter ring seed pre e) (Counter.site ring root (j.val + 1)) →
    ((bankWindowRootAfter ring seed pre e).1 root).mode = .RESET ∨
      (((bankWindowRootAfter ring seed pre e).1 root).mode = .RWAIT ∧
        ((bankWindowRootAfter ring seed pre e).2.sites root).controller = .waiting [])) := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hb0 : (compileAdvice (ceilLogTwo n)).b ≠ 0 := by omega
  have htopRole :
      ((bankWindowRootBefore ring seed pre).1 e).pack.val =
        (compileAdvice (ceilLogTwo n)).b := by
    rw [htop]
    exact hcompleteOld _ (Nat.le_refl _)
  have hrow := bankWindowOverlapTopGhostStableIrErasure
    ring hn hbank (bankWindowRootBefore ring seed pre) e
    htopRole hstable hir
  have hstablePack := bankWindowOverlapStablePackFrame
    ring hn seed pre e hstable
  have hcompletePost : Counter.Complete ring
      (bankWindowRootAfter ring seed pre e).1 root := by
    intro k hk
    exact (hstablePack (Counter.site ring root k)).trans
      (hcompleteOld k hk)
  have hearlier :
      ∀ t : Nat, t < (compileAdvice (ceilLogTwo n)).b →
        (bankWindowRootAfter ring seed pre e).1
          (Counter.site ring root t) =
            (bankWindowRootBefore ring seed pre).1
              (Counter.site ring root t) ∧
        (bankWindowRootAfter ring seed pre e).2.sites
          (Counter.site ring root t) =
            (bankWindowRootBefore ring seed pre).2.sites
              (Counter.site ring root t) := by
    intro t ht
    exact bankWindowOverlapRepairEarlierSiteFrame ring hbank
      (bankWindowRootBefore ring seed pre) e root
      (compileAdvice (ceilLogTwo n)).b t
      htop (Nat.le_refl _) ht
  have hrootFrame := hearlier 0 hb
  have hpack : bankWindowReadPackPrefix ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) root
      (compileAdvice (ceilLogTwo n)).b := by
    intro k hk
    exact hstablePack (Counter.site ring root k)
  have hgrant : bankWindowReadGrant
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) root :=
    congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.grant)
      hrootFrame.1
  have hmode : bankWindowReadMode
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) root :=
    congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.mode)
      hrootFrame.1
  have hcontroller : bankWindowReadController
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) root :=
    congrArg (fun a : RenewalBankSite n => a.controller)
      hrootFrame.2
  have hscopeBackward :
      BankWindowScope ring (bankWindowRootAfter ring seed pre e) root →
      BankWindowScope ring (bankWindowRootBefore ring seed pre) root := by
    intro hs
    exact ⟨hcompleteOld, hgrant.symm.trans hs.2⟩
  have htopDigit :
      Counter.site ring root
        ((⟨(compileAdvice (ceilLogTwo n)).b - 1,
          (show (compileAdvice (ceilLogTwo n)).b - 1 <
            (compileAdvice (ceilLogTwo n)).b by omega)⟩ :
          Fin (compileAdvice (ceilLogTwo n)).b).val + 1) = e := by
    change Counter.site ring root
      ((compileAdvice (ceilLogTwo n)).b - 1 + 1) = e
    rw [show (compileAdvice (ceilLogTwo n)).b - 1 + 1 =
      (compileAdvice (ceilLogTwo n)).b by omega]
    exact htop.symm
  have htopNotEmpty :
      ((bankWindowRootBefore ring seed pre).1 e).tok ≠ .E := by
    intro he
    rw [hir] at he
    cases he
  have hforceTop :
      ∀ i : Fin n,
        bankWindowOnlyToken ring (bankWindowRootBefore ring seed pre)
          root i → i = e := by
    intro i honly
    have hne :
        ((bankWindowRootBefore ring seed pre).1
          (Counter.site ring root
            ((⟨(compileAdvice (ceilLogTwo n)).b - 1,
              (show (compileAdvice (ceilLogTwo n)).b - 1 <
                (compileAdvice (ceilLogTwo n)).b by omega)⟩ :
              Fin (compileAdvice (ceilLogTwo n)).b).val + 1))).tok ≠
          .E := by
      rw [htopDigit]
      exact htopNotEmpty
    have hh := honly
      (⟨(compileAdvice (ceilLogTwo n)).b - 1,
        (show (compileAdvice (ceilLogTwo n)).b - 1 <
          (compileAdvice (ceilLogTwo n)).b by omega)⟩ :
        Fin (compileAdvice (ceilLogTwo n)).b) hne
    exact (htopDigit.symm.trans hh).symm
  have hnoTopTaint :
      ¬ BankWindowTainted (bankWindowRootAfter ring seed pre e) e := by
    intro ht
    rcases ht with ⟨rho, hw⟩ | ⟨p, o, hw, ho⟩
    · rw [hrow.2.1] at hw
      cases hw
    · rw [hrow.2.1] at hw
      cases hw
  have hbitRaw :
      (Counter.resetBankOld
        ((bankWindowRootBefore ring seed pre).1 e)
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e))).1.bit =
            ((bankWindowRootBefore ring seed pre).1 e).bit := by
    by_cases hyzero :
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val = 0
    · have hp :
          packNext (compileAdvice (ceilLogTwo n)).b 0
            (compileAdvice (ceilLogTwo n)).b = 0 := by
        simp [packNext]
      by_cases hyt :
          ((bankWindowRootBefore ring seed pre).1
            (ring.rightNeighbor e)).tok = .IR <;>
        simp [Counter.resetBankOld, bankPair, bankCell,
          htopRole, hyzero, hb, hb0, hp, hir, hyt, packNext,
          Id.run_pure, Id.run_bind] <;>
        repeat (first | rfl | split)
    · have hp :
          packNext (compileAdvice (ceilLogTwo n)).b
            ((bankWindowRootBefore ring seed pre).1
              (ring.rightNeighbor e)).pack.val
            (compileAdvice (ceilLogTwo n)).b =
              (compileAdvice (ceilLogTwo n)).b + 1 := by
        simp [packNext, hyzero]
      have hy :
          ((bankWindowRootBefore ring seed pre).1
            (ring.rightNeighbor e)).pack.val =
              (compileAdvice (ceilLogTwo n)).b + 1 := by
        have hs := hstable
        rw [htopRole, hp] at hs
        exact hs.symm
      have hnext :
          packNext (compileAdvice (ceilLogTwo n)).b
            ((compileAdvice (ceilLogTwo n)).b + 1)
            (compileAdvice (ceilLogTwo n)).b =
              (compileAdvice (ceilLogTwo n)).b + 1 := by
        simp [packNext]
      have houtside :
          (compileAdvice (ceilLogTwo n)).b <
            packNext (compileAdvice (ceilLogTwo n)).b
              ((compileAdvice (ceilLogTwo n)).b + 1)
              (compileAdvice (ceilLogTwo n)).b := by
        rw [hnext]
        omega
      by_cases hyt :
          ((bankWindowRootBefore ring seed pre).1
            (ring.rightNeighbor e)).tok = .IR <;>
        simp [Counter.resetBankOld, bankPair, bankCell,
          htopRole, hy, hnext, houtside, hb0, hir, hyt, packNext,
          Id.run_pure, Id.run_bind] <;>
        repeat (first | rfl | split)
  have htrip := (bankWindowClosureSelectedBankTrip
    ring hn hbank (bankWindowRootBefore ring seed pre) e).1
  have hselectedBit := congrArg
    (fun t : Mode × Bool × BTok => t.2.1) htrip
  change ((bankWindowRootAfter ring seed pre e).1 e).bit =
    (Counter.resetBankOld
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).1.bit at hselectedBit
  have hbitTop := hselectedBit.trans hbitRaw
  have hbits : bankWindowReadDigitBits ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) root := by
    intro j
    by_cases hlt :
        j.val + 1 < (compileAdvice (ceilLogTwo n)).b
    · exact congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.bit)
        (hearlier (j.val + 1) hlt).1
    · have heq :
          j.val + 1 = (compileAdvice (ceilLogTwo n)).b := by
        have hj := j.isLt
        omega
      rw [heq, ← htop]
      exact hbitTop
  have hworkerReads :
      ∀ (i : Fin n) (p : RenewalBankPayload n),
        ((bankWindowRootAfter ring seed pre e).2.sites i).worker =
          .payload p →
        bankWindowReadTok
          (bankWindowRootBefore ring seed pre)
          (bankWindowRootAfter ring seed pre e) i ∧
        bankWindowReadPack
          (bankWindowRootBefore ring seed pre)
          (bankWindowRootAfter ring seed pre e) i ∧
        bankWindowReadWorker
          (bankWindowRootBefore ring seed pre)
          (bankWindowRootAfter ring seed pre e) i := by
    intro i p hw
    by_cases hsource : i = e
    · have hbad := hw
      rw [hsource, hrow.2.1] at hbad
      cases hbad
    · by_cases htarget : i = ring.rightNeighbor e
      · have hbad := hw
        rw [htarget, hrow.2.2] at hbad
        cases hbad
      · have hf := bankWindowExactOffPairAtomicReads ring
          (bankWindowRootBefore ring seed pre) e i
          hsource htarget
        exact ⟨hf.2.2.1, hf.1, hf.2.2.2.2.2.1⟩
  have htaintBackward :
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        BankWindowTainted (bankWindowRootAfter ring seed pre e)
          (Counter.site ring root (j.val + 1)) →
        BankWindowTainted (bankWindowRootBefore ring seed pre)
          (Counter.site ring root (j.val + 1)) := by
    intro j ht
    by_cases hlt :
        j.val + 1 < (compileAdvice (ceilLogTwo n)).b
    · have hf := congrArg
        (fun a : RenewalBankSite n => a.worker)
        (hearlier (j.val + 1) hlt).2
      rcases ht with ⟨rho, hw⟩ | ⟨p, o, hw, ho⟩
      · exact Or.inl ⟨rho, hf.symm.trans hw⟩
      · exact Or.inr ⟨p, o, hf.symm.trans hw, ho⟩
    · have heq :
          j.val + 1 = (compileAdvice (ceilLogTwo n)).b := by
        have hj := j.isLt
        omega
      have hsite : Counter.site ring root (j.val + 1) = e := by
        rw [heq]
        exact htop.symm
      rw [hsite] at ht
      exact False.elim (hnoTopTaint ht)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o i p horoot hcomp
    have hi := hworkerReads i p hcomp.1
    have hm : bankWindowReadMode
        (bankWindowRootBefore ring seed pre)
        (bankWindowRootAfter ring seed pre e) o.root := by
      rw [horoot]
      exact hmode
    exact bankWindowPhaseExcludesReadTransport ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e)
      o i p hJ ⟨hi.1, hi.2.2, hm⟩ hcomp
  · intro o i p horoot hcomp hphase
    rw [horoot]
    exact hcompletePost
  · intro o i p horoot hcomp hphase j htoken
    have hi := hworkerReads i p hcomp.1
    have hcompOld : BankComparatorOriginWorker ring
        (bankWindowRootBefore ring seed pre) o i p := by
      have hlive := hcomp.2.2
      rw [hi.1] at hlive
      exact ⟨hi.2.2.symm.trans hcomp.1, hcomp.2.1, hlive⟩
    have hmodeOld :
        ((bankWindowRootBefore ring seed pre).1 o.root).mode =
          .CWAIT := by
      have hpostAtRoot := hphase
      rw [horoot] at hpostAtRoot
      rw [horoot]
      exact hmode.symm.trans hpostAtRoot
    by_cases hlt :
        j.val + 1 < (compileAdvice (ceilLogTwo n)).b
    · have htokEq := congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
        (hearlier (j.val + 1) hlt).1
      have htOld :
          BankTrialLiveComparisonToken
            ((bankWindowRootBefore ring seed pre).1
              (Counter.site ring o.root (j.val + 1))).tok := by
        rw [horoot]
        have ht := htoken
        rw [horoot] at ht
        rw [htokEq] at ht
        exact ht
      exact hJ.phaseUnique o i p hcompOld hmodeOld j htOld
    · have heq :
          j.val + 1 = (compileAdvice (ceilLogTwo n)).b := by
        have hj := j.isLt
        omega
      have hsite :
          Counter.site ring o.root (j.val + 1) = e := by
        rw [horoot, heq]
        exact htop.symm
      rw [hsite, hrow.1] at htoken
      simp [BankTrialLiveComparisonToken] at htoken
  · intro o i p horoot hcomp hphase
    have hi := hworkerReads i p hcomp.1
    have hm : bankWindowReadMode
        (bankWindowRootBefore ring seed pre)
        (bankWindowRootAfter ring seed pre e) o.root := by
      rw [horoot]
      exact hmode
    have hbitReads : bankWindowReadDigitBits ring
        (bankWindowRootBefore ring seed pre)
        (bankWindowRootAfter ring seed pre e) o.root := by
      rw [horoot]
      exact hbits
    exact bankWindowPhaseFlagsReadTransport ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e)
      o i p hJ ⟨⟨hi.1, hi.2.2, hm⟩,
        hi.2.1, hbitReads⟩ hcomp hphase
  · intro hs hi j ht
    have hiOld : BankWindowInheritedController
        (bankWindowRootBefore ring seed pre) root := by
      rcases hi with ⟨atoms, hc, hne⟩ | ⟨p, hc, horigin⟩
      · exact Or.inl ⟨atoms, hcontroller.symm.trans hc, hne⟩
      · exact Or.inr ⟨p, hcontroller.symm.trans hc, horigin⟩
    exact hJ.inheritedClean root (hscopeBackward hs)
      hiOld j (htaintBackward j ht)
  · intro hs hwait hctl
    have hmodeOld :
        ((bankWindowRootBefore ring seed pre).1 root).mode =
          .RWAIT := hmode.symm.trans hwait
    have hctlOld :
        ((bankWindowRootBefore ring seed pre).2.sites
          root).controller = .waiting [] :=
      hcontroller.symm.trans hctl
    obtain ⟨j, rho, hwOld, htOld, hzOld, heOld, hrlOld⟩ :=
      hJ.resetWait root (hscopeBackward hs) hmodeOld hctlOld
    have hfrontBelow :
        j.val + 1 < (compileAdvice (ceilLogTwo n)).b := by
      by_cases heq :
          j.val + 1 = (compileAdvice (ceilLogTwo n)).b
      · have hsite :
            Counter.site ring root (j.val + 1) = e := by
          rw [heq]
          exact htop.symm
        rw [hsite, hir] at htOld
        rcases htOld with hr | hl
        · cases hr
        · cases hl
      · have hj := j.isLt
        omega
    have hf := hearlier (j.val + 1) hfrontBelow
    have hwEq := congrArg
      (fun a : RenewalBankSite n => a.worker) hf.2
    have htEq := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
      hf.1
    refine ⟨j, rho, hwEq.trans hwOld, ?_, ?_, ?_, ?_⟩
    · rcases htOld with hr | hl
      · exact Or.inl (htEq.trans hr)
      · exact Or.inr (htEq.trans hl)
    · intro k hk
      exact (hbits k).trans (hzOld k hk)
    · intro k hk
      have hlt :
          k.val + 1 < (compileAdvice (ceilLogTwo n)).b := by
        have hj := j.isLt
        omega
      have htk := congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
        (hearlier (k.val + 1) hlt).1
      exact htk.trans (heOld k hk)
    · intro hrlPost
      have hrlBefore :
          ((bankWindowRootBefore ring seed pre).1
            (Counter.site ring root (j.val + 1))).tok = .RL :=
        htEq.symm.trans hrlPost
      have hlast := hforceTop _ (hrlOld hrlBefore).1
      rw [hlast, hir] at hrlBefore
      cases hrlBefore
  · intro o p hs hphase hactive horigin
    have hphaseOld :
        ((bankWindowRootBefore ring seed pre).1 root).mode =
          .ARMED ∨
        ((bankWindowRootBefore ring seed pre).1 root).mode =
          .CSTART := by
      rcases hphase with ha | hc
      · exact Or.inl (hmode.symm.trans ha)
      · exact Or.inr (hmode.symm.trans hc)
    have hactiveOld :
        ((bankWindowRootBefore ring seed pre).2.sites
          root).controller = .active p :=
      hcontroller.symm.trans hactive
    have hclean := (hJ.armedExact root o p
      (hscopeBackward hs) hphaseOld hactiveOld horigin).1
    have htOld := hclean
      (⟨(compileAdvice (ceilLogTwo n)).b - 1,
        (show (compileAdvice (ceilLogTwo n)).b - 1 <
          (compileAdvice (ceilLogTwo n)).b by omega)⟩ :
        Fin (compileAdvice (ceilLogTwo n)).b)
    rw [htopDigit, hir] at htOld
    cases htOld
  · intro o i p hs hphase hctl hw ho horoot
    have hi := hworkerReads i p hw
    have hmodeOld :
        ((bankWindowRootBefore ring seed pre).1 root).mode =
          .IWAIT := hmode.symm.trans hphase
    have hctlOld :
        ((bankWindowRootBefore ring seed pre).2.sites
          root).controller = .waiting [] :=
      hcontroller.symm.trans hctl
    have honly := (hJ.incrementExact root o i p
      (hscopeBackward hs) hmodeOld hctlOld
      (hi.2.2.symm.trans hw) ho horoot).1
    have hsite := hforceTop i honly
    rw [hsite, hrow.2.1] at hw
    cases hw
  · intro o i p horoot hw ho hphase hctl
    have hi := hworkerReads i p hw
    have hmodeOld :
        ((bankWindowRootBefore ring seed pre).1 o.root).mode =
          .CWAIT := by
      have hpostAtRoot := hphase
      rw [horoot] at hpostAtRoot
      rw [horoot]
      exact hmode.symm.trans hpostAtRoot
    have hctlOld :
        ((bankWindowRootBefore ring seed pre).2.sites
          o.root).controller = .waiting [] := by
      have hpostAtRoot := hctl
      rw [horoot] at hpostAtRoot
      rw [horoot]
      exact hcontroller.symm.trans hpostAtRoot
    have honly := (hJ.compareExact o i p
      (hi.2.2.symm.trans hw) ho hmodeOld hctlOld).1
    rw [horoot] at honly
    have hsite := hforceTop i honly
    rw [hsite, hrow.2.1] at hw
    cases hw
  · intro hs hphase hctl j ht
    have hmodeOld :
        ((bankWindowRootBefore ring seed pre).1 root).mode =
          .IWAIT := hmode.symm.trans hphase
    have hctlOld :
        ((bankWindowRootBefore ring seed pre).2.sites
          root).controller = .waiting [] :=
      hcontroller.symm.trans hctl
    obtain ⟨o, p, hw, ho, horoot, honly⟩ :=
      hJ.iwaitTaintedUnique root (hscopeBackward hs)
        hmodeOld hctlOld j (htaintBackward j ht)
    have hsite := hforceTop _ honly
    rw [hsite] at ht
    exact False.elim (hnoTopTaint ht)
  · intro hs hphase hctl j ht
    have hmodeOld :
        ((bankWindowRootBefore ring seed pre).1 root).mode =
          .CWAIT := hmode.symm.trans hphase
    have hctlOld :
        ((bankWindowRootBefore ring seed pre).2.sites
          root).controller = .waiting [] :=
      hcontroller.symm.trans hctl
    obtain ⟨o, p, hw, ho, horoot, hlive, honly⟩ :=
      hJ.cwaitTaintedUnique root (hscopeBackward hs)
        hmodeOld hctlOld j (htaintBackward j ht)
    have hsite := hforceTop _ honly
    rw [hsite] at ht
    exact False.elim (hnoTopTaint ht)
  · intro limit hproto
    have hwrong := hproto.2.2
    exact False.elim (hwrong
      (hcompletePost (limit + 1)
        (by have hl := hproto.1; omega)))
  · intro j howner htainted
    exact False.elim (howner.2.2
      (by
        intro k hk
        exact hcompletePost k
          (by have hj := j.isLt; omega)))

/-- M6-T TOP root: exhaustive split on the actual source token.
The IR row uses token/worker erasure; every other token uses the
previously merged full read transport.
Consumer: BankWindowOverlapJoint M6-T TOP dispatch. -/
theorem bankWindowOverlapTopGhostStableRootClauses
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hcompleteOld : Counter.Complete ring
      (bankWindowRootBefore ring seed pre).1 root)
    (htop :
      e = Counter.site ring root
        (compileAdvice (ceilLogTwo n)).b)
    (hstable :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val) :
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    o.root = root → BankComparatorOriginWorker ring (bankWindowRootAfter ring seed pre e) o i p →
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠ .ARMED ∧
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠ .CSTART ∧
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode ≠ .IWAIT) ∧
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    o.root = root → BankComparatorOriginWorker ring (bankWindowRootAfter ring seed pre e) o i p →
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode = .CWAIT →
      Counter.Complete ring (bankWindowRootAfter ring seed pre e).1 o.root) ∧
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    o.root = root → BankComparatorOriginWorker ring (bankWindowRootAfter ring seed pre e) o i p →
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode = .CWAIT →
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        BankTrialLiveComparisonToken
          ((bankWindowRootAfter ring seed pre e).1 (Counter.site ring o.root (j.val + 1))).tok →
        Counter.site ring o.root (j.val + 1) = i) ∧
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    o.root = root → BankComparatorOriginWorker ring (bankWindowRootAfter ring seed pre e) o i p →
      ((bankWindowRootAfter ring seed pre e).1 o.root).mode = .CWAIT →
      (((bankWindowRootAfter ring seed pre e).1 i).tok = .CR1 →
        bankComparatorPrefixMatched ring (bankWindowRootAfter ring seed pre e) o ((bankWindowRootAfter ring seed pre e).1 i).pack.val) ∧
      (((bankWindowRootAfter ring seed pre e).1 i).tok = .CR0 →
        ¬ bankComparatorPrefixMatched ring (bankWindowRootAfter ring seed pre e) o ((bankWindowRootAfter ring seed pre e).1 i).pack.val) ∧
      (((bankWindowRootAfter ring seed pre e).1 i).tok = .CL1 →
        bankComparatorPrefixMatched ring (bankWindowRootAfter ring seed pre e) o
          (compileAdvice (ceilLogTwo n)).b) ∧
      (((bankWindowRootAfter ring seed pre e).1 i).tok = .CL0 →
        ¬ bankComparatorPrefixMatched ring (bankWindowRootAfter ring seed pre e) o
          (compileAdvice (ceilLogTwo n)).b)) ∧
  (BankWindowScope ring (bankWindowRootAfter ring seed pre e) root →
    BankWindowInheritedController (bankWindowRootAfter ring seed pre e) root →
    ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ¬ BankWindowTainted (bankWindowRootAfter ring seed pre e) (Counter.site ring root (j.val + 1))) ∧
  (BankWindowScope ring (bankWindowRootAfter ring seed pre e) root →
    ((bankWindowRootAfter ring seed pre e).1 root).mode = .RWAIT →
    ((bankWindowRootAfter ring seed pre e).2.sites root).controller = .waiting [] →
    ∃ (j : Fin (compileAdvice (ceilLogTwo n)).b)
      (rho : RenewalBankReceipt n),
      ((bankWindowRootAfter ring seed pre e).2.sites (Counter.site ring root (j.val + 1))).worker =
        .pending rho ∧
      (((bankWindowRootAfter ring seed pre e).1 (Counter.site ring root (j.val + 1))).tok = .RR ∨
       ((bankWindowRootAfter ring seed pre e).1 (Counter.site ring root (j.val + 1))).tok = .RL) ∧
      bankWindowZeroPrefix ring (bankWindowRootAfter ring seed pre e) root (j.val + 1) ∧
      (∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
        k.val < j.val →
        ((bankWindowRootAfter ring seed pre e).1 (Counter.site ring root (k.val + 1))).tok = .E) ∧
      (((bankWindowRootAfter ring seed pre e).1 (Counter.site ring root (j.val + 1))).tok = .RL →
        bankWindowOnlyToken ring (bankWindowRootAfter ring seed pre e) root
          (Counter.site ring root (j.val + 1)) ∧
        bankWindowZeroPrefix ring (bankWindowRootAfter ring seed pre e) root
          (compileAdvice (ceilLogTwo n)).b)) ∧
  (∀ (o : RenewalBankOrigin n) (p : RenewalBankPayload n),
    BankWindowScope ring (bankWindowRootAfter ring seed pre e) root →
    (((bankWindowRootAfter ring seed pre e).1 root).mode = .ARMED ∨ ((bankWindowRootAfter ring seed pre e).1 root).mode = .CSTART) →
    ((bankWindowRootAfter ring seed pre e).2.sites root).controller = .active p →
    p.origin = some o →
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ((bankWindowRootAfter ring seed pre e).1 (Counter.site ring root (j.val + 1))).tok = .E) ∧
    p.heads = bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o ∧
    (((bankWindowRootAfter ring seed pre e).1 root).mode = .ARMED →
      bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o <
        (compileAdvice (ceilLogTwo n)).K) ∧
    (((bankWindowRootAfter ring seed pre e).1 root).mode = .CSTART →
      bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o ≤
        (compileAdvice (ceilLogTwo n)).K)) ∧
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    BankWindowScope ring (bankWindowRootAfter ring seed pre e) root →
    ((bankWindowRootAfter ring seed pre e).1 root).mode = .IWAIT →
    ((bankWindowRootAfter ring seed pre e).2.sites root).controller = .waiting [] →
    ((bankWindowRootAfter ring seed pre e).2.sites i).worker = .payload p →
    p.origin = some o → o.root = root →
    bankWindowOnlyToken ring (bankWindowRootAfter ring seed pre e) root i ∧
    ((((bankWindowRootAfter ring seed pre e).1 i).tok = .IR ∧
        bankWindowZeroPrefix ring (bankWindowRootAfter ring seed pre e) root ((bankWindowRootAfter ring seed pre e).1 i).pack.val ∧
        p.heads = bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o +
          2 ^ ((bankWindowRootAfter ring seed pre e).1 i).pack.val ∧
        bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o +
          2 ^ ((bankWindowRootAfter ring seed pre e).1 i).pack.val ≤
            (compileAdvice (ceilLogTwo n)).K) ∨
     (((bankWindowRootAfter ring seed pre e).1 i).tok = .AL ∧
        p.heads = bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o ∧
        bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o ≤
          (compileAdvice (ceilLogTwo n)).K))) ∧
  (∀ (o : RenewalBankOrigin n) (i : Fin n) (p : RenewalBankPayload n),
    o.root = root →
    ((bankWindowRootAfter ring seed pre e).2.sites i).worker = .payload p →
    p.origin = some o →
    ((bankWindowRootAfter ring seed pre e).1 o.root).mode = .CWAIT →
    ((bankWindowRootAfter ring seed pre e).2.sites o.root).controller = .waiting [] →
    bankWindowOnlyToken ring (bankWindowRootAfter ring seed pre e) o.root i ∧
    BankTrialLiveComparisonToken ((bankWindowRootAfter ring seed pre e).1 i).tok ∧
    p.heads = bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o ∧
    bankOriginBinaryValue ring (bankWindowRootAfter ring seed pre e).1 o ≤
      (compileAdvice (ceilLogTwo n)).K) ∧
  (BankWindowScope ring (bankWindowRootAfter ring seed pre e) root →
    ((bankWindowRootAfter ring seed pre e).1 root).mode = .IWAIT →
    ((bankWindowRootAfter ring seed pre e).2.sites root).controller = .waiting [] →
    ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowTainted (bankWindowRootAfter ring seed pre e) (Counter.site ring root (j.val + 1)) →
      ∃ (o : RenewalBankOrigin n) (p : RenewalBankPayload n),
        ((bankWindowRootAfter ring seed pre e).2.sites (Counter.site ring root (j.val + 1))).worker =
          .payload p ∧ p.origin = some o ∧
        o.root = root ∧
        bankWindowOnlyToken ring (bankWindowRootAfter ring seed pre e) root
          (Counter.site ring root (j.val + 1))) ∧
  (BankWindowScope ring (bankWindowRootAfter ring seed pre e) root →
    ((bankWindowRootAfter ring seed pre e).1 root).mode = .CWAIT →
    ((bankWindowRootAfter ring seed pre e).2.sites root).controller = .waiting [] →
    ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowTainted (bankWindowRootAfter ring seed pre e) (Counter.site ring root (j.val + 1)) →
      ∃ (o : RenewalBankOrigin n) (p : RenewalBankPayload n),
        ((bankWindowRootAfter ring seed pre e).2.sites (Counter.site ring root (j.val + 1))).worker =
          .payload p ∧ p.origin = some o ∧
        o.root = root ∧
        BankTrialLiveComparisonToken
          ((bankWindowRootAfter ring seed pre e).1 (Counter.site ring root (j.val + 1))).tok ∧
        bankWindowOnlyToken ring (bankWindowRootAfter ring seed pre e) root
          (Counter.site ring root (j.val + 1))) ∧
  (∀ limit : Nat, BankWindowProtoRun ring (bankWindowRootAfter ring seed pre e) root limit →
    BankWindowRootForeignProtoField ring (bankWindowRootAfter ring seed pre e) root limit) ∧
  (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
    BankWindowOrphanOwner ring (bankWindowRootAfter ring seed pre e) root j →
    BankWindowTainted (bankWindowRootAfter ring seed pre e) (Counter.site ring root (j.val + 1)) →
    ((bankWindowRootAfter ring seed pre e).1 root).mode = .RESET ∨
      (((bankWindowRootAfter ring seed pre e).1 root).mode = .RWAIT ∧
        ((bankWindowRootAfter ring seed pre e).2.sites root).controller = .waiting [])) := by
  by_cases hir :
      ((bankWindowRootBefore ring seed pre).1 e).tok = .IR
  · exact bankWindowOverlapTopGhostStableIrRootClauses
      ring hn hbank seed pre e root hJ hcompleteOld htop hstable hir
  · exact bankWindowOverlapTopGhostStableNonIrRootClauses
      ring hn hbank seed pre e root hJ hcompleteOld htop hstable hir

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

/-- The genuine CSTART source issues its selected first-digit comparison
worker. Every source-owned non-proto/non-orphan root field is
established from OLD J and the universal post-comparator bundle.
Consumer: BankWindowOverlapJoint, M2 SRC CSTART S0/S1. -/
theorem bankWindowOverlapSourceActiveCstartIssueFields
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hscope : BankWindowScope ring
      (bankWindowRootBefore ring seed pre) e)
    (hmode :
      ((bankWindowRootBefore ring seed pre).1 e).mode = .CSTART)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hactive :
      ((bankWindowRootBefore ring seed pre).2.sites e).controller =
        .active p)
    (horigin : p.origin = some o) :
    bankWindowOverlapSourceActiveOwnerFields ring
      (bankWindowRootAfter ring seed pre e) e := by
  obtain ⟨hcomplete, hpostMode, hpostCtrl, hpostWorker,
    hpostOrigin, hrootOrigin, htoken, hheads, hbits⟩ :=
    bankWindowOverlapRootCstartIssuedComparatorCore
      ring hn hbank seed pre e hJ hscope hmode p o
      hactive horigin
  obtain ⟨hcurrent, hcompleteOrigin, hunique,
    hflags, honly, htrial, hheadsCurrent, hbound⟩ :=
    bankWindowOverlapRootCstartIssuedCurrentFields
      ring hn hbank seed pre e hJ hscope hmode p o
      hactive horigin
  have houter := bankWindowOverlapSourceActiveOuterDigitsClean
    ring hn hbank seed pre e hJ hscope
    (Or.inr hmode) p o hactive horigin
  have hnoInherited :
      ¬ BankWindowInheritedController
        (bankWindowRootAfter ring seed pre e) e := by
    intro h
    rcases h with ⟨atoms, hw, hne⟩ | ⟨q, hw, ho⟩
    · rw [hpostCtrl] at hw
      have heq : atoms = [] := by
        cases hw
        rfl
      exact hne heq
    · rw [hpostCtrl] at hw
      cases hw
  have hnoOther :
      ∀ (o' : RenewalBankOrigin n) (i : Fin n)
        (q : RenewalBankPayload n),
        o'.root = e →
        ((bankWindowRootAfter ring seed pre e).2.sites i).worker =
          .payload q →
        q.origin = some o' →
        i = ring.rightNeighbor e ∧ q = p := by
    intro o' i q hroot hworker hq
    exact bankWindowOverlapSourceActiveIssuedWorkerExclusive
      ring hn hbank seed pre e p hpostWorker
      (fun j hj => (houter j hj).1)
      i q o' hroot hworker hq
  have honlyRoot :
      bankWindowOnlyToken ring
        (bankWindowRootAfter ring seed pre e)
        e (ring.rightNeighbor e) := by
    rw [hrootOrigin] at honly
    exact honly
  unfold bankWindowOverlapSourceActiveOwnerFields
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o' i q hroot hcomp
    exact (bankWindowOverlapRootCstartUniversalCurrentFields
      ring hn hbank seed pre e hJ hscope hmode p o
      hactive horigin o' i q hroot hcomp).1
  · intro o' i q hroot hcomp hwait
    rw [hroot]
    exact hcomplete
  · intro o' i q hroot hcomp hwait j ht
    exact (bankWindowOverlapRootCstartUniversalCurrentFields
      ring hn hbank seed pre e hJ hscope hmode p o
      hactive horigin o' i q hroot hcomp).2.2.1 j ht
  · intro o' i q hroot hcomp hwait
    exact (bankWindowOverlapRootCstartUniversalCurrentFields
      ring hn hbank seed pre e hJ hscope hmode p o
      hactive horigin o' i q hroot hcomp).2.2.2.1
  · intro _ hi
    exact False.elim (hnoInherited hi)
  · intro _ hm
    rw [hpostMode] at hm
    cases hm
  · intro o' q _ hm
    rw [hpostMode] at hm
    rcases hm with h | h <;> cases h
  · intro o' i q _ hm
    rw [hpostMode] at hm
    cases hm
  · intro o' i q hroot hworker hq hm hc
    obtain ⟨hi, _⟩ := hnoOther o' i q hroot hworker hq
    have hlive :
        BankTrialLiveComparisonToken
          ((bankWindowRootAfter ring seed pre e).1 i).tok := by
      rw [hi]
      exact htrial
    have hcomp : BankComparatorOriginWorker ring
        (bankWindowRootAfter ring seed pre e) o' i q :=
      ⟨hworker, hq, hlive⟩
    exact (bankWindowOverlapRootCstartUniversalCurrentFields
      ring hn hbank seed pre e hJ hscope hmode p o
      hactive horigin o' i q hroot hcomp).2.2.2.2
  · intro _ hm
    rw [hpostMode] at hm
    cases hm
  · intro _ hm hc j ht
    by_cases hzero : j.val = 0
    · have hfirstSite :
          Counter.site ring e (j.val + 1) =
            ring.rightNeighbor e := by
        rw [hzero]
        rfl
      rw [hfirstSite]
      exact ⟨o, p, hpostWorker, hpostOrigin,
        hrootOrigin, htrial, honlyRoot⟩
    · have hother := (houter j (by omega)).1
      unfold BankWindowTainted at ht
      rw [hother] at ht
      rcases ht with ⟨rho, he⟩ | ⟨q, o', he, _⟩ <;> cases he

/-- A matching first bit produces CR1 in the real CSTART issue.
Consumer: BankWindowOverlapJoint, M2 SRC CSTART S1. -/
theorem bankWindowOverlapSourceActiveCstartMatchFields
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hscope : BankWindowScope ring
      (bankWindowRootBefore ring seed pre) e)
    (hmode :
      ((bankWindowRootBefore ring seed pre).1 e).mode = .CSTART)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hactive :
      ((bankWindowRootBefore ring seed pre).2.sites e).controller =
        .active p)
    (horigin : p.origin = some o)
    (hbit :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).bit =
        (compileAdvice (ceilLogTwo n)).theta 0) :
    bankWindowOverlapSourceActiveOwnerFields ring
      (bankWindowRootAfter ring seed pre e) e ∧
    ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).tok = .CR1 := by
  have hcore := bankWindowOverlapRootCstartIssuedComparatorCore
    ring hn hbank seed pre e hJ hscope hmode p o hactive horigin
  have ht := hcore.2.2.2.2.2.2.1
  rw [if_pos hbit] at ht
  exact ⟨bankWindowOverlapSourceActiveCstartIssueFields
    ring hn hbank seed pre e hJ hscope hmode p o
    hactive horigin, ht⟩

/-- Genuine CSTART S1 without an assumed OLD complete window.
The source-owned active origin and J.proto supply completeness.
Consumer: BankWindowOverlapJoint, M2 SRC CSTART S1. -/
theorem bankWindowOverlapSourceActiveCstartMatchGenuineFields
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hx : ((bankWindowRootBefore ring seed pre).1 e).pack.val = 0)
    (hg : ((bankWindowRootBefore ring seed pre).1 e).grant = false)
    (hm : ((bankWindowRootBefore ring seed pre).1 e).mode = .CSTART)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hactive :
      ((bankWindowRootBefore ring seed pre).2.sites e).controller =
        .active p)
    (horigin : p.origin = some o)
    (hbit :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).bit =
          (compileAdvice (ceilLogTwo n)).theta 0) :
    bankWindowOverlapSourceActiveOwnerFields ring
      (bankWindowRootAfter ring seed pre e) e ∧
    ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).tok = .CR1 := by
  have hscope : BankWindowScope ring
      (bankWindowRootBefore ring seed pre) e :=
    ⟨bankWindowOverlapSourceActiveGenuineComplete
      ring (bankWindowRootBefore ring seed pre)
      e hJ hx p o hactive horigin, hg⟩
  exact bankWindowOverlapSourceActiveCstartMatchFields
    ring hn hbank seed pre e hJ hscope hm p o
    hactive horigin hbit

/-- A nonmatching first bit produces CR0 in the real CSTART issue.
Consumer: BankWindowOverlapJoint, M2 SRC CSTART S0. -/
theorem bankWindowOverlapSourceActiveCstartMismatchFields
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hscope : BankWindowScope ring
      (bankWindowRootBefore ring seed pre) e)
    (hmode :
      ((bankWindowRootBefore ring seed pre).1 e).mode = .CSTART)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hactive :
      ((bankWindowRootBefore ring seed pre).2.sites e).controller =
        .active p)
    (horigin : p.origin = some o)
    (hbit :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).bit ≠
        (compileAdvice (ceilLogTwo n)).theta 0) :
    bankWindowOverlapSourceActiveOwnerFields ring
      (bankWindowRootAfter ring seed pre e) e ∧
    ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).tok = .CR0 := by
  have hcore := bankWindowOverlapRootCstartIssuedComparatorCore
    ring hn hbank seed pre e hJ hscope hmode p o hactive horigin
  have ht := hcore.2.2.2.2.2.2.1
  rw [if_neg hbit] at ht
  exact ⟨bankWindowOverlapSourceActiveCstartIssueFields
    ring hn hbank seed pre e hJ hscope hmode p o
    hactive horigin, ht⟩

/-- Genuine CSTART S0 without an assumed OLD complete window.
The source-owned active origin and J.proto supply completeness.
Consumer: BankWindowOverlapJoint, M2 SRC CSTART S0. -/
theorem bankWindowOverlapSourceActiveCstartMismatchGenuineFields
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hx : ((bankWindowRootBefore ring seed pre).1 e).pack.val = 0)
    (hg : ((bankWindowRootBefore ring seed pre).1 e).grant = false)
    (hm : ((bankWindowRootBefore ring seed pre).1 e).mode = .CSTART)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hactive :
      ((bankWindowRootBefore ring seed pre).2.sites e).controller =
        .active p)
    (horigin : p.origin = some o)
    (hbit :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).bit ≠
          (compileAdvice (ceilLogTwo n)).theta 0) :
    bankWindowOverlapSourceActiveOwnerFields ring
      (bankWindowRootAfter ring seed pre e) e ∧
    ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).tok = .CR0 := by
  have hscope : BankWindowScope ring
      (bankWindowRootBefore ring seed pre) e :=
    ⟨bankWindowOverlapSourceActiveGenuineComplete
      ring (bankWindowRootBefore ring seed pre)
      e hJ hx p o hactive horigin, hg⟩
  exact bankWindowOverlapSourceActiveCstartMismatchFields
    ring hn hbank seed pre e hJ hscope hm p o
    hactive horigin hbit

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

/-- Genuine source-root ARMED/A1 issue preserves all eleven
non-proto/non-orphan clauses of the exact bank window.
Consumer: R11 M2 SRC ARMED A1. -/
theorem bankWindowOverlapSourceActiveArmedIssueFields
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hscope : BankWindowScope ring
      (bankWindowRootBefore ring seed pre) e)
    (hm :
      ((bankWindowRootBefore ring seed pre).1 e).mode = .ARMED)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hactive :
      ((bankWindowRootBefore ring seed pre).2.sites e).controller =
        .active p)
    (horigin : p.origin = some o)
    (hbit :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).bit = true) :
    bankWindowOverlapSourceActiveOwnerFields ring
      (bankWindowRootAfter ring seed pre e) e := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hx :
      ((bankWindowRootBefore ring seed pre).1 e).pack.val = 0 := by
    change ((bankWindowRootBefore ring seed pre).1
      (Counter.site ring e 0)).pack.val = 0
    exact hscope.1 0 (by omega)
  have hy :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val = 1 := by
    change ((bankWindowRootBefore ring seed pre).1
      (Counter.site ring e 1)).pack.val = 1
    exact hscope.1 1 (by omega)
  have hbeforeArmed := hJ.armedExact e o p hscope
    (Or.inl hm) hactive horigin
  have ht :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .E := by
    have hh := hbeforeArmed.1
      (⟨0, hb⟩ : Fin (compileAdvice (ceilLogTwo n)).b)
    change ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).tok = .E at hh
    exact hh
  have hphysical := bankWindowOverlapSourceActiveArmedPhysical
    ring hn hbank (bankWindowRootBefore ring seed pre)
    e hx hy hscope.2 hm ht
  have hpostMode :
      ((bankWindowRootAfter ring seed pre e).1 e).mode = .IWAIT := by
    have hh := hphysical.1
    rw [hbit] at hh
    exact hh
  have hpostTok :
      ((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).tok = .IR := by
    have hh := hphysical.2.1
    rw [hbit] at hh
    exact hh
  have hpostBit :
      ((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).bit = false := by
    have hh := hphysical.2.2
    rw [hbit] at hh
    exact hh
  have hrole :
      ((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).pack.val = 1 :=
    (bankWindowRootSourceRoles ring hn
      (bankWindowRootBefore ring seed pre) e hx).2
  obtain ⟨hcomplete, hpostCtrl, hpostWorker,
    hpostOrigin, hpostHeads⟩ :=
    bankWindowClosureArmedIssueGenuine
      ring hn (bankWindowRootBefore ring seed pre) e
      hJ hscope hm p o hactive horigin hbit
  have hrootOrigin : o.root = e := by
    have hi := rbReceiptInvBankWordOfInv
      ring (by omega : 2 ≤ n) seed hbank pre
    exact (hi.activeRoot e p o hactive horigin).symm
  have hvalue :
      bankOriginBinaryValue ring
        (bankWindowRootBefore ring seed pre).1 o =
      bankOriginBinaryValue ring
        (bankWindowRootAfter ring seed pre e).1 o + 1 := by
    exact bankWindowOverlapSourceActiveBitClearValue
      ring hbank (bankWindowRootBefore ring seed pre) e
      o hrootOrigin hbit hpostBit
  have hnewHeads :
      (renewalBankHead p).heads =
        bankOriginBinaryValue ring
          (bankWindowRootAfter ring seed pre e).1 o +
          2 ^ ((bankWindowRootAfter ring seed pre e).1
            (ring.rightNeighbor e)).pack.val := by
    rw [hrole]
    change (renewalBankHead p).heads =
      bankOriginBinaryValue ring
        (bankWindowRootAfter ring seed pre e).1 o + 2
    rw [hvalue] at hpostHeads
    omega
  have hnewBound :
      bankOriginBinaryValue ring
        (bankWindowRootAfter ring seed pre e).1 o +
        2 ^ ((bankWindowRootAfter ring seed pre e).1
          (ring.rightNeighbor e)).pack.val ≤
        (compileAdvice (ceilLogTwo n)).K := by
    rw [hrole]
    change bankOriginBinaryValue ring
        (bankWindowRootAfter ring seed pre e).1 o + 2 ≤
      (compileAdvice (ceilLogTwo n)).K
    have holdStrict :
        bankOriginBinaryValue ring
          (bankWindowRootBefore ring seed pre).1 o <
        (compileAdvice (ceilLogTwo n)).K :=
      hbeforeArmed.2.2.1 hm
    omega
  have houter := bankWindowOverlapSourceActiveOuterDigitsClean
    ring hn hbank seed pre e hJ hscope
    (Or.inl hm) p o hactive horigin
  have honly :
      bankWindowOnlyToken ring
        (bankWindowRootAfter ring seed pre e)
        e (ring.rightNeighbor e) := by
    intro j hne
    by_cases hz : j.val = 0
    · rw [hz]
      rfl
    · exact False.elim (hne (houter j (by omega)).2)
  have hnoInherited :
      ¬ BankWindowInheritedController
        (bankWindowRootAfter ring seed pre e) e := by
    intro hi
    rcases hi with ⟨atoms, hw, hne⟩ | ⟨q, hw, ho⟩
    · rw [hpostCtrl] at hw
      have heq : atoms = [] := by
        cases hw
        rfl
      exact hne heq
    · rw [hpostCtrl] at hw
      cases hw
  have hnoComparator :
      ∀ (o' : RenewalBankOrigin n) (i : Fin n)
        (q : RenewalBankPayload n),
        o'.root = e →
        BankComparatorOriginWorker ring
          (bankWindowRootAfter ring seed pre e) o' i q → False := by
    intro o' i q hr hcomp
    obtain ⟨hi, _⟩ :=
      bankWindowOverlapSourceActiveIssuedWorkerExclusive
        ring hn hbank seed pre e (renewalBankHead p)
        hpostWorker (fun j hj => (houter j hj).1)
        i q o' hr hcomp.1 hcomp.2.1
    have htcomp := hcomp.2.2
    rw [hi, hpostTok] at htcomp
    simp [BankTrialLiveComparisonToken] at htcomp
  unfold bankWindowOverlapSourceActiveOwnerFields
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o' i q hr hcomp
    exact False.elim (hnoComparator o' i q hr hcomp)
  · intro o' i q hr hcomp _
    exact False.elim (hnoComparator o' i q hr hcomp)
  · intro o' i q hr hcomp _ _
    exact False.elim (hnoComparator o' i q hr hcomp)
  · intro o' i q hr hcomp _
    exact False.elim (hnoComparator o' i q hr hcomp)
  · intro _ hi
    exact False.elim (hnoInherited hi)
  · intro _ hw
    rw [hpostMode] at hw
    cases hw
  · intro o' q _ hphasePost
    rw [hpostMode] at hphasePost
    rcases hphasePost with hh | hh <;> cases hh
  · intro o' i q _ hmodeI hctl hworker horiginNew hrootNew
    obtain ⟨hi, hqeq⟩ :=
      bankWindowOverlapSourceActiveIssuedWorkerExclusive
        ring hn hbank seed pre e (renewalBankHead p)
        hpostWorker (fun j hj => (houter j hj).1)
        i q o' hrootNew hworker horiginNew
    have ho : o' = o := by
      have hh : some o' = some o := by
        calc
          some o' = q.origin := horiginNew.symm
          _ = (renewalBankHead p).origin := congrArg
            (fun z : RenewalBankPayload n => z.origin) hqeq
          _ = some o := hpostOrigin
      exact Option.some.inj hh
    subst i
    subst q
    subst o'
    have hzero :
        bankWindowZeroPrefix ring
          (bankWindowRootAfter ring seed pre e) e 1 := by
      intro j hj
      have hz : j.val = 0 := by omega
      rw [hz]
      change ((bankWindowRootAfter ring seed pre e).1
        (ring.rightNeighbor e)).bit = false
      exact hpostBit
    have hzeroRole :
        bankWindowZeroPrefix ring
          (bankWindowRootAfter ring seed pre e) e
          ((bankWindowRootAfter ring seed pre e).1
            (ring.rightNeighbor e)).pack.val := by
      rw [hrole]
      exact hzero
    exact ⟨honly, Or.inl
      ⟨hpostTok, hzeroRole, hnewHeads, hnewBound⟩⟩
  · intro o' i q hr hw hq hmodeC _
    rw [hr, hpostMode] at hmodeC
    cases hmodeC
  · intro _ hmodeI hctl j ht
    by_cases hz : j.val = 0
    · have hfirstSite :
          Counter.site ring e (j.val + 1) =
            ring.rightNeighbor e := by
        rw [hz]
        rfl
      rw [hfirstSite]
      exact ⟨o, renewalBankHead p, hpostWorker,
        hpostOrigin, hrootOrigin, honly⟩
    · have hempty := (houter j (by omega)).1
      unfold BankWindowTainted at ht
      rw [hempty] at ht
      rcases ht with ⟨rho, hh⟩ |
        ⟨q, o', hh, _⟩ <;> cases hh
  · intro _ hmodeC
    rw [hpostMode] at hmodeC
    cases hmodeC

/-- The genuine-ARMED root supplies its own complete
window from OLD exact J, so the A1 issue theorem applies
without separately assuming scope.
Consumer: R11 M2 SRC ARMED A1. -/
theorem bankWindowOverlapSourceActiveArmedIssueGenuineFields
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hx : ((bankWindowRootBefore ring seed pre).1 e).pack.val = 0)
    (hg : ((bankWindowRootBefore ring seed pre).1 e).grant = false)
    (hm : ((bankWindowRootBefore ring seed pre).1 e).mode = .ARMED)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hactive :
      ((bankWindowRootBefore ring seed pre).2.sites e).controller =
        .active p)
    (horigin : p.origin = some o)
    (hbit :
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).bit = true) :
    bankWindowOverlapSourceActiveOwnerFields ring
      (bankWindowRootAfter ring seed pre e) e := by
  have hscope : BankWindowScope ring
      (bankWindowRootBefore ring seed pre) e :=
    ⟨bankWindowOverlapSourceActiveGenuineComplete
      ring (bankWindowRootBefore ring seed pre)
      e hJ hx p o hactive horigin, hg⟩
  exact bankWindowOverlapSourceActiveArmedIssueFields
    ring hn hbank seed pre e hJ hscope hm p o
    hactive horigin hbit

/-- An inherited ARMED source sends an origin-free
head payload to its right neighbor iff that digit is set,
while preserving the inherited origin-free certificate.
Consumer: R11 M2 SRC inherited ARMED A0/A1. -/
theorem bankWindowOverlapSourceActiveInheritedArmedMemory
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hm : x.mode = .ARMED) (ht : y.tok = .E)
    (p : RenewalBankPayload n)
    (hactive : (m.sites e).controller = .active p)
    (hnone : p.origin = none) :
    (renewalBankPairMemory c m e dest x y).1.controller =
      (if y.bit then .waiting [] else .active (renewalBankHead p)) ∧
    (renewalBankPairMemory c m e dest x y).2.worker =
      (if y.bit then .payload (renewalBankHead p)
        else (m.sites dest).worker) ∧
    (renewalBankHead p).origin = none := by
  have hnoneHead : (renewalBankHead p).origin = none := by
    simp [renewalBankHead, hnone]
  cases hbit : y.bit with
  | false =>
      have hrow := rbArmedIdleMemoryExact
        c m e dest x y hb hx hy hg hm ht hbit
      rw [hrow]
      simp [hbit, renewalBankActivePayload, hactive, hnoneHead]
  | true =>
      have hrow := rbArmedWorkMemoryExact
        c m e dest x y hb hx hy hg hm ht hbit
      rw [hrow]
      simp [hbit, renewalBankActivePayload, hactive, hnoneHead]

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

/-- R11 M2-j, LongWait: the native BANK and ghost first-match rows
keep the source's waiting mode and controller, and the responder's
digit bit, token, and worker. This includes non-E non-return tokens.
Consumer: bankWindowOverlapSourceLongWaitPhysicalReads. -/
theorem bankWindowOverlapSourceLongWaitCellReads
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hphase : x.mode = .RWAIT ∨ x.mode = .IWAIT ∨
      x.mode = .CWAIT)
    (hlong : 1 < x.lease.val)
    (hret : isRetTok y.tok = false) :
    (Counter.resetBankOld x y).1.mode = x.mode ∧
    (Counter.resetBankOld x y).2.bit = y.bit ∧
    (Counter.resetBankOld x y).2.tok = y.tok ∧
    (renewalBankPairMemory c m e dest x y).1.controller =
      (m.sites e).controller ∧
    (renewalBankPairMemory c m e dest x y).2.worker =
      (m.sites dest).worker := by
  have hb : 0 < c.b := by
    change 0 < c.s + 11
    omega
  have hbNotZero : c.b ≠ 0 := by omega
  have hwide : c.b ≠ 1 := by
    change c.s + 11 ≠ 1
    omega
  have hbAtLeastOne : 1 ≤ c.b := by omega
  have hp : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  have hnoRl : y.tok ≠ .RL := by
    intro h
    simp [h, isRetTok] at hret
  have hnoAl : y.tok ≠ .AL := by
    intro h
    simp [h, isRetTok] at hret
  have hnoClZero : y.tok ≠ .CL0 := by
    intro h
    simp [h, isRetTok] at hret
  have hnoClOne : y.tok ≠ .CL1 := by
    intro h
    simp [h, isRetTok] at hret
  rcases hphase with hm | hm | hm
  · simp [Counter.resetBankOld, bankPair,
      renewalBankPairMemory, renewalBankWaitSlot,
      bankCell, hx, hy, hg, hm, hlong, hret,
      hbAtLeastOne, hb, hp, isWaitMode, isRetTok,
      Id.run_pure, Id.run_bind] <;>
      simp only [if_neg hbNotZero, if_neg hwide,
        if_neg hnoRl, if_neg hnoAl,
        if_neg hnoClZero, if_neg hnoClOne,
        if_true, if_false, Id.run_pure] <;> first | rfl | simp
  · simp [Counter.resetBankOld, bankPair,
      renewalBankPairMemory, renewalBankWaitSlot,
      bankCell, hx, hy, hg, hm, hlong, hret,
      hbAtLeastOne, hb, hp, isWaitMode, isRetTok,
      Id.run_pure, Id.run_bind] <;>
      simp only [if_neg hbNotZero, if_neg hwide,
        if_neg hnoRl, if_neg hnoAl,
        if_neg hnoClZero, if_neg hnoClOne,
        if_true, if_false, Id.run_pure] <;> first | rfl | simp
  · simp [Counter.resetBankOld, bankPair,
      renewalBankPairMemory, renewalBankWaitSlot,
      bankCell, hx, hy, hg, hm, hlong, hret,
      hbAtLeastOne, hb, hp, isWaitMode, isRetTok,
      Id.run_pure, Id.run_bind] <;>
      simp only [if_neg hbNotZero, if_neg hwide,
        if_neg hnoRl, if_neg hnoAl,
        if_neg hnoClZero, if_neg hnoClOne,
        if_true, if_false, Id.run_pure] <;> first | rfl | simp

/-- Actual rbRun source edge for LongWait. All five equalities
are on renewalBankNext, not a substituted BANK-only step.
Consumer: bankWindowOverlapSourceLongWaitWindowReads. -/
theorem bankWindowOverlapSourceLongWaitPhysicalReads
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hx : ((bankWindowRootBefore ring seed pre).1 e).pack.val = 0)
    (hy : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = 1)
    (hg : ((bankWindowRootBefore ring seed pre).1 e).grant = false)
    (hphase : ((bankWindowRootBefore ring seed pre).1 e).mode =
        .RWAIT ∨
      ((bankWindowRootBefore ring seed pre).1 e).mode = .IWAIT ∨
      ((bankWindowRootBefore ring seed pre).1 e).mode = .CWAIT)
    (hlong : 1 < ((bankWindowRootBefore ring seed pre).1 e).lease.val)
    (hret : isRetTok ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).tok = false) :
    ((bankWindowRootAfter ring seed pre e).1 e).mode =
      ((bankWindowRootBefore ring seed pre).1 e).mode ∧
    ((bankWindowRootAfter ring seed pre e).2.sites e).controller =
      ((bankWindowRootBefore ring seed pre).2.sites e).controller ∧
    ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).bit =
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).bit ∧
    ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).tok =
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).tok ∧
    ((bankWindowRootAfter ring seed pre e).2.sites
      (ring.rightNeighbor e)).worker =
      ((bankWindowRootBefore ring seed pre).2.sites
        (ring.rightNeighbor e)).worker := by
  have hlocal := bankWindowOverlapSourceLongWaitCellReads
    (compileAdvice (ceilLogTwo n))
    (bankWindowRootBefore ring seed pre).2
    e (ring.rightNeighbor e)
    ((bankWindowRootBefore ring seed pre).1 e)
    ((bankWindowRootBefore ring seed pre).1 (ring.rightNeighbor e))
    hx hy hg hphase hlong hret
  have htrips := bankWindowClosureSelectedBankTrip
    ring hn hbank (bankWindowRootBefore ring seed pre) e
  have hm := congrArg
    (fun t : Mode × Bool × BTok => t.1) htrips.1
  change ((bankWindowRootAfter ring seed pre e).1 e).mode =
    (Counter.resetBankOld
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).1.mode at hm
  have hbit := congrArg
    (fun t : Mode × Bool × BTok => t.2.1) htrips.2
  change ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).bit =
    (Counter.resetBankOld
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).2.bit at hbit
  have htok := congrArg
    (fun t : Mode × Bool × BTok => t.2.2) htrips.2
  change ((bankWindowRootAfter ring seed pre e).1
      (ring.rightNeighbor e)).tok =
    (Counter.resetBankOld
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).2.tok at htok
  have hframe := (rbReferenceSelectedPairFrame ring
    (by omega : 2 ≤ n) (bankWindowRootBefore ring seed pre) e).2.2
  have hctl := congrArg
    (fun s : RenewalBankSite n => s.controller) hframe.1
  change ((bankWindowRootAfter ring seed pre e).2.sites e).controller =
    (renewalBankPairMemory
      (compileAdvice (ceilLogTwo n))
      (bankWindowRootBefore ring seed pre).2
      e (ring.rightNeighbor e)
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).1.controller at hctl
  have hw := congrArg
    (fun s : RenewalBankSite n => s.worker) hframe.2
  change ((bankWindowRootAfter ring seed pre e).2.sites
      (ring.rightNeighbor e)).worker =
    (renewalBankPairMemory
      (compileAdvice (ceilLogTwo n))
      (bankWindowRootBefore ring seed pre).2
      e (ring.rightNeighbor e)
      ((bankWindowRootBefore ring seed pre).1 e)
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e))).2.worker at hw
  exact ⟨hm.trans hlocal.1,
    hctl.trans hlocal.2.2.2.1,
    hbit.trans hlocal.2.1,
    htok.trans hlocal.2.2.1,
    hw.trans hlocal.2.2.2.2⟩

/-- LongWait preserves every source-window PACK, digit token,
digit bit, digit worker, source mode, and source controller.
The lease is deliberately not in this read interface.
Consumer: bankWindowOverlapSourceLongWaitOwnClauses. -/
theorem bankWindowOverlapSourceLongWaitWindowReads
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hx : ((bankWindowRootBefore ring seed pre).1 e).pack.val = 0)
    (hy : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = 1)
    (hg : ((bankWindowRootBefore ring seed pre).1 e).grant = false)
    (hphase : ((bankWindowRootBefore ring seed pre).1 e).mode =
        .RWAIT ∨
      ((bankWindowRootBefore ring seed pre).1 e).mode = .IWAIT ∨
      ((bankWindowRootBefore ring seed pre).1 e).mode = .CWAIT)
    (hlong : 1 < ((bankWindowRootBefore ring seed pre).1 e).lease.val)
    (hret : isRetTok ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).tok = false) :
    bankWindowReadPackPrefix ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) e
      (compileAdvice (ceilLogTwo n)).b ∧
    bankWindowReadDigitTokens ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) e ∧
    bankWindowReadDigitBits ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) e ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      bankWindowReadWorker
        (bankWindowRootBefore ring seed pre)
        (bankWindowRootAfter ring seed pre e)
        (Counter.site ring e (j.val + 1))) ∧
    bankWindowReadMode
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) e ∧
    bankWindowReadController
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) e := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hstable :
      packNext
        ((bankWindowRootBefore ring seed pre).1 e).pack.val
        ((bankWindowRootBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((bankWindowRootBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val := by
    rw [hx, hy]
    simp [packNext, hb]
  have hpackAll :=
    bankWindowOverlapStablePackFrame ring hn seed pre e hstable
  have hphysical := bankWindowOverlapSourceLongWaitPhysicalReads
    ring hn hbank seed pre e hx hy hg hphase hlong hret
  have hpack :
      bankWindowReadPackPrefix ring
        (bankWindowRootBefore ring seed pre)
        (bankWindowRootAfter ring seed pre e) e
        (compileAdvice (ceilLogTwo n)).b := by
    intro k hk
    exact hpackAll (Counter.site ring e k)
  have hslots :
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      bankWindowReadTok
        (bankWindowRootBefore ring seed pre)
        (bankWindowRootAfter ring seed pre e)
        (Counter.site ring e (j.val + 1)) ∧
      bankWindowReadBit
        (bankWindowRootBefore ring seed pre)
        (bankWindowRootAfter ring seed pre e)
        (Counter.site ring e (j.val + 1)) ∧
      bankWindowReadWorker
        (bankWindowRootBefore ring seed pre)
        (bankWindowRootAfter ring seed pre e)
        (Counter.site ring e (j.val + 1)) := by
    intro j
    by_cases hz : j.val = 0
    · have hsite :
          Counter.site ring e (j.val + 1) =
            ring.rightNeighbor e := by
        rw [hz]
        rfl
      rw [hsite]
      exact ⟨hphysical.2.2.2.1,
        hphysical.2.2.1, hphysical.2.2.2.2⟩
    · have hbound : j.val + 1 ≤
          (compileAdvice (ceilLogTwo n)).b + 1 := by
        have hj := j.isLt
        omega
      have hsource :
          Counter.site ring e (j.val + 1) ≠ e := by
        have hh := bankWindowIncidenceSiteDistinct ring hbank
          e 0 (j.val + 1) (by omega) hbound
        change e ≠ Counter.site ring e (j.val + 1) at hh
        exact hh.symm
      have htarget :
          Counter.site ring e (j.val + 1) ≠
            ring.rightNeighbor e := by
        have hh := bankWindowIncidenceSiteDistinct ring hbank
          e 1 (j.val + 1) (by omega) hbound
        change ring.rightNeighbor e ≠
          Counter.site ring e (j.val + 1) at hh
        exact hh.symm
      have hf := bankWindowExactOffPairFrame ring
        (bankWindowRootBefore ring seed pre) e
        (Counter.site ring e (j.val + 1)) hsource htarget
      exact ⟨congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok) hf.1,
        congrArg
          (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.bit) hf.1,
        congrArg
          (fun a : RenewalBankSite n => a.worker) hf.2⟩
  exact ⟨hpack,
    (fun j => (hslots j).1),
    (fun j => (hslots j).2.1),
    (fun j => (hslots j).2.2),
    hphysical.1, hphysical.2.1⟩

/-- A genuine POST worker owned by this LongWait source has its
free-site PACK, token, and worker reads preserved. The real-run
ReceiptInv excludes the PACK-zero source itself; the PACK-one
responder is covered by the first-digit read, every other site
by the selected off-pair frame.
Consumer: bankWindowOverlapSourceLongWaitReadTransport. -/
theorem bankWindowOverlapSourceLongWaitGenuineReads
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hx : ((bankWindowRootBefore ring seed pre).1 e).pack.val = 0)
    (hpack : bankWindowReadPackPrefix ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) e
      (compileAdvice (ceilLogTwo n)).b)
    (htoks : bankWindowReadDigitTokens ring
      (bankWindowRootBefore ring seed pre)
      (bankWindowRootAfter ring seed pre e) e)
    (hworkers : ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      bankWindowReadWorker
        (bankWindowRootBefore ring seed pre)
        (bankWindowRootAfter ring seed pre e)
        (Counter.site ring e (j.val + 1))) :
    ∀ (o : RenewalBankOrigin n) (i : Fin n)
      (p : RenewalBankPayload n),
      o.root = e →
      ((bankWindowRootAfter ring seed pre e).2.sites i).worker =
        .payload p →
      p.origin = some o →
      bankWindowReadPack (bankWindowRootBefore ring seed pre)
        (bankWindowRootAfter ring seed pre e) i ∧
      bankWindowReadTok (bankWindowRootBefore ring seed pre)
        (bankWindowRootAfter ring seed pre e) i ∧
      bankWindowReadWorker (bankWindowRootBefore ring seed pre)
        (bankWindowRootAfter ring seed pre e) i := by
  have hcarrier := bankWindowRootSelectedCarrierOwnership
    ring hn hbank seed pre e hJ hx
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  intro o i p ho hw horigin
  by_cases hsource : i = e
  · subst i
    exact False.elim (hcarrier.2.2.1 p o hw horigin)
  · by_cases htarget : i = ring.rightNeighbor e
    · subst i
      have hp : bankWindowReadPack
          (bankWindowRootBefore ring seed pre)
          (bankWindowRootAfter ring seed pre e)
          (ring.rightNeighbor e) := by
        change bankWindowReadPack
          (bankWindowRootBefore ring seed pre)
          (bankWindowRootAfter ring seed pre e)
          (Counter.site ring e 1)
        exact hpack 1 (by omega)
      have ht : bankWindowReadTok
          (bankWindowRootBefore ring seed pre)
          (bankWindowRootAfter ring seed pre e)
          (ring.rightNeighbor e) := by
        change bankWindowReadTok
          (bankWindowRootBefore ring seed pre)
          (bankWindowRootAfter ring seed pre e)
          (Counter.site ring e (0 + 1))
        exact htoks (⟨0, hb⟩ : Fin (compileAdvice (ceilLogTwo n)).b)
      have hworker : bankWindowReadWorker
          (bankWindowRootBefore ring seed pre)
          (bankWindowRootAfter ring seed pre e)
          (ring.rightNeighbor e) := by
        change bankWindowReadWorker
          (bankWindowRootBefore ring seed pre)
          (bankWindowRootAfter ring seed pre e)
          (Counter.site ring e (0 + 1))
        exact hworkers (⟨0, hb⟩ : Fin (compileAdvice (ceilLogTwo n)).b)
      exact ⟨hp, ht, hworker⟩
    · have hf := bankWindowExactOffPairFrame ring
        (bankWindowRootBefore ring seed pre) e i
        hsource htarget
      exact ⟨congrArg
          (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
            a.pack.val) hf.1,
        congrArg
          (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
            a.tok) hf.1,
        congrArg
          (fun a : RenewalBankSite n => a.worker) hf.2⟩

/-- The first eleven R11 source-root clauses transport across a
LongWait observational frame. Unlike a full Agent equality,
the read set does not assume that the lease remains unchanged.
The source remains in a wait mode, so armedExact is vacuous.
Consumer: M2-j complete and incomplete OLD source rows. -/
theorem bankWindowOverlapSourceLongWaitReadTransport
    {n : Nat} (ring : DirectedRing n)
    (r s : RenewalBankReference n) (root : Fin n)
    (hJ : BankWindowExact ring r)
    (hpack : bankWindowReadPackPrefix ring r s root
      (compileAdvice (ceilLogTwo n)).b)
    (htoks : bankWindowReadDigitTokens ring r s root)
    (hbits : bankWindowReadDigitBits ring r s root)
    (hworkers : ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      bankWindowReadWorker r s
        (Counter.site ring root (j.val + 1)))
    (hmode : bankWindowReadMode r s root)
    (hctrl : bankWindowReadController r s root)
    (hg : (r.1 root).grant = false)
    (hfree : ∀ (o : RenewalBankOrigin n) (i : Fin n)
        (p : RenewalBankPayload n),
      o.root = root →
      (s.2.sites i).worker = .payload p →
      p.origin = some o →
      bankWindowReadPack r s i ∧
      bankWindowReadTok r s i ∧
      bankWindowReadWorker r s i)
    (hwait : (s.1 root).mode = .RWAIT ∨
      (s.1 root).mode = .IWAIT ∨
      (s.1 root).mode = .CWAIT) :
    bankWindowOverlapSourceOwnClauses ring s root := by
  have hgrant : BankWindowScope ring s root →
      bankWindowReadGrant r s root := by
    intro hs
    change (s.1 root).grant = (r.1 root).grant
    exact hs.2.trans hg.symm
  have hphaseReads :
      ∀ (o : RenewalBankOrigin n) (i : Fin n)
        (p : RenewalBankPayload n),
        o.root = root →
        BankComparatorOriginWorker ring s o i p →
        bankWindowPhaseExcludesReadSet r s o i p := by
    intro o i p ho hw
    have hr := hfree o i p ho hw.1 hw.2.1
    exact ⟨hr.2.1, hr.2.2, by rw [ho]; exact hmode⟩
  have hnoArmed : (s.1 root).mode ≠ .ARMED := by
    intro hbad
    rcases hwait with hw | hw | hw
    · rw [hw] at hbad
      cases hbad
    · rw [hw] at hbad
      cases hbad
    · rw [hw] at hbad
      cases hbad
  have hnoCstart : (s.1 root).mode ≠ .CSTART := by
    intro hbad
    rcases hwait with hw | hw | hw
    · rw [hw] at hbad
      cases hbad
    · rw [hw] at hbad
      cases hbad
    · rw [hw] at hbad
      cases hbad
  unfold bankWindowOverlapSourceOwnClauses
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro o i p ho hw
    exact bankWindowPhaseExcludesReadTransport ring r s o i p hJ
      (hphaseReads o i p ho hw) hw
  · intro o i p ho hw hm
    exact bankWindowPhaseCompleteReadTransport ring r s o i p hJ
      ⟨hphaseReads o i p ho hw, by rw [ho]; exact hpack⟩
      hw hm
  · intro o i p ho hw hm j ht
    exact bankWindowPhaseUniqueReadTransport ring r s o i p hJ
      ⟨hphaseReads o i p ho hw, by rw [ho]; exact htoks⟩
      hw hm j ht
  · intro o i p ho hw hm
    have hr := hfree o i p ho hw.1 hw.2.1
    exact bankWindowPhaseFlagsReadTransport ring r s o i p hJ
      ⟨hphaseReads o i p ho hw, hr.1,
        by rw [ho]; exact hbits⟩ hw hm
  · intro hs hi j ht
    exact bankWindowInheritedCleanReadTransport ring r s root j hJ
      ⟨hpack, hgrant hs, hctrl, hworkers j⟩ hs hi ht
  · intro hs hm hc
    exact bankWindowResetWaitReadTransport ring r s root hJ
      ⟨hpack, hgrant hs, hmode, hctrl,
        hbits, htoks, hworkers⟩ hs hm hc
  · intro o p hs hm
    rcases hm with ha | hc
    · exact False.elim (hnoArmed ha)
    · exact False.elim (hnoCstart hc)
  · intro o i p hs hm hc hw ho hr
    have hf := hfree o i p hr hw ho
    exact bankWindowIncrementExactReadTransport ring r s root o i p hJ
      ⟨hpack, hgrant hs, hmode, hctrl, hf.2.2,
        hf.1, hf.2.1, htoks, hbits,
        by rw [hr]; exact hbits⟩
      hs hm hc hw ho hr
  · intro o i p ho hw horigin hm hc
    have hf := hfree o i p ho hw horigin
    exact bankWindowCompareExactReadTransport ring r s o i p hJ
      ⟨by rw [ho]; exact hmode,
        by rw [ho]; exact hctrl,
        hf.2.2, hf.2.1,
        by rw [ho]; exact htoks,
        by rw [ho]; exact hbits⟩
      hw horigin hm hc
  · intro hs hm hc j ht
    exact bankWindowIwaitTaintedUniqueReadTransport ring r s root j hJ
      ⟨hpack, hgrant hs, hmode, hctrl,
        htoks, hworkers j⟩ hs hm hc ht
  · intro hs hm hc j ht
    exact bankWindowCwaitTaintedUniqueReadTransport ring r s root j hJ
      ⟨hpack, hgrant hs, hmode, hctrl,
        htoks, hworkers j⟩ hs hm hc ht

/-- Authentic M2-j LongWait source-owned clauses, common to a
complete or an incomplete OLD root. This uses OLD BankWindowExact
and first-match non-return service, never a POST-J assumption.
Consumer: the two case-indexed M2-j theorems below. -/
theorem bankWindowOverlapSourceLongWaitOwnClauses
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hx : ((bankWindowRootBefore ring seed pre).1 e).pack.val = 0)
    (hy : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = 1)
    (hg : ((bankWindowRootBefore ring seed pre).1 e).grant = false)
    (hphase : ((bankWindowRootBefore ring seed pre).1 e).mode =
        .RWAIT ∨
      ((bankWindowRootBefore ring seed pre).1 e).mode = .IWAIT ∨
      ((bankWindowRootBefore ring seed pre).1 e).mode = .CWAIT)
    (hlong : 1 < ((bankWindowRootBefore ring seed pre).1 e).lease.val)
    (hret : isRetTok ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).tok = false) :
    bankWindowOverlapSourceOwnClauses ring
      (bankWindowRootAfter ring seed pre e) e := by
  have hreads := bankWindowOverlapSourceLongWaitWindowReads
    ring hn hbank seed pre e hx hy hg hphase hlong hret
  have hfree := bankWindowOverlapSourceLongWaitGenuineReads
    ring hn hbank seed pre e hJ hx
    hreads.1 hreads.2.1 hreads.2.2.2.1
  have hwait :
      ((bankWindowRootAfter ring seed pre e).1 e).mode = .RWAIT ∨
      ((bankWindowRootAfter ring seed pre e).1 e).mode = .IWAIT ∨
      ((bankWindowRootAfter ring seed pre e).1 e).mode = .CWAIT := by
    rw [hreads.2.2.2.2.1]
    exact hphase
  exact bankWindowOverlapSourceLongWaitReadTransport ring
    (bankWindowRootBefore ring seed pre)
    (bankWindowRootAfter ring seed pre e) e hJ
    hreads.1 hreads.2.1 hreads.2.2.1
    hreads.2.2.2.1 hreads.2.2.2.2.1
    hreads.2.2.2.2.2 hg hfree hwait

/-- R11 M2-j, LongWait complete OLD window (R2/I1/C2).
The post source has all eleven owned J clauses.
Joint adds proto and orphan from complete-source exclusion.
Consumer: bankWindowRootFieldsAtOfSourceOwnClauses. -/
theorem bankWindowOverlapSourceLongWaitCompleteOwnClauses
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hcomplete : Counter.Complete ring
      (bankWindowRootBefore ring seed pre).1 e)
    (hx : ((bankWindowRootBefore ring seed pre).1 e).pack.val = 0)
    (hy : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = 1)
    (hg : ((bankWindowRootBefore ring seed pre).1 e).grant = false)
    (hphase : ((bankWindowRootBefore ring seed pre).1 e).mode =
        .RWAIT ∨
      ((bankWindowRootBefore ring seed pre).1 e).mode = .IWAIT ∨
      ((bankWindowRootBefore ring seed pre).1 e).mode = .CWAIT)
    (hlong : 1 < ((bankWindowRootBefore ring seed pre).1 e).lease.val)
    (hret : isRetTok ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).tok = false) :
    bankWindowOverlapSourceOwnClauses ring
      (bankWindowRootAfter ring seed pre e) e := by
  exact bankWindowOverlapSourceLongWaitOwnClauses
    ring hn hbank seed pre e hJ hx hy hg hphase hlong hret

/-- R11 M2-j, LongWait incomplete OLD window (R2/I1/C2).
The post source has all eleven owned J clauses, even when a
non-E responder token is present. Joint adds M3's
bankWindowOverlapNonreturnLongWaitPrefixOrphan.
Consumer: bankWindowRootFieldsAtOfSourceOwnClauses. -/
theorem bankWindowOverlapSourceLongWaitIncompleteOwnClauses
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowRootBefore ring seed pre))
    (hincomplete : ¬ Counter.Complete ring
      (bankWindowRootBefore ring seed pre).1 e)
    (hx : ((bankWindowRootBefore ring seed pre).1 e).pack.val = 0)
    (hy : ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = 1)
    (hg : ((bankWindowRootBefore ring seed pre).1 e).grant = false)
    (hphase : ((bankWindowRootBefore ring seed pre).1 e).mode =
        .RWAIT ∨
      ((bankWindowRootBefore ring seed pre).1 e).mode = .IWAIT ∨
      ((bankWindowRootBefore ring seed pre).1 e).mode = .CWAIT)
    (hlong : 1 < ((bankWindowRootBefore ring seed pre).1 e).lease.val)
    (hret : isRetTok ((bankWindowRootBefore ring seed pre).1
      (ring.rightNeighbor e)).tok = false) :
    bankWindowOverlapSourceOwnClauses ring
      (bankWindowRootAfter ring seed pre e) e := by
  exact bankWindowOverlapSourceLongWaitOwnClauses
    ring hn hbank seed pre e hJ hx hy hg hphase hlong hret

end L3.BankWindow

#print axioms L3.BankWindow.bankWindowRootSourceRoles
#print axioms L3.BankWindow.bankWindowRootSelectedCarrierOwnership
#print axioms L3.BankWindow.bankWindowRootForeignCompleteOutside
#print axioms L3.BankWindow.bankWindowRootForeignCompleteFrame
#print axioms L3.BankWindow.bankWindowRootForeignWorkerOffPair
#print axioms L3.BankWindow.bankWindowRootForeignProtoPrefixAvoid
#print axioms L3.BankWindow.bankWindowRootForeignProtoStep
#print axioms L3.BankWindow.bankWindowRootForeignComparatorStep
#print axioms L3.BankWindow.bankWindowOverlapRootLaunchForeignPrefix
#print axioms L3.BankWindow.bankWindowOverlapRootReturnForeignPrefix
#print axioms L3.BankWindow.bankWindowOverlapRootExpiryForeignPrefix
#print axioms L3.BankWindow.bankWindowOverlapRootIssueForeignOrigin
#print axioms L3.BankWindow.bankWindowOverlapRootCompareIssueForeignOrigin
#print axioms L3.BankWindow.bankWindowOverlapRootWaitForeignIncrement
#print axioms L3.BankWindow.bankWindowOverlapRootWaitForeignComparison
#print axioms L3.BankWindow.bankWindowRootSourceRoles
#print axioms L3.BankWindow.bankWindowRootSelectedCarrierOwnership
#print axioms L3.BankWindow.bankWindowRootForeignCompleteOutside
#print axioms L3.BankWindow.bankWindowRootForeignCompleteFrame
#print axioms L3.BankWindow.bankWindowRootForeignWorkerOffPair
#print axioms L3.BankWindow.bankWindowRootForeignProtoPrefixAvoid
#print axioms L3.BankWindow.bankWindowRootForeignProtoStep
#print axioms L3.BankWindow.bankWindowRootForeignComparatorStep
#print axioms L3.BankWindow.bankWindowOverlapRootLaunchForeignPrefix
#print axioms L3.BankWindow.bankWindowOverlapRootReturnForeignPrefix
#print axioms L3.BankWindow.bankWindowOverlapRootExpiryForeignPrefix
#print axioms L3.BankWindow.bankWindowOverlapRootIssueForeignOrigin
#print axioms L3.BankWindow.bankWindowOverlapRootCompareIssueForeignOrigin
#print axioms L3.BankWindow.bankWindowOverlapRootWaitForeignIncrement
#print axioms L3.BankWindow.bankWindowOverlapRootWaitForeignComparison
#print axioms L3.BankWindow.bankWindowRootForeignOrphanOnSource
#print axioms L3.BankWindow.bankWindowRootResponderNoRootActivation
#print axioms L3.BankWindow.bankWindowOverlapChangedResponderOwnerFields
#print axioms L3.BankWindow.bankWindowOverlapRepairCompletedForeignFields
#print axioms L3.BankWindow.bankWindowOverlapIncomingStableOwnerFields
#print axioms L3.BankWindow.bankWindowOverlapIncomingBrokenOwnerFields
#print axioms L3.BankWindow.bankWindowRootForeignPhaseExcludesOnSource
#print axioms L3.BankWindow.bankWindowRootForeignCompareExactOnSource
#print axioms L3.BankWindow.bankWindowOverlapRepairCompletedForeignNoOriginWorker
#print axioms L3.BankWindow.bankWindowOverlapForeignPrefixCannotBreak
#print axioms L3.BankWindow.bankWindowOverlapRepairForeignOrphanStep
#print axioms L3.BankWindow.bankWindowOverlapRepairIncompleteForeignCwaitNoWorker
#print axioms L3.BankWindow.bankWindowOverlapRepairPendingRrKeeps
#print axioms L3.BankWindow.bankWindowOverlapRepairEarlierSiteFrame
#print axioms L3.BankWindow.bankWindowOverlapInheritedRootExcludesEmptyModes
#print axioms L3.BankWindow.bankWindowOverlapRepairExtendedProtoOld
#print axioms L3.BankWindow.bankWindowOverlapRepairExtendedProtoRrFront
#print axioms L3.BankWindow.bankWindowOverlapRepairExtendedProtoTailMode
#print axioms L3.BankWindow.bankWindowOverlapRepairExtendedProtoForeign
#print axioms L3.BankWindow.bankWindowOverlapRepairSourceComparisonBackward
#print axioms L3.BankWindow.bankWindowOverlapRepairComparatorBackward
#print axioms L3.BankWindow.bankWindowOverlapRepairForeignPhaseExcludes
#print axioms L3.BankWindow.bankWindowOverlapRepairIncompleteForeignNoComparator
#print axioms L3.BankWindow.bankWindowOverlapRepairForeignProtoStep
#print axioms L3.BankWindow.bankWindowOverlapRepairIncompleteForeignFieldBundle
#print axioms L3.BankWindow.bankWindowOverlapStablePackFrame
#print axioms L3.BankWindow.bankWindowOverlapStableProtoBackward
#print axioms L3.BankWindow.bankWindowOverlapStableOrphanOwnerBackward
#print axioms L3.BankWindow.bankWindowOverlapStableForeignProtoOffSegment
#print axioms L3.BankWindow.bankWindowOverlapStableForeignOrphanOffPair
#print axioms L3.BankWindow.bankWindowOverlapIncomingBrokenMultiwindowFields
#print axioms L3.BankWindow.bankWindowOverlapStableOrphanNextOld
#print axioms L3.BankWindow.bankWindowOverlapStableTopTaintedResponderImpossible
#print axioms L3.BankWindow.bankWindowOverlapStableResponderPredecessorRole
#print axioms L3.BankWindow.bankWindowOverlapStableOrphanPreviousOld
#print axioms L3.BankWindow.bankWindowOverlapStableForeignOrphanOnSource
#print axioms L3.BankWindow.bankWindowOverlapStableForeignOrphanOnResponder
#print axioms L3.BankWindow.bankWindowOverlapStableForeignOrphanStep
#print axioms L3.BankWindow.bankWindowOverlapForeignComparisonOffWindow
#print axioms L3.BankWindow.bankWindowOverlapIncomingWaitMultiwindowFields
#print axioms L3.BankWindow.bankWindowOverlapIncomingSourceNonzero
#print axioms L3.BankWindow.bankWindowOverlapIncomingZeroBankModes
#print axioms L3.BankWindow.bankWindowOverlapIncomingZeroPhysicalModes
#print axioms L3.BankWindow.bankWindowOverlapIncomingGrantOrArmedOwnerFields
#print axioms L3.BankWindow.bankWindowOverlapIncomingCstartControllerKeep
#print axioms L3.BankWindow.bankWindowOverlapIncomingCstartOwnerFields
#print axioms L3.BankWindow.bankWindowOverlapIncomingGenuineWorkerOffPair
#print axioms L3.BankWindow.bankWindowOverlapIncomingCurrentComparisonFields
#print axioms L3.BankWindow.bankWindowOverlapRootForeignProtoWithInterior
#print axioms L3.BankWindow.bankWindowOverlapRootForeignOrphanAll
#print axioms L3.BankWindow.bankWindowOverlapIncomingWaitingKeepsController
#print axioms L3.BankWindow.bankWindowOverlapIncomingResetWaitField
#print axioms L3.BankWindow.bankWindowOverlapIncomingWaitTaintedFields
#print axioms L3.BankWindow.bankWindowOverlapIncomingIncrementExactField
#print axioms L3.BankWindow.bankWindowOverlapIncomingCstartArmedExactField
#print axioms L3.BankWindow.bankWindowOverlapInteriorComparisonCollisionMemory
#print axioms L3.BankWindow.bankWindowOverlapInteriorComparisonCollisionNoWorker
#print axioms L3.BankWindow.bankWindowOverlapInteriorComparisonReturnMemory
#print axioms L3.BankWindow.bankWindowOverlapInteriorComparisonReturnWorkers
#print axioms L3.BankWindow.bankWindowOverlapInteriorComparisonAdvanceWorkers
#print axioms L3.BankWindow.bankWindowOverlapRootFields
#print axioms L3.BankWindow.bankWindowOverlapInteriorComparisonAdvancePhysical
#print axioms L3.BankWindow.bankWindowOverlapInteriorComparisonReturnPhysical
#print axioms L3.BankWindow.bankWindowOverlapComparatorPrefixExtension
#print axioms L3.BankWindow.bankWindowOverlapComparatorPrefixBitTransport
#print axioms L3.BankWindow.bankWindowOverlapComparatorBinaryBitTransport
#print axioms L3.BankWindow.bankWindowOverlapInteriorComparisonAdvanceSelected
#print axioms L3.BankWindow.bankWindowOverlapInteriorComparisonReturnSelected
#print axioms L3.BankWindow.bankWindowOverlapSelectedBitFrame
#print axioms L3.BankWindow.bankWindowOverlapInteriorComparisonAdvanceFlags
#print axioms L3.BankWindow.bankWindowOverlapOnlyTokenForward
#print axioms L3.BankWindow.bankWindowOverlapOnlyTokenBackward
#print axioms L3.BankWindow.bankWindowOverlapInteriorComparisonReturnFlags
#print axioms L3.BankWindow.bankWindowOverlapInteriorComparisonAdvanceCompareExact
#print axioms L3.BankWindow.bankWindowOverlapInteriorComparisonReturnCompareExact
#print axioms L3.BankWindow.bankWindowOverlapInteriorComparisonAdvanceCurrentFields
#print axioms L3.BankWindow.bankWindowOverlapInteriorComparisonReturnCurrentFields
#print axioms L3.BankWindow.bankWindowOverlapInteriorComparisonCollisionPhysical
#print axioms L3.BankWindow.bankWindowOverlapInteriorComparisonCollisionSelected
#print axioms L3.BankWindow.bankWindowOverlapOnlyTokenBothCleared
#print axioms L3.BankWindow.bankWindowOverlapInteriorComparisonCollisionOffPairFields
#print axioms L3.BankWindow.bankWindowOverlapOutsideCurrentPhaseFields
#print axioms L3.BankWindow.bankWindowOverlapOutsideGenuineWorkerOffPair
#print axioms L3.BankWindow.bankWindowOverlapOutsideOriginCurrentPhaseFields
#print axioms L3.BankWindow.bankWindowOverlapOutsideOriginPhaseExcludes
#print axioms L3.BankWindow.bankWindowOverlapOutsideTaintedOwnerFields
#print axioms L3.BankWindow.bankWindowOverlapOutsideArmedExactField
#print axioms L3.BankWindow.bankWindowOverlapOutsideIncrementExactField
#print axioms L3.BankWindow.bankWindowOverlapRootSourceForeignCurrentPhaseFields
#print axioms L3.BankWindow.bankWindowOverlapIncomingCurrentPhaseFields
#print axioms L3.BankWindow.bankWindowOverlapOutsideOriginPhasePackage
#print axioms L3.BankWindow.bankWindowOverlapOutsideProtoField
#print axioms L3.BankWindow.bankWindowOverlapCstartComparatorIssueCell
#print axioms L3.BankWindow.bankWindowOverlapRootCstartComparatorIssuePhysical
#print axioms L3.BankWindow.bankWindowOverlapRootCstartIssuedComparatorCore
#print axioms L3.BankWindow.bankWindowOverlapRootCstartIssuedOnlyToken
#print axioms L3.BankWindow.bankWindowOverlapRootCstartIssuedCurrentFields
#print axioms L3.BankWindow.bankWindowOverlapRootCstartIssuedComparatorExclusive
#print axioms L3.BankWindow.bankWindowOverlapRootCstartUniversalCurrentFields
#print axioms L3.BankWindow.bankWindowOverlapRepairCompleteResponderOutside
#print axioms L3.BankWindow.bankWindowOverlapRepairCompleteIncidentTop
#print axioms L3.BankWindow.bankWindowOverlapRepairCompleteTopTargetOutside
#print axioms L3.BankWindow.bankWindowOverlapRepairCompleteTopRaw
#print axioms L3.BankWindow.bankWindowOverlapRepairCompleteTopSourceReads
#print axioms L3.BankWindow.bankWindowOverlapRepairCompleteTopWindowReads
#print axioms L3.BankWindow.bankWindowOverlapRepairCompleteTopGenuineWorkerReads
#print axioms L3.BankWindow.bankWindowOverlapRepairCompleteTopRootClauses
#print axioms L3.BankWindow.bankWindowOverlapRepairCompleteIncidentRootClauses
#print axioms L3.BankWindow.bankWindowOverlapSourceOwnResetModeClauses
#print axioms L3.BankWindow.bankWindowOverlapSourceOwnRwaitModeClauses
#print axioms L3.BankWindow.bankWindowOverlapSourceOwnResetLaunch
#print axioms L3.BankWindow.bankWindowOverlapSourceOwnRwaitNonreturnExpiry
#print axioms L3.BankWindow.bankWindowOverlapSourceOwnRwaitBirthCertificate
#print axioms L3.BankWindow.bankWindowOverlapSourceOwnRwaitInheritedRlPhysical
#print axioms L3.BankWindow.bankWindowOverlapSourceActiveResetFields
#print axioms L3.BankWindow.bankWindowOverlapSourceActiveCollisionPhysical
#print axioms L3.BankWindow.bankWindowOverlapSourceActiveCollisionFields
#print axioms L3.BankWindow.bankWindowOverlapSourceActiveOuterDigitsClean
#print axioms L3.BankWindow.bankWindowOverlapSourceActiveIssuedWorkerExclusive
#print axioms L3.BankWindow.bankWindowOverlapSourceActiveFirstWeightSum
#print axioms L3.BankWindow.bankWindowOverlapSourceActiveOtherBits
#print axioms L3.BankWindow.bankWindowOverlapSourceActiveBitSetValue
#print axioms L3.BankWindow.bankWindowOverlapSourceActiveBitClearValue
#print axioms L3.BankWindow.bankWindowOverlapSourceActiveArmedCell
#print axioms L3.BankWindow.bankWindowOverlapSourceActiveArmedPhysical
#print axioms L3.BankWindow.bankWindowOverlapSourceActiveNoOriginWorker
#print axioms L3.BankWindow.bankWindowOverlapSourceActiveEmptyTokensClean
#print axioms L3.BankWindow.bankWindowOverlapSourceActiveArmedSetFields
#print axioms L3.BankWindow.bankWindowOverlapSourceActiveIncompleteProto
#print axioms L3.BankWindow.bankWindowOverlapSourceActiveGenuineComplete
#print axioms L3.BankWindow.bankWindowOverlapSourceActiveArmedSetGenuineFields
#print axioms L3.BankWindow.bankWindowOverlapSourceActiveInheritedOldClean
#print axioms L3.BankWindow.bankWindowOverlapSourceActiveNoOwnGenuineFromClean
#print axioms L3.BankWindow.bankWindowOverlapSourceActiveCleanOwnerFields
#print axioms L3.BankWindow.bankWindowOverlapSourceActiveInheritedCstartMemory
#print axioms L3.BankWindow.bankWindowOverlapSourceCountingResetOwnFields
#print axioms L3.BankWindow.bankWindowOverlapSourceCountingCwaitClOneOwnFields
#print axioms L3.BankWindow.bankWindowOverlapSourceCountingTimedOutPair
#print axioms L3.BankWindow.bankWindowOverlapSourceCountingTimedOutOwnFields
#print axioms L3.BankWindow.bankWindowOverlapSourceCountingIwaitExpiredOwnFields
#print axioms L3.BankWindow.bankWindowOverlapSourceCountingCwaitExpiredOwnFields
#print axioms L3.BankWindow.bankWindowOverlapSourceCountingNonexpiredPair
#print axioms L3.BankWindow.bankWindowOverlapSourceCountingNonexpiredReal
#print axioms L3.BankWindow.bankWindowOverlapSourceCountingCstartOwnFieldsFromReturn
#print axioms L3.BankWindow.bankWindowOverlapSourceCountingCwaitClZeroMismatch
#print axioms L3.BankWindow.bankWindowOverlapTopGhostStablePairRaw
#print axioms L3.BankWindow.bankWindowOverlapTopGhostStableTaintPreimage
#print axioms L3.BankWindow.bankWindowOverlapTopGhostStableSourceReads
#print axioms L3.BankWindow.bankWindowOverlapTopGhostStableWindowReads
#print axioms L3.BankWindow.bankWindowOverlapTopGhostStableGenuineWorkerReads
#print axioms L3.BankWindow.bankWindowOverlapTopGhostStableNonIrRootClauses
#print axioms L3.BankWindow.bankWindowOverlapSourceCountingIwaitAlReturnFields
#print axioms L3.BankWindow.bankWindowOverlapSourceCountingCwaitClZeroReturnFields
#print axioms L3.BankWindow.bankWindowOverlapSourceCountingIwaitNoPostComparator
#print axioms L3.BankWindow.bankWindowOverlapSourceCountingIwaitAlEndpointReads
#print axioms L3.BankWindow.bankWindowOverlapSourceCountingIwaitAlDigitCredit
#print axioms L3.BankWindow.bankWindowOverlapSourceCountingIwaitAlOwnFields
#print axioms L3.BankWindow.bankWindowOverlapTopGhostStableIrErasure
#print axioms L3.BankWindow.bankWindowOverlapTopGhostStableIrRootClauses
#print axioms L3.BankWindow.bankWindowOverlapTopGhostStableRootClauses
#print axioms L3.BankWindow.bankWindowOverlapSourceActiveCstartIssueFields
#print axioms L3.BankWindow.bankWindowOverlapSourceActiveCstartMatchFields
#print axioms L3.BankWindow.bankWindowOverlapSourceActiveCstartMatchGenuineFields
#print axioms L3.BankWindow.bankWindowOverlapSourceActiveCstartMismatchFields
#print axioms L3.BankWindow.bankWindowOverlapSourceActiveCstartMismatchGenuineFields
#print axioms L3.BankWindow.bankWindowOverlapSourceActiveArmedIssueFields
#print axioms L3.BankWindow.bankWindowOverlapSourceActiveArmedIssueGenuineFields
#print axioms L3.BankWindow.bankWindowOverlapSourceActiveInheritedArmedMemory
#print axioms L3.BankWindow.bankWindowOverlapSourceLongWaitCellReads
#print axioms L3.BankWindow.bankWindowOverlapSourceLongWaitPhysicalReads
#print axioms L3.BankWindow.bankWindowOverlapSourceLongWaitWindowReads
#print axioms L3.BankWindow.bankWindowOverlapSourceLongWaitGenuineReads
#print axioms L3.BankWindow.bankWindowOverlapSourceLongWaitReadTransport
#print axioms L3.BankWindow.bankWindowOverlapSourceLongWaitOwnClauses
#print axioms L3.BankWindow.bankWindowOverlapSourceLongWaitCompleteOwnClauses
#print axioms L3.BankWindow.bankWindowOverlapSourceLongWaitIncompleteOwnClauses
