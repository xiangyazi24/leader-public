import Leader.L3.Bank.WindowOverlap

/-!
R11 group 13, items 14 (PFX) and 15 (ORPH), interior cases: the stable-PACK
selected-source orphan case at the tainted digit, the PFX stable aligned
interior, two RR-front witness branches and the remote interior
physical/ghost reads.  Consumer: the group-13 overlap assembly of
bankWindowExactStep (R11).
-/

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open Classical


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

theorem bankWindowOverlapProtoInteriorOldRead
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n) (k limit : Nat)
    (hsource : e = Counter.site ring root k)
    (hk : 1 ≤ k) (hinterior : k < limit)
    (hstable :
      packNext
        ((bankWindowOverlapBefore ring seed pre).1 e).pack.val
        ((bankWindowOverlapBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val)
    (hproto : BankWindowProtoRun ring
      (bankWindowOverlapAfter ring seed pre e) root limit) :
    BankWindowProtoRun ring (bankWindowOverlapBefore ring seed pre)
      root limit ∧
    ((bankWindowOverlapAfter ring seed pre e).1 root =
        (bankWindowOverlapBefore ring seed pre).1 root ∧
      (bankWindowOverlapAfter ring seed pre e).2.sites root =
        (bankWindowOverlapBefore ring seed pre).2.sites root) ∧
    (((bankWindowOverlapBefore ring seed pre).1 e).pack.val = k ∧
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val = k + 1) ∧
    bankWindowReadPackPrefix ring
      (bankWindowOverlapBefore ring seed pre)
      (bankWindowOverlapAfter ring seed pre e) root (limit + 1) := by
  have hlimit : limit < (compileAdvice (ceilLogTwo n)).b := hproto.1
  have hnextSite :
      ring.rightNeighbor e = Counter.site ring root (k + 1) := by
    rw [hsource]
    rfl
  have hpack :
      bankWindowReadPackPrefix ring
        (bankWindowOverlapBefore ring seed pre)
        (bankWindowOverlapAfter ring seed pre e)
        root (limit + 1) := by
    intro t ht
    by_cases htarget : t = k + 1
    · rw [htarget, ← hnextSite]
      exact (bankWindowExactResponderPack ring
        (bankWindowOverlapBefore ring seed pre) e
        (clockNeighborDifferent ring (by omega : 2 ≤ n) e)).trans
          hstable
    · have havoid :
          Counter.site ring root t ≠ ring.rightNeighbor e := by
        rw [hnextSite]
        by_cases hless : t < k + 1
        · exact bankWindowIncidenceSiteDistinct ring hbank root
            t (k + 1) hless (by omega)
        · exact (bankWindowIncidenceSiteDistinct ring hbank root
            (k + 1) t (by omega) (by omega)).symm
      exact bankWindowClosureRepairNonresponderPackFixed
        ring (by omega : 2 ≤ n)
        (bankWindowOverlapBefore ring seed pre) e
        (Counter.site ring root t) havoid
  have holdProto : BankWindowProtoRun ring
      (bankWindowOverlapBefore ring seed pre) root limit := by
    refine ⟨hproto.1, ?_, ?_⟩
    · intro t ht
      exact (hpack t (by omega)).symm.trans (hproto.2.1 t ht)
    · intro hcorrect
      exact hproto.2.2 ((hpack (limit + 1)
        (Nat.le_refl _)).trans hcorrect)
  have hrootSource : root ≠ e := by
    rw [hsource]
    have hd := bankWindowIncidenceSiteDistinct
      ring hbank root 0 k (by omega) (by omega)
    change root ≠ Counter.site ring root k at hd
    exact hd
  have hrootTarget : root ≠ ring.rightNeighbor e := by
    rw [hnextSite]
    have hd := bankWindowIncidenceSiteDistinct
      ring hbank root 0 (k + 1) (by omega) (by omega)
    change root ≠ Counter.site ring root (k + 1) at hd
    exact hd
  have hrootFrame := bankWindowExactOffPairFrame ring
    (bankWindowOverlapBefore ring seed pre) e root
    hrootSource hrootTarget
  have hpostSource :
      ((bankWindowOverlapAfter ring seed pre e).1 e).pack.val = k := by
    have hs := hproto.2.1 k (by omega)
    rw [← hsource] at hs
    exact hs
  have hsourceFixed := bankWindowClosureRepairNonresponderPackFixed
    ring (by omega : 2 ≤ n)
    (bankWindowOverlapBefore ring seed pre) e e
    (clockNeighborDifferent ring (by omega : 2 ≤ n) e).symm
  have holdSource :
      ((bankWindowOverlapBefore ring seed pre).1 e).pack.val = k :=
    hsourceFixed.symm.trans hpostSource
  have hpostTarget :
      ((bankWindowOverlapAfter ring seed pre e).1
        (ring.rightNeighbor e)).pack.val = k + 1 := by
    have ht := hproto.2.1 (k + 1) (by omega)
    rw [← hnextSite] at ht
    exact ht
  have holdTarget :
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val = k + 1 :=
    hstable.symm.trans
      ((bankWindowExactResponderPack ring
        (bankWindowOverlapBefore ring seed pre) e
        (clockNeighborDifferent ring (by omega : 2 ≤ n) e)).symm.trans
          hpostTarget)
  exact ⟨holdProto, hrootFrame, ⟨holdSource, holdTarget⟩, hpack⟩

/-- The entire selected source/target is outside every strictly
earlier digit of a stable interior proto segment.  This is an exact
full physical/ghost same-word frame, even without complete PACK.
Consumer: PFX's pending front strictly before the selected edge. -/
theorem bankWindowOverlapProtoInteriorEarlierFrame
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n)
    (e root : Fin n) (k : Nat)
    (hsource : e = Counter.site ring root k)
    (hbound : k ≤ (compileAdvice (ceilLogTwo n)).b)
    (t : Nat) (ht : t < k) :
    (renewalBankNext ring r e).1 (Counter.site ring root t) =
      r.1 (Counter.site ring root t) ∧
    (renewalBankNext ring r e).2.sites (Counter.site ring root t) =
      r.2.sites (Counter.site ring root t) := by
  have hsourceNe :
      Counter.site ring root t ≠ e := by
    rw [hsource]
    exact bankWindowIncidenceSiteDistinct ring hbank root
      t k ht (by omega)
  have htargetNe :
      Counter.site ring root t ≠ ring.rightNeighbor e := by
    rw [hsource]
    change Counter.site ring root t ≠
      Counter.site ring root (k + 1)
    exact bankWindowIncidenceSiteDistinct ring hbank root
      t (k + 1) (by omega) (by omega)
  exact bankWindowExactOffPairFrame ring r e
    (Counter.site ring root t) hsourceNe htargetNe

/-- PFX group-13, three of the four POST proto clauses on a stable
aligned interior edge, with no extra invariant at the successor.
OLD J.proto and the actual six-way nonroot worker preimage jointly
exclude new taint in either guarded mode. In particular, a foreign
inherited IR/CR token cannot mint a genuinely originated worker in
this aligned proto segment. Consumer: bankWindowExactOverlapStep.
The missing fourth clause is the pending RR front, not any of these
three assertions. -/
theorem bankWindowOverlapProtoInteriorSafeFields
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n) (k limit : Nat)
    (hJ : BankWindowExact ring
      (bankWindowOverlapBefore ring seed pre))
    (hsource : e = Counter.site ring root k)
    (hk : 1 ≤ k) (hinterior : k < limit)
    (hstable :
      packNext
        ((bankWindowOverlapBefore ring seed pre).1 e).pack.val
        ((bankWindowOverlapBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val)
    (hproto : BankWindowProtoRun ring
      (bankWindowOverlapAfter ring seed pre e) root limit) :
    (∀ p o,
      ((bankWindowOverlapAfter ring seed pre e).2.sites root).controller =
        .active p → p.origin = some o → False) ∧
    (BankWindowInheritedController
      (bankWindowOverlapAfter ring seed pre e) root →
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        j.val + 1 ≤ limit →
        ¬ BankWindowTainted
          (bankWindowOverlapAfter ring seed pre e)
          (Counter.site ring root (j.val + 1))) ∧
    (((bankWindowOverlapAfter ring seed pre e).1 root).mode ≠ .RESET →
      ((bankWindowOverlapAfter ring seed pre e).1 root).mode ≠ .RWAIT →
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        j.val + 1 ≤ limit →
        ¬ BankWindowTainted
          (bankWindowOverlapAfter ring seed pre e)
          (Counter.site ring root (j.val + 1))) := by
  obtain ⟨holdProto, hrootFrame, hroles, _⟩ :=
    bankWindowOverlapProtoInteriorOldRead
      ring hn hbank seed pre e root k limit
      hsource hk hinterior hstable hproto
  have hOld := hJ.proto root limit holdProto
  have hmode := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.mode)
    hrootFrame.1
  have hcontroller := congrArg
    (fun a : RenewalBankSite n => a.controller) hrootFrame.2
  have hnonroot :
      ((bankWindowOverlapBefore ring seed pre).1 e).pack.val ≠ 0 := by
    rw [hroles.1]
    omega
  have hnextSite :
      ring.rightNeighbor e = Counter.site ring root (k + 1) := by
    rw [hsource]
    rfl
  have htransfer :
      (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        j.val + 1 ≤ limit →
        ¬ BankWindowTainted (bankWindowOverlapBefore ring seed pre)
          (Counter.site ring root (j.val + 1))) →
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        j.val + 1 ≤ limit →
        ¬ BankWindowTainted (bankWindowOverlapAfter ring seed pre e)
          (Counter.site ring root (j.val + 1)) := by
    intro hclean j hj hpostTaint
    have hindexSource :
        k - 1 < (compileAdvice (ceilLogTwo n)).b := by
      have hl := hproto.1
      omega
    have hsourceBound :
        (⟨k - 1, hindexSource⟩ :
          Fin (compileAdvice (ceilLogTwo n)).b).val + 1 ≤ limit := by
      change k - 1 + 1 ≤ limit
      omega
    have hcleanSource :
        ¬ BankWindowTainted
          (bankWindowOverlapBefore ring seed pre) e := by
      have hc := hclean
        (⟨k - 1, hindexSource⟩ :
          Fin (compileAdvice (ceilLogTwo n)).b) hsourceBound
      change ¬ BankWindowTainted
        (bankWindowOverlapBefore ring seed pre)
        (Counter.site ring root (k - 1 + 1)) at hc
      have heq : k - 1 + 1 = k := by omega
      rw [heq, ← hsource] at hc
      exact hc
    have hindexTarget :
        k < (compileAdvice (ceilLogTwo n)).b := by
      have hl := hproto.1
      omega
    have htargetBound :
        (⟨k, hindexTarget⟩ :
          Fin (compileAdvice (ceilLogTwo n)).b).val + 1 ≤ limit := by
      change k + 1 ≤ limit
      omega
    have hcleanTarget :
        ¬ BankWindowTainted
          (bankWindowOverlapBefore ring seed pre)
          (ring.rightNeighbor e) := by
      have hc := hclean
        (⟨k, hindexTarget⟩ :
          Fin (compileAdvice (ceilLogTwo n)).b) htargetBound
      change ¬ BankWindowTainted
        (bankWindowOverlapBefore ring seed pre)
        (Counter.site ring root (k + 1)) at hc
      rw [← hnextSite] at hc
      exact hc
    by_cases hsourceHit :
        Counter.site ring root (j.val + 1) = e
    · have ht :
          BankWindowTainted (bankWindowOverlapAfter ring seed pre e)
            e := by
        rw [hsourceHit] at hpostTaint
        exact hpostTaint
      rcases bankWindowOverlapNonrootPairTaintPreimage
        ring (by omega : 2 ≤ n)
        (bankWindowOverlapBefore ring seed pre)
        e e hnonroot (Or.inl rfl) ht with hs | hd
      · exact hcleanSource hs
      · exact hcleanTarget hd
    · by_cases htargetHit :
          Counter.site ring root (j.val + 1) =
            ring.rightNeighbor e
      · have ht :
            BankWindowTainted (bankWindowOverlapAfter ring seed pre e)
              (ring.rightNeighbor e) := by
          rw [htargetHit] at hpostTaint
          exact hpostTaint
        rcases bankWindowOverlapNonrootPairTaintPreimage
          ring (by omega : 2 ≤ n)
          (bankWindowOverlapBefore ring seed pre)
          e (ring.rightNeighbor e) hnonroot
          (Or.inr rfl) ht with hs | hd
        · exact hcleanSource hs
        · exact hcleanTarget hd
      · have hf := (bankWindowExactOffPairFrame ring
          (bankWindowOverlapBefore ring seed pre) e
          (Counter.site ring root (j.val + 1))
          hsourceHit htargetHit).2
        have hw := congrArg
          (fun s : RenewalBankSite n => s.worker) hf
        have holdTaint :
            BankWindowTainted (bankWindowOverlapBefore ring seed pre)
              (Counter.site ring root (j.val + 1)) := by
          unfold BankWindowTainted at hpostTaint ⊢
          rw [hw] at hpostTaint
          exact hpostTaint
        exact (hclean j hj) holdTaint
  refine ⟨?_, ?_, ?_⟩
  · intro p o hactive horigin
    rw [hcontroller] at hactive
    exact hOld.1 p o hactive horigin
  · intro hinherited
    have holdInherited : BankWindowInheritedController
        (bankWindowOverlapBefore ring seed pre) root := by
      unfold BankWindowInheritedController at hinherited ⊢
      rw [hcontroller] at hinherited
      exact hinherited
    exact htransfer (hOld.2.1 holdInherited)
  · intro hnotReset hnotWait
    have hnotOldReset :
        ((bankWindowOverlapBefore ring seed pre).1 root).mode ≠
          .RESET := by
      intro h
      exact hnotReset (hmode.trans h)
    have hnotOldWait :
        ((bankWindowOverlapBefore ring seed pre).1 root).mode ≠
          .RWAIT := by
      intro h
      exact hnotWait (hmode.trans h)
    exact htransfer (hOld.2.2.2 hnotOldReset hnotOldWait)

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- PFX group-13: a genuine OLD pending RR witness strictly before
the selected interior source keeps its token, zero-bit prefix,
pending ghost, and every earlier-E token. Unlike a read-mask sketch,
this transports the exact witness used by J.proto.
Consumer: the early-front branch of bankWindowExactOverlapStep. -/
theorem bankWindowOverlapProtoFrontBefore
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n) (k limit : Nat)
    (hsource : e = Counter.site ring root k)
    (hkbound : k ≤ (compileAdvice (ceilLogTwo n)).b)
    (front : Fin (compileAdvice (ceilLogTwo n)).b)
    (rho : RenewalBankReceipt n)
    (hfrontBound : front.val + 1 ≤ limit)
    (hbefore : front.val + 1 < k)
    (hworker :
      ((bankWindowOverlapBefore ring seed pre).2.sites
        (Counter.site ring root (front.val + 1))).worker =
          .pending rho)
    (htok :
      ((bankWindowOverlapBefore ring seed pre).1
        (Counter.site ring root (front.val + 1))).tok = .RR)
    (hzero : bankWindowZeroPrefix ring
      (bankWindowOverlapBefore ring seed pre)
      root (front.val + 1))
    (hearlier :
      ∀ t : Fin (compileAdvice (ceilLogTwo n)).b,
        t.val < front.val →
        ((bankWindowOverlapBefore ring seed pre).1
          (Counter.site ring root (t.val + 1))).tok = .E) :
    ∃ j : Fin (compileAdvice (ceilLogTwo n)).b,
      j.val + 1 ≤ limit ∧
      ∃ sigma : RenewalBankReceipt n,
        ((bankWindowOverlapAfter ring seed pre e).2.sites
          (Counter.site ring root (j.val + 1))).worker =
            .pending sigma ∧
        ((bankWindowOverlapAfter ring seed pre e).1
          (Counter.site ring root (j.val + 1))).tok = .RR ∧
        bankWindowZeroPrefix ring
          (bankWindowOverlapAfter ring seed pre e)
          root (j.val + 1) ∧
        (∀ t : Fin (compileAdvice (ceilLogTwo n)).b,
          t.val < j.val →
          ((bankWindowOverlapAfter ring seed pre e).1
            (Counter.site ring root (t.val + 1))).tok = .E) := by
  refine ⟨front, hfrontBound, rho, ?_, ?_, ?_, ?_⟩
  · have hf := (bankWindowOverlapProtoInteriorEarlierFrame
      ring hbank (bankWindowOverlapBefore ring seed pre)
      e root k hsource hkbound (front.val + 1) hbefore).2
    have hw := congrArg
      (fun s : RenewalBankSite n => s.worker) hf
    exact hw.trans hworker
  · have hf := (bankWindowOverlapProtoInteriorEarlierFrame
      ring hbank (bankWindowOverlapBefore ring seed pre)
      e root k hsource hkbound (front.val + 1) hbefore).1
    have ht := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok) hf
    exact ht.trans htok
  · intro t ht
    have hlt : t.val + 1 < k := by
      change t.val + 1 ≤ front.val + 1 at ht
      omega
    have hf := (bankWindowOverlapProtoInteriorEarlierFrame
      ring hbank (bankWindowOverlapBefore ring seed pre)
      e root k hsource hkbound (t.val + 1) hlt).1
    have hb := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.bit) hf
    exact hb.trans (hzero t ht)
  · intro t ht
    have hlt : t.val + 1 < k := by omega
    have hf := (bankWindowOverlapProtoInteriorEarlierFrame
      ring hbank (bankWindowOverlapBefore ring seed pre)
      e root k hsource hkbound (t.val + 1) hlt).1
    have htoken := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok) hf
    exact htoken.trans (hearlier t ht)

/-- PFX group-13: when the OLD RR witness itself occupies the
selected source D_root(k), its first-match forward step produces
a valid new pending RR witness at D_root(k+1). All earlier E and
zero-bit reads are transferred, including the overwritten source
and responder fields. This is the precise J.proto front-at-source
branch and uses the installed physical/ghost RR-forward theorem.
Consumer: bankWindowExactOverlapStep's PFX case decomposition. -/
theorem bankWindowOverlapProtoFrontMoves
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n) (k limit : Nat)
    (hsource : e = Counter.site ring root k)
    (hk : 1 ≤ k) (hinterior : k < limit)
    (hstable :
      packNext
        ((bankWindowOverlapBefore ring seed pre).1 e).pack.val
        ((bankWindowOverlapBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val)
    (hproto : BankWindowProtoRun ring
      (bankWindowOverlapAfter ring seed pre e) root limit)
    (rho : RenewalBankReceipt n)
    (hworker :
      ((bankWindowOverlapBefore ring seed pre).2.sites e).worker =
        .pending rho)
    (htok : ((bankWindowOverlapBefore ring seed pre).1 e).tok = .RR)
    (hzero : bankWindowZeroPrefix ring
      (bankWindowOverlapBefore ring seed pre) root k)
    (hearlier :
      ∀ t : Fin (compileAdvice (ceilLogTwo n)).b,
        t.val + 1 < k →
        ((bankWindowOverlapBefore ring seed pre).1
          (Counter.site ring root (t.val + 1))).tok = .E) :
    ∃ j : Fin (compileAdvice (ceilLogTwo n)).b,
      j.val + 1 ≤ limit ∧
      ∃ sigma : RenewalBankReceipt n,
        ((bankWindowOverlapAfter ring seed pre e).2.sites
          (Counter.site ring root (j.val + 1))).worker =
            .pending sigma ∧
        ((bankWindowOverlapAfter ring seed pre e).1
          (Counter.site ring root (j.val + 1))).tok = .RR ∧
        bankWindowZeroPrefix ring
          (bankWindowOverlapAfter ring seed pre e)
          root (j.val + 1) ∧
        (∀ t : Fin (compileAdvice (ceilLogTwo n)).b,
          t.val < j.val →
          ((bankWindowOverlapAfter ring seed pre e).1
            (Counter.site ring root (t.val + 1))).tok = .E) := by
  have hlimit : limit < (compileAdvice (ceilLogTwo n)).b := hproto.1
  obtain ⟨_, _, hroles, _⟩ :=
    bankWindowOverlapProtoInteriorOldRead
      ring hn hbank seed pre e root k limit
      hsource hk hinterior hstable hproto
  have hroleNext :
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val =
      ((bankWindowOverlapBefore ring seed pre).1 e).pack.val + 1 := by
    rw [hroles.1, hroles.2]
  have hindexSource :
      k - 1 < (compileAdvice (ceilLogTwo n)).b := by omega
  have hsourceBound :
      (⟨k - 1, hindexSource⟩ :
        Fin (compileAdvice (ceilLogTwo n)).b).val + 1 ≤ k := by
    change k - 1 + 1 ≤ k
    omega
  have hsourceBit :
      ((bankWindowOverlapBefore ring seed pre).1 e).bit = false := by
    have hb := hzero
      (⟨k - 1, hindexSource⟩ :
        Fin (compileAdvice (ceilLogTwo n)).b) hsourceBound
    change ((bankWindowOverlapBefore ring seed pre).1
      (Counter.site ring root (k - 1 + 1))).bit = false at hb
    have hkeq : k - 1 + 1 = k := by omega
    rw [hkeq, ← hsource] at hb
    exact hb
  have hstep := bankWindowOverlapProtoRRForwardFields ring
    hn hbank seed pre e rho
    (by rw [hroles.1]; exact hk)
    (by rw [hroles.1]; omega)
    hroleNext htok hsourceBit hworker
  have hnextSite :
      ring.rightNeighbor e = Counter.site ring root (k + 1) := by
    rw [hsource]
    rfl
  have hkIndex : k < (compileAdvice (ceilLogTwo n)).b := by omega
  have hnewFrontBound :
      (⟨k, hkIndex⟩ :
        Fin (compileAdvice (ceilLogTwo n)).b).val + 1 ≤ limit := by
    change k + 1 ≤ limit
    omega
  refine ⟨(⟨k, hkIndex⟩ :
    Fin (compileAdvice (ceilLogTwo n)).b),
    hnewFrontBound, rho, ?_, ?_, ?_, ?_⟩
  · rw [← hnextSite]
    exact hstep.2.2.2.2
  · rw [← hnextSite]
    exact hstep.2.2.1
  · intro t ht
    have hle : t.val + 1 ≤ k + 1 := by
      change t.val + 1 ≤ k + 1 at ht
      exact ht
    by_cases htarget : t.val + 1 = k + 1
    · rw [htarget, ← hnextSite]
      exact hstep.2.2.2.1
    · by_cases hselected : t.val + 1 = k
      · rw [hselected, ← hsource]
        exact hstep.2.1
      · have hbefore : t.val + 1 < k := by omega
        have hf := (bankWindowOverlapProtoInteriorEarlierFrame
          ring hbank (bankWindowOverlapBefore ring seed pre)
          e root k hsource (by omega) (t.val + 1) hbefore).1
        have hb := congrArg
          (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.bit) hf
        exact hb.trans (hzero t (by omega))
  · intro t ht
    have hle : t.val < k := ht
    by_cases hselected : t.val + 1 = k
    · rw [hselected, ← hsource]
      exact hstep.1
    · have hbefore : t.val + 1 < k := by omega
      have hf := (bankWindowOverlapProtoInteriorEarlierFrame
        ring hbank (bankWindowOverlapBefore ring seed pre)
        e root k hsource (by omega) (t.val + 1) hbefore).1
      have htokFrame := congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok) hf
      exact htokFrame.trans (hearlier t hbefore)

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock

set_option autoImplicit false
set_option Elab.async false

/-- PFX group-13: any digit other than the selected aligned source
and responder has an identical OLD/POST physical agent and ghost
site. This uses the BANK spatial cutoff and allows a front after
the selected edge, including positions in an incomplete window.
Consumer: the remaining at-responder and after-responder RR-front
branches of bankWindowExactOverlapStep. -/
theorem bankWindowOverlapProtoInteriorRemoteFrame
    {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n) (k t : Nat)
    (hsource : e = Counter.site ring root k)
    (hkbound : k ≤ (compileAdvice (ceilLogTwo n)).b)
    (htbound : t ≤ (compileAdvice (ceilLogTwo n)).b + 1)
    (hneSource : t ≠ k) (hneTarget : t ≠ k + 1) :
    (bankWindowOverlapAfter ring seed pre e).1
        (Counter.site ring root t) =
      (bankWindowOverlapBefore ring seed pre).1
        (Counter.site ring root t) ∧
    (bankWindowOverlapAfter ring seed pre e).2.sites
        (Counter.site ring root t) =
      (bankWindowOverlapBefore ring seed pre).2.sites
        (Counter.site ring root t) := by
  have hsourceAvoid :
      Counter.site ring root t ≠ e := by
    rw [hsource]
    by_cases hlt : t < k
    · exact bankWindowIncidenceSiteDistinct ring hbank root
        t k hlt (by omega)
    · exact (bankWindowIncidenceSiteDistinct ring hbank root
        k t (by omega) htbound).symm
  have htargetAvoid :
      Counter.site ring root t ≠ ring.rightNeighbor e := by
    rw [hsource]
    change Counter.site ring root t ≠
      Counter.site ring root (k + 1)
    by_cases hlt : t < k + 1
    · exact bankWindowIncidenceSiteDistinct ring hbank root
        t (k + 1) hlt (by omega)
    · exact (bankWindowIncidenceSiteDistinct ring hbank root
        (k + 1) t (by omega) htbound).symm
  exact bankWindowExactOffPairFrame ring
    (bankWindowOverlapBefore ring seed pre) e
    (Counter.site ring root t)
    hsourceAvoid htargetAvoid

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock

set_option autoImplicit false

/-- ORPH stable-source row: the actual PACK update fixes the
OLD responder role, without asking omega to see a site offset.
Consumer: bankWindowOverlapOrphanStableSource. -/
theorem bankWindowOverlapStableInteriorResponderPack
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n) (j : Nat)
    (hinside : j + 1 < (compileAdvice (ceilLogTwo n)).b)
    (hsource : (r.1 e).pack.val = j + 1)
    (hstable :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      (r.1 (ring.rightNeighbor e)).pack.val) :
    (r.1 (ring.rightNeighbor e)).pack.val = j + 2 := by
  have hnext :
      packNext (j + 1)
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b = j + 2 := by
    simp [packNext, hinside]
  have hactual :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b = j + 2 := by
    rw [hsource]
    exact hnext
  exact hstable.symm.trans hactual

/-- ORPH top-source: a stable BANK top edge with an OLD tainted
responder would force a worker to inhabit spacer role b+1.
The real-run in-band invariant rules this out.
Consumer: bankWindowOverlapOrphanStableSource. -/
theorem bankWindowOverlapTopRejectsTaintedResponder
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (htop :
      ((bankWindowOverlapBefore ring seed pre).1 e).pack.val =
        (compileAdvice (ceilLogTwo n)).b)
    (hstable :
      packNext
        ((bankWindowOverlapBefore ring seed pre).1 e).pack.val
        ((bankWindowOverlapBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val)
    (htainted : BankWindowTainted
      (bankWindowOverlapBefore ring seed pre)
      (ring.rightNeighbor e)) : False := by
  have hband := bankWindowOverlapReachableTaintedInBand
    ring hn hbank seed pre (ring.rightNeighbor e) htainted
  have hnonzero :
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val ≠ 0 :=
    Nat.ne_of_gt hband.1
  have hnext :
      packNext (compileAdvice (ceilLogTwo n)).b
        ((bankWindowOverlapBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      (compileAdvice (ceilLogTwo n)).b + 1 := by
    simp [packNext, hnonzero]
  have hstableTop :
      packNext (compileAdvice (ceilLogTwo n)).b
        ((bankWindowOverlapBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val := by
    have hh := hstable
    rw [htop] at hh
    exact hh
  have hwrong :
      (compileAdvice (ceilLogTwo n)).b + 1 =
        ((bankWindowOverlapBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val :=
    hnext.symm.trans hstableTop
  have hupper :
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val ≤
      (compileAdvice (ceilLogTwo n)).b := hband.2
  omega

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open Classical

set_option autoImplicit false

/-- Group-13 ORPH: complete stable-PACK selected-source case at
the named tainted digit, including RL/AL/CL backward transport
from the responder. The real pair preimage gives an OLD tainted
source or responder. The source case uses OLD J.orphan at j;
the responder case uses OLD J.orphan at the next digit when
j+2 <= b. At the top, an OLD responder carrying a tainted
worker would lie at PACK 0 or b+1, contradicting the real-run
tainted-in-band certificate.

Consumer: bankWindowExactOverlapStep, ORPH stable-source row.
No POST J premise, no invented no-foreign-worker assumption. -/
theorem bankWindowOverlapOrphanStableSource
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (hJ : BankWindowExact ring
      (bankWindowOverlapBefore ring seed pre))
    (hsource : e = Counter.site ring root (j.val + 1))
    (hstable :
      packNext
        ((bankWindowOverlapBefore ring seed pre).1 e).pack.val
        ((bankWindowOverlapBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val)
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
  have hnextSite :
      ring.rightNeighbor e = Counter.site ring root (j.val + 2) := by
    rw [hsource]
    rfl
  have hne : e ≠ ring.rightNeighbor e :=
    (clockNeighborDifferent ring (by omega : 2 ≤ n) e).symm
  have hfixed := bankWindowClosureRepairNonresponderPackFixed
    ring (by omega : 2 ≤ n)
    (bankWindowOverlapBefore ring seed pre) e e hne
  have hpostRole :
      ((bankWindowOverlapAfter ring seed pre e).1 e).pack.val =
        j.val + 1 := by
    have hpostAtSite := howner.2.1
    rw [← hsource] at hpostAtSite
    exact hpostAtSite
  have holdRole :
      ((bankWindowOverlapBefore ring seed pre).1 e).pack.val =
        j.val + 1 :=
    hfixed.symm.trans hpostRole
  have hnonroot :
      ((bankWindowOverlapBefore ring seed pre).1 e).pack.val ≠ 0 := by
    rw [holdRole]
    exact Nat.succ_ne_zero j.val
  have hrootSource : root ≠ e := by
    rw [hsource]
    have hd := bankWindowIncidenceSiteDistinct
      ring hbank root 0 (j.val + 1) (by omega) (by omega)
    change root ≠ Counter.site ring root (j.val + 1) at hd
    exact hd
  have hrootTarget : root ≠ ring.rightNeighbor e := by
    rw [hnextSite]
    have hd := bankWindowIncidenceSiteDistinct
      ring hbank root 0 (j.val + 2) (by omega) (by omega)
    change root ≠ Counter.site ring root (j.val + 2) at hd
    exact hd
  have havoid :
      ∀ k : Nat, k ≤ j.val + 1 →
        Counter.site ring root k ≠ ring.rightNeighbor e := by
    intro k hk
    rw [hnextSite]
    exact bankWindowIncidenceSiteDistinct
      ring hbank root k (j.val + 2) (by omega) (by omega)
  have holdOwner : BankWindowOrphanOwner
      ring (bankWindowOverlapBefore ring seed pre) root j :=
    (bankWindowClosureRepairOrphanReadSetFrame
      ring (by omega : 2 ≤ n)
      (bankWindowOverlapBefore ring seed pre) e root j havoid).mp
        howner
  have hframe := bankWindowExactOffPairFrame ring
    (bankWindowOverlapBefore ring seed pre) e root
    hrootSource hrootTarget
  have hmode := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.mode)
    hframe.1
  have hcontroller := congrArg
    (fun a : RenewalBankSite n => a.controller) hframe.2
  have hlift :
      ((bankWindowOverlapBefore ring seed pre).1 root).mode = .RESET ∨
      (((bankWindowOverlapBefore ring seed pre).1 root).mode = .RWAIT ∧
        ((bankWindowOverlapBefore ring seed pre).2.sites root).controller =
          .waiting []) →
      ((bankWindowOverlapAfter ring seed pre e).1 root).mode = .RESET ∨
      (((bankWindowOverlapAfter ring seed pre e).1 root).mode = .RWAIT ∧
        ((bankWindowOverlapAfter ring seed pre e).2.sites root).controller =
          .waiting []) := by
    intro h
    rcases h with hr | ⟨hr, hc⟩
    · exact Or.inl (hmode.trans hr)
    · exact Or.inr ⟨hmode.trans hr, hcontroller.trans hc⟩
  have hnewSource : BankWindowTainted
      (bankWindowOverlapAfter ring seed pre e) e := by
    simpa only [hsource] using htainted
  have hpre := bankWindowOverlapNonrootPairTaintPreimage
    ring (by omega : 2 ≤ n)
    (bankWindowOverlapBefore ring seed pre)
    e e hnonroot (Or.inl rfl) hnewSource
  rcases hpre with holdSource | holdTarget
  · exact hlift (hJ.orphan root j holdOwner
      (by simpa only [hsource] using holdSource))
  · by_cases hinside : j.val + 1 <
        (compileAdvice (ceilLogTwo n)).b
    · have htargetRole :
          ((bankWindowOverlapBefore ring seed pre).1
            (ring.rightNeighbor e)).pack.val = j.val + 2 :=
        bankWindowOverlapStableInteriorResponderPack ring
          (bankWindowOverlapBefore ring seed pre) e j.val
          hinside holdRole hstable
      have hnextOwner : BankWindowOrphanOwner
          ring (bankWindowOverlapBefore ring seed pre)
          root (⟨j.val + 1, hinside⟩ :
            Fin (compileAdvice (ceilLogTwo n)).b) := by
        refine ⟨holdOwner.1, ?_, ?_⟩
        · change
            ((bankWindowOverlapBefore ring seed pre).1
              (Counter.site ring root (j.val + 2))).pack.val =
                j.val + 2
          rw [← hnextSite]
          exact htargetRole
        · intro hprefix
          apply holdOwner.2.2
          intro k hk
          have hindexBound :
              k ≤ (⟨j.val + 1, hinside⟩ :
                Fin (compileAdvice (ceilLogTwo n)).b).val + 1 := by
            change k ≤ j.val + 2
            omega
          exact hprefix k hindexBound
      have hnextTainted : BankWindowTainted
          (bankWindowOverlapBefore ring seed pre)
          (Counter.site ring root (j.val + 2)) := by
        rw [← hnextSite]
        exact holdTarget
      exact hlift (hJ.orphan root
        (⟨j.val + 1, hinside⟩ :
          Fin (compileAdvice (ceilLogTwo n)).b)
        hnextOwner hnextTainted)
    · have htop : j.val + 1 =
          (compileAdvice (ceilLogTwo n)).b := by
        omega
      have hsourceTop :
          ((bankWindowOverlapBefore ring seed pre).1 e).pack.val =
            (compileAdvice (ceilLogTwo n)).b :=
        holdRole.trans htop
      exact False.elim
        (bankWindowOverlapTopRejectsTaintedResponder
          ring hn hbank seed pre e hsourceTop hstable holdTarget)

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock

set_option autoImplicit false

/-- First-match non-top HOLD for the two outstanding PFX branches:
an empty source paired with an empty responder or an RR responder.
The genuine bankPair controls the physical bit/token fields, and
the literal renewalBankPairMemory retains the responder worker.
Consumer: bankWindowOverlapProtoHoldSelected and the RR-front
at-responder/after-responder cases of bankWindowExactOverlapStep. -/
theorem bankWindowOverlapProtoHoldPair
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (k : Nat)
    (hk : 1 ≤ k) (hbelow : k + 1 < c.b)
    (hx : x.pack.val = k) (hy : y.pack.val = k + 1)
    (hsourceE : x.tok = .E)
    (htarget : y.tok = .E ∨ y.tok = .RR)
    (hsourceZero : x.bit = false)
    (htargetZero : y.bit = false) :
    (renewalBankPairMemory c m e dest x y).2.worker =
      (m.sites dest).worker ∧
    (Counter.resetBankOld x y).1.tok = .E ∧
    (Counter.resetBankOld x y).1.bit = false ∧
    (Counter.resetBankOld x y).2.tok = y.tok ∧
    (Counter.resetBankOld x y).2.bit = false := by
  have hinside : k < c.b := by omega
  have hle : k ≤ c.b := by omega
  have hnz : k ≠ 0 := by omega
  have hne : k ≠ c.b := by omega
  have hnextLe : k + 1 ≤ c.b := by omega
  have hnextPos : 1 ≤ k + 1 := by omega
  have hnextNz : k + 1 ≠ 0 := by omega
  have hbz : c.b ≠ 0 := by omega
  have hnotTop : k + 1 ≠ c.b := by omega
  have hpostRole : packNext k (k + 1) c.b = k + 1 := by
    simp [packNext, hinside]
  have hnextRole : packNext x.pack.val y.pack.val c.b =
      y.pack.val := by
    rw [hx, hy]
    exact hpostRole
  have hlocal :
      renewalBankPairMemory c m e dest x y =
        ({ worker := (m.sites e).worker, controller := .empty },
         { worker := (m.sites dest).worker, controller := .empty }) := by
    rcases htarget with hempty | hrr
    · simp [renewalBankPairMemory, bankCell,
        hx, hy, hk, hinside, hle, hnz, hne,
        hnextLe, hnextPos, hnextNz, hbz,
        hnotTop, hpostRole, hnextRole, hsourceE, hempty]
    · simp [renewalBankPairMemory, bankCell,
        hx, hy, hk, hinside, hle, hnz, hne,
        hnextLe, hnextPos, hnextNz, hbz,
        hnotTop, hpostRole, hnextRole, hsourceE, hrr]
  have hworker :
      (renewalBankPairMemory c m e dest x y).2.worker =
        (m.sites dest).worker := by
    rw [hlocal]
  have hphysical :
      (Counter.resetBankOld x y).1.tok = .E ∧
      (Counter.resetBankOld x y).1.bit = false ∧
      (Counter.resetBankOld x y).2.tok = y.tok ∧
      (Counter.resetBankOld x y).2.bit = false := by
    rcases htarget with hempty | hrr
    · have hrow := Counter.resetTrialBankEmptyHoldsSymbolic
        (bankCell x x.pack.val) (bankCell y y.pack.val)
        c.b c.theta (by rw [hx]; exact hk)
        (by rw [hx]; exact hinside)
        (by rw [hx, hy]; rfl)
        hsourceE hempty hsourceZero htargetZero
      have hraw :
          (Counter.resetBankOld x y).1.tok = .E ∧
          (Counter.resetBankOld x y).1.bit = false ∧
          (Counter.resetBankOld x y).2.tok = .E ∧
          (Counter.resetBankOld x y).2.bit = false := by
        unfold Counter.resetBankOld
        rw [hnextRole]
        exact hrow
      exact ⟨hraw.1, hraw.2.1,
        by rw [hempty]; exact hraw.2.2.1,
        hraw.2.2.2⟩
    · have hrow := Counter.resetTrialBankPredecessorHoldsSymbolic
        (bankCell x x.pack.val) (bankCell y y.pack.val)
        c.b c.theta (by rw [hx]; exact hk)
        (by rw [hx]; exact hinside)
        (by rw [hx, hy]; rfl)
        (by rw [hy]; exact hbelow)
        hsourceE hrr hsourceZero htargetZero
      have hraw :
          (Counter.resetBankOld x y).1.tok = .E ∧
          (Counter.resetBankOld x y).1.bit = false ∧
          (Counter.resetBankOld x y).2.tok = .RR ∧
          (Counter.resetBankOld x y).2.bit = false := by
        unfold Counter.resetBankOld
        rw [hnextRole]
        exact hrow
      exact ⟨hraw.1, hraw.2.1,
        by rw [hrr]; exact hraw.2.2.1,
        hraw.2.2.2⟩
  exact ⟨hworker, hphysical⟩

/-- Physical and ghost HOLD fields at the actual masked BANK edge,
under genuine OLD PACK/token/bit hypotheses. The selected source
stays empty with bit zero, the selected responder retains its
old token/worker and has bit zero. No POST-J assumption.
Consumer: PFX RR front at or behind the responder. -/
theorem bankWindowOverlapProtoHoldSelected
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n) (k : Nat)
    (hk : 1 ≤ k)
    (hbelow : k + 1 < (compileAdvice (ceilLogTwo n)).b)
    (hx : ((bankWindowOverlapBefore ring seed pre).1 e).pack.val = k)
    (hy : ((bankWindowOverlapBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = k + 1)
    (he : ((bankWindowOverlapBefore ring seed pre).1 e).tok = .E)
    (ht : ((bankWindowOverlapBefore ring seed pre).1
      (ring.rightNeighbor e)).tok = .E ∨
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .RR)
    (hbx : ((bankWindowOverlapBefore ring seed pre).1 e).bit = false)
    (hby : ((bankWindowOverlapBefore ring seed pre).1
      (ring.rightNeighbor e)).bit = false) :
    ((bankWindowOverlapAfter ring seed pre e).1 e).tok = .E ∧
    ((bankWindowOverlapAfter ring seed pre e).1 e).bit = false ∧
    ((bankWindowOverlapAfter ring seed pre e).1
      (ring.rightNeighbor e)).tok =
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor e)).tok ∧
    ((bankWindowOverlapAfter ring seed pre e).1
      (ring.rightNeighbor e)).bit = false ∧
    ((bankWindowOverlapAfter ring seed pre e).2.sites
      (ring.rightNeighbor e)).worker =
      ((bankWindowOverlapBefore ring seed pre).2.sites
        (ring.rightNeighbor e)).worker := by
  have hpair := bankWindowOverlapProtoHoldPair
    (compileAdvice (ceilLogTwo n))
    (bankWindowOverlapBefore ring seed pre).2
    e (ring.rightNeighbor e)
    ((bankWindowOverlapBefore ring seed pre).1 e)
    ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor e))
    k hk hbelow hx hy he ht hbx hby
  have htrip := bankWindowClosureSelectedBankTrip
    ring hn hbank (bankWindowOverlapBefore ring seed pre) e
  have hsourceTok := congrArg
    (fun t : Mode × Bool × BTok => t.2.2) htrip.1
  have hsourceBit := congrArg
    (fun t : Mode × Bool × BTok => t.2.1) htrip.1
  have htargetTok := congrArg
    (fun t : Mode × Bool × BTok => t.2.2) htrip.2
  have htargetBit := congrArg
    (fun t : Mode × Bool × BTok => t.2.1) htrip.2
  have hghost := congrArg
    (fun s : RenewalBankSite n => s.worker)
    (rbReferenceSelectedPairFrame ring
      (by omega : 2 ≤ n)
      (bankWindowOverlapBefore ring seed pre) e).2.2.2
  exact ⟨hsourceTok.trans hpair.2.1,
    hsourceBit.trans hpair.2.2.1,
    htargetTok.trans hpair.2.2.2.1,
    htargetBit.trans hpair.2.2.2.2,
    hghost.trans hpair.1⟩

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock

set_option autoImplicit false

/-- Group-13 PFX non-top HOLD: an OLD proto pending RR front at
the selected responder or strictly after it survives the same
actual BANK edge with its old receipt. The first-match HOLD
row is proved on the OLD physical/ghost pair by
bankWindowOverlapProtoHoldSelected; other digits are framed
by the spatial-cutoff lemma. Consumer: J.proto's pending-RR
consequent in bankWindowExactOverlapStep. -/
theorem bankWindowOverlapProtoFrontAtOrAfterResponder
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n) (k limit : Nat)
    (hsource : e = Counter.site ring root k)
    (hk : 1 ≤ k) (hinterior : k < limit)
    (hstable :
      packNext
        ((bankWindowOverlapBefore ring seed pre).1 e).pack.val
        ((bankWindowOverlapBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val)
    (hproto : BankWindowProtoRun ring
      (bankWindowOverlapAfter ring seed pre e) root limit)
    (front : Fin (compileAdvice (ceilLogTwo n)).b)
    (rho : RenewalBankReceipt n)
    (hfrontBound : front.val + 1 ≤ limit)
    (hfrontAfter : k + 1 ≤ front.val + 1)
    (hworker :
      ((bankWindowOverlapBefore ring seed pre).2.sites
        (Counter.site ring root (front.val + 1))).worker =
          .pending rho)
    (hfrontRR :
      ((bankWindowOverlapBefore ring seed pre).1
        (Counter.site ring root (front.val + 1))).tok = .RR)
    (hzero : bankWindowZeroPrefix ring
      (bankWindowOverlapBefore ring seed pre)
      root (front.val + 1))
    (hearlier :
      ∀ t : Fin (compileAdvice (ceilLogTwo n)).b,
        t.val < front.val →
        ((bankWindowOverlapBefore ring seed pre).1
          (Counter.site ring root (t.val + 1))).tok = .E) :
    ∃ j : Fin (compileAdvice (ceilLogTwo n)).b,
      j.val + 1 ≤ limit ∧
      ∃ sigma : RenewalBankReceipt n,
        ((bankWindowOverlapAfter ring seed pre e).2.sites
          (Counter.site ring root (j.val + 1))).worker =
            .pending sigma ∧
        ((bankWindowOverlapAfter ring seed pre e).1
          (Counter.site ring root (j.val + 1))).tok = .RR ∧
        bankWindowZeroPrefix ring
          (bankWindowOverlapAfter ring seed pre e)
          root (j.val + 1) ∧
        (∀ t : Fin (compileAdvice (ceilLogTwo n)).b,
          t.val < j.val →
          ((bankWindowOverlapAfter ring seed pre e).1
            (Counter.site ring root (t.val + 1))).tok = .E) := by
  have hlimit : limit < (compileAdvice (ceilLogTwo n)).b := hproto.1
  obtain ⟨_, _, hroles, _⟩ :=
    bankWindowOverlapProtoInteriorOldRead
      ring hn hbank seed pre e root k limit
      hsource hk hinterior hstable hproto
  have hbelow : k + 1 < (compileAdvice (ceilLogTwo n)).b := by
    omega
  have hnextSite :
      ring.rightNeighbor e = Counter.site ring root (k + 1) := by
    rw [hsource]
    rfl
  have hindexSource :
      k - 1 < (compileAdvice (ceilLogTwo n)).b := by
    omega
  have hsourceLt :
      (⟨k - 1, hindexSource⟩ :
        Fin (compileAdvice (ceilLogTwo n)).b).val < front.val := by
    change k - 1 < front.val
    omega
  have hsourceE :
      ((bankWindowOverlapBefore ring seed pre).1 e).tok = .E := by
    have ht := hearlier
      (⟨k - 1, hindexSource⟩ :
        Fin (compileAdvice (ceilLogTwo n)).b) hsourceLt
    change ((bankWindowOverlapBefore ring seed pre).1
      (Counter.site ring root (k - 1 + 1))).tok = .E at ht
    have hkeq : k - 1 + 1 = k := by omega
    rw [hkeq, ← hsource] at ht
    exact ht
  have hsourceZero :
      ((bankWindowOverlapBefore ring seed pre).1 e).bit = false := by
    have hbound :
        (⟨k - 1, hindexSource⟩ :
          Fin (compileAdvice (ceilLogTwo n)).b).val + 1 ≤
            front.val + 1 := by
      change k - 1 + 1 ≤ front.val + 1
      omega
    have ht := hzero
      (⟨k - 1, hindexSource⟩ :
        Fin (compileAdvice (ceilLogTwo n)).b) hbound
    change ((bankWindowOverlapBefore ring seed pre).1
      (Counter.site ring root (k - 1 + 1))).bit = false at ht
    have hkeq : k - 1 + 1 = k := by omega
    rw [hkeq, ← hsource] at ht
    exact ht
  have hindexTarget : k < (compileAdvice (ceilLogTwo n)).b := by
    omega
  have htargetZero :
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor e)).bit = false := by
    have hbound :
        (⟨k, hindexTarget⟩ :
          Fin (compileAdvice (ceilLogTwo n)).b).val + 1 ≤
            front.val + 1 := by
      change k + 1 ≤ front.val + 1
      exact hfrontAfter
    have ht := hzero
      (⟨k, hindexTarget⟩ :
        Fin (compileAdvice (ceilLogTwo n)).b) hbound
    change ((bankWindowOverlapBefore ring seed pre).1
      (Counter.site ring root (k + 1))).bit = false at ht
    rw [← hnextSite] at ht
    exact ht
  have htargetToken :
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .E ∨
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor e)).tok = .RR := by
    by_cases hfrontAt : front.val + 1 = k + 1
    · have ht := hfrontRR
      rw [hfrontAt, ← hnextSite] at ht
      exact Or.inr ht
    · have htargetLt :
          (⟨k, hindexTarget⟩ :
            Fin (compileAdvice (ceilLogTwo n)).b).val <
              front.val := by
        change k < front.val
        omega
      have ht := hearlier
        (⟨k, hindexTarget⟩ :
          Fin (compileAdvice (ceilLogTwo n)).b) htargetLt
      change ((bankWindowOverlapBefore ring seed pre).1
        (Counter.site ring root (k + 1))).tok = .E at ht
      rw [← hnextSite] at ht
      exact Or.inl ht
  have hselected := bankWindowOverlapProtoHoldSelected
    ring hn hbank seed pre e k hk hbelow
    hroles.1 hroles.2 hsourceE htargetToken
    hsourceZero htargetZero
  refine ⟨front, hfrontBound, rho, ?_, ?_, ?_, ?_⟩
  · by_cases hfrontAt : front.val + 1 = k + 1
    · rw [hfrontAt, ← hnextSite] at hworker ⊢
      exact hselected.2.2.2.2.trans hworker
    · have hfrontNeSource : front.val + 1 ≠ k := by omega
      have hf := bankWindowOverlapProtoInteriorRemoteFrame
        ring hbank seed pre e root k (front.val + 1)
        hsource (by omega) (by omega)
        hfrontNeSource hfrontAt
      have hw := congrArg
        (fun s : RenewalBankSite n => s.worker) hf.2
      exact hw.trans hworker
  · by_cases hfrontAt : front.val + 1 = k + 1
    · rw [hfrontAt, ← hnextSite] at hfrontRR ⊢
      exact hselected.2.2.1.trans hfrontRR
    · have hfrontNeSource : front.val + 1 ≠ k := by omega
      have hf := bankWindowOverlapProtoInteriorRemoteFrame
        ring hbank seed pre e root k (front.val + 1)
        hsource (by omega) (by omega)
        hfrontNeSource hfrontAt
      have ht := congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok) hf.1
      exact ht.trans hfrontRR
  · intro t ht
    by_cases hsourceAt : t.val + 1 = k
    · have hsite : Counter.site ring root (t.val + 1) = e := by
        rw [hsourceAt]
        exact hsource.symm
      rw [hsite]
      exact hselected.2.1
    · by_cases htargetAt : t.val + 1 = k + 1
      · have hsite :
            Counter.site ring root (t.val + 1) =
              ring.rightNeighbor e := by
          rw [htargetAt]
          exact hnextSite.symm
        rw [hsite]
        exact hselected.2.2.2.1
      · have hf := bankWindowOverlapProtoInteriorRemoteFrame
          ring hbank seed pre e root k (t.val + 1)
          hsource (by omega) (by omega)
          hsourceAt htargetAt
        have hb := congrArg
          (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.bit) hf.1
        exact hb.trans (hzero t ht)
  · intro t ht
    by_cases hsourceAt : t.val + 1 = k
    · have hsite : Counter.site ring root (t.val + 1) = e := by
        rw [hsourceAt]
        exact hsource.symm
      rw [hsite]
      exact hselected.1
    · by_cases htargetAt : t.val + 1 = k + 1
      · have hsite :
            Counter.site ring root (t.val + 1) =
              ring.rightNeighbor e := by
          rw [htargetAt]
          exact hnextSite.symm
        rw [hsite]
        exact hselected.2.2.1.trans (by
          rw [← hsite]
          exact hearlier t ht)
      · have hf := bankWindowOverlapProtoInteriorRemoteFrame
          ring hbank seed pre e root k (t.val + 1)
          hsource (by omega) (by omega)
          hsourceAt htargetAt
        have htokFrame := congrArg
          (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok) hf.1
        exact htokFrame.trans (hearlier t ht)

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock

set_option autoImplicit false

/-- PFX group-13: all four POST J.proto consequents on a genuine
stable-PACK selected internal digit edge D_root(k) -> D_root(k+1)
with 1 <= k < limit < b. The OLD J.proto front is on one of four
positions relative to the selected pair: strictly before source,
source (RR-forward), responder (non-top E/RR HOLD), or beyond
responder (E/E HOLD). Both the physical token/bit and ghost worker
are transported from the SAME OLD snapshot; there is no post-J
hypothesis. Consumer: bankWindowExactOverlapStep, group-13 PFX. -/
theorem bankWindowOverlapProtoInteriorAll
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n) (k limit : Nat)
    (hJ : BankWindowExact ring
      (bankWindowOverlapBefore ring seed pre))
    (hsource : e = Counter.site ring root k)
    (hk : 1 ≤ k) (hinterior : k < limit)
    (hstable :
      packNext
        ((bankWindowOverlapBefore ring seed pre).1 e).pack.val
        ((bankWindowOverlapBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b =
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val)
    (hproto : BankWindowProtoRun ring
      (bankWindowOverlapAfter ring seed pre e) root limit) :
    (∀ p o,
      ((bankWindowOverlapAfter ring seed pre e).2.sites root).controller =
        .active p → p.origin = some o → False) ∧
    (BankWindowInheritedController
      (bankWindowOverlapAfter ring seed pre e) root →
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        j.val + 1 ≤ limit →
        ¬ BankWindowTainted
          (bankWindowOverlapAfter ring seed pre e)
          (Counter.site ring root (j.val + 1))) ∧
    (((bankWindowOverlapAfter ring seed pre e).1 root).mode = .RWAIT ∧
      ((bankWindowOverlapAfter ring seed pre e).2.sites root).controller =
        .waiting [] →
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
          (∀ t : Fin (compileAdvice (ceilLogTwo n)).b,
            t.val < j.val →
            ((bankWindowOverlapAfter ring seed pre e).1
              (Counter.site ring root (t.val + 1))).tok = .E)) ∧
    (((bankWindowOverlapAfter ring seed pre e).1 root).mode ≠ .RESET →
      ((bankWindowOverlapAfter ring seed pre e).1 root).mode ≠ .RWAIT →
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        j.val + 1 ≤ limit →
        ¬ BankWindowTainted
          (bankWindowOverlapAfter ring seed pre e)
          (Counter.site ring root (j.val + 1))) := by
  have hsafe := bankWindowOverlapProtoInteriorSafeFields
    ring hn hbank seed pre e root k limit hJ
    hsource hk hinterior hstable hproto
  obtain ⟨holdProto, hrootFrame, _, _⟩ :=
    bankWindowOverlapProtoInteriorOldRead
      ring hn hbank seed pre e root k limit
      hsource hk hinterior hstable hproto
  have hOld := hJ.proto root limit holdProto
  have hmode := congrArg
    (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.mode)
    hrootFrame.1
  have hcontroller := congrArg
    (fun s : RenewalBankSite n => s.controller) hrootFrame.2
  refine ⟨hsafe.1, hsafe.2.1, ?_, hsafe.2.2⟩
  intro hpostWait
  have holdWait :
      ((bankWindowOverlapBefore ring seed pre).1 root).mode = .RWAIT ∧
      ((bankWindowOverlapBefore ring seed pre).2.sites root).controller =
        .waiting [] := by
    exact ⟨hmode.symm.trans hpostWait.1,
      hcontroller.symm.trans hpostWait.2⟩
  obtain ⟨front, hfrontBound, rho, hworker, htok, hzero, hearlier⟩ :=
    hOld.2.2.1 holdWait
  by_cases hbefore : front.val + 1 < k
  · have hkBound : k ≤ (compileAdvice (ceilLogTwo n)).b := by
      have hl := hproto.1
      omega
    exact bankWindowOverlapProtoFrontBefore
      ring hbank seed pre e root k limit
      hsource hkBound front rho hfrontBound hbefore
      hworker htok hzero hearlier
  · by_cases hat : front.val + 1 = k
    · have hsite :
          Counter.site ring root (front.val + 1) = e := by
        rw [hat]
        exact hsource.symm
      have hsourceWorker :
          ((bankWindowOverlapBefore ring seed pre).2.sites e).worker =
            .pending rho := by
        rw [← hsite]
        exact hworker
      have hsourceRR :
          ((bankWindowOverlapBefore ring seed pre).1 e).tok = .RR := by
        rw [← hsite]
        exact htok
      have hzeroSource : bankWindowZeroPrefix ring
          (bankWindowOverlapBefore ring seed pre) root k := by
        rw [← hat]
        exact hzero
      have hearlierSource :
          ∀ t : Fin (compileAdvice (ceilLogTwo n)).b,
            t.val + 1 < k →
            ((bankWindowOverlapBefore ring seed pre).1
              (Counter.site ring root (t.val + 1))).tok = .E := by
        intro t ht
        have hlt : t.val < front.val := by omega
        exact hearlier t hlt
      exact bankWindowOverlapProtoFrontMoves
        ring hn hbank seed pre e root k limit
        hsource hk hinterior hstable hproto rho
        hsourceWorker hsourceRR hzeroSource hearlierSource
    · have hafter : k + 1 ≤ front.val + 1 := by omega
      exact bankWindowOverlapProtoFrontAtOrAfterResponder
        ring hn hbank seed pre e root k limit
        hsource hk hinterior hstable hproto
        front rho hfrontBound hafter hworker htok hzero hearlier

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The selected predecessor of a proto first-mismatch digit
must correct that digit's PACK, so the same POST prefix cannot
still be a proto-run ending at the repaired position.
Consumer: group-13 PFX k=limit and first-digit boundary.
This is the actual physical packNext rule, not a case of
hypothetical post-J closure. -/
theorem bankWindowOverlapProtoMismatchPredecessorExit
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n) (limit : Nat)
    (hsource : e = Counter.site ring root limit)
    (hproto : BankWindowProtoRun ring
      (bankWindowOverlapAfter ring seed pre e) root limit) :
    False := by
  have hlimit : limit < (compileAdvice (ceilLogTwo n)).b :=
    hproto.1
  have hpostSource :
      ((bankWindowOverlapAfter ring seed pre e).1 e).pack.val =
        limit := by
    have hh := hproto.2.1 limit (Nat.le_refl _)
    rw [← hsource] at hh
    exact hh
  have hsourceFrame := bankWindowClosureRepairNonresponderPackFixed
    ring (by omega : 2 ≤ n)
    (bankWindowOverlapBefore ring seed pre) e e
    (clockNeighborDifferent ring (by omega : 2 ≤ n) e).symm
  have holdSource :
      ((bankWindowOverlapBefore ring seed pre).1 e).pack.val =
        limit :=
    hsourceFrame.symm.trans hpostSource
  have hnext :
      packNext
        ((bankWindowOverlapBefore ring seed pre).1 e).pack.val
        ((bankWindowOverlapBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b = limit + 1 := by
    rw [holdSource]
    simp [packNext, hlimit]
  have hresponder := bankWindowExactResponderPack ring
    (bankWindowOverlapBefore ring seed pre) e
    (clockNeighborDifferent ring (by omega : 2 ≤ n) e)
  have htarget :
      ((bankWindowOverlapAfter ring seed pre e).1
        (Counter.site ring root (limit + 1))).pack.val =
          limit + 1 := by
    have hnextSite :
        ring.rightNeighbor e =
          Counter.site ring root (limit + 1) := by
      rw [hsource]
      rfl
    rw [← hnextSite]
    exact hresponder.trans hnext
  exact hproto.2.2 htarget

/-- A changed responder that is now aligned in the first
limit digits of a POST incomplete proto-run was the FIRST
wrong PACK after a strictly shorter OLD aligned prefix.
Consumer: group-13 PFX repair activation and OLD J.proto,
without assuming that the POST window became complete. -/
theorem bankWindowOverlapRepairOldProtoAtPartialDigit
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n) (j limit : Nat)
    (hj : j < limit)
    (hresponder :
      ring.rightNeighbor e = Counter.site ring root (j + 1))
    (hchanged :
      packNext
        ((bankWindowOverlapBefore ring seed pre).1 e).pack.val
        ((bankWindowOverlapBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val)
    (hproto : BankWindowProtoRun ring
      (bankWindowOverlapAfter ring seed pre e) root limit) :
    BankWindowProtoRun ring
      (bankWindowOverlapBefore ring seed pre) root j := by
  have hlimit : limit < (compileAdvice (ceilLogTwo n)).b :=
    hproto.1
  have hjlt : j < (compileAdvice (ceilLogTwo n)).b := by
    omega
  have hsourceSite : e = Counter.site ring root j :=
    Counter.resetTrialSitePredecessor ring root e j hresponder
  have hpostSource :
      ((bankWindowOverlapAfter ring seed pre e).1 e).pack.val = j := by
    have hh := hproto.2.1 j (by omega)
    rw [← hsourceSite] at hh
    exact hh
  have hsourceFrame := bankWindowClosureRepairNonresponderPackFixed
    ring (by omega : 2 ≤ n)
    (bankWindowOverlapBefore ring seed pre) e e
    (clockNeighborDifferent ring (by omega : 2 ≤ n) e).symm
  have holdSource :
      ((bankWindowOverlapBefore ring seed pre).1 e).pack.val = j :=
    hsourceFrame.symm.trans hpostSource
  have hpostTarget :
      ((bankWindowOverlapAfter ring seed pre e).1
        (ring.rightNeighbor e)).pack.val = j + 1 := by
    have hh := hproto.2.1 (j + 1) (by omega)
    rw [← hresponder] at hh
    exact hh
  have hresponderPack := bankWindowExactResponderPack ring
    (bankWindowOverlapBefore ring seed pre) e
    (clockNeighborDifferent ring (by omega : 2 ≤ n) e)
  have hnext :
      packNext
        ((bankWindowOverlapBefore ring seed pre).1 e).pack.val
        ((bankWindowOverlapBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b = j + 1 := by
    rw [holdSource]
    simp [packNext, hjlt]
  have hwrong :
      ((bankWindowOverlapBefore ring seed pre).1
        (Counter.site ring root (j + 1))).pack.val ≠ j + 1 := by
    intro hcorrect
    have hcorrectAt :
        ((bankWindowOverlapBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val = j + 1 := by
      rw [hresponder]
      exact hcorrect
    exact hchanged (hnext.trans hcorrectAt.symm)
  refine ⟨hjlt, ?_, hwrong⟩
  intro k hk
  have havoid :
      Counter.site ring root k ≠ ring.rightNeighbor e := by
    rw [hresponder]
    exact bankWindowIncidenceSiteDistinct
      ring hbank root k (j + 1) (by omega) (by omega)
  have hfixed := bankWindowClosureRepairNonresponderPackFixed
    ring (by omega : 2 ≤ n)
    (bankWindowOverlapBefore ring seed pre) e
    (Counter.site ring root k) havoid
  exact hfixed.symm.trans (hproto.2.1 k (by omega))

theorem bankWindowOverlapIncomingWaitPrefixOrphan
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowOverlapBefore ring seed pre))
    (hpackOld :
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val = 0)
    (hpackPost :
      ((bankWindowOverlapAfter ring seed pre e).1
        (ring.rightNeighbor e)).pack.val = 0)
    (hgrant :
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor e)).grant = false)
    (hwait :
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor e)).mode = .RWAIT) :
    (∀ limit : Nat,
      BankWindowProtoRun ring
        (bankWindowOverlapAfter ring seed pre e)
        (ring.rightNeighbor e) limit →
      (∀ p o,
        ((bankWindowOverlapAfter ring seed pre e).2.sites
          (ring.rightNeighbor e)).controller = .active p →
        p.origin = some o → False) ∧
      (BankWindowInheritedController
        (bankWindowOverlapAfter ring seed pre e)
        (ring.rightNeighbor e) →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted
            (bankWindowOverlapAfter ring seed pre e)
            (Counter.site ring (ring.rightNeighbor e) (j.val + 1))) ∧
      ((((bankWindowOverlapAfter ring seed pre e).1
          (ring.rightNeighbor e)).mode = .RWAIT ∧
          ((bankWindowOverlapAfter ring seed pre e).2.sites
            (ring.rightNeighbor e)).controller = .waiting []) →
        ∃ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit ∧
          ∃ rho : RenewalBankReceipt n,
            ((bankWindowOverlapAfter ring seed pre e).2.sites
              (Counter.site ring (ring.rightNeighbor e)
                (j.val + 1))).worker = .pending rho ∧
            ((bankWindowOverlapAfter ring seed pre e).1
              (Counter.site ring (ring.rightNeighbor e)
                (j.val + 1))).tok = .RR ∧
            bankWindowZeroPrefix ring
              (bankWindowOverlapAfter ring seed pre e)
              (ring.rightNeighbor e) (j.val + 1) ∧
            (∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
              k.val < j.val →
              ((bankWindowOverlapAfter ring seed pre e).1
                (Counter.site ring (ring.rightNeighbor e)
                  (k.val + 1))).tok = .E)) ∧
      (((bankWindowOverlapAfter ring seed pre e).1
          (ring.rightNeighbor e)).mode ≠ .RESET →
        ((bankWindowOverlapAfter ring seed pre e).1
          (ring.rightNeighbor e)).mode ≠ .RWAIT →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted
            (bankWindowOverlapAfter ring seed pre e)
            (Counter.site ring (ring.rightNeighbor e) (j.val + 1)))) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowOrphanOwner ring
        (bankWindowOverlapAfter ring seed pre e)
        (ring.rightNeighbor e) j →
      BankWindowTainted
        (bankWindowOverlapAfter ring seed pre e)
        (Counter.site ring (ring.rightNeighbor e) (j.val + 1)) →
      ((bankWindowOverlapAfter ring seed pre e).1
        (ring.rightNeighbor e)).mode = .RESET ∨
      (((bankWindowOverlapAfter ring seed pre e).1
          (ring.rightNeighbor e)).mode = .RWAIT ∧
        ((bankWindowOverlapAfter ring seed pre e).2.sites
          (ring.rightNeighbor e)).controller = .waiting [])) := by
  have hcore := bankWindowIncomingRootCoreStep
    ring hn hbank seed pre e hJ hpackOld
  have hcases := hcore.2.2.2.2.2 hpackPost hgrant hwait
  by_cases hlease :
      1 < ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor e)).lease.val
  · have hcontinue := hcases.1 hlease
    have hmodeKeep :
        ((bankWindowOverlapAfter ring seed pre e).1
          (ring.rightNeighbor e)).mode =
        ((bankWindowOverlapBefore ring seed pre).1
          (ring.rightNeighbor e)).mode :=
      hcontinue.1.trans hwait.symm
    refine ⟨?_, ?_⟩
    · intro limit hproto
      exact bankWindowIncomingProtoOwnerSurvivor ring hbank
        (bankWindowOverlapBefore ring seed pre) hJ
        (ring.rightNeighbor e) e rfl
        hpackOld hpackPost hmodeKeep hcontinue.2
        limit hproto
    · exact bankWindowIncomingOrphanOwnerSurvivor ring hbank
        (bankWindowOverlapBefore ring seed pre) hJ
        (ring.rightNeighbor e) e rfl
        hpackOld hpackPost hmodeKeep hcontinue.2
  · have hshort :
        ((bankWindowOverlapBefore ring seed pre).1
          (ring.rightNeighbor e)).lease.val ≤ 1 := by
      omega
    have hreset := hcases.2 hshort
    have hfields := bankWindowIncomingResetOwnerFields ring
      (bankWindowOverlapBefore ring seed pre)
      (ring.rightNeighbor e) e hpackPost
      hreset.1 hcore.1
    exact ⟨hfields.2.2.1, hfields.2.2.2⟩

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Group-13 XD: a changed PACK on a selected edge is
*responder only*. The OLD source PACK stays unchanged.
The repaired responder is RESET, bit-zero, token-empty and
has no tainted worker. If this responder is the POST root
of a proto-run or an orphan, the RESET branch discharges
the entire four-clause PFX consequent and the ORPH restriction.
Consumer: bankWindowExactStep, changed-responder root owner.
The remaining FOREIGN root reads are not asserted. -/
theorem bankWindowOverlapChangedResponderPrefixOrphan
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowOverlapBefore ring seed pre))
    (hchanged :
      packNext
        ((bankWindowOverlapBefore ring seed pre).1 e).pack.val
        ((bankWindowOverlapBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val) :
    ((bankWindowOverlapAfter ring seed pre e).1 e).pack.val =
      ((bankWindowOverlapBefore ring seed pre).1 e).pack.val ∧
    (((bankWindowOverlapAfter ring seed pre e).1
        (ring.rightNeighbor e)).mode = .RESET ∧
      ((bankWindowOverlapAfter ring seed pre e).1
        (ring.rightNeighbor e)).bit = false ∧
      ((bankWindowOverlapAfter ring seed pre e).1
        (ring.rightNeighbor e)).tok = .E ∧
      ¬ BankWindowTainted
        (bankWindowOverlapAfter ring seed pre e)
        (ring.rightNeighbor e)) ∧
    (∀ limit : Nat,
      BankWindowProtoRun ring
        (bankWindowOverlapAfter ring seed pre e)
        (ring.rightNeighbor e) limit →
      (∀ p o,
        ((bankWindowOverlapAfter ring seed pre e).2.sites
          (ring.rightNeighbor e)).controller = .active p →
        p.origin = some o → False) ∧
      (BankWindowInheritedController
        (bankWindowOverlapAfter ring seed pre e)
        (ring.rightNeighbor e) →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted
            (bankWindowOverlapAfter ring seed pre e)
            (Counter.site ring (ring.rightNeighbor e) (j.val + 1))) ∧
      ((((bankWindowOverlapAfter ring seed pre e).1
          (ring.rightNeighbor e)).mode = .RWAIT ∧
          ((bankWindowOverlapAfter ring seed pre e).2.sites
            (ring.rightNeighbor e)).controller = .waiting []) →
        ∃ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit ∧
          ∃ rho : RenewalBankReceipt n,
            ((bankWindowOverlapAfter ring seed pre e).2.sites
              (Counter.site ring (ring.rightNeighbor e)
                (j.val + 1))).worker = .pending rho ∧
            ((bankWindowOverlapAfter ring seed pre e).1
              (Counter.site ring (ring.rightNeighbor e)
                (j.val + 1))).tok = .RR ∧
            bankWindowZeroPrefix ring
              (bankWindowOverlapAfter ring seed pre e)
              (ring.rightNeighbor e) (j.val + 1) ∧
            (∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
              k.val < j.val →
              ((bankWindowOverlapAfter ring seed pre e).1
                (Counter.site ring (ring.rightNeighbor e)
                  (k.val + 1))).tok = .E)) ∧
      (((bankWindowOverlapAfter ring seed pre e).1
          (ring.rightNeighbor e)).mode ≠ .RESET →
        ((bankWindowOverlapAfter ring seed pre e).1
          (ring.rightNeighbor e)).mode ≠ .RWAIT →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted
            (bankWindowOverlapAfter ring seed pre e)
            (Counter.site ring (ring.rightNeighbor e) (j.val + 1)))) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowOrphanOwner ring
        (bankWindowOverlapAfter ring seed pre e)
        (ring.rightNeighbor e) j →
      BankWindowTainted
        (bankWindowOverlapAfter ring seed pre e)
        (Counter.site ring (ring.rightNeighbor e) (j.val + 1)) →
      ((bankWindowOverlapAfter ring seed pre e).1
        (ring.rightNeighbor e)).mode = .RESET ∨
      (((bankWindowOverlapAfter ring seed pre e).1
          (ring.rightNeighbor e)).mode = .RWAIT ∧
        ((bankWindowOverlapAfter ring seed pre e).2.sites
          (ring.rightNeighbor e)).controller = .waiting [])) := by
  have hsource := bankWindowClosureRepairNonresponderPackFixed
    ring (by omega : 2 ≤ n)
    (bankWindowOverlapBefore ring seed pre) e e
    (clockNeighborDifferent ring (by omega : 2 ≤ n) e).symm
  have hclean := bankWindowClosureChangedDigitClean
    ring hn hbank (bankWindowOverlapBefore ring seed pre)
    e hchanged
  have hframe := bankWindowExactFrameStep
    ring hn hbank seed pre e hJ
  refine ⟨hsource, ⟨hclean.1, hclean.2.1,
    hclean.2.2.1, hclean.2.2.2.1⟩, ?_, ?_⟩
  · intro limit hproto
    have hpostZero :
        ((bankWindowOverlapAfter ring seed pre e).1
          (ring.rightNeighbor e)).pack.val = 0 := by
      have hzero := hproto.2.1 0 (by omega)
      change ((bankWindowOverlapAfter ring seed pre e).1
        (ring.rightNeighbor e)).pack.val = 0 at hzero
      exact hzero
    have hfields := bankWindowIncomingResetOwnerFields ring
      (bankWindowOverlapBefore ring seed pre)
      (ring.rightNeighbor e) e hpostZero hclean.1 hframe
    exact hfields.2.2.1 limit hproto
  · intro j howner htaint
    have hpostZero :
        ((bankWindowOverlapAfter ring seed pre e).1
          (ring.rightNeighbor e)).pack.val = 0 := howner.1
    have hfields := bankWindowIncomingResetOwnerFields ring
      (bankWindowOverlapBefore ring seed pre)
      (ring.rightNeighbor e) e hpostZero hclean.1 hframe
    exact hfields.2.2.2 j howner htaint

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Group-13 IN/B0 with an OLD IWAIT or CWAIT root:
the actual lease test either retains its mode and ghost
controller or resets the root. Both outcomes preserve the
four PFX clauses and the ORPH restriction at that very root,
even when its PACK window is incomplete. Consumer:
bankWindowExactStep incoming comparator/increment wait rows.
No assumption about a POST J field is made. -/
theorem bankWindowOverlapIncomingPhaseWaitPrefixOrphan
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowOverlapBefore ring seed pre))
    (hpackOld :
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val = 0)
    (hpackPost :
      ((bankWindowOverlapAfter ring seed pre e).1
        (ring.rightNeighbor e)).pack.val = 0)
    (hgrant :
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor e)).grant = false)
    (hmode :
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor e)).mode = .IWAIT ∨
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor e)).mode = .CWAIT) :
    (∀ limit : Nat,
      BankWindowProtoRun ring
        (bankWindowOverlapAfter ring seed pre e)
        (ring.rightNeighbor e) limit →
      (∀ p o,
        ((bankWindowOverlapAfter ring seed pre e).2.sites
          (ring.rightNeighbor e)).controller = .active p →
        p.origin = some o → False) ∧
      (BankWindowInheritedController
        (bankWindowOverlapAfter ring seed pre e)
        (ring.rightNeighbor e) →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted
            (bankWindowOverlapAfter ring seed pre e)
            (Counter.site ring (ring.rightNeighbor e) (j.val + 1))) ∧
      ((((bankWindowOverlapAfter ring seed pre e).1
          (ring.rightNeighbor e)).mode = .RWAIT ∧
          ((bankWindowOverlapAfter ring seed pre e).2.sites
            (ring.rightNeighbor e)).controller = .waiting []) →
        ∃ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit ∧
          ∃ rho : RenewalBankReceipt n,
            ((bankWindowOverlapAfter ring seed pre e).2.sites
              (Counter.site ring (ring.rightNeighbor e)
                (j.val + 1))).worker = .pending rho ∧
            ((bankWindowOverlapAfter ring seed pre e).1
              (Counter.site ring (ring.rightNeighbor e)
                (j.val + 1))).tok = .RR ∧
            bankWindowZeroPrefix ring
              (bankWindowOverlapAfter ring seed pre e)
              (ring.rightNeighbor e) (j.val + 1) ∧
            (∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
              k.val < j.val →
              ((bankWindowOverlapAfter ring seed pre e).1
                (Counter.site ring (ring.rightNeighbor e)
                  (k.val + 1))).tok = .E)) ∧
      (((bankWindowOverlapAfter ring seed pre e).1
          (ring.rightNeighbor e)).mode ≠ .RESET →
        ((bankWindowOverlapAfter ring seed pre e).1
          (ring.rightNeighbor e)).mode ≠ .RWAIT →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted
            (bankWindowOverlapAfter ring seed pre e)
            (Counter.site ring (ring.rightNeighbor e) (j.val + 1)))) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowOrphanOwner ring
        (bankWindowOverlapAfter ring seed pre e)
        (ring.rightNeighbor e) j →
      BankWindowTainted
        (bankWindowOverlapAfter ring seed pre e)
        (Counter.site ring (ring.rightNeighbor e) (j.val + 1)) →
      ((bankWindowOverlapAfter ring seed pre e).1
        (ring.rightNeighbor e)).mode = .RESET ∨
      (((bankWindowOverlapAfter ring seed pre e).1
          (ring.rightNeighbor e)).mode = .RWAIT ∧
        ((bankWindowOverlapAfter ring seed pre e).2.sites
          (ring.rightNeighbor e)).controller = .waiting [])) := by
  have hbranch :
      (1 < ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor e)).lease.val →
        ((bankWindowOverlapAfter ring seed pre e).1
          (ring.rightNeighbor e)).mode =
          ((bankWindowOverlapBefore ring seed pre).1
            (ring.rightNeighbor e)).mode ∧
        ((bankWindowOverlapAfter ring seed pre e).2.sites
          (ring.rightNeighbor e)).controller =
          ((bankWindowOverlapBefore ring seed pre).2.sites
            (ring.rightNeighbor e)).controller) ∧
      (((bankWindowOverlapBefore ring seed pre).1
          (ring.rightNeighbor e)).lease.val ≤ 1 →
        ((bankWindowOverlapAfter ring seed pre e).1
          (ring.rightNeighbor e)).mode = .RESET ∧
        ((bankWindowOverlapAfter ring seed pre e).2.sites
          (ring.rightNeighbor e)).controller = .empty) := by
    rcases hmode with hi | hc
    · have h := bankWindowIncomingIwaitExact
        ring hn hbank seed pre e hJ
        hpackOld hpackPost hgrant hi
      constructor
      · intro hlease
        have hkeep := h.1 hlease
        exact ⟨hkeep.1.trans hi.symm, hkeep.2⟩
      · exact h.2
    · have h := bankWindowIncomingCwaitExact
        ring hn hbank seed pre e hJ
        hpackOld hpackPost hgrant hc
      constructor
      · intro hlease
        have hkeep := h.1 hlease
        exact ⟨hkeep.1.trans hc.symm, hkeep.2⟩
      · exact h.2
  by_cases hlease :
      1 < ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor e)).lease.val
  · have hkeep := hbranch.1 hlease
    refine ⟨?_, ?_⟩
    · intro limit hproto
      exact bankWindowIncomingProtoOwnerSurvivor ring hbank
        (bankWindowOverlapBefore ring seed pre) hJ
        (ring.rightNeighbor e) e rfl
        hpackOld hpackPost hkeep.1 hkeep.2 limit hproto
    · exact bankWindowIncomingOrphanOwnerSurvivor ring hbank
        (bankWindowOverlapBefore ring seed pre) hJ
        (ring.rightNeighbor e) e rfl
        hpackOld hpackPost hkeep.1 hkeep.2
  · have hshort :
        ((bankWindowOverlapBefore ring seed pre).1
          (ring.rightNeighbor e)).lease.val ≤ 1 := by
      omega
    have hreset := hbranch.2 hshort
    have hframe := bankWindowExactFrameStep
      ring hn hbank seed pre e hJ
    have hfields := bankWindowIncomingResetOwnerFields ring
      (bankWindowOverlapBefore ring seed pre)
      (ring.rightNeighbor e) e hpackPost hreset.1 hframe
    exact ⟨hfields.2.2.1, hfields.2.2.2⟩

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open Classical

set_option autoImplicit false
set_option Elab.async false


end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Literal grant-reset of an outgoing PACK-zero source.
Consumer: group-13 PFX/ORPH selected-root grant row. -/
theorem bankWindowOverlapGrantSourceResetMode
    {c : Compiled} (x y : Agent c)
    (hx : x.pack.val = 0) (hg : x.grant = true) :
    (Counter.resetBankOld x y).1.mode = .RESET := by
  have hb : 0 < c.b := by
    change 0 < c.s + 11
    omega
  have hpost : packNext x.pack.val y.pack.val c.b = 1 := by
    rw [hx]
    simp [packNext, hb]
  unfold Counter.resetBankOld
  rw [hpost]
  by_cases hy : y.pack.val = 1
  · simp [bankPair, bankCell, hx, hg, hy,
      Id.run_pure, Id.run_bind]
  · have hne : 1 ≠ y.pack.val := by
      intro h
      exact hy h.symm
    simp [bankPair, bankCell, hx, hg, hy, hne,
      Id.run_pure, Id.run_bind]

/-- Selected-root grant case, using the real bank-source row and
the OLD-J-to-POST frame. Consumer: group-13 PFX/ORPH own root. -/
theorem bankWindowOverlapRootGrantPrefixOrphan
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (root : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowOverlapBefore ring seed pre))
    (hroot :
      ((bankWindowOverlapBefore ring seed pre).1 root).pack.val = 0)
    (hgrant :
      ((bankWindowOverlapBefore ring seed pre).1 root).grant = true) :
    ((bankWindowOverlapAfter ring seed pre root).1 root).mode =
      .RESET ∧
    ((bankWindowOverlapAfter ring seed pre root).2.sites root).controller =
      .empty ∧
    (∀ limit : Nat,
      BankWindowProtoRun ring
        (bankWindowOverlapAfter ring seed pre root) root limit →
      (∀ p o,
        ((bankWindowOverlapAfter ring seed pre root).2.sites
          root).controller = .active p →
        p.origin = some o → False) ∧
      (BankWindowInheritedController
        (bankWindowOverlapAfter ring seed pre root) root →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted
            (bankWindowOverlapAfter ring seed pre root)
            (Counter.site ring root (j.val + 1))) ∧
      ((((bankWindowOverlapAfter ring seed pre root).1 root).mode =
          .RWAIT ∧
          ((bankWindowOverlapAfter ring seed pre root).2.sites
            root).controller = .waiting []) →
        ∃ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit ∧
          ∃ rho : RenewalBankReceipt n,
            ((bankWindowOverlapAfter ring seed pre root).2.sites
              (Counter.site ring root (j.val + 1))).worker =
              .pending rho ∧
            ((bankWindowOverlapAfter ring seed pre root).1
              (Counter.site ring root (j.val + 1))).tok = .RR ∧
            bankWindowZeroPrefix ring
              (bankWindowOverlapAfter ring seed pre root)
              root (j.val + 1) ∧
            (∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
              k.val < j.val →
              ((bankWindowOverlapAfter ring seed pre root).1
                (Counter.site ring root (k.val + 1))).tok = .E)) ∧
      (((bankWindowOverlapAfter ring seed pre root).1 root).mode
          ≠ .RESET →
        ((bankWindowOverlapAfter ring seed pre root).1 root).mode
          ≠ .RWAIT →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted
            (bankWindowOverlapAfter ring seed pre root)
            (Counter.site ring root (j.val + 1)))) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowOrphanOwner ring
        (bankWindowOverlapAfter ring seed pre root) root j →
      BankWindowTainted
        (bankWindowOverlapAfter ring seed pre root)
        (Counter.site ring root (j.val + 1)) →
      ((bankWindowOverlapAfter ring seed pre root).1 root).mode =
        .RESET ∨
      (((bankWindowOverlapAfter ring seed pre root).1 root).mode =
          .RWAIT ∧
        ((bankWindowOverlapAfter ring seed pre root).2.sites
          root).controller = .waiting [])) := by
  have htrip := (bankWindowClosureSelectedBankTrip
    ring hn hbank (bankWindowOverlapBefore ring seed pre) root).1
  have hmode := congrArg
    (fun t : Mode × Bool × BTok => t.1) htrip
  change ((bankWindowOverlapAfter ring seed pre root).1 root).mode =
    (Counter.resetBankOld
      ((bankWindowOverlapBefore ring seed pre).1 root)
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor root))).1.mode at hmode
  have hreset :
      ((bankWindowOverlapAfter ring seed pre root).1 root).mode =
        .RESET :=
    hmode.trans (bankWindowOverlapGrantSourceResetMode
      ((bankWindowOverlapBefore ring seed pre).1 root)
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor root)) hroot hgrant)
  have hsourcePack := bankWindowClosureRepairNonresponderPackFixed
    ring (by omega : 2 ≤ n)
    (bankWindowOverlapBefore ring seed pre) root root
    (clockNeighborDifferent ring (by omega : 2 ≤ n) root).symm
  have hpostPack :
      ((bankWindowOverlapAfter ring seed pre root).1 root).pack.val =
        0 := hsourcePack.trans hroot
  have hframe := bankWindowExactFrameStep
    ring hn hbank seed pre root hJ
  have hfields := bankWindowIncomingResetOwnerFields ring
    (bankWindowOverlapBefore ring seed pre) root root
    hpostPack hreset hframe
  exact ⟨hreset, hfields.1, hfields.2.2.1, hfields.2.2.2⟩

/-- Authentic RESET launch creates the first pending RR witness;
every aligned post proto-prefix of the own root has that front.
Consumer: group-13 PFX/ORPH selected-root launch row. -/
theorem bankWindowOverlapRootLaunchPrefixOrphan
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (root : Fin n)
    (hx : ((bankWindowOverlapBefore ring seed pre).1 root).pack.val = 0)
    (hy : ((bankWindowOverlapBefore ring seed pre).1
      (ring.rightNeighbor root)).pack.val = 1)
    (hg : ((bankWindowOverlapBefore ring seed pre).1 root).grant = false)
    (hm : ((bankWindowOverlapBefore ring seed pre).1 root).mode =
      .RESET) :
    ((bankWindowOverlapAfter ring seed pre root).1 root).mode =
      .RWAIT ∧
    ((bankWindowOverlapAfter ring seed pre root).2.sites root).controller =
      .waiting [] ∧
    (∀ limit : Nat,
      BankWindowProtoRun ring
        (bankWindowOverlapAfter ring seed pre root) root limit →
      (∀ p o,
        ((bankWindowOverlapAfter ring seed pre root).2.sites
          root).controller = .active p →
        p.origin = some o → False) ∧
      (BankWindowInheritedController
        (bankWindowOverlapAfter ring seed pre root) root →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted
            (bankWindowOverlapAfter ring seed pre root)
            (Counter.site ring root (j.val + 1))) ∧
      ((((bankWindowOverlapAfter ring seed pre root).1 root).mode =
          .RWAIT ∧
          ((bankWindowOverlapAfter ring seed pre root).2.sites
            root).controller = .waiting []) →
        ∃ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit ∧
          ∃ rho : RenewalBankReceipt n,
            ((bankWindowOverlapAfter ring seed pre root).2.sites
              (Counter.site ring root (j.val + 1))).worker =
              .pending rho ∧
            ((bankWindowOverlapAfter ring seed pre root).1
              (Counter.site ring root (j.val + 1))).tok = .RR ∧
            bankWindowZeroPrefix ring
              (bankWindowOverlapAfter ring seed pre root)
              root (j.val + 1) ∧
            (∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
              k.val < j.val →
              ((bankWindowOverlapAfter ring seed pre root).1
                (Counter.site ring root (k.val + 1))).tok = .E)) ∧
      (((bankWindowOverlapAfter ring seed pre root).1 root).mode
          ≠ .RESET →
        ((bankWindowOverlapAfter ring seed pre root).1 root).mode
          ≠ .RWAIT →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted
            (bankWindowOverlapAfter ring seed pre root)
            (Counter.site ring root (j.val + 1)))) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowOrphanOwner ring
        (bankWindowOverlapAfter ring seed pre root) root j →
      BankWindowTainted
        (bankWindowOverlapAfter ring seed pre root)
        (Counter.site ring root (j.val + 1)) →
      ((bankWindowOverlapAfter ring seed pre root).1 root).mode =
        .RESET ∨
      (((bankWindowOverlapAfter ring seed pre root).1 root).mode =
          .RWAIT ∧
        ((bankWindowOverlapAfter ring seed pre root).2.sites
          root).controller = .waiting [])) := by
  have hphysical := bankWindowClosureResetLaunchPhysicalPair
    ring hn hbank (bankWindowOverlapBefore ring seed pre) root
    hx hy hg hm
  have hghost := bankWindowClosureResetLaunchGhost
    ring (by omega : 2 ≤ n)
    (bankWindowOverlapBefore ring seed pre) root hx hy hg hm
  have hbpos : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hpostFirstPack :
      ((bankWindowOverlapAfter ring seed pre root).1
        (ring.rightNeighbor root)).pack.val = 1 := by
    have hresp := bankWindowExactResponderPack ring
      (bankWindowOverlapBefore ring seed pre) root
      (clockNeighborDifferent ring (by omega : 2 ≤ n) root)
    rw [hresp, hx]
    simp [packNext, hbpos]
  refine ⟨hphysical.1, hghost.1, ?_, ?_⟩
  · intro limit hproto
    by_cases hzeroLimit : limit = 0
    · have hbad : ((bankWindowOverlapAfter ring seed pre root).1
          (ring.rightNeighbor root)).pack.val ≠ 1 := by
        have hh := hproto.2.2
        rw [hzeroLimit] at hh
        change ((bankWindowOverlapAfter ring seed pre root).1
          (ring.rightNeighbor root)).pack.val ≠ 1 at hh
        exact hh
      exact False.elim (hbad hpostFirstPack)
    · have hpositive : 1 ≤ limit := by omega
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro p o hactive _
        rw [hghost.1] at hactive
        cases hactive
      · intro hinherited
        rcases hinherited with ⟨atoms, hc, hnonempty⟩ |
          ⟨p, hc, horigin⟩
        · rw [hghost.1] at hc
          have heq : atoms = [] := by
            cases hc
            rfl
          exact False.elim (hnonempty heq)
        · rw [hghost.1] at hc
          cases hc
      · intro _
        refine ⟨(⟨0, hbpos⟩ :
          Fin (compileAdvice (ceilLogTwo n)).b),
          (by change 1 ≤ limit; exact hpositive),
          { service := (bankWindowOverlapBefore ring seed pre).2.service,
            root := root }, ?_, ?_, ?_, ?_⟩
        · change ((bankWindowOverlapAfter ring seed pre root).2.sites
            (ring.rightNeighbor root)).worker =
            .pending
              { service := (bankWindowOverlapBefore ring seed pre).2.service,
                root := root }
          exact hghost.2
        · change ((bankWindowOverlapAfter ring seed pre root).1
            (ring.rightNeighbor root)).tok = .RR
          exact hphysical.2.2
        · intro k hk
          have hbound : k.val + 1 ≤ 1 := by
            change k.val + 1 ≤ 0 + 1 at hk
            exact hk
          have hindex : k.val = 0 := by omega
          rw [hindex]
          change ((bankWindowOverlapAfter ring seed pre root).1
            (ring.rightNeighbor root)).bit = false
          exact hphysical.2.1
        · intro k hk
          have hbad : k.val < 0 := hk
          omega
      · intro _ hnotWait
        exact False.elim (hnotWait hphysical.1)
  · intro j _ _
    exact Or.inr ⟨hphysical.1, hghost.1⟩

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open Classical

set_option autoImplicit false
set_option Elab.async false

theorem bankWindowOverlapSelectedResponderNoPrefixOrphan
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (hx : ((bankWindowOverlapBefore ring seed pre).1 e).pack.val = 0) :
    (∀ limit : Nat,
      ¬ BankWindowProtoRun ring
        (bankWindowOverlapAfter ring seed pre e)
        (ring.rightNeighbor e) limit) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ¬ BankWindowOrphanOwner ring
        (bankWindowOverlapAfter ring seed pre e)
        (ring.rightNeighbor e) j) := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hresp := bankWindowExactResponderPack ring
    (bankWindowOverlapBefore ring seed pre) e
    (clockNeighborDifferent ring (by omega : 2 ≤ n) e)
  have hpack :
      ((bankWindowOverlapAfter ring seed pre e).1
        (ring.rightNeighbor e)).pack.val = 1 := by
    rw [hresp, hx]
    simp [packNext, hb]
  constructor
  · intro limit hproto
    have hzero := hproto.2.1 0 (by omega)
    change ((bankWindowOverlapAfter ring seed pre e).1
      (ring.rightNeighbor e)).pack.val = 0 at hzero
    omega
  · intro j horphan
    have hzero := horphan.1
    omega

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- A selected PACK-zero source cannot simultaneously carry the
tainted worker of another proto-prefix or orphan witness at its
foreign digit. The post edge is an actual extended run; its
ReceiptInv worker-band certificate, together with the literal
nonresponder PACK row, excludes that collision. Consumer:
group-13 PFX digit cleanliness and ORPH at the selected source. -/
theorem bankWindowOverlapSelectedRootIncidentPrefixOrphan
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (hx : ((bankWindowOverlapBefore ring seed pre).1 e).pack.val = 0)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (hsite : Counter.site ring root (j.val + 1) = e) :
    (∀ limit : Nat,
      BankWindowProtoRun ring
        (bankWindowOverlapAfter ring seed pre e) root limit →
      j.val + 1 ≤ limit →
      ¬ BankWindowTainted
        (bankWindowOverlapAfter ring seed pre e)
        (Counter.site ring root (j.val + 1))) ∧
    (BankWindowOrphanOwner ring
      (bankWindowOverlapAfter ring seed pre e) root j →
      BankWindowTainted
        (bankWindowOverlapAfter ring seed pre e)
        (Counter.site ring root (j.val + 1)) →
      ((bankWindowOverlapAfter ring seed pre e).1 root).mode =
        .RESET ∨
      (((bankWindowOverlapAfter ring seed pre e).1 root).mode =
          .RWAIT ∧
        ((bankWindowOverlapAfter ring seed pre e).2.sites
          root).controller = .waiting [])) := by
  have hdistinct : e ≠ ring.rightNeighbor e :=
    (clockNeighborDifferent ring (by omega : 2 ≤ n) e).symm
  have hfixed := bankWindowClosureRepairNonresponderPackFixed
    ring (by omega : 2 ≤ n)
    (bankWindowOverlapBefore ring seed pre) e e hdistinct
  have hpostZero :
      ((bankWindowOverlapAfter ring seed pre e).1 e).pack.val =
        0 := hfixed.trans hx
  have hrun :
      bankWindowOverlapBefore ring seed (pre ++ [e]) =
        bankWindowOverlapAfter ring seed pre e := by
    change rbRun ring (renewalBankStart ring seed) (pre ++ [e]) =
      renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e
    rw [rbRunAppend]
    rfl
  have hclean :
      ¬ BankWindowTainted
        (bankWindowOverlapAfter ring seed pre e) e := by
    intro ht
    have htRun :
        BankWindowTainted
          (bankWindowOverlapBefore ring seed (pre ++ [e])) e := by
      rw [hrun]
      exact ht
    have hband := bankWindowOverlapReachableTaintedInBand
      ring hn hbank seed (pre ++ [e]) e htRun
    have hpositive :
        1 ≤ ((bankWindowOverlapAfter ring seed pre e).1 e).pack.val := by
      have hraw := hband.1
      change 1 ≤ ((rbRun ring (renewalBankStart ring seed)
        (pre ++ [e])).1 e).pack.val at hraw
      rw [rbRunAppend] at hraw
      exact hraw
    omega
  have hslotClean :
      ¬ BankWindowTainted
        (bankWindowOverlapAfter ring seed pre e)
        (Counter.site ring root (j.val + 1)) := by
    rw [hsite]
    exact hclean
  constructor
  · intro limit _ _
    exact hslotClean
  · intro _ ht
    exact False.elim (hslotClean ht)

/-- For a complete OLD source window, every selected-root
BANK mode preserves completion at this real edge, excluding any
POST proto-run or orphan for that same root. Consumer:
group-13 PFX/ORPH selected-root complete branch. -/
theorem bankWindowOverlapSelectedCompleteSourceNoPrefixOrphan
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (root : Fin n)
    (hcomplete : Counter.Complete ring
      (bankWindowOverlapBefore ring seed pre).1 root) :
    (∀ limit : Nat,
      ¬ BankWindowProtoRun ring
        (bankWindowOverlapAfter ring seed pre root) root limit) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ¬ BankWindowOrphanOwner ring
        (bankWindowOverlapAfter ring seed pre root) root j) := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  exact bankWindowClosureInternalNoProtoOrphan
    ring hn (bankWindowOverlapBefore ring seed pre)
    root hcomplete 0 hb

/-- The literal changed-responder BANK row resets a PACK-zero
source when it is in RESET, either active phase, or an expiring
waiting phase. Consumer: the changed selected-root PFX/ORPH case. -/
theorem bankWindowOverlapChangedSourceExitMode
    {c : Compiled} (x y : Agent c)
    (hx : x.pack.val = 0)
    (hnotFirst : y.pack.val ≠ 1)
    (hphase :
      x.mode = .RESET ∨ x.mode = .ARMED ∨ x.mode = .CSTART ∨
      ((x.mode = .RWAIT ∨ x.mode = .IWAIT ∨ x.mode = .CWAIT) ∧
        x.lease.val ≤ 1)) :
    (Counter.resetBankOld x y).1.mode = .RESET := by
  have hb : 0 < c.b := by
    change 0 < c.s + 11
    omega
  have hpost : packNext x.pack.val y.pack.val c.b = 1 := by
    rw [hx]
    simp [packNext, hb]
  have hne : 1 ≠ y.pack.val := Ne.symm hnotFirst
  unfold Counter.resetBankOld
  rw [hpost]
  rcases hphase with hm | hm | hm | ⟨hw, hshort⟩
  · cases hg : x.grant <;>
      simp [bankPair, bankCell, hx, hnotFirst, hne, hm, hg,
        isWaitMode, Id.run_pure, Id.run_bind]
  · cases hg : x.grant <;>
      simp [bankPair, bankCell, hx, hnotFirst, hne, hm, hg,
        isWaitMode, Id.run_pure, Id.run_bind]
  · cases hg : x.grant <;>
      simp [bankPair, bankCell, hx, hnotFirst, hne, hm, hg,
        isWaitMode, Id.run_pure, Id.run_bind]
  · have hshortWait : ¬ 1 < x.lease.val := by omega
    rcases hw with hm | hm | hm
    · cases hg : x.grant <;>
        simp [bankPair, bankCell, hx, hnotFirst, hne, hm, hg,
          hshortWait, isWaitMode, Id.run_pure, Id.run_bind]
    · cases hg : x.grant <;>
        simp [bankPair, bankCell, hx, hnotFirst, hne, hm, hg,
          hshortWait, isWaitMode, Id.run_pure, Id.run_bind]
    · cases hg : x.grant <;>
        simp [bankPair, bankCell, hx, hnotFirst, hne, hm, hg,
          hshortWait, isWaitMode, Id.run_pure, Id.run_bind]

/-- An OLD incomplete source-root in RESET, ARMED, CSTART, or an
expiring RWAIT/IWAIT/CWAIT row with a changed first responder
cannot retain root authority. The actual BANK mode and OLD-J
POST frame discharge all four PFX clauses and ORPH for its
selected root. Consumer: group-13 selected source-root row. -/
theorem bankWindowOverlapChangedSourceExitPrefixOrphan
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (root : Fin n)
    (hJ : BankWindowExact ring
      (bankWindowOverlapBefore ring seed pre))
    (hroot :
      ((bankWindowOverlapBefore ring seed pre).1 root).pack.val = 0)
    (hchanged :
      packNext
        ((bankWindowOverlapBefore ring seed pre).1 root).pack.val
        ((bankWindowOverlapBefore ring seed pre).1
          (ring.rightNeighbor root)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor root)).pack.val)
    (hphase :
      ((bankWindowOverlapBefore ring seed pre).1 root).mode = .RESET ∨
      ((bankWindowOverlapBefore ring seed pre).1 root).mode = .ARMED ∨
      ((bankWindowOverlapBefore ring seed pre).1 root).mode = .CSTART ∨
      (((bankWindowOverlapBefore ring seed pre).1 root).mode = .RWAIT ∨
        ((bankWindowOverlapBefore ring seed pre).1 root).mode = .IWAIT ∨
        ((bankWindowOverlapBefore ring seed pre).1 root).mode = .CWAIT) ∧
      ((bankWindowOverlapBefore ring seed pre).1 root).lease.val ≤ 1) :
    ((bankWindowOverlapAfter ring seed pre root).1 root).mode =
      .RESET ∧
    ((bankWindowOverlapAfter ring seed pre root).2.sites root).controller =
      .empty ∧
    (∀ limit : Nat,
      BankWindowProtoRun ring
        (bankWindowOverlapAfter ring seed pre root) root limit →
      (∀ p o,
        ((bankWindowOverlapAfter ring seed pre root).2.sites
          root).controller = .active p →
        p.origin = some o → False) ∧
      (BankWindowInheritedController
        (bankWindowOverlapAfter ring seed pre root) root →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted
            (bankWindowOverlapAfter ring seed pre root)
            (Counter.site ring root (j.val + 1))) ∧
      ((((bankWindowOverlapAfter ring seed pre root).1 root).mode =
          .RWAIT ∧
          ((bankWindowOverlapAfter ring seed pre root).2.sites
            root).controller = .waiting []) →
        ∃ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit ∧
          ∃ rho : RenewalBankReceipt n,
            ((bankWindowOverlapAfter ring seed pre root).2.sites
              (Counter.site ring root (j.val + 1))).worker =
              .pending rho ∧
            ((bankWindowOverlapAfter ring seed pre root).1
              (Counter.site ring root (j.val + 1))).tok = .RR ∧
            bankWindowZeroPrefix ring
              (bankWindowOverlapAfter ring seed pre root)
              root (j.val + 1) ∧
            (∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
              k.val < j.val →
              ((bankWindowOverlapAfter ring seed pre root).1
                (Counter.site ring root (k.val + 1))).tok = .E)) ∧
      (((bankWindowOverlapAfter ring seed pre root).1 root).mode
          ≠ .RESET →
        ((bankWindowOverlapAfter ring seed pre root).1 root).mode
          ≠ .RWAIT →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted
            (bankWindowOverlapAfter ring seed pre root)
            (Counter.site ring root (j.val + 1)))) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowOrphanOwner ring
        (bankWindowOverlapAfter ring seed pre root) root j →
      BankWindowTainted
        (bankWindowOverlapAfter ring seed pre root)
        (Counter.site ring root (j.val + 1)) →
      ((bankWindowOverlapAfter ring seed pre root).1 root).mode =
        .RESET ∨
      (((bankWindowOverlapAfter ring seed pre root).1 root).mode =
          .RWAIT ∧
        ((bankWindowOverlapAfter ring seed pre root).2.sites
          root).controller = .waiting [])) := by
  have hbpos : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hpostOne :
      packNext
        ((bankWindowOverlapBefore ring seed pre).1 root).pack.val
        ((bankWindowOverlapBefore ring seed pre).1
          (ring.rightNeighbor root)).pack.val
        (compileAdvice (ceilLogTwo n)).b = 1 := by
    rw [hroot]
    simp [packNext, hbpos]
  have hnotFirst :
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor root)).pack.val ≠ 1 := by
    intro hfirst
    exact hchanged (hpostOne.trans hfirst.symm)
  have hraw := bankWindowOverlapChangedSourceExitMode
    ((bankWindowOverlapBefore ring seed pre).1 root)
    ((bankWindowOverlapBefore ring seed pre).1
      (ring.rightNeighbor root))
    hroot hnotFirst hphase
  have htrip := (bankWindowClosureSelectedBankTrip
    ring hn hbank (bankWindowOverlapBefore ring seed pre) root).1
  have hmode := congrArg
    (fun t : Mode × Bool × BTok => t.1) htrip
  change ((bankWindowOverlapAfter ring seed pre root).1 root).mode =
    (Counter.resetBankOld
      ((bankWindowOverlapBefore ring seed pre).1 root)
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor root))).1.mode at hmode
  have hreset :
      ((bankWindowOverlapAfter ring seed pre root).1 root).mode =
        .RESET := hmode.trans hraw
  have hsourcePack := bankWindowClosureRepairNonresponderPackFixed
    ring (by omega : 2 ≤ n)
    (bankWindowOverlapBefore ring seed pre) root root
    (clockNeighborDifferent ring (by omega : 2 ≤ n) root).symm
  have hpostPack :
      ((bankWindowOverlapAfter ring seed pre root).1 root).pack.val =
        0 := hsourcePack.trans hroot
  have hframe := bankWindowExactFrameStep
    ring hn hbank seed pre root hJ
  have hfields := bankWindowIncomingResetOwnerFields ring
    (bankWindowOverlapBefore ring seed pre) root root
    hpostPack hreset hframe
  exact ⟨hreset, hfields.1, hfields.2.2.1, hfields.2.2.2⟩

/-- ReceiptInv of the actual extended run pins the root of
every post-step pending or originated worker at an aligned
physical digit. A distinct foreign root cannot own such a
carrier, even when this digit is one of the selected sites.
Consumer: PFX/ORPH foreign worker collision decomposition. -/
theorem bankWindowOverlapPostAlignedForeignWorkerExcluded
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e site root foreign : Fin n) (k : Nat)
    (hpositive : 1 ≤ k)
    (hbound : k ≤ (compileAdvice (ceilLogTwo n)).b)
    (hsite : site = Counter.site ring root k)
    (hrole :
      ((bankWindowOverlapAfter ring seed pre e).1 site).pack.val = k)
    (hne : root ≠ foreign) :
    (∀ rho : RenewalBankReceipt n,
      ((bankWindowOverlapAfter ring seed pre e).2.sites site).worker =
        .pending rho → rho.root ≠ foreign) ∧
    (∀ (p : RenewalBankPayload n) (o : RenewalBankOrigin n),
      ((bankWindowOverlapAfter ring seed pre e).2.sites site).worker =
        .payload p → p.origin = some o → o.root ≠ foreign) := by
  have hreceipt := bankWindowOverlapPostReceipt
    ring hn hbank seed pre e
  have hown := bankWindowOverlapAlignedCarrierOwnRoot
    ring seed (pre ++ [e])
    (bankWindowOverlapAfter ring seed pre e) hreceipt
    root site k hpositive hbound hsite hrole
  constructor
  · intro rho hw hf
    exact hne ((hown.1 rho hw).symm.trans hf)
  · intro p o hw ho hf
    exact hne ((hown.2 p o hw ho).symm.trans hf)

/-- A physical PACK change erases the responder's ghost
worker. Thus a foreign digit colliding with that selected
responder is clean in any POST proto prefix and cannot be
the tainted orphan. Consumer: group-13 changed-responder
foreign PFX/ORPH collision. -/
theorem bankWindowOverlapChangedResponderForeignSlotClean
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (hchanged :
      packNext
        ((bankWindowOverlapBefore ring seed pre).1 e).pack.val
        ((bankWindowOverlapBefore ring seed pre).1
          (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor e)).pack.val)
    (hsite :
      Counter.site ring root (j.val + 1) = ring.rightNeighbor e) :
    ¬ BankWindowTainted
        (bankWindowOverlapAfter ring seed pre e)
        (Counter.site ring root (j.val + 1)) ∧
    (∀ limit : Nat,
      BankWindowProtoRun ring
        (bankWindowOverlapAfter ring seed pre e) root limit →
      j.val + 1 ≤ limit →
      ¬ BankWindowTainted
        (bankWindowOverlapAfter ring seed pre e)
        (Counter.site ring root (j.val + 1))) ∧
    (BankWindowOrphanOwner ring
      (bankWindowOverlapAfter ring seed pre e) root j →
      BankWindowTainted
        (bankWindowOverlapAfter ring seed pre e)
        (Counter.site ring root (j.val + 1)) →
      ((bankWindowOverlapAfter ring seed pre e).1 root).mode =
        .RESET ∨
      (((bankWindowOverlapAfter ring seed pre e).1 root).mode =
          .RWAIT ∧
        ((bankWindowOverlapAfter ring seed pre e).2.sites
          root).controller = .waiting [])) := by
  have hclean := (bankWindowClosureChangedDigitClean
    ring hn hbank (bankWindowOverlapBefore ring seed pre)
    e hchanged).2.2.2.1
  have hslot :
      ¬ BankWindowTainted
        (bankWindowOverlapAfter ring seed pre e)
        (Counter.site ring root (j.val + 1)) := by
    rw [hsite]
    exact hclean
  refine ⟨hslot, ?_, ?_⟩
  · intro limit _ _
    exact hslot
  · intro _ ht
    exact False.elim (hslot ht)

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- An actually misaligned OLD first digit makes the PACK-zero
root a proto-owner at limit zero. OLD J.proto therefore forbids
an empty RWAIT controller at that root. Consumer: changed
source-root long-wait PFX witness and orphan exclusion. -/
theorem bankWindowOverlapBrokenRootNoEmptyWaiting
    {n : Nat} (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (root : Fin n)
    (hJ : BankWindowExact ring (bankWindowOverlapBefore ring seed pre))
    (hx : ((bankWindowOverlapBefore ring seed pre).1 root).pack.val = 0)
    (hwrong : ((bankWindowOverlapBefore ring seed pre).1
      (ring.rightNeighbor root)).pack.val ≠ 1) :
    ¬ (((bankWindowOverlapBefore ring seed pre).1 root).mode = .RWAIT ∧
      ((bankWindowOverlapBefore ring seed pre).2.sites root).controller = .waiting []) := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hproto : BankWindowProtoRun ring
      (bankWindowOverlapBefore ring seed pre) root 0 := by
    refine ⟨hb, ?_, ?_⟩
    · intro k hk
      have hz : k = 0 := by omega
      rw [hz]
      change ((bankWindowOverlapBefore ring seed pre).1 root).pack.val = 0
      exact hx
    · change ((bankWindowOverlapBefore ring seed pre).1
          (ring.rightNeighbor root)).pack.val ≠ 1
      exact hwrong
  intro hwaiting
  obtain ⟨j, hj, rho, hworker, htok, hzero, hearlier⟩ :=
    (hJ.proto root 0 hproto).2.2.1 hwaiting
  omega

/-- Every OLD aligned physical digit beyond a broken first digit
is free of tainted workers whenever the root is not RESET.
Otherwise that digit is an OLD orphan, and OLD J.orphan would
force RESET or the empty RWAIT state ruled out by J.proto at
zero. Consumer: changed-root PFX/ORPH incident sector. -/
theorem bankWindowOverlapBrokenRootOldAlignedClean
    {n : Nat} (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (root : Fin n)
    (hJ : BankWindowExact ring (bankWindowOverlapBefore ring seed pre))
    (hx : ((bankWindowOverlapBefore ring seed pre).1 root).pack.val = 0)
    (hwrong : ((bankWindowOverlapBefore ring seed pre).1
      (ring.rightNeighbor root)).pack.val ≠ 1)
    (hnotReset : ((bankWindowOverlapBefore ring seed pre).1 root).mode ≠ .RESET)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (haligned : ((bankWindowOverlapBefore ring seed pre).1
      (Counter.site ring root (j.val + 1))).pack.val =
        j.val + 1) :
    ¬ BankWindowTainted (bankWindowOverlapBefore ring seed pre)
      (Counter.site ring root (j.val + 1)) := by
  intro htainted
  have howner : BankWindowOrphanOwner ring
      (bankWindowOverlapBefore ring seed pre) root j := by
    refine ⟨hx, haligned, ?_⟩
    intro hprefix
    have hfirst := hprefix 1 (by omega)
    change ((bankWindowOverlapBefore ring seed pre).1
      (ring.rightNeighbor root)).pack.val = 1 at hfirst
    exact hwrong hfirst
  have hnoEmpty := bankWindowOverlapBrokenRootNoEmptyWaiting
    ring seed pre root hJ hx hwrong
  rcases hJ.orphan root j howner htainted with
    hreset | hwait
  · exact hnotReset hreset
  · exact hnoEmpty hwait

/-- The changed physical responder is untainted, and every
other newly aligned digit with a non-RESET OLD source-root
would have been a forbidden OLD orphan. Consumer: both
PFX cleanliness clauses and the ORPH taint antecedent. -/
theorem bankWindowOverlapChangedRootAlignedClean
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (root : Fin n)
    (hJ : BankWindowExact ring (bankWindowOverlapBefore ring seed pre))
    (hx : ((bankWindowOverlapBefore ring seed pre).1 root).pack.val = 0)
    (hwrong : ((bankWindowOverlapBefore ring seed pre).1
      (ring.rightNeighbor root)).pack.val ≠ 1)
    (hnotReset : ((bankWindowOverlapBefore ring seed pre).1 root).mode ≠ .RESET)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (hpostAligned : ((bankWindowOverlapAfter ring seed pre root).1
      (Counter.site ring root (j.val + 1))).pack.val =
        j.val + 1) :
    ¬ BankWindowTainted (bankWindowOverlapAfter ring seed pre root)
      (Counter.site ring root (j.val + 1)) := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hpostOne :
      packNext ((bankWindowOverlapBefore ring seed pre).1 root).pack.val
        ((bankWindowOverlapBefore ring seed pre).1
          (ring.rightNeighbor root)).pack.val
        (compileAdvice (ceilLogTwo n)).b = 1 := by
    rw [hx]
    simp [packNext, hb]
  have hchanged :
      packNext ((bankWindowOverlapBefore ring seed pre).1 root).pack.val
        ((bankWindowOverlapBefore ring seed pre).1
          (ring.rightNeighbor root)).pack.val
        (compileAdvice (ceilLogTwo n)).b ≠
      ((bankWindowOverlapBefore ring seed pre).1
        (ring.rightNeighbor root)).pack.val := by
    intro h
    exact hwrong (h.symm.trans hpostOne)
  have hcleanResponder := (bankWindowClosureChangedDigitClean
    ring hn hbank (bankWindowOverlapBefore ring seed pre) root hchanged).2.2.2.1
  intro htainted
  by_cases hfirst : j.val = 0
  · have hsite : Counter.site ring root (j.val + 1) =
        ring.rightNeighbor root := by
      rw [hfirst]
      rfl
    rw [hsite] at htainted
    exact hcleanResponder htainted
  · have hindex : 1 ≤ j.val := by omega
    have hbound : j.val + 1 ≤
        (compileAdvice (ceilLogTwo n)).b + 1 := by
      have := j.isLt
      omega
    have hsourceNe :
        Counter.site ring root (j.val + 1) ≠ root := by
      have h := bankWindowIncidenceSiteDistinct
        ring hbank root 0 (j.val + 1)
        (by omega) hbound
      change root ≠ Counter.site ring root (j.val + 1) at h
      exact h.symm
    have htargetNe :
        Counter.site ring root (j.val + 1) ≠
          ring.rightNeighbor root := by
      have h := bankWindowIncidenceSiteDistinct
        ring hbank root 1 (j.val + 1)
        (by omega) hbound
      change ring.rightNeighbor root ≠
        Counter.site ring root (j.val + 1) at h
      exact h.symm
    have hf := bankWindowExactOffPairFrame ring
      (bankWindowOverlapBefore ring seed pre) root
      (Counter.site ring root (j.val + 1))
      hsourceNe htargetNe
    have hphysical := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
        a.pack.val) hf.1
    have holdAligned :
        ((bankWindowOverlapBefore ring seed pre).1
          (Counter.site ring root (j.val + 1))).pack.val =
            j.val + 1 :=
      hphysical.symm.trans hpostAligned
    have hworker := congrArg
      (fun s : RenewalBankSite n => s.worker) hf.2
    have holdTainted : BankWindowTainted
        (bankWindowOverlapBefore ring seed pre)
        (Counter.site ring root (j.val + 1)) := by
      unfold BankWindowTainted at htainted ⊢
      rw [hworker] at htainted
      exact htainted
    exact (bankWindowOverlapBrokenRootOldAlignedClean
      ring seed pre root hJ hx hwrong
      hnotReset j holdAligned) holdTainted

theorem bankWindowOverlapSourceRootSamePortReadSets
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (root : Fin n)
    (hx : ((bankWindowOverlapBefore ring seed pre).1 root).pack.val = 0)
    (hy : ((bankWindowOverlapBefore ring seed pre).1
      (ring.rightNeighbor root)).pack.val = 1)
    (hmode : ((bankWindowOverlapAfter ring seed pre root).1 root).mode =
      ((bankWindowOverlapBefore ring seed pre).1 root).mode)
    (hcontroller : ((bankWindowOverlapAfter ring seed pre root).2.sites root).controller =
      ((bankWindowOverlapBefore ring seed pre).2.sites root).controller)
    (hfirstBit : ((bankWindowOverlapAfter ring seed pre root).1
      (ring.rightNeighbor root)).bit =
      ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).bit)
    (hfirstTok : ((bankWindowOverlapAfter ring seed pre root).1
      (ring.rightNeighbor root)).tok =
      ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).tok)
    (hfirstWorker : ((bankWindowOverlapAfter ring seed pre root).2.sites
      (ring.rightNeighbor root)).worker =
      ((bankWindowOverlapBefore ring seed pre).2.sites
        (ring.rightNeighbor root)).worker) :
    (∀ limit : Nat,
      BankWindowProtoRun ring (bankWindowOverlapAfter ring seed pre root) root limit →
      bankWindowProtoReadSet ring (bankWindowOverlapBefore ring seed pre)
        (bankWindowOverlapAfter ring seed pre root) root limit) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      bankWindowOrphanReadSet ring (bankWindowOverlapBefore ring seed pre)
        (bankWindowOverlapAfter ring seed pre root) root j) := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hsourcePack := bankWindowClosureRepairNonresponderPackFixed
    ring (by omega : 2 ≤ n)
    (bankWindowOverlapBefore ring seed pre) root root
    (clockNeighborDifferent ring (by omega : 2 ≤ n) root).symm
  have hresponderStep := bankWindowExactResponderPack ring
    (bankWindowOverlapBefore ring seed pre) root
    (clockNeighborDifferent ring (by omega : 2 ≤ n) root)
  have htargetPack :
      ((bankWindowOverlapAfter ring seed pre root).1 (ring.rightNeighbor root)).pack.val =
      ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).pack.val := by
    rw [hresponderStep, hx, hy]
    simp [packNext, hb]
  have hpack :
      bankWindowReadPackPrefix ring (bankWindowOverlapBefore ring seed pre)
        (bankWindowOverlapAfter ring seed pre root) root
        ((compileAdvice (ceilLogTwo n)).b + 1) := by
    intro k hk
    by_cases hz : k = 0
    · rw [hz]
      change ((bankWindowOverlapAfter ring seed pre root).1 root).pack.val =
        ((bankWindowOverlapBefore ring seed pre).1 root).pack.val
      exact hsourcePack
    · by_cases ho : k = 1
      · rw [ho]
        change ((bankWindowOverlapAfter ring seed pre root).1
          (ring.rightNeighbor root)).pack.val =
          ((bankWindowOverlapBefore ring seed pre).1
            (ring.rightNeighbor root)).pack.val
        exact htargetPack
      · have hpos : 2 ≤ k := by omega
        have hsrc :
            Counter.site ring root k ≠ root := by
          have h := bankWindowIncidenceSiteDistinct
            ring hbank root 0 k (by omega) hk
          change root ≠ Counter.site ring root k at h
          exact h.symm
        have hdst :
            Counter.site ring root k ≠
              ring.rightNeighbor root := by
          have h := bankWindowIncidenceSiteDistinct
            ring hbank root 1 k (by omega) hk
          change ring.rightNeighbor root ≠
            Counter.site ring root k at h
          exact h.symm
        exact congrArg
          (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
            a.pack.val)
          (bankWindowExactOffPairFrame ring
            (bankWindowOverlapBefore ring seed pre) root
            (Counter.site ring root k) hsrc hdst).1
  have hslots :
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      bankWindowReadTok (bankWindowOverlapBefore ring seed pre) (bankWindowOverlapAfter ring seed pre root)
        (Counter.site ring root (j.val + 1)) ∧
      bankWindowReadBit (bankWindowOverlapBefore ring seed pre) (bankWindowOverlapAfter ring seed pre root)
        (Counter.site ring root (j.val + 1)) ∧
      bankWindowReadWorker (bankWindowOverlapBefore ring seed pre) (bankWindowOverlapAfter ring seed pre root)
        (Counter.site ring root (j.val + 1)) := by
    intro j
    by_cases hz : j.val = 0
    · rw [hz]
      change
        ((bankWindowOverlapAfter ring seed pre root).1 (ring.rightNeighbor root)).tok =
          ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).tok ∧
        ((bankWindowOverlapAfter ring seed pre root).1 (ring.rightNeighbor root)).bit =
          ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).bit ∧
        ((bankWindowOverlapAfter ring seed pre root).2.sites (ring.rightNeighbor root)).worker =
          ((bankWindowOverlapBefore ring seed pre).2.sites (ring.rightNeighbor root)).worker
      exact ⟨hfirstTok, hfirstBit, hfirstWorker⟩
    · have hbound : j.val + 1 ≤
          (compileAdvice (ceilLogTwo n)).b + 1 := by
        have hj := j.isLt
        omega
      have hsrc :
          Counter.site ring root (j.val + 1) ≠ root := by
        have h := bankWindowIncidenceSiteDistinct ring hbank
          root 0 (j.val + 1) (by omega) hbound
        change root ≠ Counter.site ring root (j.val + 1) at h
        exact h.symm
      have hdst :
          Counter.site ring root (j.val + 1) ≠
            ring.rightNeighbor root := by
        have h := bankWindowIncidenceSiteDistinct ring hbank
          root 1 (j.val + 1) (by omega) hbound
        change ring.rightNeighbor root ≠
          Counter.site ring root (j.val + 1) at h
        exact h.symm
      have hf := bankWindowExactOffPairFrame ring
        (bankWindowOverlapBefore ring seed pre) root
        (Counter.site ring root (j.val + 1)) hsrc hdst
      exact ⟨congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok) hf.1,
        congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.bit) hf.1,
        congrArg
        (fun s : RenewalBankSite n => s.worker) hf.2⟩
  constructor
  · intro limit hproto
    refine ⟨?_, hmode, hcontroller, ?_⟩
    · intro k hk
      exact hpack k (by have hl := hproto.1; omega)
    · intro j hj
      exact hslots j
  · intro j
    refine ⟨?_, hmode, hcontroller, (hslots j).2.2⟩
    intro k hk
    have hj := j.isLt
    exact hpack k (by omega)

theorem bankWindowOverlapAlignedNonrootPairCustody
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n) (k : Nat)
    (hsource : e = Counter.site ring root k)
    (hk : 1 ≤ k)
    (hbelow : k < (compileAdvice (ceilLogTwo n)).b)
    (hx : ((bankWindowOverlapBefore ring seed pre).1 e).pack.val = k)
    (hy : ((bankWindowOverlapBefore ring seed pre).1
      (ring.rightNeighbor e)).pack.val = k + 1) :
    (∀ rho : RenewalBankReceipt n,
      ((bankWindowOverlapBefore ring seed pre).2.sites e).worker =
        .pending rho → rho.root = root) ∧
    (∀ (p : RenewalBankPayload n) (o : RenewalBankOrigin n),
      ((bankWindowOverlapBefore ring seed pre).2.sites e).worker = .payload p →
      p.origin = some o → o.root = root) ∧
    (∀ rho : RenewalBankReceipt n,
      ((bankWindowOverlapBefore ring seed pre).2.sites
        (ring.rightNeighbor e)).worker = .pending rho →
      rho.root = root) ∧
    (∀ (p : RenewalBankPayload n) (o : RenewalBankOrigin n),
      ((bankWindowOverlapBefore ring seed pre).2.sites
        (ring.rightNeighbor e)).worker = .payload p →
      p.origin = some o → o.root = root) ∧
    (∀ rho : RenewalBankReceipt n,
      ((bankWindowOverlapAfter ring seed pre e).2.sites e).worker = .pending rho →
      rho.root = root) ∧
    (∀ (p : RenewalBankPayload n) (o : RenewalBankOrigin n),
      ((bankWindowOverlapAfter ring seed pre e).2.sites e).worker = .payload p →
      p.origin = some o → o.root = root) ∧
    (∀ rho : RenewalBankReceipt n,
      ((bankWindowOverlapAfter ring seed pre e).2.sites
        (ring.rightNeighbor e)).worker = .pending rho →
      rho.root = root) ∧
    (∀ (p : RenewalBankPayload n) (o : RenewalBankOrigin n),
      ((bankWindowOverlapAfter ring seed pre e).2.sites
        (ring.rightNeighbor e)).worker = .payload p →
      p.origin = some o → o.root = root) := by
  have htargetSite :
      ring.rightNeighbor e =
        Counter.site ring root (k + 1) := by
    rw [hsource]
    rfl
  have hpostSource := bankWindowClosureRepairNonresponderPackFixed
    ring (by omega : 2 ≤ n)
    (bankWindowOverlapBefore ring seed pre) e e
    (clockNeighborDifferent ring (by omega : 2 ≤ n) e).symm
  have hpostSourceRole :
      ((bankWindowOverlapAfter ring seed pre e).1 e).pack.val = k :=
    hpostSource.trans hx
  have hresp := bankWindowExactResponderPack ring
    (bankWindowOverlapBefore ring seed pre) e
    (clockNeighborDifferent ring (by omega : 2 ≤ n) e)
  have hpostTargetRole :
      ((bankWindowOverlapAfter ring seed pre e).1 (ring.rightNeighbor e)).pack.val =
        k + 1 := by
    rw [hresp, hx]
    simp [packNext, hbelow]
  have hpreReceipt := rbReceiptInvBankWordOfInv
    ring (by omega : 2 ≤ n) seed hbank pre
  have hpostReceipt := bankWindowOverlapPostReceipt
    ring hn hbank seed pre e
  have hsourceOld := bankWindowOverlapAlignedCarrierOwnRoot
    ring seed pre (bankWindowOverlapBefore ring seed pre) hpreReceipt
    root e k hk (by omega) hsource hx
  have htargetOld := bankWindowOverlapAlignedCarrierOwnRoot
    ring seed pre (bankWindowOverlapBefore ring seed pre) hpreReceipt
    root (ring.rightNeighbor e) (k + 1)
    (by omega) (by omega) htargetSite hy
  have hsourceNew := bankWindowOverlapAlignedCarrierOwnRoot
    ring seed (pre ++ [e]) (bankWindowOverlapAfter ring seed pre e) hpostReceipt
    root e k hk (by omega) hsource hpostSourceRole
  have htargetNew := bankWindowOverlapAlignedCarrierOwnRoot
    ring seed (pre ++ [e]) (bankWindowOverlapAfter ring seed pre e) hpostReceipt
    root (ring.rightNeighbor e) (k + 1)
    (by omega) (by omega) htargetSite hpostTargetRole
  exact ⟨hsourceOld.1, hsourceOld.2,
    htargetOld.1, htargetOld.2,
    hsourceNew.1, hsourceNew.2,
    htargetNew.1, htargetNew.2⟩

/-- At an OLD proto-run interior digit pair, inherited
authority or a non-RESET/non-RWAIT phase makes both
selected endpoints clean by OLD J.proto. The real
nonroot BANK row cannot mint taint at either endpoint
without an OLD tainted preimage. Consumer: group-13
foreign PFX worker-collision and old-clean sector split. -/
theorem bankWindowOverlapOldProtoInteriorPairTaintExcluded
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e root : Fin n) (k limit : Nat)
    (hJ : BankWindowExact ring (bankWindowOverlapBefore ring seed pre))
    (hsource : e = Counter.site ring root k)
    (hk : 1 ≤ k) (hinterior : k + 1 ≤ limit)
    (hproto : BankWindowProtoRun ring
      (bankWindowOverlapBefore ring seed pre) root limit)
    (hguard :
      BankWindowInheritedController (bankWindowOverlapBefore ring seed pre) root ∨
      (((bankWindowOverlapBefore ring seed pre).1 root).mode ≠ .RESET ∧
        ((bankWindowOverlapBefore ring seed pre).1 root).mode ≠ .RWAIT)) :
    ¬ BankWindowTainted (bankWindowOverlapAfter ring seed pre e) e ∧
    ¬ BankWindowTainted (bankWindowOverlapAfter ring seed pre e)
      (ring.rightNeighbor e) := by
  have hclean :
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        j.val + 1 ≤ limit →
        ¬ BankWindowTainted (bankWindowOverlapBefore ring seed pre)
          (Counter.site ring root (j.val + 1)) := by
    rcases hguard with hi | hm
    · exact (hJ.proto root limit hproto).2.1 hi
    · exact (hJ.proto root limit hproto).2.2.2
        hm.1 hm.2
  have hsourceRole :
      ((bankWindowOverlapBefore ring seed pre).1 e).pack.val = k := by
    have hp := hproto.2.1 k (by omega)
    rw [← hsource] at hp
    exact hp
  have hnonroot :
      ((bankWindowOverlapBefore ring seed pre).1 e).pack.val ≠ 0 := by
    rw [hsourceRole]
    omega
  have hsourceIndex :
      k - 1 < (compileAdvice (ceilLogTwo n)).b := by
    have hl := hproto.1
    omega
  have hsourceBound :
      (⟨k - 1, hsourceIndex⟩ :
        Fin (compileAdvice (ceilLogTwo n)).b).val + 1 ≤
        limit := by
    change k - 1 + 1 ≤ limit
    omega
  have hsourceClean :
      ¬ BankWindowTainted (bankWindowOverlapBefore ring seed pre) e := by
    have hc := hclean
      (⟨k - 1, hsourceIndex⟩ :
        Fin (compileAdvice (ceilLogTwo n)).b)
      hsourceBound
    change ¬ BankWindowTainted (bankWindowOverlapBefore ring seed pre)
      (Counter.site ring root (k - 1 + 1)) at hc
    have heq : k - 1 + 1 = k := by omega
    rw [heq, ← hsource] at hc
    exact hc
  have htargetSite :
      ring.rightNeighbor e =
        Counter.site ring root (k + 1) := by
    rw [hsource]
    rfl
  have htargetIndex :
      k < (compileAdvice (ceilLogTwo n)).b := by
    have hl := hproto.1
    omega
  have htargetClean :
      ¬ BankWindowTainted (bankWindowOverlapBefore ring seed pre)
        (ring.rightNeighbor e) := by
    have hc := hclean
      (⟨k, htargetIndex⟩ :
        Fin (compileAdvice (ceilLogTwo n)).b)
      (by change k + 1 ≤ limit; exact hinterior)
    change ¬ BankWindowTainted (bankWindowOverlapBefore ring seed pre)
      (Counter.site ring root (k + 1)) at hc
    rw [← htargetSite] at hc
    exact hc
  constructor
  · intro htainted
    rcases bankWindowOverlapNonrootPairTaintPreimage
      ring (by omega : 2 ≤ n)
      (bankWindowOverlapBefore ring seed pre) e e hnonroot
      (Or.inl rfl) htainted with
      hsrc | hdst
    · exact hsourceClean hsrc
    · exact htargetClean hdst
  · intro htainted
    rcases bankWindowOverlapNonrootPairTaintPreimage
      ring (by omega : 2 ≤ n)
      (bankWindowOverlapBefore ring seed pre) e (ring.rightNeighbor e) hnonroot
      (Or.inr rfl) htainted with
      hsrc | hdst
    · exact hsourceClean hsrc
    · exact htargetClean hdst

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Consumer: group-13 PFX/ORPH real-run row; bankWindowOverlapChangedLongWaitPair. -/
theorem bankWindowOverlapChangedLongWaitPair
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (root dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = 0) (hwrong : y.pack.val ≠ 1)
    (hg : x.grant = false)
    (hphase : x.mode = .RWAIT ∨ x.mode = .IWAIT ∨
      x.mode = .CWAIT)
    (hlong : 1 < x.lease.val) :
    (Counter.resetBankOld x y).1.mode = x.mode ∧
    (renewalBankPairMemory c m root dest x y).1.controller =
      (m.sites root).controller := by
  have hb : 0 < c.b := by
    change 0 < c.s + 11
    omega
  have hbNotZero : c.b ≠ 0 := by omega
  have hbAtLeastOne : 1 ≤ c.b := by omega
  have hfirstNot : (1 : Nat) ≠ y.pack.val := by
    intro hfirst
    exact hwrong hfirst.symm
  have hpost : packNext x.pack.val y.pack.val c.b = 1 := by
    rw [hx]
    simp [packNext, hb]
  have hpostZero : packNext 0 y.pack.val c.b = 1 := by
    simp [packNext, hb]
  rcases hphase with hm | hm | hm
  · constructor
    · unfold Counter.resetBankOld
      rw [hpost]
      simp [bankPair, bankCell, hx, hg, hm, hlong,
        hbAtLeastOne, isWaitMode, Id.run_pure, Id.run_bind] <;>
        simp only [if_neg hfirstNot, if_neg hwrong,
          if_neg hbNotZero, if_true, Id.run_pure] <;> rfl
    · simp [renewalBankPairMemory, renewalBankWaitSlot,
        bankCell, hx, hg, hm, hlong, hpostZero,
        hbAtLeastOne, isWaitMode, Id.run_pure, Id.run_bind] <;>
        simp only [hpostZero, if_neg hfirstNot, if_neg hwrong,
          if_neg hbNotZero, if_true, Id.run_pure] <;>
        simp [renewalBankWaitSlot, hm, hlong, isWaitMode]
  · constructor
    · unfold Counter.resetBankOld
      rw [hpost]
      simp [bankPair, bankCell, hx, hg, hm, hlong,
        hbAtLeastOne, isWaitMode, Id.run_pure, Id.run_bind] <;>
        simp only [if_neg hfirstNot, if_neg hwrong,
          if_neg hbNotZero, if_true, Id.run_pure] <;> rfl
    · simp [renewalBankPairMemory, renewalBankWaitSlot,
        bankCell, hx, hg, hm, hlong, hpostZero,
        hbAtLeastOne, isWaitMode, Id.run_pure, Id.run_bind] <;>
        simp only [hpostZero, if_neg hfirstNot, if_neg hwrong,
          if_neg hbNotZero, if_true, Id.run_pure] <;>
        simp [renewalBankWaitSlot, hm, hlong, isWaitMode]
  · constructor
    · unfold Counter.resetBankOld
      rw [hpost]
      simp [bankPair, bankCell, hx, hg, hm, hlong,
        hbAtLeastOne, isWaitMode, Id.run_pure, Id.run_bind] <;>
        simp only [if_neg hfirstNot, if_neg hwrong,
          if_neg hbNotZero, if_true, Id.run_pure] <;> rfl
    · simp [renewalBankPairMemory, renewalBankWaitSlot,
        bankCell, hx, hg, hm, hlong, hpostZero,
        hbAtLeastOne, isWaitMode, Id.run_pure, Id.run_bind] <;>
        simp only [hpostZero, if_neg hfirstNot, if_neg hwrong,
          if_neg hbNotZero, if_true, Id.run_pure] <;>
        simp [renewalBankWaitSlot, hm, hlong, isWaitMode]

/-- Consumer: group-13 PFX/ORPH real-run row; bankWindowOverlapChangedLongWaitFields. -/
theorem bankWindowOverlapChangedLongWaitFields
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (root : Fin n)
    (hx : ((bankWindowOverlapBefore ring seed pre).1 root).pack.val = 0)
    (hwrong : ((bankWindowOverlapBefore ring seed pre).1
      (ring.rightNeighbor root)).pack.val ≠ 1)
    (hg : ((bankWindowOverlapBefore ring seed pre).1 root).grant = false)
    (hphase : ((bankWindowOverlapBefore ring seed pre).1 root).mode = .RWAIT ∨
      ((bankWindowOverlapBefore ring seed pre).1 root).mode = .IWAIT ∨
      ((bankWindowOverlapBefore ring seed pre).1 root).mode = .CWAIT)
    (hlong : 1 < ((bankWindowOverlapBefore ring seed pre).1 root).lease.val) :
    ((bankWindowOverlapAfter ring seed pre root).1 root).mode =
      ((bankWindowOverlapBefore ring seed pre).1 root).mode ∧
    ((bankWindowOverlapAfter ring seed pre root).2.sites root).controller =
      ((bankWindowOverlapBefore ring seed pre).2.sites root).controller := by
  have hlocal := bankWindowOverlapChangedLongWaitPair
    (compileAdvice (ceilLogTwo n))
    ((bankWindowOverlapBefore ring seed pre).2) root
    (ring.rightNeighbor root)
    ((bankWindowOverlapBefore ring seed pre).1 root)
    ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root))
    hx hwrong hg hphase hlong
  have htrip := (bankWindowClosureSelectedBankTrip
    ring hn hbank (bankWindowOverlapBefore ring seed pre) root).1
  have hm := congrArg
    (fun t : Mode × Bool × BTok => t.1) htrip
  change ((bankWindowOverlapAfter ring seed pre root).1 root).mode =
    (Counter.resetBankOld
      ((bankWindowOverlapBefore ring seed pre).1 root)
      ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root))).1.mode at hm
  have hframe := (rbReferenceSelectedPairFrame ring
    (by omega : 2 ≤ n) (bankWindowOverlapBefore ring seed pre) root).2.2.1
  have hc := congrArg
    (fun s : RenewalBankSite n => s.controller) hframe
  change ((bankWindowOverlapAfter ring seed pre root).2.sites root).controller =
    (renewalBankPairMemory
      (compileAdvice (ceilLogTwo n))
      ((bankWindowOverlapBefore ring seed pre).2)
      root (ring.rightNeighbor root)
      ((bankWindowOverlapBefore ring seed pre).1 root)
      ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root))).1.controller at hc
  exact ⟨hm.trans hlocal.1, hc.trans hlocal.2⟩

/-- Consumer: group-13 PFX/ORPH real-run row; bankWindowOverlapChangedLongWaitPrefixOrphan. -/
theorem bankWindowOverlapChangedLongWaitPrefixOrphan
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (root : Fin n)
    (hJ : BankWindowExact ring (bankWindowOverlapBefore ring seed pre))
    (hx : ((bankWindowOverlapBefore ring seed pre).1 root).pack.val = 0)
    (hwrong : ((bankWindowOverlapBefore ring seed pre).1
      (ring.rightNeighbor root)).pack.val ≠ 1)
    (hg : ((bankWindowOverlapBefore ring seed pre).1 root).grant = false)
    (hphase : ((bankWindowOverlapBefore ring seed pre).1 root).mode = .RWAIT ∨
      ((bankWindowOverlapBefore ring seed pre).1 root).mode = .IWAIT ∨
      ((bankWindowOverlapBefore ring seed pre).1 root).mode = .CWAIT)
    (hlong : 1 < ((bankWindowOverlapBefore ring seed pre).1 root).lease.val) :
    (∀ limit : Nat,
      BankWindowProtoRun ring
        (bankWindowOverlapAfter ring seed pre root) root limit →
      (∀ p o,
        ((bankWindowOverlapAfter ring seed pre root).2.sites
          root).controller = .active p →
        p.origin = some o → False) ∧
      (BankWindowInheritedController
        (bankWindowOverlapAfter ring seed pre root) root →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted
            (bankWindowOverlapAfter ring seed pre root)
            (Counter.site ring root (j.val + 1))) ∧
      ((((bankWindowOverlapAfter ring seed pre root).1 root).mode =
          .RWAIT ∧
          ((bankWindowOverlapAfter ring seed pre root).2.sites
            root).controller = .waiting []) →
        ∃ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit ∧
          ∃ rho : RenewalBankReceipt n,
            ((bankWindowOverlapAfter ring seed pre root).2.sites
              (Counter.site ring root (j.val + 1))).worker =
              .pending rho ∧
            ((bankWindowOverlapAfter ring seed pre root).1
              (Counter.site ring root (j.val + 1))).tok = .RR ∧
            bankWindowZeroPrefix ring
              (bankWindowOverlapAfter ring seed pre root)
              root (j.val + 1) ∧
            (∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
              k.val < j.val →
              ((bankWindowOverlapAfter ring seed pre root).1
                (Counter.site ring root (k.val + 1))).tok = .E)) ∧
      (((bankWindowOverlapAfter ring seed pre root).1 root).mode
          ≠ .RESET →
        ((bankWindowOverlapAfter ring seed pre root).1 root).mode
          ≠ .RWAIT →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted
            (bankWindowOverlapAfter ring seed pre root)
            (Counter.site ring root (j.val + 1)))) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowOrphanOwner ring
        (bankWindowOverlapAfter ring seed pre root) root j →
      BankWindowTainted
        (bankWindowOverlapAfter ring seed pre root)
        (Counter.site ring root (j.val + 1)) →
      ((bankWindowOverlapAfter ring seed pre root).1 root).mode =
        .RESET ∨
      (((bankWindowOverlapAfter ring seed pre root).1 root).mode =
          .RWAIT ∧
        ((bankWindowOverlapAfter ring seed pre root).2.sites
          root).controller = .waiting [])) := by
  have hfields := bankWindowOverlapChangedLongWaitFields
    ring hn hbank seed pre root hx hwrong hg hphase hlong
  have hnoEmpty := bankWindowOverlapBrokenRootNoEmptyWaiting
    ring seed pre root hJ hx hwrong
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hprotoOldZero : BankWindowProtoRun ring
      (bankWindowOverlapBefore ring seed pre) root 0 := by
    refine ⟨hb, ?_, ?_⟩
    · intro k hk
      have hz : k = 0 := by omega
      rw [hz]
      change ((bankWindowOverlapBefore ring seed pre).1 root).pack.val = 0
      exact hx
    · change ((bankWindowOverlapBefore ring seed pre).1
          (ring.rightNeighbor root)).pack.val ≠ 1
      exact hwrong
  have hOldProto := hJ.proto root 0 hprotoOldZero
  have hnotReset :
      ((bankWindowOverlapBefore ring seed pre).1 root).mode ≠ .RESET := by
    rcases hphase with hm | hm | hm <;>
      (intro h; rw [hm] at h; cases h)
  have hclean :
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      ((bankWindowOverlapAfter ring seed pre root).1
        (Counter.site ring root (j.val + 1))).pack.val =
          j.val + 1 →
      ¬ BankWindowTainted (bankWindowOverlapAfter ring seed pre root)
        (Counter.site ring root (j.val + 1)) := by
    intro j haligned
    exact bankWindowOverlapChangedRootAlignedClean
      ring hn hbank seed pre root hJ hx hwrong
      hnotReset j haligned
  constructor
  · intro limit hproto
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro p o hactive ho
      have holdActive :
          ((bankWindowOverlapBefore ring seed pre).2.sites root).controller =
            .active p := hfields.2.symm.trans hactive
      exact hOldProto.1 p o holdActive ho
    · intro _ j hj
      exact hclean j (hproto.2.1 (j.val + 1) hj)
    · intro hpostWait
      have holdMode :
          ((bankWindowOverlapBefore ring seed pre).1 root).mode = .RWAIT :=
        hfields.1.symm.trans hpostWait.1
      have holdController :
          ((bankWindowOverlapBefore ring seed pre).2.sites root).controller =
            .waiting [] :=
        hfields.2.symm.trans hpostWait.2
      exact False.elim (hnoEmpty ⟨holdMode, holdController⟩)
    · intro _ _ j hj
      exact hclean j (hproto.2.1 (j.val + 1) hj)
  · intro j howner htainted
    exact False.elim (hclean j howner.2.1 htainted)




/-- Consumer: group-13 PFX/ORPH real-run row; bankWindowOverlapNonreturnShortWaitMode. -/
theorem bankWindowOverlapNonreturnShortWaitMode
    {c : Compiled} (x y : Agent c)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hphase : x.mode = .RWAIT ∨ x.mode = .IWAIT ∨
      x.mode = .CWAIT)
    (hshort : x.lease.val ≤ 1)
    (hret : isRetTok y.tok = false) :
    (Counter.resetBankOld x y).1.mode = .RESET := by
  have hb : 0 < c.b := by
    change 0 < c.s + 11
    omega
  have hbNotZero : c.b ≠ 0 := by omega
  have hwide : c.b ≠ 1 := by
    change c.s + 11 ≠ 1
    omega
  have hp : packNext x.pack.val y.pack.val c.b = 1 := by
    rw [hx, hy]
    simp [packNext, hb]
  have hnotLong : ¬ 1 < x.lease.val := by omega
  unfold Counter.resetBankOld
  rw [hp]
  rcases hphase with hm | hm | hm
  · simp [bankPair, bankCell, hx, hy, hg, hm, hret,
      hnotLong, hwide, hp, isWaitMode,
      Id.run_pure, Id.run_bind] <;>
      simp only [if_neg hbNotZero, if_neg hwide,
        if_true, if_false, Id.run_pure] <;> rfl
  · simp [bankPair, bankCell, hx, hy, hg, hm, hret,
      hnotLong, hwide, hp, isWaitMode,
      Id.run_pure, Id.run_bind] <;>
      simp only [if_neg hbNotZero, if_neg hwide,
        if_true, if_false, Id.run_pure] <;> rfl
  · simp [bankPair, bankCell, hx, hy, hg, hm, hret,
      hnotLong, hwide, hp, isWaitMode,
      Id.run_pure, Id.run_bind] <;>
      simp only [if_neg hbNotZero, if_neg hwide,
        if_true, if_false, Id.run_pure] <;> rfl

/-- Consumer: group-13 PFX/ORPH real-run row; bankWindowOverlapNonreturnShortWaitPrefixOrphan. -/
theorem bankWindowOverlapNonreturnShortWaitPrefixOrphan
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (root : Fin n)
    (hJ : BankWindowExact ring (bankWindowOverlapBefore ring seed pre))
    (hx : ((bankWindowOverlapBefore ring seed pre).1 root).pack.val = 0)
    (hy : ((bankWindowOverlapBefore ring seed pre).1
      (ring.rightNeighbor root)).pack.val = 1)
    (hg : ((bankWindowOverlapBefore ring seed pre).1 root).grant = false)
    (hphase : ((bankWindowOverlapBefore ring seed pre).1 root).mode = .RWAIT ∨
      ((bankWindowOverlapBefore ring seed pre).1 root).mode = .IWAIT ∨
      ((bankWindowOverlapBefore ring seed pre).1 root).mode = .CWAIT)
    (hshort : ((bankWindowOverlapBefore ring seed pre).1 root).lease.val ≤ 1)
    (hret : isRetTok
      ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).tok = false) :
    (∀ limit : Nat,
      BankWindowProtoRun ring
        (bankWindowOverlapAfter ring seed pre root) root limit →
      (∀ p o,
        ((bankWindowOverlapAfter ring seed pre root).2.sites
          root).controller = .active p →
        p.origin = some o → False) ∧
      (BankWindowInheritedController
        (bankWindowOverlapAfter ring seed pre root) root →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted
            (bankWindowOverlapAfter ring seed pre root)
            (Counter.site ring root (j.val + 1))) ∧
      ((((bankWindowOverlapAfter ring seed pre root).1 root).mode =
          .RWAIT ∧
          ((bankWindowOverlapAfter ring seed pre root).2.sites
            root).controller = .waiting []) →
        ∃ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit ∧
          ∃ rho : RenewalBankReceipt n,
            ((bankWindowOverlapAfter ring seed pre root).2.sites
              (Counter.site ring root (j.val + 1))).worker =
              .pending rho ∧
            ((bankWindowOverlapAfter ring seed pre root).1
              (Counter.site ring root (j.val + 1))).tok = .RR ∧
            bankWindowZeroPrefix ring
              (bankWindowOverlapAfter ring seed pre root)
              root (j.val + 1) ∧
            (∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
              k.val < j.val →
              ((bankWindowOverlapAfter ring seed pre root).1
                (Counter.site ring root (k.val + 1))).tok = .E)) ∧
      (((bankWindowOverlapAfter ring seed pre root).1 root).mode
          ≠ .RESET →
        ((bankWindowOverlapAfter ring seed pre root).1 root).mode
          ≠ .RWAIT →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted
            (bankWindowOverlapAfter ring seed pre root)
            (Counter.site ring root (j.val + 1)))) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowOrphanOwner ring
        (bankWindowOverlapAfter ring seed pre root) root j →
      BankWindowTainted
        (bankWindowOverlapAfter ring seed pre root)
        (Counter.site ring root (j.val + 1)) →
      ((bankWindowOverlapAfter ring seed pre root).1 root).mode =
        .RESET ∨
      (((bankWindowOverlapAfter ring seed pre root).1 root).mode =
          .RWAIT ∧
        ((bankWindowOverlapAfter ring seed pre root).2.sites
          root).controller = .waiting [])) := by
  have hraw := bankWindowOverlapNonreturnShortWaitMode
    ((bankWindowOverlapBefore ring seed pre).1 root)
    ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root))
    hx hy hg hphase hshort hret
  have htrip := (bankWindowClosureSelectedBankTrip
    ring hn hbank (bankWindowOverlapBefore ring seed pre) root).1
  have hm := congrArg
    (fun t : Mode × Bool × BTok => t.1) htrip
  change ((bankWindowOverlapAfter ring seed pre root).1 root).mode =
    (Counter.resetBankOld
      ((bankWindowOverlapBefore ring seed pre).1 root)
      ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root))).1.mode at hm
  have hreset :
      ((bankWindowOverlapAfter ring seed pre root).1 root).mode = .RESET := hm.trans hraw
  have hsourcePack := bankWindowClosureRepairNonresponderPackFixed
    ring (by omega : 2 ≤ n)
    (bankWindowOverlapBefore ring seed pre) root root
    (clockNeighborDifferent ring (by omega : 2 ≤ n) root).symm
  have hpostPack :
      ((bankWindowOverlapAfter ring seed pre root).1 root).pack.val = 0 := hsourcePack.trans hx
  have hframe := bankWindowExactFrameStep
    ring hn hbank seed pre root hJ
  have hfields := bankWindowIncomingResetOwnerFields ring
    (bankWindowOverlapBefore ring seed pre) root root
    hpostPack hreset hframe
  exact ⟨hfields.2.2.1, hfields.2.2.2⟩



end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open Classical

/-- Consumer: group-13 PFX/ORPH real-run row; bankWindowOverlapActiveCollisionResetMode. -/
theorem bankWindowOverlapActiveCollisionResetMode
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
  have hbNotZero : c.b ≠ 0 := by omega
  have hp : packNext x.pack.val y.pack.val c.b = 1 := by
    rw [hx, hy]
    simp [packNext, hb]
  unfold Counter.resetBankOld
  rw [hp]
  rcases hphase with hm | hm
  · simp [bankPair, bankCell, hx, hy, hg, hm,
      hret, htok, hp, isRetTok,
      Id.run_pure, Id.run_bind] <;>
      simp only [if_neg hbNotZero, if_neg htok,
        if_true, if_false, Id.run_pure] <;> first | rfl | simp | (cases hT : y.tok <;> simp_all [isRetTok, bankPair, bankCell])
  · simp [bankPair, bankCell, hx, hy, hg, hm,
      hret, htok, hp, isRetTok,
      Id.run_pure, Id.run_bind] <;>
      simp only [if_neg hbNotZero, if_neg htok,
        if_true, if_false, Id.run_pure] <;> first | rfl | simp | (cases hT : y.tok <;> simp_all [isRetTok, bankPair, bankCell])

/-- Consumer: group-13 PFX/ORPH real-run row; bankWindowOverlapNonreturnLongWaitPair. -/
theorem bankWindowOverlapNonreturnLongWaitPair
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (root dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hphase : x.mode = .RWAIT ∨ x.mode = .IWAIT ∨
      x.mode = .CWAIT)
    (hlong : 1 < x.lease.val)
    (hret : isRetTok y.tok = false) :
    (Counter.resetBankOld x y).1.mode = x.mode ∧
    (Counter.resetBankOld x y).2.bit = y.bit ∧
    (Counter.resetBankOld x y).2.tok = y.tok ∧
    (renewalBankPairMemory c m root dest x y).1.controller =
      (m.sites root).controller ∧
    (renewalBankPairMemory c m root dest x y).2.worker =
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

/-- Consumer: group-13 PFX/ORPH real-run row; bankWindowOverlapActiveCollisionPrefixOrphan. -/
theorem bankWindowOverlapActiveCollisionPrefixOrphan
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (root : Fin n)
    (hJ : BankWindowExact ring (bankWindowOverlapBefore ring seed pre))
    (hx : ((bankWindowOverlapBefore ring seed pre).1 root).pack.val = 0)
    (hy : ((bankWindowOverlapBefore ring seed pre).1
      (ring.rightNeighbor root)).pack.val = 1)
    (hg : ((bankWindowOverlapBefore ring seed pre).1 root).grant = false)
    (hphase : ((bankWindowOverlapBefore ring seed pre).1 root).mode = .ARMED ∨
      ((bankWindowOverlapBefore ring seed pre).1 root).mode = .CSTART)
    (hret : isRetTok
      ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).tok = false)
    (htok : ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).tok ≠ .E) :
    (∀ limit : Nat,
      BankWindowProtoRun ring
        (bankWindowOverlapAfter ring seed pre root) root limit →
      (∀ p o,
        ((bankWindowOverlapAfter ring seed pre root).2.sites
          root).controller = .active p →
        p.origin = some o → False) ∧
      (BankWindowInheritedController
        (bankWindowOverlapAfter ring seed pre root) root →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted
            (bankWindowOverlapAfter ring seed pre root)
            (Counter.site ring root (j.val + 1))) ∧
      ((((bankWindowOverlapAfter ring seed pre root).1 root).mode =
          .RWAIT ∧
          ((bankWindowOverlapAfter ring seed pre root).2.sites
            root).controller = .waiting []) →
        ∃ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit ∧
          ∃ rho : RenewalBankReceipt n,
            ((bankWindowOverlapAfter ring seed pre root).2.sites
              (Counter.site ring root (j.val + 1))).worker =
              .pending rho ∧
            ((bankWindowOverlapAfter ring seed pre root).1
              (Counter.site ring root (j.val + 1))).tok = .RR ∧
            bankWindowZeroPrefix ring
              (bankWindowOverlapAfter ring seed pre root)
              root (j.val + 1) ∧
            (∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
              k.val < j.val →
              ((bankWindowOverlapAfter ring seed pre root).1
                (Counter.site ring root (k.val + 1))).tok = .E)) ∧
      (((bankWindowOverlapAfter ring seed pre root).1 root).mode
          ≠ .RESET →
        ((bankWindowOverlapAfter ring seed pre root).1 root).mode
          ≠ .RWAIT →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted
            (bankWindowOverlapAfter ring seed pre root)
            (Counter.site ring root (j.val + 1)))) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowOrphanOwner ring
        (bankWindowOverlapAfter ring seed pre root) root j →
      BankWindowTainted
        (bankWindowOverlapAfter ring seed pre root)
        (Counter.site ring root (j.val + 1)) →
      ((bankWindowOverlapAfter ring seed pre root).1 root).mode =
        .RESET ∨
      (((bankWindowOverlapAfter ring seed pre root).1 root).mode =
          .RWAIT ∧
        ((bankWindowOverlapAfter ring seed pre root).2.sites
          root).controller = .waiting [])) := by
  have hraw := bankWindowOverlapActiveCollisionResetMode
    ((bankWindowOverlapBefore ring seed pre).1 root)
    ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root))
    hx hy hg hphase hret htok
  have htrip := (bankWindowClosureSelectedBankTrip
    ring hn hbank (bankWindowOverlapBefore ring seed pre) root).1
  have hm := congrArg
    (fun t : Mode × Bool × BTok => t.1) htrip
  change ((bankWindowOverlapAfter ring seed pre root).1 root).mode =
    (Counter.resetBankOld
      ((bankWindowOverlapBefore ring seed pre).1 root)
      ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root))).1.mode at hm
  have hreset :
      ((bankWindowOverlapAfter ring seed pre root).1 root).mode = .RESET := hm.trans hraw
  have hsourcePack := bankWindowClosureRepairNonresponderPackFixed
    ring (by omega : 2 ≤ n)
    (bankWindowOverlapBefore ring seed pre) root root
    (clockNeighborDifferent ring (by omega : 2 ≤ n) root).symm
  have hpostPack :
      ((bankWindowOverlapAfter ring seed pre root).1 root).pack.val = 0 := hsourcePack.trans hx
  have hframe := bankWindowExactFrameStep
    ring hn hbank seed pre root hJ
  have hfields := bankWindowIncomingResetOwnerFields ring
    (bankWindowOverlapBefore ring seed pre) root root
    hpostPack hreset hframe
  exact ⟨hfields.2.2.1, hfields.2.2.2⟩

/-- Consumer: group-13 PFX/ORPH real-run row; bankWindowOverlapNonreturnLongWaitFields. -/
theorem bankWindowOverlapNonreturnLongWaitFields
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (root : Fin n)
    (hx : ((bankWindowOverlapBefore ring seed pre).1 root).pack.val = 0)
    (hy : ((bankWindowOverlapBefore ring seed pre).1
      (ring.rightNeighbor root)).pack.val = 1)
    (hg : ((bankWindowOverlapBefore ring seed pre).1 root).grant = false)
    (hphase : ((bankWindowOverlapBefore ring seed pre).1 root).mode = .RWAIT ∨
      ((bankWindowOverlapBefore ring seed pre).1 root).mode = .IWAIT ∨
      ((bankWindowOverlapBefore ring seed pre).1 root).mode = .CWAIT)
    (hlong : 1 < ((bankWindowOverlapBefore ring seed pre).1 root).lease.val)
    (hret : isRetTok
      ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).tok = false) :
    ((bankWindowOverlapAfter ring seed pre root).1 root).mode =
      ((bankWindowOverlapBefore ring seed pre).1 root).mode ∧
    ((bankWindowOverlapAfter ring seed pre root).2.sites root).controller =
      ((bankWindowOverlapBefore ring seed pre).2.sites root).controller ∧
    ((bankWindowOverlapAfter ring seed pre root).1 (ring.rightNeighbor root)).bit =
      ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).bit ∧
    ((bankWindowOverlapAfter ring seed pre root).1 (ring.rightNeighbor root)).tok =
      ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).tok ∧
    ((bankWindowOverlapAfter ring seed pre root).2.sites (ring.rightNeighbor root)).worker =
      ((bankWindowOverlapBefore ring seed pre).2.sites (ring.rightNeighbor root)).worker := by
  have hlocal := bankWindowOverlapNonreturnLongWaitPair
    (compileAdvice (ceilLogTwo n))
    ((bankWindowOverlapBefore ring seed pre).2) root
    (ring.rightNeighbor root)
    ((bankWindowOverlapBefore ring seed pre).1 root)
    ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root))
    hx hy hg hphase hlong hret
  have htrips := bankWindowClosureSelectedBankTrip
    ring hn hbank (bankWindowOverlapBefore ring seed pre) root
  have hm := congrArg
    (fun t : Mode × Bool × BTok => t.1) htrips.1
  change ((bankWindowOverlapAfter ring seed pre root).1 root).mode =
    (Counter.resetBankOld
      ((bankWindowOverlapBefore ring seed pre).1 root)
      ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root))).1.mode at hm
  have hbit := congrArg
    (fun t : Mode × Bool × BTok => t.2.1) htrips.2
  change ((bankWindowOverlapAfter ring seed pre root).1
      (ring.rightNeighbor root)).bit =
    (Counter.resetBankOld
      ((bankWindowOverlapBefore ring seed pre).1 root)
      ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root))).2.bit at hbit
  have htok := congrArg
    (fun t : Mode × Bool × BTok => t.2.2) htrips.2
  change ((bankWindowOverlapAfter ring seed pre root).1
      (ring.rightNeighbor root)).tok =
    (Counter.resetBankOld
      ((bankWindowOverlapBefore ring seed pre).1 root)
      ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root))).2.tok at htok
  have hframe := (rbReferenceSelectedPairFrame ring
    (by omega : 2 ≤ n) (bankWindowOverlapBefore ring seed pre) root).2.2
  have hctl := congrArg
    (fun s : RenewalBankSite n => s.controller) hframe.1
  change ((bankWindowOverlapAfter ring seed pre root).2.sites root).controller =
    (renewalBankPairMemory
      (compileAdvice (ceilLogTwo n))
      ((bankWindowOverlapBefore ring seed pre).2)
      root (ring.rightNeighbor root)
      ((bankWindowOverlapBefore ring seed pre).1 root)
      ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root))).1.controller at hctl
  have hworker := congrArg
    (fun s : RenewalBankSite n => s.worker) hframe.2
  change ((bankWindowOverlapAfter ring seed pre root).2.sites
      (ring.rightNeighbor root)).worker =
    (renewalBankPairMemory
      (compileAdvice (ceilLogTwo n))
      ((bankWindowOverlapBefore ring seed pre).2)
      root (ring.rightNeighbor root)
      ((bankWindowOverlapBefore ring seed pre).1 root)
      ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root))).2.worker at hworker
  exact ⟨hm.trans hlocal.1,
    hctl.trans hlocal.2.2.2.1,
    hbit.trans hlocal.2.1,
    htok.trans hlocal.2.2.1,
    hworker.trans hlocal.2.2.2.2⟩

/-- Consumer: group-13 PFX/ORPH real-run row; bankWindowOverlapNonreturnLongWaitPrefixOrphan. -/
theorem bankWindowOverlapNonreturnLongWaitPrefixOrphan
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (root : Fin n)
    (hJ : BankWindowExact ring (bankWindowOverlapBefore ring seed pre))
    (hx : ((bankWindowOverlapBefore ring seed pre).1 root).pack.val = 0)
    (hy : ((bankWindowOverlapBefore ring seed pre).1
      (ring.rightNeighbor root)).pack.val = 1)
    (hg : ((bankWindowOverlapBefore ring seed pre).1 root).grant = false)
    (hphase : ((bankWindowOverlapBefore ring seed pre).1 root).mode = .RWAIT ∨
      ((bankWindowOverlapBefore ring seed pre).1 root).mode = .IWAIT ∨
      ((bankWindowOverlapBefore ring seed pre).1 root).mode = .CWAIT)
    (hlong : 1 < ((bankWindowOverlapBefore ring seed pre).1 root).lease.val)
    (hret : isRetTok
      ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).tok = false) :
    (∀ limit : Nat,
      BankWindowProtoRun ring
        (bankWindowOverlapAfter ring seed pre root) root limit →
      (∀ p o,
        ((bankWindowOverlapAfter ring seed pre root).2.sites
          root).controller = .active p →
        p.origin = some o → False) ∧
      (BankWindowInheritedController
        (bankWindowOverlapAfter ring seed pre root) root →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted
            (bankWindowOverlapAfter ring seed pre root)
            (Counter.site ring root (j.val + 1))) ∧
      ((((bankWindowOverlapAfter ring seed pre root).1 root).mode =
          .RWAIT ∧
          ((bankWindowOverlapAfter ring seed pre root).2.sites
            root).controller = .waiting []) →
        ∃ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit ∧
          ∃ rho : RenewalBankReceipt n,
            ((bankWindowOverlapAfter ring seed pre root).2.sites
              (Counter.site ring root (j.val + 1))).worker =
              .pending rho ∧
            ((bankWindowOverlapAfter ring seed pre root).1
              (Counter.site ring root (j.val + 1))).tok = .RR ∧
            bankWindowZeroPrefix ring
              (bankWindowOverlapAfter ring seed pre root)
              root (j.val + 1) ∧
            (∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
              k.val < j.val →
              ((bankWindowOverlapAfter ring seed pre root).1
                (Counter.site ring root (k.val + 1))).tok = .E)) ∧
      (((bankWindowOverlapAfter ring seed pre root).1 root).mode
          ≠ .RESET →
        ((bankWindowOverlapAfter ring seed pre root).1 root).mode
          ≠ .RWAIT →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted
            (bankWindowOverlapAfter ring seed pre root)
            (Counter.site ring root (j.val + 1)))) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowOrphanOwner ring
        (bankWindowOverlapAfter ring seed pre root) root j →
      BankWindowTainted
        (bankWindowOverlapAfter ring seed pre root)
        (Counter.site ring root (j.val + 1)) →
      ((bankWindowOverlapAfter ring seed pre root).1 root).mode =
        .RESET ∨
      (((bankWindowOverlapAfter ring seed pre root).1 root).mode =
          .RWAIT ∧
        ((bankWindowOverlapAfter ring seed pre root).2.sites
          root).controller = .waiting [])) := by
  have hfields := bankWindowOverlapNonreturnLongWaitFields
    ring hn hbank seed pre root
    hx hy hg hphase hlong hret
  have hreads := bankWindowOverlapSourceRootSamePortReadSets
    ring hn hbank seed pre root hx hy
    hfields.1 hfields.2.1 hfields.2.2.1
    hfields.2.2.2.1 hfields.2.2.2.2
  constructor
  · intro limit hproto
    exact bankWindowProtoReadTransport ring
      (bankWindowOverlapBefore ring seed pre) (bankWindowOverlapAfter ring seed pre root)
      root limit hJ (hreads.1 limit hproto) hproto
  · intro j howner htainted
    exact bankWindowOrphanReadTransport ring
      (bankWindowOverlapBefore ring seed pre) (bankWindowOverlapAfter ring seed pre root)
      root j hJ (hreads.2 j) howner htainted

end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- The genuine role-zero CWAIT/CL1 return always resets the
source root, independent of completion. Consumer: M3 SRC
comparison-return PFX/ORPH in bankWindowOverlapJoint. -/
theorem bankWindowOverlapSourceClOneResetMode
    {c : Compiled} (x y : Agent c)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hm : x.mode = .CWAIT) (ht : y.tok = .CL1) :
    (Counter.resetBankOld x y).1.mode = .RESET := by
  have hb : 0 < c.b := by
    change 0 < c.s + 11
    omega
  have hbz : c.b ≠ 0 := by omega
  have hpost : packNext x.pack.val y.pack.val c.b = 1 := by
    rw [hx, hy]
    simp [packNext, hb]
  unfold Counter.resetBankOld
  rw [hpost]
  simp [bankPair, bankCell, hx, hy, hg, hm, ht, hb, hbz,
    hpost, isRetTok, Id.run_pure, Id.run_bind] <;>
    simp only [if_neg hbz, if_true, Id.run_pure] <;> rfl

/-- The literal CWAIT/CL1 selected source returns to RESET
whether or not its OLD window was complete. OLD J gives the
actual POST frame; RESET then discharges all four PFX and ORPH
consequents. Consumer: M3 SRC comparison-return in
bankWindowOverlapJoint, bankWindowExactStep. -/
theorem bankWindowOverlapSourceClOnePrefixOrphan
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (root : Fin n)
    (hJ : BankWindowExact ring (bankWindowOverlapBefore ring seed pre))
    (hx : ((bankWindowOverlapBefore ring seed pre).1 root).pack.val = 0)
    (hy : ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).pack.val = 1)
    (hg : ((bankWindowOverlapBefore ring seed pre).1 root).grant = false)
    (hm : ((bankWindowOverlapBefore ring seed pre).1 root).mode = .CWAIT)
    (ht : ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).tok = .CL1) :
    (∀ limit : Nat,
      BankWindowProtoRun ring
        (bankWindowOverlapAfter ring seed pre root) root limit →
      (∀ p o,
        ((bankWindowOverlapAfter ring seed pre root).2.sites
          root).controller = .active p →
        p.origin = some o → False) ∧
      (BankWindowInheritedController
        (bankWindowOverlapAfter ring seed pre root) root →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted
            (bankWindowOverlapAfter ring seed pre root)
            (Counter.site ring root (j.val + 1))) ∧
      ((((bankWindowOverlapAfter ring seed pre root).1 root).mode =
          .RWAIT ∧
          ((bankWindowOverlapAfter ring seed pre root).2.sites
            root).controller = .waiting []) →
        ∃ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit ∧
          ∃ rho : RenewalBankReceipt n,
            ((bankWindowOverlapAfter ring seed pre root).2.sites
              (Counter.site ring root (j.val + 1))).worker =
              .pending rho ∧
            ((bankWindowOverlapAfter ring seed pre root).1
              (Counter.site ring root (j.val + 1))).tok = .RR ∧
            bankWindowZeroPrefix ring
              (bankWindowOverlapAfter ring seed pre root)
              root (j.val + 1) ∧
            (∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
              k.val < j.val →
              ((bankWindowOverlapAfter ring seed pre root).1
                (Counter.site ring root (k.val + 1))).tok = .E)) ∧
      (((bankWindowOverlapAfter ring seed pre root).1 root).mode
          ≠ .RESET →
        ((bankWindowOverlapAfter ring seed pre root).1 root).mode
          ≠ .RWAIT →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted
            (bankWindowOverlapAfter ring seed pre root)
            (Counter.site ring root (j.val + 1)))) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowOrphanOwner ring
        (bankWindowOverlapAfter ring seed pre root) root j →
      BankWindowTainted
        (bankWindowOverlapAfter ring seed pre root)
        (Counter.site ring root (j.val + 1)) →
      ((bankWindowOverlapAfter ring seed pre root).1 root).mode =
        .RESET ∨
      (((bankWindowOverlapAfter ring seed pre root).1 root).mode =
          .RWAIT ∧
        ((bankWindowOverlapAfter ring seed pre root).2.sites
          root).controller = .waiting [])) := by
  have hraw := bankWindowOverlapSourceClOneResetMode
    ((bankWindowOverlapBefore ring seed pre).1 root)
    ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)) hx hy hg hm ht
  have htrip := (bankWindowClosureSelectedBankTrip
    ring hn hbank (bankWindowOverlapBefore ring seed pre) root).1
  have hmode := congrArg
    (fun t : Mode × Bool × BTok => t.1) htrip
  change ((bankWindowOverlapAfter ring seed pre root).1 root).mode =
    (Counter.resetBankOld
      ((bankWindowOverlapBefore ring seed pre).1 root)
      ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root))).1.mode at hmode
  have hreset :
      ((bankWindowOverlapAfter ring seed pre root).1 root).mode = .RESET := hmode.trans hraw
  have hsourcePack := bankWindowClosureRepairNonresponderPackFixed
    ring (by omega : 2 ≤ n)
    (bankWindowOverlapBefore ring seed pre) root root
    (clockNeighborDifferent ring (by omega : 2 ≤ n) root).symm
  have hpostPack :
      ((bankWindowOverlapAfter ring seed pre root).1 root).pack.val = 0 := hsourcePack.trans hx
  have hframe := bankWindowExactFrameStep
    ring hn hbank seed pre root hJ
  have hfields := bankWindowIncomingResetOwnerFields
    ring (bankWindowOverlapBefore ring seed pre) root root hpostPack hreset hframe
  exact ⟨hfields.2.2.1, hfields.2.2.2⟩

/-- Every mismatched returning token (AL/CL0/CL1 at
RWAIT, RL/CL0/CL1 at IWAIT, RL/AL at CWAIT) enters RESET
when the OLD root wait lease has expired. Matching returns
are intentionally excluded. Consumer: M3 SRC exhausted
return-token PFX/ORPH branches. -/
theorem bankWindowOverlapSourceMismatchReturnTimeoutMode
    {c : Compiled} (x y : Agent c)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hcases : ((x.mode = .RWAIT ∧ y.tok = .AL) ∨
       (x.mode = .RWAIT ∧ y.tok = .CL0) ∨
       (x.mode = .RWAIT ∧ y.tok = .CL1) ∨
       (x.mode = .IWAIT ∧ y.tok = .RL) ∨
       (x.mode = .IWAIT ∧ y.tok = .CL0) ∨
       (x.mode = .IWAIT ∧ y.tok = .CL1) ∨
       (x.mode = .CWAIT ∧ y.tok = .RL) ∨
       (x.mode = .CWAIT ∧ y.tok = .AL)))
    (hshort : x.lease.val ≤ 1) :
    (Counter.resetBankOld x y).1.mode = .RESET := by
  have hb : 0 < c.b := by
    change 0 < c.s + 11
    omega
  have hbz : c.b ≠ 0 := by omega
  have hpost : packNext x.pack.val y.pack.val c.b = 1 := by
    rw [hx, hy]
    simp [packNext, hb]
  have hnotLong : ¬ 1 < x.lease.val := by omega
  unfold Counter.resetBankOld
  rw [hpost]
  rcases hcases with h | h | h | h | h | h | h | h <;>
    rcases h with ⟨hm, ht⟩ <;>
    simp [bankPair, bankCell, hx, hy, hg, hm, ht,
      hb, hbz, hpost, hnotLong, isRetTok, isWaitMode,
      Id.run_pure, Id.run_bind] <;>
    simp only [if_neg hbz, if_true, Id.run_pure] <;> rfl

/-- Real mismatched-return SRC edge with expired OLD lease.
The BANK source is RESET afterward, so OLD J's POST frame
settles PFX and ORPH without inventing any post-J contract.
Consumer: M3 SRC mismatched return timeout, bankWindowOverlapJoint. -/
theorem bankWindowOverlapSourceMismatchReturnTimeoutPrefixOrphan
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (root : Fin n)
    (hJ : BankWindowExact ring (bankWindowOverlapBefore ring seed pre))
    (hx : ((bankWindowOverlapBefore ring seed pre).1 root).pack.val = 0)
    (hy : ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).pack.val = 1)
    (hg : ((bankWindowOverlapBefore ring seed pre).1 root).grant = false)
    (hcases : ((((bankWindowOverlapBefore ring seed pre).1 root).mode = .RWAIT ∧ ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).tok = .AL) ∨
       (((bankWindowOverlapBefore ring seed pre).1 root).mode = .RWAIT ∧ ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).tok = .CL0) ∨
       (((bankWindowOverlapBefore ring seed pre).1 root).mode = .RWAIT ∧ ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).tok = .CL1) ∨
       (((bankWindowOverlapBefore ring seed pre).1 root).mode = .IWAIT ∧ ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).tok = .RL) ∨
       (((bankWindowOverlapBefore ring seed pre).1 root).mode = .IWAIT ∧ ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).tok = .CL0) ∨
       (((bankWindowOverlapBefore ring seed pre).1 root).mode = .IWAIT ∧ ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).tok = .CL1) ∨
       (((bankWindowOverlapBefore ring seed pre).1 root).mode = .CWAIT ∧ ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).tok = .RL) ∨
       (((bankWindowOverlapBefore ring seed pre).1 root).mode = .CWAIT ∧ ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).tok = .AL)))
    (hshort : ((bankWindowOverlapBefore ring seed pre).1 root).lease.val ≤ 1) :
    (∀ limit : Nat,
      BankWindowProtoRun ring
        (bankWindowOverlapAfter ring seed pre root) root limit →
      (∀ p o,
        ((bankWindowOverlapAfter ring seed pre root).2.sites
          root).controller = .active p →
        p.origin = some o → False) ∧
      (BankWindowInheritedController
        (bankWindowOverlapAfter ring seed pre root) root →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted
            (bankWindowOverlapAfter ring seed pre root)
            (Counter.site ring root (j.val + 1))) ∧
      ((((bankWindowOverlapAfter ring seed pre root).1 root).mode =
          .RWAIT ∧
          ((bankWindowOverlapAfter ring seed pre root).2.sites
            root).controller = .waiting []) →
        ∃ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit ∧
          ∃ rho : RenewalBankReceipt n,
            ((bankWindowOverlapAfter ring seed pre root).2.sites
              (Counter.site ring root (j.val + 1))).worker =
              .pending rho ∧
            ((bankWindowOverlapAfter ring seed pre root).1
              (Counter.site ring root (j.val + 1))).tok = .RR ∧
            bankWindowZeroPrefix ring
              (bankWindowOverlapAfter ring seed pre root)
              root (j.val + 1) ∧
            (∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
              k.val < j.val →
              ((bankWindowOverlapAfter ring seed pre root).1
                (Counter.site ring root (k.val + 1))).tok = .E)) ∧
      (((bankWindowOverlapAfter ring seed pre root).1 root).mode
          ≠ .RESET →
        ((bankWindowOverlapAfter ring seed pre root).1 root).mode
          ≠ .RWAIT →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted
            (bankWindowOverlapAfter ring seed pre root)
            (Counter.site ring root (j.val + 1)))) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowOrphanOwner ring
        (bankWindowOverlapAfter ring seed pre root) root j →
      BankWindowTainted
        (bankWindowOverlapAfter ring seed pre root)
        (Counter.site ring root (j.val + 1)) →
      ((bankWindowOverlapAfter ring seed pre root).1 root).mode =
        .RESET ∨
      (((bankWindowOverlapAfter ring seed pre root).1 root).mode =
          .RWAIT ∧
        ((bankWindowOverlapAfter ring seed pre root).2.sites
          root).controller = .waiting [])) := by
  have hraw := bankWindowOverlapSourceMismatchReturnTimeoutMode
    ((bankWindowOverlapBefore ring seed pre).1 root)
    ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root))
    hx hy hg hcases hshort
  have htrip := (bankWindowClosureSelectedBankTrip
    ring hn hbank (bankWindowOverlapBefore ring seed pre) root).1
  have hmode := congrArg
    (fun t : Mode × Bool × BTok => t.1) htrip
  change ((bankWindowOverlapAfter ring seed pre root).1 root).mode =
    (Counter.resetBankOld
      ((bankWindowOverlapBefore ring seed pre).1 root)
      ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root))).1.mode at hmode
  have hreset :
      ((bankWindowOverlapAfter ring seed pre root).1 root).mode = .RESET := hmode.trans hraw
  have hsourcePack := bankWindowClosureRepairNonresponderPackFixed
    ring (by omega : 2 ≤ n)
    (bankWindowOverlapBefore ring seed pre) root root
    (clockNeighborDifferent ring (by omega : 2 ≤ n) root).symm
  have hpostPack :
      ((bankWindowOverlapAfter ring seed pre root).1 root).pack.val = 0 := hsourcePack.trans hx
  have hframe := bankWindowExactFrameStep
    ring hn hbank seed pre root hJ
  have hfields := bankWindowIncomingResetOwnerFields
    ring (bankWindowOverlapBefore ring seed pre) root root hpostPack hreset hframe
  exact ⟨hfields.2.2.1, hfields.2.2.2⟩

/-- A BANK root whose first PACK is zero and whose physical
window is incomplete has an exact first mismatch. This is a
bounded induction on physical Counter.site.
Consumer: M3 SRC inherited/matching return and issue rows. -/
theorem bankWindowOverlapIncompleteProtoExists
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n)
    (hroot : (r.1 root).pack.val = 0)
    (hnot : ¬ Counter.Complete ring r.1 root) :
    ∃ limit : Nat, BankWindowProtoRun ring r root limit := by
  have hchain :
      ∀ k : Nat, k ≤ (compileAdvice (ceilLogTwo n)).b →
        (∀ t : Nat, t ≤ k →
          (r.1 (Counter.site ring root t)).pack.val = t) ∨
        ∃ limit : Nat, limit < k ∧
          (∀ t : Nat, t ≤ limit →
            (r.1 (Counter.site ring root t)).pack.val = t) ∧
          (r.1 (Counter.site ring root (limit + 1))).pack.val ≠
            limit + 1 := by
    intro k
    induction k with
    | zero =>
        intro _
        left
        intro t ht
        have hz : t = 0 := by omega
        rw [hz]
        change (r.1 root).pack.val = 0
        exact hroot
    | succ k ih =>
        intro hk
        rcases ih (by omega) with hall | ⟨limit, hlt, hgood, hbad⟩
        · by_cases hnext :
            (r.1 (Counter.site ring root (k + 1))).pack.val =
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

/-- OLD J.proto excludes a genuine root controller at every
incomplete ARMED/CSTART root. The OLD controller must be an
inherited active payload (origin none), even if an independent
inherited atom is present. Consumer: M3 SRC ARMED/CSTART
empty-token first-match rows. -/
theorem bankWindowOverlapIncompleteActiveRootInherited
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n)
    (hJ : BankWindowExact ring r)
    (hroot : (r.1 root).pack.val = 0)
    (hnot : ¬ Counter.Complete ring r.1 root)
    (hmode : (r.1 root).mode = .ARMED ∨
      (r.1 root).mode = .CSTART) :
    ∃ p : RenewalBankPayload n,
      (r.2.sites root).controller = .active p ∧
      p.origin = none := by
  obtain ⟨limit, hproto⟩ :=
    bankWindowOverlapIncompleteProtoExists
      ring r root hroot hnot
  have hshape :
      ∃ p : RenewalBankPayload n,
        (r.2.sites root).controller = .active p := by
    rcases hmode with hm | hm
    · have hh := (hJ.frame root).1
      simpa [bankInFlightControllerShape, hroot, hm] using hh
    · have hh := (hJ.frame root).1
      simpa [bankInFlightControllerShape, hroot, hm] using hh
  obtain ⟨p, hctl⟩ := hshape
  have hnone : p.origin = none := by
    cases ho : p.origin with
    | none => rfl
    | some o =>
        exact False.elim
          ((hJ.proto root limit hproto).1 p o hctl ho)
  exact ⟨p, hctl, hnone⟩

/-- At an OLD incomplete root outside RESET/RWAIT, all
physically aligned digit workers are untainted. Either the
digit lies in the first proto prefix, or its aligned PACK
after that first mismatch makes it an orphan. Both alternatives
are excluded by OLD J. Consumer: M3 SRC ARMED/CSTART issue
and IWAIT/CWAIT return-token sanitation. -/
theorem bankWindowOverlapIncompleteNonwaitAlignedClean
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n)
    (hJ : BankWindowExact ring r)
    (hroot : (r.1 root).pack.val = 0)
    (hnot : ¬ Counter.Complete ring r.1 root)
    (hnotReset : (r.1 root).mode ≠ .RESET)
    (hnotWait : (r.1 root).mode ≠ .RWAIT)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (haligned :
      (r.1 (Counter.site ring root (j.val + 1))).pack.val =
        j.val + 1) :
    ¬ BankWindowTainted r
      (Counter.site ring root (j.val + 1)) := by
  obtain ⟨limit, hproto⟩ :=
    bankWindowOverlapIncompleteProtoExists
      ring r root hroot hnot
  intro ht
  by_cases hbefore : j.val + 1 ≤ limit
  · exact ((hJ.proto root limit hproto).2.2.2
      hnotReset hnotWait j hbefore) ht
  · have howner : BankWindowOrphanOwner ring r root j := by
      refine ⟨hroot, haligned, ?_⟩
      intro hfull
      exact hproto.2.2 (hfull (limit + 1) (by omega))
    rcases hJ.orphan root j howner ht with
      hr | ⟨hw, _⟩
    · exact hnotReset hr
    · exact hnotWait hw

/-- Literal ARMED/E 0->1 BANK output: bit zero sets
CSTART and bit one issues IR and enters IWAIT. The
responder test is on its OLD bit; all return-token guards
are false because isRetTok E is false. Consumer: M3 SRC
ARMED empty-token PFX/ORPH physical branch. -/
theorem bankWindowOverlapSourceArmedEmptyPhysical
    {c : Compiled} (x y : Agent c)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hm : x.mode = .ARMED) (ht : y.tok = .E) :
    (Counter.resetBankOld x y).1.mode =
      (if y.bit then .IWAIT else .CSTART) ∧
    (Counter.resetBankOld x y).2.tok =
      (if y.bit then .IR else .E) := by
  have hb : 0 < c.b := by
    change 0 < c.s + 11
    omega
  have hbz : c.b ≠ 0 := by omega
  have hp : packNext x.pack.val y.pack.val c.b = 1 := by
    rw [hx, hy]
    simp [packNext, hb]
  unfold Counter.resetBankOld
  rw [hp]
  cases hbit : y.bit <;>
    simp [bankPair, bankCell, hx, hy, hg, hm, ht,
      hbit, hb, hbz, hp, isRetTok,
      Id.run_pure, Id.run_bind] <;>
    simp only [if_neg hbz, if_true, Id.run_pure] <;> rfl

/-- Literal CSTART/E 0->1 BANK output: the source begins CWAIT
and the first responder receives CR0 or CR1 according to OLD
bit versus theta zero. Consumer: M3 SRC CSTART empty-token
PFX/ORPH physical branch. -/
theorem bankWindowOverlapSourceCstartEmptyPhysical
    {c : Compiled} (x y : Agent c)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hm : x.mode = .CSTART) (ht : y.tok = .E) :
    (Counter.resetBankOld x y).1.mode = .CWAIT ∧
    (Counter.resetBankOld x y).2.tok =
      (if y.bit == c.theta 0 then .CR1 else .CR0) := by
  have hb : 0 < c.b := by
    change 0 < c.s + 11
    omega
  have hbz : c.b ≠ 0 := by omega
  have hp : packNext x.pack.val y.pack.val c.b = 1 := by
    rw [hx, hy]
    simp [packNext, hb]
  unfold Counter.resetBankOld
  rw [hp]
  simp [bankPair, bankCell, hx, hy, hg, hm, ht,
    hb, hbz, hp, isRetTok,
    Id.run_pure, Id.run_bind] <;>
    simp only [if_neg hbz, if_true, Id.run_pure] <;> rfl

/-- At an OLD-incomplete ARMED/CSTART SRC row with OLD first
responder token E, the real BANK ghost cannot issue a
completed-origin worker into that responder, and the root
cannot have a genuine active controller afterward. The
ARMED bit-zero set, bit-one issue and CSTART compare-issue
branches are all covered. Consumer: M3 SRC PFX/ORPH
empty-token issue cases in bankWindowOverlapJoint. -/
theorem bankWindowOverlapSourceActiveEmptyFirstClean
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (root : Fin n)
    (hJ : BankWindowExact ring r)
    (hnot : ¬ Counter.Complete ring r.1 root)
    (hx : (r.1 root).pack.val = 0)
    (hy : (r.1 (ring.rightNeighbor root)).pack.val = 1)
    (hg : (r.1 root).grant = false)
    (hphase : (r.1 root).mode = .ARMED ∨
      (r.1 root).mode = .CSTART)
    (ht : (r.1 (ring.rightNeighbor root)).tok = .E) :
    (∀ p o,
      ((renewalBankNext ring r root).2.sites root).controller =
        .active p → p.origin = some o → False) ∧
    ¬ BankWindowTainted (renewalBankNext ring r root)
      (ring.rightNeighbor root) ∧
    ((renewalBankNext ring r root).1 root).mode ≠ .RWAIT := by
  obtain ⟨p, hactiveOld, hnone⟩ :=
    bankWindowOverlapIncompleteActiveRootInherited
      ring r root hJ hx hnot hphase
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have holdEmpty :
      (r.2.sites (ring.rightNeighbor root)).worker = .empty := by
    have hs := (hJ.frame (ring.rightNeighbor root)).2
    simpa [bankInFlightWorkerShape, ht] using hs
  have hframe := (rbReferenceSelectedPairFrame
    ring (by omega : 2 ≤ n) r root).2.2
  have hsource := congrArg
    (fun ss : RenewalBankSite n => ss.controller) hframe.1
  have htarget := congrArg
    (fun ss : RenewalBankSite n => ss.worker) hframe.2
  change ((renewalBankNext ring r root).2.sites root).controller =
    (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
      r.2 root (ring.rightNeighbor root)
      (r.1 root) (r.1 (ring.rightNeighbor root))).1.controller
    at hsource
  change ((renewalBankNext ring r root).2.sites
      (ring.rightNeighbor root)).worker =
    (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
      r.2 root (ring.rightNeighbor root)
      (r.1 root) (r.1 (ring.rightNeighbor root))).2.worker
    at htarget
  have htrip := (bankWindowClosureSelectedBankTrip
    ring hn hbank r root).1
  have hmode := congrArg
    (fun t : Mode × Bool × BTok => t.1) htrip
  change ((renewalBankNext ring r root).1 root).mode =
    (Counter.resetBankOld (r.1 root)
      (r.1 (ring.rightNeighbor root))).1.mode at hmode
  rcases hphase with harm | hstart
  · have hphysical := (bankWindowOverlapSourceArmedEmptyPhysical
      (r.1 root) (r.1 (ring.rightNeighbor root))
      hx hy hg harm ht).1
    cases hbit : (r.1 (ring.rightNeighbor root)).bit with
    | false =>
        have hrow := rbArmedIdleMemoryExact
          (compileAdvice (ceilLogTwo n)) r.2
          root (ring.rightNeighbor root)
          (r.1 root) (r.1 (ring.rightNeighbor root))
          hb hx hy hg harm ht hbit
        rw [hrow] at hsource htarget
        change ((renewalBankNext ring r root).2.sites root).controller =
          .active (renewalBankHead
            (renewalBankActivePayload (r.2.sites root).controller root))
          at hsource
        rw [hactiveOld] at hsource
        change ((renewalBankNext ring r root).2.sites root).controller =
          .active (renewalBankHead p) at hsource
        change ((renewalBankNext ring r root).2.sites
          (ring.rightNeighbor root)).worker =
          (r.2.sites (ring.rightNeighbor root)).worker at htarget
        have hsourceMode :
            ((renewalBankNext ring r root).1 root).mode = .CSTART := by
          have hr := hphysical
          rw [hbit] at hr
          exact hmode.trans (by simpa using hr)
        refine ⟨?_, ?_, ?_⟩
        · intro q o hq ho
          rw [hsource] at hq
          cases hq
          simp [renewalBankHead, hnone] at ho
        · intro htainted
          unfold BankWindowTainted at htainted
          rw [htarget, holdEmpty] at htainted
          rcases htainted with ⟨rho, hh⟩ |
            ⟨q, o, hh, ho⟩ <;> cases hh
        · intro hw
          rw [hsourceMode] at hw
          cases hw
    | true =>
        have hrow := rbArmedWorkMemoryExact
          (compileAdvice (ceilLogTwo n)) r.2
          root (ring.rightNeighbor root)
          (r.1 root) (r.1 (ring.rightNeighbor root))
          hb hx hy hg harm ht hbit
        rw [hrow] at hsource htarget
        change ((renewalBankNext ring r root).2.sites root).controller =
          .waiting [] at hsource
        change ((renewalBankNext ring r root).2.sites
          (ring.rightNeighbor root)).worker =
          .payload (renewalBankHead
            (renewalBankActivePayload (r.2.sites root).controller root))
          at htarget
        rw [hactiveOld] at htarget
        change ((renewalBankNext ring r root).2.sites
          (ring.rightNeighbor root)).worker =
          .payload (renewalBankHead p) at htarget
        have hsourceMode :
            ((renewalBankNext ring r root).1 root).mode = .IWAIT := by
          have hr := hphysical
          rw [hbit] at hr
          exact hmode.trans (by simpa using hr)
        refine ⟨?_, ?_, ?_⟩
        · intro q o hq ho
          rw [hsource] at hq
          cases hq
        · intro htainted
          rcases htainted with ⟨rho, hh⟩ |
            ⟨q, o, hh, ho⟩
          · rw [htarget] at hh
            cases hh
          · rw [htarget] at hh
            cases hh
            simp [renewalBankHead, hnone] at ho
        · intro hw
          rw [hsourceMode] at hw
          cases hw
  · have hrow := rbRootCstartMemoryExact
      (compileAdvice (ceilLogTwo n)) r.2
      root (ring.rightNeighbor root)
      (r.1 root) (r.1 (ring.rightNeighbor root))
      hb hx hy hg hstart ht
    rw [hrow] at hsource htarget
    change ((renewalBankNext ring r root).2.sites root).controller =
      .waiting [] at hsource
    change ((renewalBankNext ring r root).2.sites
      (ring.rightNeighbor root)).worker =
      .payload (renewalBankActivePayload
        (r.2.sites root).controller root) at htarget
    rw [hactiveOld] at htarget
    change ((renewalBankNext ring r root).2.sites
      (ring.rightNeighbor root)).worker = .payload p at htarget
    have hphysical := (bankWindowOverlapSourceCstartEmptyPhysical
      (r.1 root) (r.1 (ring.rightNeighbor root))
      hx hy hg hstart ht).1
    have hsourceMode :
        ((renewalBankNext ring r root).1 root).mode = .CWAIT :=
      hmode.trans hphysical
    refine ⟨?_, ?_, ?_⟩
    · intro q o hq ho
      rw [hsource] at hq
      cases hq
    · intro htainted
      rcases htainted with ⟨rho, hh⟩ |
        ⟨q, o, hh, ho⟩
      · rw [htarget] at hh
        cases hh
      · rw [htarget] at hh
        cases hh
        rw [hnone] at ho
        cases ho
    · intro hw
      rw [hsourceMode] at hw
      cases hw

/-- A physically aligned digit of an OLD-incomplete ARMED/CSTART
SRC window is clean after the selected root service, provided
the first responder was sanitized. All other digit sites are
off-pair and were already clean by OLD J.proto/J.orphan.
Consumer: M3 SRC empty-token issue PFX/ORPH taint tests. -/
theorem bankWindowOverlapSourceActiveEmptyAlignedClean
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (root : Fin n)
    (hJ : BankWindowExact ring (bankWindowOverlapBefore ring seed pre))
    (hnot : ¬ Counter.Complete ring (bankWindowOverlapBefore ring seed pre).1 root)
    (hx : ((bankWindowOverlapBefore ring seed pre).1 root).pack.val = 0)
    (hphase : ((bankWindowOverlapBefore ring seed pre).1 root).mode = .ARMED ∨
      ((bankWindowOverlapBefore ring seed pre).1 root).mode = .CSTART)
    (hfirst :
      ¬ BankWindowTainted (bankWindowOverlapAfter ring seed pre root)
        (ring.rightNeighbor root))
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (haligned :
      ((bankWindowOverlapAfter ring seed pre root).1
        (Counter.site ring root (j.val + 1))).pack.val =
          j.val + 1) :
    ¬ BankWindowTainted (bankWindowOverlapAfter ring seed pre root)
      (Counter.site ring root (j.val + 1)) := by
  have hnotReset :
      ((bankWindowOverlapBefore ring seed pre).1 root).mode ≠ .RESET := by
    rcases hphase with hm | hm <;>
      (intro h; rw [hm] at h; cases h)
  have hnotWait :
      ((bankWindowOverlapBefore ring seed pre).1 root).mode ≠ .RWAIT := by
    rcases hphase with hm | hm <;>
      (intro h; rw [hm] at h; cases h)
  by_cases hz : j.val = 0
  · have hsite : Counter.site ring root (j.val + 1) =
        ring.rightNeighbor root := by
      rw [hz]
      rfl
    rw [hsite]
    exact hfirst
  · have hjpositive : 1 ≤ j.val := by omega
    have hbound : j.val + 1 ≤
        (compileAdvice (ceilLogTwo n)).b + 1 := by
      have hj := j.isLt
      omega
    have hsrc :
        Counter.site ring root (j.val + 1) ≠ root := by
      have hh := bankWindowIncidenceSiteDistinct ring hbank
        root 0 (j.val + 1) (by omega) hbound
      change root ≠ Counter.site ring root (j.val + 1) at hh
      exact hh.symm
    have hdst :
        Counter.site ring root (j.val + 1) ≠
          ring.rightNeighbor root := by
      have hh := bankWindowIncidenceSiteDistinct ring hbank
        root 1 (j.val + 1) (by omega) hbound
      change ring.rightNeighbor root ≠
        Counter.site ring root (j.val + 1) at hh
      exact hh.symm
    have hf := bankWindowExactOffPairFrame ring
      (bankWindowOverlapBefore ring seed pre) root
      (Counter.site ring root (j.val + 1)) hsrc hdst
    have hrole := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
        a.pack.val) hf.1
    have holdAligned :
        ((bankWindowOverlapBefore ring seed pre).1
          (Counter.site ring root (j.val + 1))).pack.val =
            j.val + 1 := hrole.symm.trans haligned
    have holdClean := bankWindowOverlapIncompleteNonwaitAlignedClean
      ring (bankWindowOverlapBefore ring seed pre) root hJ hx hnot
      hnotReset hnotWait j holdAligned
    have hworker := congrArg
      (fun ss : RenewalBankSite n => ss.worker) hf.2
    intro ht
    have holdTainted : BankWindowTainted (bankWindowOverlapBefore ring seed pre)
        (Counter.site ring root (j.val + 1)) := by
      unfold BankWindowTainted at ht ⊢
      rw [hworker] at ht
      exact ht
    exact holdClean holdTainted

/-- OLD-incomplete grant-free ARMED or CSTART source, OLD first
responder PACK one and token E. The real BANK row either sets
the ARMED head, issues an inherited IR, or issues an inherited
CR0/CR1. All four J.proto and J.orphan consequences hold after
the service from OLD J and the literal physical/ghost pair.
Consumer: M3 SRC in bankWindowOverlapJoint and bankWindowExactStep. -/
theorem bankWindowOverlapSourceActiveEmptyPrefixOrphan
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (root : Fin n)
    (hJ : BankWindowExact ring (bankWindowOverlapBefore ring seed pre))
    (hnot : ¬ Counter.Complete ring (bankWindowOverlapBefore ring seed pre).1 root)
    (hx : ((bankWindowOverlapBefore ring seed pre).1 root).pack.val = 0)
    (hy : ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).pack.val = 1)
    (hg : ((bankWindowOverlapBefore ring seed pre).1 root).grant = false)
    (hphase : ((bankWindowOverlapBefore ring seed pre).1 root).mode = .ARMED ∨
      ((bankWindowOverlapBefore ring seed pre).1 root).mode = .CSTART)
    (ht : ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).tok = .E) :
    (∀ limit : Nat,
      BankWindowProtoRun ring
        (bankWindowOverlapAfter ring seed pre root) root limit →
      (∀ p o,
        ((bankWindowOverlapAfter ring seed pre root).2.sites
          root).controller = .active p →
        p.origin = some o → False) ∧
      (BankWindowInheritedController
        (bankWindowOverlapAfter ring seed pre root) root →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted
            (bankWindowOverlapAfter ring seed pre root)
            (Counter.site ring root (j.val + 1))) ∧
      ((((bankWindowOverlapAfter ring seed pre root).1 root).mode =
          .RWAIT ∧
          ((bankWindowOverlapAfter ring seed pre root).2.sites
            root).controller = .waiting []) →
        ∃ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit ∧
          ∃ rho : RenewalBankReceipt n,
            ((bankWindowOverlapAfter ring seed pre root).2.sites
              (Counter.site ring root (j.val + 1))).worker =
              .pending rho ∧
            ((bankWindowOverlapAfter ring seed pre root).1
              (Counter.site ring root (j.val + 1))).tok = .RR ∧
            bankWindowZeroPrefix ring
              (bankWindowOverlapAfter ring seed pre root)
              root (j.val + 1) ∧
            (∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
              k.val < j.val →
              ((bankWindowOverlapAfter ring seed pre root).1
                (Counter.site ring root (k.val + 1))).tok = .E)) ∧
      (((bankWindowOverlapAfter ring seed pre root).1 root).mode
          ≠ .RESET →
        ((bankWindowOverlapAfter ring seed pre root).1 root).mode
          ≠ .RWAIT →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted
            (bankWindowOverlapAfter ring seed pre root)
            (Counter.site ring root (j.val + 1)))) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowOrphanOwner ring
        (bankWindowOverlapAfter ring seed pre root) root j →
      BankWindowTainted
        (bankWindowOverlapAfter ring seed pre root)
        (Counter.site ring root (j.val + 1)) →
      ((bankWindowOverlapAfter ring seed pre root).1 root).mode =
        .RESET ∨
      (((bankWindowOverlapAfter ring seed pre root).1 root).mode =
          .RWAIT ∧
        ((bankWindowOverlapAfter ring seed pre root).2.sites
          root).controller = .waiting [])) := by
  have hfields := bankWindowOverlapSourceActiveEmptyFirstClean
    ring hn hbank (bankWindowOverlapBefore ring seed pre) root hJ hnot
    hx hy hg hphase ht
  have hclean :
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        ((bankWindowOverlapAfter ring seed pre root).1
          (Counter.site ring root (j.val + 1))).pack.val =
            j.val + 1 →
        ¬ BankWindowTainted (bankWindowOverlapAfter ring seed pre root)
          (Counter.site ring root (j.val + 1)) := by
    intro j haligned
    exact bankWindowOverlapSourceActiveEmptyAlignedClean
      ring hn hbank seed pre root hJ hnot hx hphase
      hfields.2.1 j haligned
  constructor
  · intro limit hproto
    refine ⟨hfields.1, ?_, ?_, ?_⟩
    · intro _ j hj
      exact hclean j (hproto.2.1 (j.val + 1) hj)
    · intro hwait
      exact False.elim (hfields.2.2 hwait.1)
    · intro _ _ j hj
      exact hclean j (hproto.2.1 (j.val + 1) hj)
  · intro j howner htainted
    exact False.elim (hclean j howner.2.1 htainted)

/-- An OLD-incomplete 0->1 RWAIT root with any literal
return token (RL, AL, CL0 or CL1) cannot have the
empty waiting controller. OLD J.proto demands a pending
RR front in its prefix; at the first digit that would
be either RR or E, contradicting the actual return token.
Consumer: M3 SRC RWAIT-return inherited-scratch case. -/
theorem bankWindowOverlapIncompleteRwaitReturnNoEmpty
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n)
    (hJ : BankWindowExact ring r)
    (hnot : ¬ Counter.Complete ring r.1 root)
    (hx : (r.1 root).pack.val = 0)
    (hy : (r.1 (ring.rightNeighbor root)).pack.val = 1)
    (hm : (r.1 root).mode = .RWAIT)
    (hret : isRetTok (r.1 (ring.rightNeighbor root)).tok = true) :
    (r.2.sites root).controller ≠ .waiting [] := by
  obtain ⟨limit, hproto⟩ :=
    bankWindowOverlapIncompleteProtoExists
      ring r root hx hnot
  have hpositive : 1 ≤ limit := by
    by_cases hz : limit = 0
    · have hwrong := hproto.2.2
      rw [hz] at hwrong
      change (r.1 (ring.rightNeighbor root)).pack.val ≠ 1
        at hwrong
      exact False.elim (hwrong hy)
    · omega
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hnotRR :
      (r.1 (ring.rightNeighbor root)).tok ≠ .RR := by
    intro ht
    rw [ht] at hret
    simp [isRetTok] at hret
  have hnotE :
      (r.1 (ring.rightNeighbor root)).tok ≠ .E := by
    intro ht
    rw [ht] at hret
    simp [isRetTok] at hret
  intro hempty
  obtain ⟨j, hj, rho, hworker, htok, hzero, hbefore⟩ :=
    (hJ.proto root limit hproto).2.2.1 ⟨hm, hempty⟩
  by_cases hz : j.val = 0
  · have hfirst : (r.1 (ring.rightNeighbor root)).tok = .RR := by
      rw [hz] at htok
      change (r.1 (ring.rightNeighbor root)).tok = .RR at htok
      exact htok
    exact hnotRR hfirst
  · have hfirst := hbefore
      (⟨0, hb⟩ : Fin (compileAdvice (ceilLogTwo n)).b)
      (show 0 < j.val by omega)
    change (r.1 (ring.rightNeighbor root)).tok = .E at hfirst
    exact hnotE hfirst

/-- The OLD RWAIT return-token root is inherited, not
empty-wait, and neither proto-prefix nor orphaned aligned
digit can contain a tainted worker. The exact RWAIT clause
of OLD J is used; no completed-window assumption.
Consumer: M3 SRC RWAIT RL/AL/CL0/CL1 first digit and suffix. -/
theorem bankWindowOverlapIncompleteRwaitReturnAlignedClean
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n)
    (hJ : BankWindowExact ring r)
    (hnot : ¬ Counter.Complete ring r.1 root)
    (hx : (r.1 root).pack.val = 0)
    (hy : (r.1 (ring.rightNeighbor root)).pack.val = 1)
    (hm : (r.1 root).mode = .RWAIT)
    (hret : isRetTok (r.1 (ring.rightNeighbor root)).tok = true)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (haligned :
      (r.1 (Counter.site ring root (j.val + 1))).pack.val =
        j.val + 1) :
    ¬ BankWindowTainted r
      (Counter.site ring root (j.val + 1)) := by
  have hnoEmpty := bankWindowOverlapIncompleteRwaitReturnNoEmpty
    ring r root hJ hnot hx hy hm hret
  have hshape :
      ∃ atoms : List (RenewalBankAtom n),
        (r.2.sites root).controller = .waiting atoms := by
    have hh := (hJ.frame root).1
    simpa [bankInFlightControllerShape, hx, hm] using hh
  obtain ⟨atoms, hctl⟩ := hshape
  have hnonempty : atoms ≠ [] := by
    intro he
    apply hnoEmpty
    rw [he] at hctl
    exact hctl
  have hinherited : BankWindowInheritedController r root :=
    Or.inl ⟨atoms, hctl, hnonempty⟩
  obtain ⟨limit, hproto⟩ :=
    bankWindowOverlapIncompleteProtoExists
      ring r root hx hnot
  intro htainted
  by_cases hbefore : j.val + 1 ≤ limit
  · exact ((hJ.proto root limit hproto).2.1
      hinherited j hbefore) htainted
  · have howner : BankWindowOrphanOwner ring r root j := by
      refine ⟨hx, haligned, ?_⟩
      intro hfull
      exact hproto.2.2 (hfull (limit + 1) (by omega))
    rcases hJ.orphan root j howner htainted with
      hreset | ⟨hwait, hempty⟩
    · rw [hm] at hreset
      cases hreset
    · exact hnoEmpty hempty

/-- OLD J rules out taint at every aligned digit of an
incomplete, return-token, grant-free waiting source-root.
The RWAIT case uses its inherited/earliest-RR barrier;
IWAIT/CWAIT use the non-RESET/non-RWAIT proto/orphan clauses.
Consumer: M3 SRC return-token PFX/ORPH post-clean proof. -/
theorem bankWindowOverlapIncompleteReturnAlignedClean
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n)
    (hJ : BankWindowExact ring r)
    (hnot : ¬ Counter.Complete ring r.1 root)
    (hx : (r.1 root).pack.val = 0)
    (hy : (r.1 (ring.rightNeighbor root)).pack.val = 1)
    (hphase : (r.1 root).mode = .RWAIT ∨
      (r.1 root).mode = .IWAIT ∨
      (r.1 root).mode = .CWAIT)
    (hret : isRetTok (r.1 (ring.rightNeighbor root)).tok = true)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (haligned :
      (r.1 (Counter.site ring root (j.val + 1))).pack.val =
        j.val + 1) :
    ¬ BankWindowTainted r
      (Counter.site ring root (j.val + 1)) := by
  rcases hphase with hm | hm | hm
  · exact bankWindowOverlapIncompleteRwaitReturnAlignedClean
      ring r root hJ hnot hx hy hm hret j haligned
  · have hnr : (r.1 root).mode ≠ .RESET := by
      intro h
      rw [hm] at h
      cases h
    have hnwait : (r.1 root).mode ≠ .RWAIT := by
      intro h
      rw [hm] at h
      cases h
    exact bankWindowOverlapIncompleteNonwaitAlignedClean
      ring r root hJ hx hnot hnr hnwait j haligned
  · have hnr : (r.1 root).mode ≠ .RESET := by
      intro h
      rw [hm] at h
      cases h
    have hnwait : (r.1 root).mode ≠ .RWAIT := by
      intro h
      rw [hm] at h
      cases h
    exact bankWindowOverlapIncompleteNonwaitAlignedClean
      ring r root hJ hx hnot hnr hnwait j haligned

theorem bankWindowOverlapSourceMatchedReturnPhysical
    {c : Compiled} (x y : Agent c)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hcases :
      (x.mode = .RWAIT ∧ y.tok = .RL) ∨
      (x.mode = .IWAIT ∧ y.tok = .AL) ∨
      (x.mode = .CWAIT ∧ y.tok = .CL0)) :
    ((Counter.resetBankOld x y).1.mode = .ARMED ∨
     (Counter.resetBankOld x y).1.mode = .CSTART) ∧
    (Counter.resetBankOld x y).2.tok = .E := by
  have hb : 0 < c.b := by
    change 0 < c.s + 11
    omega
  have hbz : c.b ≠ 0 := by omega
  have hp : packNext x.pack.val y.pack.val c.b = 1 := by
    rw [hx, hy]
    simp [packNext, hb]
  unfold Counter.resetBankOld
  rw [hp]
  rcases hcases with ⟨hm, ht⟩ | ⟨hm, ht⟩ | ⟨hm, ht⟩
  · simp [bankPair, bankCell, hx, hy, hg, hm, ht,
      hb, hbz, hp, isRetTok,
      Id.run_pure, Id.run_bind] <;>
      simp only [if_neg hbz, if_true, Id.run_pure] <;> rfl
  · simp [bankPair, bankCell, hx, hy, hg, hm, ht,
      hb, hbz, hp, isRetTok,
      Id.run_pure, Id.run_bind] <;>
      simp only [if_neg hbz, if_true, Id.run_pure] <;> rfl
  · simp [bankPair, bankCell, hx, hy, hg, hm, ht,
      hb, hbz, hp, isRetTok,
      Id.run_pure, Id.run_bind] <;>
      simp only [if_neg hbz, if_true, Id.run_pure] <;> rfl

/-- A returned controller cannot have a genuine origin if its
OLD worker is neither pending nor a genuine-origin payload.
This includes an empty inherited worker fallback and an
inherited worker with independent waiting ancestry.
Consumer: M3 SRC AL/IWAIT, CL0/CWAIT and inherited RL/RWAIT. -/
theorem bankWindowOverlapUntaintedReturnedOriginNone
    {n : Nat} (controller : RenewalBankController n)
    (worker : RenewalBankWorker n) (dest : Fin n)
    (hnoPending : ∀ rho : RenewalBankReceipt n,
      worker ≠ .pending rho)
    (hnoGenuine : ∀ (p : RenewalBankPayload n)
      (o : RenewalBankOrigin n),
      worker = .payload p → p.origin = some o → False) :
    (renewalBankReturned controller worker dest).origin = none := by
  cases hw : worker with
  | empty =>
      simp [renewalBankReturned, renewalBankWorkerPayload,
        renewalBankEntrancePayload]
  | pending rho =>
      exact False.elim (hnoPending rho hw)
  | payload p =>
      have hn : p.origin = none := by
        cases ho : p.origin with
        | none => rfl
        | some o =>
            exact False.elim (hnoGenuine p o hw ho)
      simp [renewalBankReturned, renewalBankWorkerPayload, hn]

/-- An incomplete OLD IWAIT/AL or CWAIT/CL0 source
reactivates an inherited (non-genuine) controller, and
consumes the first-digit worker. Its NEW mode is CSTART
or ARMED, never RWAIT. Consumer: M3 SRC matching-return
proto/orphan owner, bankWindowOverlapJoint. -/
theorem bankWindowOverlapSourceMatchedIncrementCompareSafe
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (root : Fin n)
    (hJ : BankWindowExact ring r)
    (hnot : ¬ Counter.Complete ring r.1 root)
    (hx : (r.1 root).pack.val = 0)
    (hy : (r.1 (ring.rightNeighbor root)).pack.val = 1)
    (hg : (r.1 root).grant = false)
    (hmatch :
      ((r.1 root).mode = .IWAIT ∧
        (r.1 (ring.rightNeighbor root)).tok = .AL) ∨
      ((r.1 root).mode = .CWAIT ∧
        (r.1 (ring.rightNeighbor root)).tok = .CL0)) :
    (∀ p o,
      ((renewalBankNext ring r root).2.sites root).controller =
        .active p → p.origin = some o → False) ∧
    ((renewalBankNext ring r root).1 root).mode ≠ .RWAIT ∧
    ((renewalBankNext ring r root).2.sites
      (ring.rightNeighbor root)).worker = .empty := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hret :
      isRetTok (r.1 (ring.rightNeighbor root)).tok = true := by
    rcases hmatch with ⟨hm, ht⟩ | ⟨hm, ht⟩ <;>
      simp [ht, isRetTok]
  have hphase :
      (r.1 root).mode = .RWAIT ∨
      (r.1 root).mode = .IWAIT ∨
      (r.1 root).mode = .CWAIT := by
    rcases hmatch with ⟨hm, _⟩ | ⟨hm, _⟩
    · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inr hm)
  have hfirst :
      ¬ BankWindowTainted r (ring.rightNeighbor root) := by
    have hclean := bankWindowOverlapIncompleteReturnAlignedClean
      ring r root hJ hnot hx hy hphase hret
      (⟨0, hb⟩ : Fin (compileAdvice (ceilLogTwo n)).b)
      (by change (r.1 (ring.rightNeighbor root)).pack.val = 1; exact hy)
    change ¬ BankWindowTainted r (ring.rightNeighbor root)
      at hclean
    exact hclean
  have hnoPending :
      ∀ rho : RenewalBankReceipt n,
        (r.2.sites (ring.rightNeighbor root)).worker ≠
          .pending rho := by
    intro rho hw
    exact hfirst (Or.inl ⟨rho, hw⟩)
  have hnoGenuine :
      ∀ (p : RenewalBankPayload n) (o : RenewalBankOrigin n),
        (r.2.sites (ring.rightNeighbor root)).worker =
          .payload p → p.origin = some o → False := by
    intro p o hw ho
    exact hfirst (Or.inr ⟨p, o, hw, ho⟩)
  have hreturned := bankWindowOverlapUntaintedReturnedOriginNone
    (r.2.sites root).controller
    (r.2.sites (ring.rightNeighbor root)).worker
    (ring.rightNeighbor root) hnoPending hnoGenuine
  have hpair := rbMatchedReturnMemoryExact
    (compileAdvice (ceilLogTwo n)) r.2 root
    (ring.rightNeighbor root)
    (r.1 root) (r.1 (ring.rightNeighbor root))
    hb hx hy hg hmatch
  have hf := (rbReferenceSelectedPairFrame
    ring (by omega : 2 ≤ n) r root).2.2
  have hctl := congrArg
    (fun ss : RenewalBankSite n => ss.controller) hf.1
  have hworker := congrArg
    (fun ss : RenewalBankSite n => ss.worker) hf.2
  change ((renewalBankNext ring r root).2.sites root).controller =
    (renewalBankPairMemory
      (compileAdvice (ceilLogTwo n)) r.2
      root (ring.rightNeighbor root)
      (r.1 root) (r.1 (ring.rightNeighbor root))).1.controller at hctl
  change ((renewalBankNext ring r root).2.sites
      (ring.rightNeighbor root)).worker =
    (renewalBankPairMemory
      (compileAdvice (ceilLogTwo n)) r.2
      root (ring.rightNeighbor root)
      (r.1 root) (r.1 (ring.rightNeighbor root))).2.worker at hworker
  rw [hpair] at hctl hworker
  change ((renewalBankNext ring r root).2.sites root).controller =
    .active (renewalBankReturned
      (r.2.sites root).controller
      (r.2.sites (ring.rightNeighbor root)).worker
      (ring.rightNeighbor root)) at hctl
  change ((renewalBankNext ring r root).2.sites
      (ring.rightNeighbor root)).worker = .empty at hworker
  have hraw := bankWindowOverlapSourceMatchedReturnPhysical
    (r.1 root) (r.1 (ring.rightNeighbor root))
    hx hy hg (by
      rcases hmatch with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h))
  have htrip := (bankWindowClosureSelectedBankTrip
    ring hn hbank r root).1
  have hmode := congrArg
    (fun t : Mode × Bool × BTok => t.1) htrip
  change ((renewalBankNext ring r root).1 root).mode =
    (Counter.resetBankOld (r.1 root)
      (r.1 (ring.rightNeighbor root))).1.mode at hmode
  refine ⟨?_, ?_, hworker⟩
  · intro p o hactive ho
    rw [hctl] at hactive
    cases hactive
    rw [hreturned] at ho
    cases ho
  · intro hh
    rcases hraw.1 with hm | hm
    · have hnew : ((renewalBankNext ring r root).1 root).mode =
          .ARMED := hmode.trans hm
      rw [hnew] at hh
      cases hh
    · have hnew : ((renewalBankNext ring r root).1 root).mode =
          .CSTART := hmode.trans hm
      rw [hnew] at hh
      cases hh


end L3.BankWindow

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- All RWAIT/IWAIT/CWAIT source return rows erase the OLD responder worker after a stable role-zero to role-one service. RESET is excluded because it creates a pending worker before the return guard. Consumer: bankWindowOverlapSourceReturnFirstClean, R11 M3. -/
theorem bankWindowOverlapReturnResponderWorkerErase
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (root dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hphase : x.mode = .RWAIT ∨ x.mode = .IWAIT ∨ x.mode = .CWAIT)
    (hret : isRetTok y.tok = true) :
    (renewalBankPairMemory c m root dest x y).2.worker =
      .empty := by
  have hb : 0 < c.b := by
    change 0 < c.s + 11
    omega
  have hbOne : 1 ≤ c.b := by omega
  have hbz : c.b ≠ 0 := by omega
  have hpzero : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  rcases hphase with hm | hm | hm <;>
    cases ht : y.tok <;>
    simp [isRetTok, ht] at hret <;>
    cases hw : (m.sites dest).worker <;>
    simp [renewalBankPairMemory, bankCell,
      hx, hy, hg, hm, ht, hw, hb, hbOne, hbz, hpzero,
      isRetTok, isWaitMode, renewalBankWaitSlot,
      Id.run_pure, Id.run_bind] <;>
    (try split) <;> rfl

/-- The actual selected waiting-source return erases the first-digit ghost, hence it cannot remain tainted. Consumer: bankWindowOverlapSourceReturnAlignedClean, R11 M3. -/
theorem bankWindowOverlapSourceReturnFirstClean
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (root : Fin n)
    (hx : ((bankWindowOverlapBefore ring seed pre).1 root).pack.val = 0)
    (hy : ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).pack.val = 1)
    (hg : ((bankWindowOverlapBefore ring seed pre).1 root).grant = false)
    (hphase :
      ((bankWindowOverlapBefore ring seed pre).1 root).mode = .RWAIT ∨
      ((bankWindowOverlapBefore ring seed pre).1 root).mode = .IWAIT ∨
      ((bankWindowOverlapBefore ring seed pre).1 root).mode = .CWAIT)
    (hret : isRetTok
      ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).tok = true) :
    ¬ BankWindowTainted (bankWindowOverlapAfter ring seed pre root)
      (ring.rightNeighbor root) := by
  have hraw := bankWindowOverlapReturnResponderWorkerErase
    (compileAdvice (ceilLogTwo n))
    ((bankWindowOverlapBefore ring seed pre).2) root (ring.rightNeighbor root)
    ((bankWindowOverlapBefore ring seed pre).1 root)
    ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root))
    hx hy hg hphase hret
  have hf := (rbReferenceSelectedPairFrame
    ring (by omega : 2 ≤ n)
    (bankWindowOverlapBefore ring seed pre) root).2.2.2
  have hworker := congrArg
    (fun ss : RenewalBankSite n => ss.worker) hf
  change ((bankWindowOverlapAfter ring seed pre root).2.sites
      (ring.rightNeighbor root)).worker =
    (renewalBankPairMemory
      (compileAdvice (ceilLogTwo n))
      ((bankWindowOverlapBefore ring seed pre).2)
      root (ring.rightNeighbor root)
      ((bankWindowOverlapBefore ring seed pre).1 root)
      ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root))).2.worker
    at hworker
  have hempty :
      ((bankWindowOverlapAfter ring seed pre root).2.sites
        (ring.rightNeighbor root)).worker = .empty :=
    hworker.trans hraw
  intro ht
  unfold BankWindowTainted at ht
  rw [hempty] at ht
  rcases ht with ⟨rho, hh⟩ |
    ⟨p, o, hh, ho⟩ <;> cases hh

/-- When the OLD RWAIT/RL worker is not pending, the returned payload is inherited and the respondent worker clears. Consumer: bankWindowOverlapSourceRwaitRlInheritedSafe, R11 M3. -/
theorem bankWindowOverlapSourceRlInheritedMemory
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (root dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
    (hm : x.mode = .RWAIT) (ht : y.tok = .RL)
    (hnoPending : ∀ rho : RenewalBankReceipt n,
      (m.sites dest).worker ≠ .pending rho) :
    (renewalBankPairMemory c m root dest x y).1.controller =
      .active (renewalBankReturned
        (m.sites root).controller
        (m.sites dest).worker dest) ∧
    (renewalBankPairMemory c m root dest x y).2.worker =
      .empty := by
  have hb : 0 < c.b := by
    change 0 < c.s + 11
    omega
  have hbz : c.b ≠ 0 := by omega
  have hpzero : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  cases hw : (m.sites dest).worker with
  | empty =>
      simp [renewalBankPairMemory, bankCell,
        hx, hy, hg, hm, ht, hw, hb, hbz, hpzero,
        isRetTok, renewalBankReturned,
        Id.run_pure, Id.run_bind] <;> rfl
  | pending rho =>
      exact False.elim (hnoPending rho hw)
  | payload p =>
      simp [renewalBankPairMemory, bankCell,
        hx, hy, hg, hm, ht, hw, hb, hbz, hpzero,
        isRetTok, renewalBankReturned,
        Id.run_pure, Id.run_bind] <;> rfl

/-- OLD-incomplete RWAIT/RL excludes pending and genuine source-origin workers, and its return is not a RWAIT controller. Consumer: bankWindowOverlapSourceRwaitRlPrefixOrphan, R11 M3. -/
theorem bankWindowOverlapSourceRwaitRlInheritedSafe
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (root : Fin n)
    (hJ : BankWindowExact ring r)
    (hnot : ¬ Counter.Complete ring r.1 root)
    (hx : (r.1 root).pack.val = 0)
    (hy : (r.1 (ring.rightNeighbor root)).pack.val = 1)
    (hg : (r.1 root).grant = false)
    (hm : (r.1 root).mode = .RWAIT)
    (ht : (r.1 (ring.rightNeighbor root)).tok = .RL) :
    (∀ p o,
      ((renewalBankNext ring r root).2.sites root).controller =
        .active p → p.origin = some o → False) ∧
    ((renewalBankNext ring r root).1 root).mode ≠ .RWAIT ∧
    ((renewalBankNext ring r root).2.sites
      (ring.rightNeighbor root)).worker = .empty := by
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hret : isRetTok (r.1 (ring.rightNeighbor root)).tok =
      true := by simp [ht, isRetTok]
  have hfirst :
      ¬ BankWindowTainted r (ring.rightNeighbor root) := by
    have hh := bankWindowOverlapIncompleteRwaitReturnAlignedClean
      ring r root hJ hnot hx hy hm hret
      (⟨0, hb⟩ : Fin (compileAdvice (ceilLogTwo n)).b)
      (by change (r.1 (ring.rightNeighbor root)).pack.val = 1; exact hy)
    change ¬ BankWindowTainted r (ring.rightNeighbor root) at hh
    exact hh
  have hnoPending :
      ∀ rho : RenewalBankReceipt n,
        (r.2.sites (ring.rightNeighbor root)).worker ≠
          .pending rho := by
    intro rho hw
    exact hfirst (Or.inl ⟨rho, hw⟩)
  have hnoGenuine :
      ∀ (p : RenewalBankPayload n) (o : RenewalBankOrigin n),
        (r.2.sites (ring.rightNeighbor root)).worker =
          .payload p → p.origin = some o → False := by
    intro p o hw ho
    exact hfirst (Or.inr ⟨p, o, hw, ho⟩)
  have hreturned := bankWindowOverlapUntaintedReturnedOriginNone
    (r.2.sites root).controller
    (r.2.sites (ring.rightNeighbor root)).worker
    (ring.rightNeighbor root) hnoPending hnoGenuine
  have hraw := bankWindowOverlapSourceRlInheritedMemory
    (compileAdvice (ceilLogTwo n)) r.2 root
    (ring.rightNeighbor root)
    (r.1 root) (r.1 (ring.rightNeighbor root))
    hx hy hg hm ht hnoPending
  have hf := (rbReferenceSelectedPairFrame
    ring (by omega : 2 ≤ n) r root).2.2
  have hctl := congrArg
    (fun ss : RenewalBankSite n => ss.controller) hf.1
  have hworker := congrArg
    (fun ss : RenewalBankSite n => ss.worker) hf.2
  change ((renewalBankNext ring r root).2.sites root).controller =
    (renewalBankPairMemory
      (compileAdvice (ceilLogTwo n)) r.2
      root (ring.rightNeighbor root)
      (r.1 root) (r.1 (ring.rightNeighbor root))).1.controller at hctl
  change ((renewalBankNext ring r root).2.sites
      (ring.rightNeighbor root)).worker =
    (renewalBankPairMemory
      (compileAdvice (ceilLogTwo n)) r.2
      root (ring.rightNeighbor root)
      (r.1 root) (r.1 (ring.rightNeighbor root))).2.worker at hworker
  rw [hraw.1] at hctl
  rw [hraw.2] at hworker
  have hphysical := bankWindowOverlapSourceMatchedReturnPhysical
    (r.1 root) (r.1 (ring.rightNeighbor root))
    hx hy hg (Or.inl ⟨hm, ht⟩)
  have htrip := (bankWindowClosureSelectedBankTrip
    ring hn hbank r root).1
  have hmode := congrArg
    (fun t : Mode × Bool × BTok => t.1) htrip
  change ((renewalBankNext ring r root).1 root).mode =
    (Counter.resetBankOld (r.1 root)
      (r.1 (ring.rightNeighbor root))).1.mode at hmode
  refine ⟨?_, ?_, hworker⟩
  · intro p o hactive ho
    rw [hctl] at hactive
    cases hactive
    rw [hreturned] at ho
    cases ho
  · intro hh
    rcases hphysical.1 with harm | hstart
    · have hnew : ((renewalBankNext ring r root).1 root).mode =
          .ARMED := hmode.trans harm
      rw [hnew] at hh
      cases hh
    · have hnew : ((renewalBankNext ring r root).1 root).mode =
          .CSTART := hmode.trans hstart
      rw [hnew] at hh
      cases hh

/-- At a waiting-mode return, first digit clears while all later aligned digits use off-pair OLD J frames. Consumer: bankWindowOverlapSourceRwaitRlPrefixOrphan and bankWindowOverlapSourceMatchedIncrementComparePrefixOrphan, R11 M3. -/
theorem bankWindowOverlapSourceReturnAlignedClean
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (root : Fin n)
    (hJ : BankWindowExact ring (bankWindowOverlapBefore ring seed pre))
    (hnot : ¬ Counter.Complete ring (bankWindowOverlapBefore ring seed pre).1 root)
    (hx : ((bankWindowOverlapBefore ring seed pre).1 root).pack.val = 0)
    (hy : ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).pack.val = 1)
    (hg : ((bankWindowOverlapBefore ring seed pre).1 root).grant = false)
    (hphase : ((bankWindowOverlapBefore ring seed pre).1 root).mode = .RWAIT ∨
      ((bankWindowOverlapBefore ring seed pre).1 root).mode = .IWAIT ∨
      ((bankWindowOverlapBefore ring seed pre).1 root).mode = .CWAIT)
    (hret : isRetTok
      ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).tok = true)
    (j : Fin (compileAdvice (ceilLogTwo n)).b)
    (haligned :
      ((bankWindowOverlapAfter ring seed pre root).1
        (Counter.site ring root (j.val + 1))).pack.val =
          j.val + 1) :
    ¬ BankWindowTainted (bankWindowOverlapAfter ring seed pre root)
      (Counter.site ring root (j.val + 1)) := by
  have hfirst := bankWindowOverlapSourceReturnFirstClean
    ring hn seed pre root hx hy hg hphase hret
  by_cases hz : j.val = 0
  · have hsite : Counter.site ring root (j.val + 1) =
        ring.rightNeighbor root := by
      rw [hz]
      rfl
    rw [hsite]
    exact hfirst
  · have hbound : j.val + 1 ≤
        (compileAdvice (ceilLogTwo n)).b + 1 := by
      have hj := j.isLt
      omega
    have hsrc :
        Counter.site ring root (j.val + 1) ≠ root := by
      have hh := bankWindowIncidenceSiteDistinct ring hbank
        root 0 (j.val + 1) (by omega) hbound
      change root ≠ Counter.site ring root (j.val + 1) at hh
      exact hh.symm
    have hdst :
        Counter.site ring root (j.val + 1) ≠
          ring.rightNeighbor root := by
      have hh := bankWindowIncidenceSiteDistinct ring hbank
        root 1 (j.val + 1) (by omega) hbound
      change ring.rightNeighbor root ≠
        Counter.site ring root (j.val + 1) at hh
      exact hh.symm
    have hf := bankWindowExactOffPairFrame ring
      (bankWindowOverlapBefore ring seed pre) root
      (Counter.site ring root (j.val + 1)) hsrc hdst
    have hrole := congrArg
      (fun a : Agent (compileAdvice (ceilLogTwo n)) =>
        a.pack.val) hf.1
    have holdAligned :
        ((bankWindowOverlapBefore ring seed pre).1
          (Counter.site ring root (j.val + 1))).pack.val =
            j.val + 1 := hrole.symm.trans haligned
    have holdClean := bankWindowOverlapIncompleteReturnAlignedClean
      ring (bankWindowOverlapBefore ring seed pre) root hJ hnot
      hx hy hphase hret j holdAligned
    have hworker := congrArg
      (fun ss : RenewalBankSite n => ss.worker) hf.2
    intro ht
    have holdTainted : BankWindowTainted (bankWindowOverlapBefore ring seed pre)
        (Counter.site ring root (j.val + 1)) := by
      unfold BankWindowTainted at ht ⊢
      rw [hworker] at ht
      exact ht
    exact holdClean holdTainted

/-- The selected inherited RWAIT/RL return preserves POST PFX and ORPH using the safe inherited controller and clean aligned workers. Consumer: bankWindowExactStep M3. -/
theorem bankWindowOverlapSourceRwaitRlPrefixOrphan
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (root : Fin n)
    (hJ : BankWindowExact ring (bankWindowOverlapBefore ring seed pre))
    (hnot : ¬ Counter.Complete ring (bankWindowOverlapBefore ring seed pre).1 root)
    (hx : ((bankWindowOverlapBefore ring seed pre).1 root).pack.val = 0)
    (hy : ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).pack.val = 1)
    (hg : ((bankWindowOverlapBefore ring seed pre).1 root).grant = false)
    (hm : ((bankWindowOverlapBefore ring seed pre).1 root).mode = .RWAIT)
    (ht : ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).tok = .RL) :
    (∀ limit : Nat,
      BankWindowProtoRun ring
        (bankWindowOverlapAfter ring seed pre root) root limit →
      (∀ p o,
        ((bankWindowOverlapAfter ring seed pre root).2.sites
          root).controller = .active p →
        p.origin = some o → False) ∧
      (BankWindowInheritedController
        (bankWindowOverlapAfter ring seed pre root) root →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted
            (bankWindowOverlapAfter ring seed pre root)
            (Counter.site ring root (j.val + 1))) ∧
      ((((bankWindowOverlapAfter ring seed pre root).1 root).mode =
          .RWAIT ∧
          ((bankWindowOverlapAfter ring seed pre root).2.sites
            root).controller = .waiting []) →
        ∃ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit ∧
          ∃ rho : RenewalBankReceipt n,
            ((bankWindowOverlapAfter ring seed pre root).2.sites
              (Counter.site ring root (j.val + 1))).worker =
              .pending rho ∧
            ((bankWindowOverlapAfter ring seed pre root).1
              (Counter.site ring root (j.val + 1))).tok = .RR ∧
            bankWindowZeroPrefix ring
              (bankWindowOverlapAfter ring seed pre root)
              root (j.val + 1) ∧
            (∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
              k.val < j.val →
              ((bankWindowOverlapAfter ring seed pre root).1
                (Counter.site ring root (k.val + 1))).tok = .E)) ∧
      (((bankWindowOverlapAfter ring seed pre root).1 root).mode
          ≠ .RESET →
        ((bankWindowOverlapAfter ring seed pre root).1 root).mode
          ≠ .RWAIT →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted
            (bankWindowOverlapAfter ring seed pre root)
            (Counter.site ring root (j.val + 1)))) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowOrphanOwner ring
        (bankWindowOverlapAfter ring seed pre root) root j →
      BankWindowTainted
        (bankWindowOverlapAfter ring seed pre root)
        (Counter.site ring root (j.val + 1)) →
      ((bankWindowOverlapAfter ring seed pre root).1 root).mode =
        .RESET ∨
      (((bankWindowOverlapAfter ring seed pre root).1 root).mode =
          .RWAIT ∧
        ((bankWindowOverlapAfter ring seed pre root).2.sites
          root).controller = .waiting [])) := by
  have hfields := bankWindowOverlapSourceRwaitRlInheritedSafe
    ring hn hbank (bankWindowOverlapBefore ring seed pre) root hJ hnot
    hx hy hg hm ht
  have hret :
      isRetTok ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).tok =
        true := by simp [ht, isRetTok]
  have hphase :
      ((bankWindowOverlapBefore ring seed pre).1 root).mode = .RWAIT ∨
      ((bankWindowOverlapBefore ring seed pre).1 root).mode = .IWAIT ∨
      ((bankWindowOverlapBefore ring seed pre).1 root).mode = .CWAIT := Or.inl hm
  have hclean :
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        ((bankWindowOverlapAfter ring seed pre root).1
          (Counter.site ring root (j.val + 1))).pack.val =
            j.val + 1 →
        ¬ BankWindowTainted (bankWindowOverlapAfter ring seed pre root)
          (Counter.site ring root (j.val + 1)) := by
    intro j haligned
    exact bankWindowOverlapSourceReturnAlignedClean
      ring hn hbank seed pre root hJ hnot
      hx hy hg hphase hret j haligned
  constructor
  · intro limit hproto
    refine ⟨hfields.1, ?_, ?_, ?_⟩
    · intro _ j hj
      exact hclean j (hproto.2.1 (j.val + 1) hj)
    · intro hwait
      exact False.elim (hfields.2.1 hwait.1)
    · intro _ _ j hj
      exact hclean j (hproto.2.1 (j.val + 1) hj)
  · intro j howner htainted
    exact False.elim (hclean j howner.2.1 htainted)

/-- Matched IWAIT/AL or CWAIT/CL0 return leaves no genuine active root or aligned tainted POST digit. Consumer: bankWindowExactStep M3. -/
theorem bankWindowOverlapSourceMatchedIncrementComparePrefixOrphan
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (root : Fin n)
    (hJ : BankWindowExact ring (bankWindowOverlapBefore ring seed pre))
    (hnot : ¬ Counter.Complete ring (bankWindowOverlapBefore ring seed pre).1 root)
    (hx : ((bankWindowOverlapBefore ring seed pre).1 root).pack.val = 0)
    (hy : ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).pack.val = 1)
    (hg : ((bankWindowOverlapBefore ring seed pre).1 root).grant = false)
    (hmatch :
      (((bankWindowOverlapBefore ring seed pre).1 root).mode = .IWAIT ∧
        ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).tok = .AL) ∨
      (((bankWindowOverlapBefore ring seed pre).1 root).mode = .CWAIT ∧
        ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).tok = .CL0)) :
    (∀ limit : Nat,
      BankWindowProtoRun ring
        (bankWindowOverlapAfter ring seed pre root) root limit →
      (∀ p o,
        ((bankWindowOverlapAfter ring seed pre root).2.sites
          root).controller = .active p →
        p.origin = some o → False) ∧
      (BankWindowInheritedController
        (bankWindowOverlapAfter ring seed pre root) root →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted
            (bankWindowOverlapAfter ring seed pre root)
            (Counter.site ring root (j.val + 1))) ∧
      ((((bankWindowOverlapAfter ring seed pre root).1 root).mode =
          .RWAIT ∧
          ((bankWindowOverlapAfter ring seed pre root).2.sites
            root).controller = .waiting []) →
        ∃ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit ∧
          ∃ rho : RenewalBankReceipt n,
            ((bankWindowOverlapAfter ring seed pre root).2.sites
              (Counter.site ring root (j.val + 1))).worker =
              .pending rho ∧
            ((bankWindowOverlapAfter ring seed pre root).1
              (Counter.site ring root (j.val + 1))).tok = .RR ∧
            bankWindowZeroPrefix ring
              (bankWindowOverlapAfter ring seed pre root)
              root (j.val + 1) ∧
            (∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
              k.val < j.val →
              ((bankWindowOverlapAfter ring seed pre root).1
                (Counter.site ring root (k.val + 1))).tok = .E)) ∧
      (((bankWindowOverlapAfter ring seed pre root).1 root).mode
          ≠ .RESET →
        ((bankWindowOverlapAfter ring seed pre root).1 root).mode
          ≠ .RWAIT →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted
            (bankWindowOverlapAfter ring seed pre root)
            (Counter.site ring root (j.val + 1)))) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowOrphanOwner ring
        (bankWindowOverlapAfter ring seed pre root) root j →
      BankWindowTainted
        (bankWindowOverlapAfter ring seed pre root)
        (Counter.site ring root (j.val + 1)) →
      ((bankWindowOverlapAfter ring seed pre root).1 root).mode =
        .RESET ∨
      (((bankWindowOverlapAfter ring seed pre root).1 root).mode =
          .RWAIT ∧
        ((bankWindowOverlapAfter ring seed pre root).2.sites
          root).controller = .waiting [])) := by
  have hret :
      isRetTok ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).tok =
        true := by
    rcases hmatch with ⟨hm, ht⟩ | ⟨hm, ht⟩ <;>
      simp [ht, isRetTok]
  have hphase :
      ((bankWindowOverlapBefore ring seed pre).1 root).mode = .RWAIT ∨
      ((bankWindowOverlapBefore ring seed pre).1 root).mode = .IWAIT ∨
      ((bankWindowOverlapBefore ring seed pre).1 root).mode = .CWAIT := by
    rcases hmatch with ⟨hm, _⟩ | ⟨hm, _⟩
    · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inr hm)
  have hfields := bankWindowOverlapSourceMatchedIncrementCompareSafe
    ring hn hbank (bankWindowOverlapBefore ring seed pre) root hJ hnot
    hx hy hg hmatch
  have hclean :
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        ((bankWindowOverlapAfter ring seed pre root).1
          (Counter.site ring root (j.val + 1))).pack.val =
            j.val + 1 →
        ¬ BankWindowTainted (bankWindowOverlapAfter ring seed pre root)
          (Counter.site ring root (j.val + 1)) := by
    intro j haligned
    exact bankWindowOverlapSourceReturnAlignedClean
      ring hn hbank seed pre root
      hJ hnot hx hy hg hphase hret j haligned
  constructor
  · intro limit hproto
    refine ⟨hfields.1, ?_, ?_, ?_⟩
    · intro _ j hj
      exact hclean j (hproto.2.1 (j.val + 1) hj)
    · intro hwait
      exact False.elim (hfields.2.1 hwait.1)
    · intro _ _ j hj
      exact hclean j (hproto.2.1 (j.val + 1) hj)
  · intro j howner htainted
    exact False.elim (hclean j howner.2.1 htainted)

/-- Each of the eight wrong-phase return tokens with lease > 1 preserves the OLD source mode and waiting controller. Consumer: bankWindowOverlapSourceMismatchReturnLongPrefixOrphan, R11 M3. -/
theorem bankWindowOverlapSourceMismatchReturnLongPair
    {n : Nat} (c : Compiled) (m : RenewalBankMemory n)
    (root dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false)
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
    (renewalBankPairMemory c m root dest x y).1.controller =
      (m.sites root).controller := by
  have hb : 0 < c.b := by
    change 0 < c.s + 11
    omega
  have hbz : c.b ≠ 0 := by omega
  have hwide : c.b ≠ 1 := by
    change c.s + 11 ≠ 1
    omega
  have hpzero : packNext 0 1 c.b = 1 := by
    simp [packNext, hb]
  rcases hcases with h | h | h | h | h | h | h | h <;>
    rcases h with ⟨hm, ht⟩ <;>
    constructor <;>
    simp [Counter.resetBankOld, bankPair,
      renewalBankPairMemory, renewalBankWaitSlot,
      bankCell, hx, hy, hg, hm, ht, hlong,
      hb, hbz, hwide, hpzero, isRetTok, isWaitMode,
      Id.run_pure, Id.run_bind] <;>
    (try split) <;> rfl

/-- An OLD-incomplete mismatched return with long lease preserves PFX and ORPH; no aligned tainted worker or inherited empty RWAIT is created. Consumer: bankWindowExactStep M3. -/
theorem bankWindowOverlapSourceMismatchReturnLongPrefixOrphan
    {n : Nat} (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (root : Fin n)
    (hJ : BankWindowExact ring (bankWindowOverlapBefore ring seed pre))
    (hnot : ¬ Counter.Complete ring (bankWindowOverlapBefore ring seed pre).1 root)
    (hx : ((bankWindowOverlapBefore ring seed pre).1 root).pack.val = 0)
    (hy : ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).pack.val = 1)
    (hg : ((bankWindowOverlapBefore ring seed pre).1 root).grant = false)
    (hcases : ((((bankWindowOverlapBefore ring seed pre).1 root).mode = .RWAIT ∧ ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).tok = .AL) ∨
       (((bankWindowOverlapBefore ring seed pre).1 root).mode = .RWAIT ∧ ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).tok = .CL0) ∨
       (((bankWindowOverlapBefore ring seed pre).1 root).mode = .RWAIT ∧ ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).tok = .CL1) ∨
       (((bankWindowOverlapBefore ring seed pre).1 root).mode = .IWAIT ∧ ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).tok = .RL) ∨
       (((bankWindowOverlapBefore ring seed pre).1 root).mode = .IWAIT ∧ ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).tok = .CL0) ∨
       (((bankWindowOverlapBefore ring seed pre).1 root).mode = .IWAIT ∧ ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).tok = .CL1) ∨
       (((bankWindowOverlapBefore ring seed pre).1 root).mode = .CWAIT ∧ ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).tok = .RL) ∨
       (((bankWindowOverlapBefore ring seed pre).1 root).mode = .CWAIT ∧ ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).tok = .AL)))
    (hret : isRetTok
      ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root)).tok = true)
    (hlong : 1 < ((bankWindowOverlapBefore ring seed pre).1 root).lease.val) :
    (∀ limit : Nat,
      BankWindowProtoRun ring
        (bankWindowOverlapAfter ring seed pre root) root limit →
      (∀ p o,
        ((bankWindowOverlapAfter ring seed pre root).2.sites
          root).controller = .active p →
        p.origin = some o → False) ∧
      (BankWindowInheritedController
        (bankWindowOverlapAfter ring seed pre root) root →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted
            (bankWindowOverlapAfter ring seed pre root)
            (Counter.site ring root (j.val + 1))) ∧
      ((((bankWindowOverlapAfter ring seed pre root).1 root).mode =
          .RWAIT ∧
          ((bankWindowOverlapAfter ring seed pre root).2.sites
            root).controller = .waiting []) →
        ∃ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit ∧
          ∃ rho : RenewalBankReceipt n,
            ((bankWindowOverlapAfter ring seed pre root).2.sites
              (Counter.site ring root (j.val + 1))).worker =
              .pending rho ∧
            ((bankWindowOverlapAfter ring seed pre root).1
              (Counter.site ring root (j.val + 1))).tok = .RR ∧
            bankWindowZeroPrefix ring
              (bankWindowOverlapAfter ring seed pre root)
              root (j.val + 1) ∧
            (∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
              k.val < j.val →
              ((bankWindowOverlapAfter ring seed pre root).1
                (Counter.site ring root (k.val + 1))).tok = .E)) ∧
      (((bankWindowOverlapAfter ring seed pre root).1 root).mode
          ≠ .RESET →
        ((bankWindowOverlapAfter ring seed pre root).1 root).mode
          ≠ .RWAIT →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted
            (bankWindowOverlapAfter ring seed pre root)
            (Counter.site ring root (j.val + 1)))) ∧
    (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
      BankWindowOrphanOwner ring
        (bankWindowOverlapAfter ring seed pre root) root j →
      BankWindowTainted
        (bankWindowOverlapAfter ring seed pre root)
        (Counter.site ring root (j.val + 1)) →
      ((bankWindowOverlapAfter ring seed pre root).1 root).mode =
        .RESET ∨
      (((bankWindowOverlapAfter ring seed pre root).1 root).mode =
          .RWAIT ∧
        ((bankWindowOverlapAfter ring seed pre root).2.sites
          root).controller = .waiting [])) := by
  have hraw := bankWindowOverlapSourceMismatchReturnLongPair
    (compileAdvice (ceilLogTwo n)) ((bankWindowOverlapBefore ring seed pre).2)
    root (ring.rightNeighbor root)
    ((bankWindowOverlapBefore ring seed pre).1 root)
    ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root))
    hx hy hg hcases hlong
  have htrip := (bankWindowClosureSelectedBankTrip
    ring hn hbank (bankWindowOverlapBefore ring seed pre) root).1
  have hmode := congrArg
    (fun t : Mode × Bool × BTok => t.1) htrip
  change ((bankWindowOverlapAfter ring seed pre root).1 root).mode =
    (Counter.resetBankOld
      ((bankWindowOverlapBefore ring seed pre).1 root)
      ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root))).1.mode at hmode
  have hmodeKeep :
      ((bankWindowOverlapAfter ring seed pre root).1 root).mode =
        ((bankWindowOverlapBefore ring seed pre).1 root).mode := hmode.trans hraw.1
  have hf := (rbReferenceSelectedPairFrame
    ring (by omega : 2 ≤ n)
    (bankWindowOverlapBefore ring seed pre) root).2.2.1
  have hctl := congrArg
    (fun ss : RenewalBankSite n => ss.controller) hf
  change ((bankWindowOverlapAfter ring seed pre root).2.sites root).controller =
    (renewalBankPairMemory
      (compileAdvice (ceilLogTwo n))
      ((bankWindowOverlapBefore ring seed pre).2) root (ring.rightNeighbor root)
      ((bankWindowOverlapBefore ring seed pre).1 root)
      ((bankWindowOverlapBefore ring seed pre).1 (ring.rightNeighbor root))).1.controller at hctl
  have hctlKeep :
      ((bankWindowOverlapAfter ring seed pre root).2.sites root).controller =
        ((bankWindowOverlapBefore ring seed pre).2.sites root).controller :=
    hctl.trans hraw.2
  have hphase :
      ((bankWindowOverlapBefore ring seed pre).1 root).mode = .RWAIT ∨
      ((bankWindowOverlapBefore ring seed pre).1 root).mode = .IWAIT ∨
      ((bankWindowOverlapBefore ring seed pre).1 root).mode = .CWAIT := by
    rcases hcases with
      ⟨hm, _⟩ | ⟨hm, _⟩ | ⟨hm, _⟩ |
      ⟨hm, _⟩ | ⟨hm, _⟩ | ⟨hm, _⟩ |
      ⟨hm, _⟩ | ⟨hm, _⟩
    · exact Or.inl hm
    · exact Or.inl hm
    · exact Or.inl hm
    · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inr hm)
    · exact Or.inr (Or.inr hm)
  have hnoActive :
      ∀ p o, ((bankWindowOverlapAfter ring seed pre root).2.sites root).controller =
        .active p → p.origin = some o → False := by
    have hwaitShape :
        ∃ atoms : List (RenewalBankAtom n),
          ((bankWindowOverlapBefore ring seed pre).2.sites root).controller =
            .waiting atoms := by
      rcases hphase with hm | hm | hm
      · have hh := (hJ.frame root).1
        simpa [bankInFlightControllerShape, hx, hm] using hh
      · have hh := (hJ.frame root).1
        simpa [bankInFlightControllerShape, hx, hm] using hh
      · have hh := (hJ.frame root).1
        simpa [bankInFlightControllerShape, hx, hm] using hh
    obtain ⟨atoms, hw⟩ := hwaitShape
    intro p o ha ho
    have holdActive :
        ((bankWindowOverlapBefore ring seed pre).2.sites root).controller = .active p :=
      hctlKeep.symm.trans ha
    rw [hw] at holdActive
    cases holdActive
  have hnoEmptyRwait :
      ¬ (((bankWindowOverlapAfter ring seed pre root).1 root).mode = .RWAIT ∧
        ((bankWindowOverlapAfter ring seed pre root).2.sites root).controller = .waiting []) := by
    intro hh
    have holdMode :
        ((bankWindowOverlapBefore ring seed pre).1 root).mode = .RWAIT :=
      hmodeKeep.symm.trans hh.1
    have holdCtrl :
        ((bankWindowOverlapBefore ring seed pre).2.sites root).controller = .waiting [] :=
      hctlKeep.symm.trans hh.2
    exact (bankWindowOverlapIncompleteRwaitReturnNoEmpty
      ring (bankWindowOverlapBefore ring seed pre) root hJ hnot hx hy
      holdMode hret) holdCtrl
  have hclean :
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        ((bankWindowOverlapAfter ring seed pre root).1
          (Counter.site ring root (j.val + 1))).pack.val =
            j.val + 1 →
        ¬ BankWindowTainted (bankWindowOverlapAfter ring seed pre root)
          (Counter.site ring root (j.val + 1)) := by
    intro j haligned
    exact bankWindowOverlapSourceReturnAlignedClean
      ring hn hbank seed pre root hJ hnot
      hx hy hg hphase hret j haligned
  constructor
  · intro limit hproto
    refine ⟨hnoActive, ?_, ?_, ?_⟩
    · intro _ j hj
      exact hclean j (hproto.2.1 (j.val + 1) hj)
    · intro hwait
      exact False.elim (hnoEmptyRwait hwait)
    · intro _ _ j hj
      exact hclean j (hproto.2.1 (j.val + 1) hj)
  · intro j howner htainted
    exact False.elim (hclean j howner.2.1 htainted)

end L3.BankWindow

#print axioms L3.BankWindow.bankWindowOverlapProtoInteriorOldRead
#print axioms L3.BankWindow.bankWindowOverlapProtoInteriorEarlierFrame
#print axioms L3.BankWindow.bankWindowOverlapProtoInteriorSafeFields
#print axioms L3.BankWindow.bankWindowOverlapProtoFrontBefore
#print axioms L3.BankWindow.bankWindowOverlapProtoFrontMoves
#print axioms L3.BankWindow.bankWindowOverlapProtoInteriorRemoteFrame
#print axioms L3.BankWindow.bankWindowOverlapStableInteriorResponderPack
#print axioms L3.BankWindow.bankWindowOverlapTopRejectsTaintedResponder
#print axioms L3.BankWindow.bankWindowOverlapOrphanStableSource
#print axioms L3.BankWindow.bankWindowOverlapProtoHoldPair
#print axioms L3.BankWindow.bankWindowOverlapProtoHoldSelected
#print axioms L3.BankWindow.bankWindowOverlapProtoFrontAtOrAfterResponder
#print axioms L3.BankWindow.bankWindowOverlapProtoInteriorAll
#print axioms L3.BankWindow.bankWindowOverlapProtoMismatchPredecessorExit
#print axioms L3.BankWindow.bankWindowOverlapRepairOldProtoAtPartialDigit
#print axioms L3.BankWindow.bankWindowOverlapIncomingWaitPrefixOrphan
#print axioms L3.BankWindow.bankWindowOverlapChangedResponderPrefixOrphan
#print axioms L3.BankWindow.bankWindowOverlapIncomingPhaseWaitPrefixOrphan
#print axioms L3.BankWindow.bankWindowOverlapGrantSourceResetMode
#print axioms L3.BankWindow.bankWindowOverlapRootGrantPrefixOrphan
#print axioms L3.BankWindow.bankWindowOverlapRootLaunchPrefixOrphan
#print axioms L3.BankWindow.bankWindowOverlapSelectedResponderNoPrefixOrphan
#print axioms L3.BankWindow.bankWindowOverlapSelectedRootIncidentPrefixOrphan
#print axioms L3.BankWindow.bankWindowOverlapSelectedCompleteSourceNoPrefixOrphan
#print axioms L3.BankWindow.bankWindowOverlapChangedSourceExitMode
#print axioms L3.BankWindow.bankWindowOverlapChangedSourceExitPrefixOrphan
#print axioms L3.BankWindow.bankWindowOverlapPostAlignedForeignWorkerExcluded
#print axioms L3.BankWindow.bankWindowOverlapChangedResponderForeignSlotClean
#print axioms L3.BankWindow.bankWindowOverlapBrokenRootNoEmptyWaiting
#print axioms L3.BankWindow.bankWindowOverlapBrokenRootOldAlignedClean
#print axioms L3.BankWindow.bankWindowOverlapChangedRootAlignedClean
#print axioms L3.BankWindow.bankWindowOverlapSourceRootSamePortReadSets
#print axioms L3.BankWindow.bankWindowOverlapAlignedNonrootPairCustody
#print axioms L3.BankWindow.bankWindowOverlapOldProtoInteriorPairTaintExcluded
#print axioms L3.BankWindow.bankWindowOverlapChangedLongWaitPair
#print axioms L3.BankWindow.bankWindowOverlapChangedLongWaitFields
#print axioms L3.BankWindow.bankWindowOverlapChangedLongWaitPrefixOrphan
#print axioms L3.BankWindow.bankWindowOverlapNonreturnShortWaitMode
#print axioms L3.BankWindow.bankWindowOverlapNonreturnShortWaitPrefixOrphan
#print axioms L3.BankWindow.bankWindowOverlapActiveCollisionResetMode
#print axioms L3.BankWindow.bankWindowOverlapNonreturnLongWaitPair
#print axioms L3.BankWindow.bankWindowOverlapActiveCollisionPrefixOrphan
#print axioms L3.BankWindow.bankWindowOverlapNonreturnLongWaitFields
#print axioms L3.BankWindow.bankWindowOverlapNonreturnLongWaitPrefixOrphan
#print axioms L3.BankWindow.bankWindowOverlapSourceClOneResetMode
#print axioms L3.BankWindow.bankWindowOverlapSourceClOnePrefixOrphan
#print axioms L3.BankWindow.bankWindowOverlapSourceMismatchReturnTimeoutMode
#print axioms L3.BankWindow.bankWindowOverlapSourceMismatchReturnTimeoutPrefixOrphan
#print axioms L3.BankWindow.bankWindowOverlapIncompleteProtoExists
#print axioms L3.BankWindow.bankWindowOverlapIncompleteActiveRootInherited
#print axioms L3.BankWindow.bankWindowOverlapIncompleteNonwaitAlignedClean
#print axioms L3.BankWindow.bankWindowOverlapSourceArmedEmptyPhysical
#print axioms L3.BankWindow.bankWindowOverlapSourceCstartEmptyPhysical
#print axioms L3.BankWindow.bankWindowOverlapSourceActiveEmptyFirstClean
#print axioms L3.BankWindow.bankWindowOverlapSourceActiveEmptyAlignedClean
#print axioms L3.BankWindow.bankWindowOverlapSourceActiveEmptyPrefixOrphan
#print axioms L3.BankWindow.bankWindowOverlapIncompleteRwaitReturnNoEmpty
#print axioms L3.BankWindow.bankWindowOverlapIncompleteRwaitReturnAlignedClean
#print axioms L3.BankWindow.bankWindowOverlapIncompleteReturnAlignedClean
#print axioms L3.BankWindow.bankWindowOverlapSourceMatchedReturnPhysical
#print axioms L3.BankWindow.bankWindowOverlapUntaintedReturnedOriginNone
#print axioms L3.BankWindow.bankWindowOverlapSourceMatchedIncrementCompareSafe
#print axioms L3.BankWindow.bankWindowOverlapReturnResponderWorkerErase
#print axioms L3.BankWindow.bankWindowOverlapSourceReturnFirstClean
#print axioms L3.BankWindow.bankWindowOverlapSourceRlInheritedMemory
#print axioms L3.BankWindow.bankWindowOverlapSourceRwaitRlInheritedSafe
#print axioms L3.BankWindow.bankWindowOverlapSourceReturnAlignedClean
#print axioms L3.BankWindow.bankWindowOverlapSourceRwaitRlPrefixOrphan
#print axioms L3.BankWindow.bankWindowOverlapSourceMatchedIncrementComparePrefixOrphan
#print axioms L3.BankWindow.bankWindowOverlapSourceMismatchReturnLongPair
#print axioms L3.BankWindow.bankWindowOverlapSourceMismatchReturnLongPrefixOrphan
