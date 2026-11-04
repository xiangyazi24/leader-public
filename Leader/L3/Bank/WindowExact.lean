import Leader.L3.Bank.WindowInv

/-!
BANK-PHASE: uncapped-head and repair-aware J on the real reference.

This module introduces a distinct exact J: it does not import the
capped S_armed/S_iwait/S_cwait clauses of BankWindowInv as fields.
The full J step, especially PACK completion, remains unproved.
-/

namespace L3.BankWindow

open L3
open L3.HeadlineRenewal
open L3.RenewalReferenceClock
open L3.BankComparatorExclusive
open L3.BankCounterRows
open L3.BankHeadThreshold
open L3.BankRetryCoverage
open L3.BankRootPhase
open Classical

set_option autoImplicit false
set_option Elab.async false

/-- Exact B.7 PACK fixed point for an internal complete-window
edge. Consumer: the physical responder PACK lemma below. -/
theorem bankWindowExactPackNextInside
    (b j : Nat) (hj : j < b) :
    packNext j (j + 1) b = j + 1 := by
  simp [packNext, hj]

/-- The actual grant mask does not overwrite PACK. -/
private theorem bankWindowExactMaskedResponderPack
    (c : Compiled) (mask : Bool) (x y : Agent c) :
    ((renewalMaskedPair c mask x y).2).pack.val =
      packNext x.pack.val y.pack.val c.b := by
  have hf := (renewalMaskedPairFrames c mask x y).2
  have hp := congrArg
    (fun a : Agent c => a.pack.val) hf
  change ((renewalMaskedPair c mask x y).2).pack.val =
    ((transition c x y).2).pack.val at hp
  have ht := congrArg Fin.val
    (transition_pack_pair c x y).2
  rw [roleUpdate_val] at ht
  exact hp.trans ht

/-- A real renewalBankNext responder gets exactly the B.7 PACK
successor, including when the mask suppresses a grant. -/
theorem bankWindowExactResponderPack
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e) :
    ((renewalBankNext ring r e).1
      (ring.rightNeighbor e)).pack.val =
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b := by
  have hat : renewalMaskedStep ring r.1 e
      (renewalBankCut ring r.1 r.2 e) (ring.rightNeighbor e) =
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring r.1 r.2 e)
        (r.1 e) (r.1 (ring.rightNeighbor e))).2 :=
    (if_neg hne).trans (if_pos rfl)
  change
    (renewalMaskedStep ring r.1 e
      (renewalBankCut ring r.1 r.2 e)
      (ring.rightNeighbor e)).pack.val = _
  rw [hat]
  exact bankWindowExactMaskedResponderPack
    (compileAdvice (ceilLogTwo n))
    (renewalBankCut ring r.1 r.2 e)
    (r.1 e) (r.1 (ring.rightNeighbor e))

/-- On the actual root-to-digit or digit-to-digit edge of any
complete OLD window, its responder PACK stays aligned. -/
theorem bankWindowExactCompleteDigitPackFixed
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n)
    (hcomplete : Counter.Complete ring r.1 root)
    (j : Nat) (hj : j < (compileAdvice (ceilLogTwo n)).b) :
    ((renewalBankNext ring r
      (Counter.site ring root j)).1
      (Counter.site ring root (j + 1))).pack.val =
      j + 1 := by
  have hne :
      Counter.site ring root (j + 1) ≠
        Counter.site ring root j := by
    intro he
    have hp := congrArg
      (fun i : Fin n => (r.1 i).pack.val) he
    rw [hcomplete (j + 1) (by omega),
      hcomplete j (by omega)] at hp
    omega
  have hstep := bankWindowExactResponderPack ring r
    (Counter.site ring root j) (by
      change Counter.site ring root (j + 1) ≠
        Counter.site ring root j
      exact hne)
  change
    ((renewalBankNext ring r
      (Counter.site ring root j)).1
        (Counter.site ring root (j + 1))).pack.val =
      packNext
        (r.1 (Counter.site ring root j)).pack.val
        (r.1 (Counter.site ring root (j + 1))).pack.val
        (compileAdvice (ceilLogTwo n)).b at hstep
  rw [hcomplete j (by omega),
    hcomplete (j + 1) (by omega)] at hstep
  rw [bankWindowExactPackNextInside
    (compileAdvice (ceilLogTwo n)).b j hj] at hstep
  exact hstep

/-- Both real and ghost BANK fields are framed outside the
selected pair, even if the selected pair produces a new grant. -/
theorem bankWindowExactOffPairFrame
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (e i : Fin n)
    (hsource : i ≠ e)
    (htarget : i ≠ ring.rightNeighbor e) :
    (renewalBankNext ring r e).1 i = r.1 i ∧
      ((renewalBankNext ring r e).2.sites i) =
        (r.2.sites i) := by
  constructor
  · change
      renewalMaskedStep ring r.1 e
        (renewalBankCut ring r.1 r.2 e) i = r.1 i
    simp [renewalMaskedStep, hsource, htarget]
  · change
      (renewalBankMemoryNext ring r.1 r.2 e).sites i =
        (r.2.sites i)
    simp [renewalBankMemoryNext, hsource, htarget]

/-- Case (a): the *local* complete-window physical/ghost frame
on a real off-window edge. This is not global J closure. -/
theorem bankWindowExactOffWindowFrame
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root e : Fin n)
    (houtside : Counter.OutsideSites
      (q := ceilLogTwo n) ring root e) :
    ∀ j : Nat, j ≤ (compileAdvice (ceilLogTwo n)).b →
      (renewalBankNext ring r e).1
          (Counter.site ring root j) =
        r.1 (Counter.site ring root j) ∧
      ((renewalBankNext ring r e).2.sites
          (Counter.site ring root j)) =
        (r.2.sites (Counter.site ring root j)) := by
  intro j hj
  have he := houtside j hj
  exact bankWindowExactOffPairFrame ring r e
    (Counter.site ring root j) (Ne.symm he.1) (Ne.symm he.2)

/-- A proto-run ends at the first incorrect next role, so an
aligned prefix may be present even without a complete window. -/
def BankWindowProtoRun
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n)
    (root : Fin n) (limit : Nat) : Prop :=
  limit < (compileAdvice (ceilLogTwo n)).b ∧
  (∀ j : Nat, j ≤ limit →
    (r.1 (Counter.site ring root j)).pack.val = j) ∧
  (r.1 (Counter.site ring root (limit + 1))).pack.val ≠
    limit + 1

/-- The named digit is tainted yet the PACK-zero predecessor's
aligned run fails before reaching that digit. -/
def BankWindowOrphanOwner
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n)
    (root : Fin n)
    (j : Fin (compileAdvice (ceilLogTwo n)).b) : Prop :=
  (r.1 root).pack.val = 0 ∧
  (r.1 (Counter.site ring root (j.val + 1))).pack.val =
    j.val + 1 ∧
  ¬ (∀ k : Nat, k ≤ j.val + 1 →
    (r.1 (Counter.site ring root k)).pack.val = k)

/-- Exact J: uncapped heads, explicit genuine-empty payload,
tainted uniqueness in IWAIT/CWAIT, proto-run sanitation
(a waiting proto-run root's leftmost token is its pending RR, as in
the model check, research/lean-l3/wip/phase-mc/FOLLOWUP.md), and
orphan restriction. This is a stronger *state* contract,
not yet a theorem about every reached prefix. -/
structure BankWindowExact
    {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) : Prop where
  frame : BankInFlightAligned ring r
  payloadShape :
    ∀ i p, p ∈ rbSiteLivePayloads (r.2.sites i) →
      p.origin = none → p.atoms ≠ [] ∧ p.heads = 0
  genuinePayloadEmpty :
    ∀ i p o, p ∈ rbSiteLivePayloads (r.2.sites i) →
      p.origin = some o → p.atoms = []
  phaseExcludes :
    ∀ o i p, BankComparatorOriginWorker ring r o i p →
      (r.1 o.root).mode ≠ .ARMED ∧
      (r.1 o.root).mode ≠ .CSTART ∧
      (r.1 o.root).mode ≠ .IWAIT
  phaseComplete :
    ∀ o i p, BankComparatorOriginWorker ring r o i p →
      (r.1 o.root).mode = .CWAIT →
      Counter.Complete ring r.1 o.root
  phaseUnique :
    ∀ o i p, BankComparatorOriginWorker ring r o i p →
      (r.1 o.root).mode = .CWAIT →
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        BankTrialLiveComparisonToken
          (r.1 (Counter.site ring o.root (j.val + 1))).tok →
        Counter.site ring o.root (j.val + 1) = i
  phaseFlags :
    ∀ o i p, BankComparatorOriginWorker ring r o i p →
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
          (compileAdvice (ceilLogTwo n)).b)
  inheritedClean :
    ∀ root, BankWindowScope ring r root →
      BankWindowInheritedController r root →
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        ¬ BankWindowTainted r
          (Counter.site ring root (j.val + 1))
  resetWait :
    ∀ root, BankWindowScope ring r root →
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
            (compileAdvice (ceilLogTwo n)).b)
  armedExact :
    ∀ root o p, BankWindowScope ring r root →
      ((r.1 root).mode = .ARMED ∨
       (r.1 root).mode = .CSTART) →
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
          (compileAdvice (ceilLogTwo n)).K)
  incrementExact :
    ∀ root o i p, BankWindowScope ring r root →
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
            (compileAdvice (ceilLogTwo n)).K))
  compareExact :
    ∀ o i p,
      (r.2.sites i).worker = .payload p →
      p.origin = some o →
      (r.1 o.root).mode = .CWAIT →
      (r.2.sites o.root).controller = .waiting [] →
      bankWindowOnlyToken ring r o.root i ∧
      BankTrialLiveComparisonToken (r.1 i).tok ∧
      p.heads = bankOriginBinaryValue ring r.1 o ∧
      bankOriginBinaryValue ring r.1 o ≤
        (compileAdvice (ceilLogTwo n)).K
  iwaitTaintedUnique :
    ∀ root, BankWindowScope ring r root →
      (r.1 root).mode = .IWAIT →
      (r.2.sites root).controller = .waiting [] →
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        BankWindowTainted r
          (Counter.site ring root (j.val + 1)) →
        ∃ o p,
          (r.2.sites (Counter.site ring root (j.val + 1))).worker =
            .payload p ∧ p.origin = some o ∧
          o.root = root ∧
          bankWindowOnlyToken ring r root
            (Counter.site ring root (j.val + 1))
  cwaitTaintedUnique :
    ∀ root, BankWindowScope ring r root →
      (r.1 root).mode = .CWAIT →
      (r.2.sites root).controller = .waiting [] →
      ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        BankWindowTainted r
          (Counter.site ring root (j.val + 1)) →
        ∃ o p,
          (r.2.sites (Counter.site ring root (j.val + 1))).worker =
            .payload p ∧ p.origin = some o ∧
          o.root = root ∧
          BankTrialLiveComparisonToken
            (r.1 (Counter.site ring root (j.val + 1))).tok ∧
          bankWindowOnlyToken ring r root
            (Counter.site ring root (j.val + 1))
  proto :
    ∀ root limit, BankWindowProtoRun ring r root limit →
      (∀ p o, (r.2.sites root).controller = .active p →
        p.origin = some o → False) ∧
      (BankWindowInheritedController r root →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted r
            (Counter.site ring root (j.val + 1))) ∧
      (((r.1 root).mode = .RWAIT ∧
          (r.2.sites root).controller = .waiting []) →
        ∃ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit ∧
          ∃ rho : RenewalBankReceipt n,
            (r.2.sites
                (Counter.site ring root (j.val + 1))).worker =
              .pending rho ∧
            (r.1 (Counter.site ring root (j.val + 1))).tok = .RR ∧
            bankWindowZeroPrefix ring r root (j.val + 1) ∧
            (∀ k : Fin (compileAdvice (ceilLogTwo n)).b,
              k.val < j.val →
              (r.1 (Counter.site ring root (k.val + 1))).tok = .E)) ∧
      ((r.1 root).mode ≠ .RESET →
        (r.1 root).mode ≠ .RWAIT →
        ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
          j.val + 1 ≤ limit →
          ¬ BankWindowTainted r
            (Counter.site ring root (j.val + 1)))
  orphan :
    ∀ root j, BankWindowOrphanOwner ring r root j →
      BankWindowTainted r
        (Counter.site ring root (j.val + 1)) →
      (r.1 root).mode = .RESET ∨
        ((r.1 root).mode = .RWAIT ∧
          (r.2.sites root).controller = .waiting [])

/-- All real entrance payloads, worker and controller, have
no genuine origin. Used by the initial exact-J proof. -/
private theorem bankWindowExactInitialPayload
    {n : Nat} (C : HeadlineConfiguration n) (i : Fin n)
    (p : RenewalBankPayload n)
    (hp : p ∈ rbSiteLivePayloads (renewalBankInitialSite C i)) :
    p.origin = none := by
  have hchoice :
      p = renewalBankEntrancePayload i false ∨
      p = renewalBankEntrancePayload i true := by
    unfold rbSiteLivePayloads at hp
    rw [List.mem_append] at hp
    rcases hp with hw | hc
    · left
      by_cases ht : (C i).tok = .E
      · simp [renewalBankInitialSite, ht] at hw
      · simpa [renewalBankInitialSite, ht] using hw
    · right
      by_cases hr : (C i).pack.val = 0
      · cases hm : (C i).mode <;>
          simp [renewalBankInitialSite, hr, hm] at hc <;>
          exact hc
      · simp [renewalBankInitialSite, hr] at hc
  rcases hchoice with hh | hh
  · rw [hh]
    simp [renewalBankEntrancePayload]
  · rw [hh]
    simp [renewalBankEntrancePayload]

private theorem bankWindowExactInitialNoOrigin
    {n : Nat} (ring : DirectedRing n)
    (seed : RootedSeed ring) (i : Fin n)
    (p : RenewalBankPayload n) (o : RenewalBankOrigin n)
    (hsite :
      ((renewalBankStart ring seed).2.sites i).worker = .payload p ∨
      ((renewalBankStart ring seed).2.sites i).controller = .active p)
    (ho : p.origin = some o) : False := by
  have hp : p ∈ rbSiteLivePayloads
      ((renewalBankStart ring seed).2.sites i) := by
    rcases hsite with hw | hc
    · simp [rbSiteLivePayloads, hw]
    · simp [rbSiteLivePayloads, hc]
  change p ∈ rbSiteLivePayloads
    (renewalBankInitialSite seed.val i) at hp
  have hn := bankWindowExactInitialPayload seed.val i p hp
  rw [hn] at ho
  cases ho

private theorem bankWindowExactInitialNoTainted
    {n : Nat} (ring : DirectedRing n)
    (seed : RootedSeed ring) (i : Fin n) :
    ¬ BankWindowTainted (renewalBankStart ring seed) i := by
  intro ht
  rcases ht with ⟨rho, hp⟩ | ⟨p, o, hw, ho⟩
  · change (renewalBankInitialSite seed.val i).worker =
      .pending rho at hp
    by_cases he : (seed.val i).tok = .E
    · simp [renewalBankInitialSite, he] at hp
    · simp [renewalBankInitialSite, he] at hp
  · exact bankWindowExactInitialNoOrigin
      ring seed i p o (Or.inl hw) ho

private theorem bankWindowExactInitialNoEmptyWait
    {n : Nat} (ring : DirectedRing n)
    (seed : RootedSeed ring) (root : Fin n)
    (hm : ((renewalBankStart ring seed).1 root).mode = .RWAIT)
    (hc : ((renewalBankStart ring seed).2.sites root).controller =
      .waiting []) : False := by
  change (seed.val root).mode = .RWAIT at hm
  change (renewalBankInitialSite seed.val root).controller =
    .waiting [] at hc
  by_cases hr : (seed.val root).pack.val = 0
  · simp [renewalBankInitialSite, hr, hm] at hc
  · simp [renewalBankInitialSite, hr] at hc

/-- J holds at renewalBankStart for arbitrary private BANK scratch:
all genuine-origin and tainted premises are empty. -/
theorem bankWindowExactStart
    {n : Nat} (ring : DirectedRing n)
    (seed : RootedSeed ring) :
    BankWindowExact ring (renewalBankStart ring seed) := by
  have hold := bankWindowInvStart ring seed
  refine {
    frame := hold.frame
    payloadShape := hold.payloadShape
    genuinePayloadEmpty := ?_
    phaseExcludes := hold.phaseExcludes
    phaseComplete := hold.phaseComplete
    phaseUnique := hold.phaseUnique
    phaseFlags := hold.phaseFlags
    inheritedClean := hold.inheritedClean
    resetWait := hold.resetWait
    armedExact := ?_
    incrementExact := ?_
    compareExact := ?_
    iwaitTaintedUnique := ?_
    cwaitTaintedUnique := ?_
    proto := ?_
    orphan := ?_ }
  · intro i p o hp ho
    change p ∈ rbSiteLivePayloads
      (renewalBankInitialSite seed.val i) at hp
    have hn := bankWindowExactInitialPayload seed.val i p hp
    rw [hn] at ho
    cases ho
  · intro root o p _ _ hc ho
    exact False.elim (bankWindowExactInitialNoOrigin
      ring seed root p o (Or.inr hc) ho)
  · intro root o i p _ _ _ hw ho _
    exact False.elim (bankWindowExactInitialNoOrigin
      ring seed i p o (Or.inl hw) ho)
  · intro o i p hw ho _ _
    exact False.elim (bankWindowExactInitialNoOrigin
      ring seed i p o (Or.inl hw) ho)
  · intro root _ _ _ j ht
    exact False.elim
      (bankWindowExactInitialNoTainted ring seed
        (Counter.site ring root (j.val + 1)) ht)
  · intro root _ _ _ j ht
    exact False.elim
      (bankWindowExactInitialNoTainted ring seed
        (Counter.site ring root (j.val + 1)) ht)
  · intro root limit _
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro p o hc ho
      exact bankWindowExactInitialNoOrigin
        ring seed root p o (Or.inr hc) ho
    · intro _ j _
      exact bankWindowExactInitialNoTainted ring seed
        (Counter.site ring root (j.val + 1))
    · intro hwait
      exact False.elim
        (bankWindowExactInitialNoEmptyWait
          ring seed root hwait.1 hwait.2)
    · intro _ _ j _
      exact bankWindowExactInitialNoTainted ring seed
        (Counter.site ring root (j.val + 1))
  · intro root j _ ht
    exact False.elim
      (bankWindowExactInitialNoTainted ring seed
        (Counter.site ring root (j.val + 1)) ht)

/-- The same unconditional R7 frame transport used by the old I
also transports the frame field of exact J on each real edge. -/
theorem bankWindowExactFrameStep
    {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (h : BankWindowExact ring
      (rbRun ring (renewalBankStart ring seed) pre)) :
    BankInFlightAligned ring
      (renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e) := by
  change BankInFlightAligned ring
    (rbRun ring
      (rbRun ring (renewalBankStart ring seed) pre) [e])
  exact bankInFlightAlignedStep ring hn seed pre
    (rbRun ring (renewalBankStart ring seed) pre) e
    h.frame
    (rbReceiptInvBankWordOfInv ring
      (by omega : 2 ≤ n) seed hbank pre) hbank

end L3.BankWindow
#print axioms L3.BankWindow.bankWindowExactPackNextInside
#print axioms L3.BankWindow.bankWindowExactResponderPack
#print axioms L3.BankWindow.bankWindowExactCompleteDigitPackFixed
#print axioms L3.BankWindow.bankWindowExactOffPairFrame
#print axioms L3.BankWindow.bankWindowExactOffWindowFrame
#print axioms L3.BankWindow.bankWindowExactStart
#print axioms L3.BankWindow.bankWindowExactFrameStep
