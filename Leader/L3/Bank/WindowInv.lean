import Leader.L3.Bank.RootPhase
import Leader.L3.RenewalReferenceClockInFlightRows

/-!
BANK-PHASE: real-reference formulation of the phase-MC invariant.
No unconditional R11 claim.
The unrestricted real-bank row closure is OPEN below.
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

/-- A complete and root-grant-free physical window. Newly complete
windows after PACK repairs must still satisfy the row invariant;
this is not automatic from the fixed-PACK model check. -/
def BankWindowScope {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n) : Prop :=
  Counter.Complete ring r.1 root ∧ (r.1 root).grant = false

def bankWindowCap (n v : Nat) : Nat :=
  min v ((compileAdvice (ceilLogTwo n)).K + 1)

def BankWindowTainted {n : Nat}
    (r : RenewalBankReference n) (i : Fin n) : Prop :=
  (∃ rho : RenewalBankReceipt n,
    (r.2.sites i).worker = .pending rho) ∨
  (∃ p : RenewalBankPayload n, ∃ o : RenewalBankOrigin n,
    (r.2.sites i).worker = .payload p ∧ p.origin = some o)

def BankWindowInheritedController {n : Nat}
    (r : RenewalBankReference n) (root : Fin n) : Prop :=
  (∃ atoms : List (RenewalBankAtom n),
    (r.2.sites root).controller = .waiting atoms ∧ atoms ≠ []) ∨
  (∃ p : RenewalBankPayload n,
    (r.2.sites root).controller = .active p ∧ p.origin = none)

def bankWindowOnlyToken {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (root i : Fin n) : Prop :=
  ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
    (r.1 (Counter.site ring root (j.val + 1))).tok ≠ .E →
      Counter.site ring root (j.val + 1) = i

def bankWindowZeroPrefix {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (root : Fin n) (last : Nat) : Prop :=
  ∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
    j.val + 1 ≤ last →
      (r.1 (Counter.site ring root (j.val + 1))).bit = false

/-- The F/P/S clause package, on the *actual* decorated BANK
reference. F_tok/F_ctl are supplied by the already proved R7
frame. F_payload, P_phase and the nontrivial S clauses do not
follow from that frame alone.

P_phase and S_cwait are global for genuine origin workers, not
restricted to a convenient fixed-PACK/no-grant submodel: genuine
R11 cuts must remain in scope. -/
structure BankWindowInv {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalBankReference n) : Prop where
  frame : BankInFlightAligned ring r
  payloadShape :
    ∀ i p, p ∈ rbSiteLivePayloads (r.2.sites i) →
      p.origin = none → p.atoms ≠ [] ∧ p.heads = 0
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
  armed :
    ∀ root o p, BankWindowScope ring r root →
      ((r.1 root).mode = .ARMED ∨
       (r.1 root).mode = .CSTART) →
      (r.2.sites root).controller = .active p →
      p.origin = some o →
      (∀ j : Fin (compileAdvice (ceilLogTwo n)).b,
        (r.1 (Counter.site ring root (j.val + 1))).tok = .E) ∧
      p.heads = bankWindowCap n (bankOriginBinaryValue ring r.1 o)
  increment :
    ∀ root o i p, BankWindowScope ring r root →
      (r.1 root).mode = .IWAIT →
      (r.2.sites root).controller = .waiting [] →
      (r.2.sites i).worker = .payload p →
      p.origin = some o → o.root = root →
      bankWindowOnlyToken ring r root i ∧
      (((r.1 i).tok = .IR ∧
          bankWindowZeroPrefix ring r root (r.1 i).pack.val ∧
          p.heads = bankWindowCap n
            (bankOriginBinaryValue ring r.1 o +
              2 ^ (r.1 i).pack.val)) ∨
       ((r.1 i).tok = .AL ∧
          p.heads = bankWindowCap n
            (bankOriginBinaryValue ring r.1 o)))
  compare :
    ∀ o i p,
      (r.2.sites i).worker = .payload p →
      p.origin = some o →
      (r.1 o.root).mode = .CWAIT →
      (r.2.sites o.root).controller = .waiting [] →
      bankWindowOnlyToken ring r o.root i ∧
      BankTrialLiveComparisonToken (r.1 i).tok ∧
      p.heads = bankWindowCap n (bankOriginBinaryValue ring r.1 o)

/-- Every actual initial payload is either the inherited worker
or the inherited controller payload, both with zero heads. -/
private theorem bankWindowInitialLiveShape {n : Nat}
    (C : HeadlineConfiguration n) (i : Fin n)
    (p : RenewalBankPayload n)
    (hp : p ∈ rbSiteLivePayloads (renewalBankInitialSite C i)) :
    p.origin = none ∧ p.atoms ≠ [] ∧ p.heads = 0 := by
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

private theorem bankWindowStartNoOrigin {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (i : Fin n) (p : RenewalBankPayload n)
    (o : RenewalBankOrigin n)
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
  have hn := (bankWindowInitialLiveShape seed.val i p hp).1
  rw [hn] at ho
  cases ho

private theorem bankWindowStartNoTainted {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (i : Fin n) :
    ¬ BankWindowTainted (renewalBankStart ring seed) i := by
  intro ht
  rcases ht with ⟨rho, hp⟩ | ⟨p, o, hw, ho⟩
  · change (renewalBankInitialSite seed.val i).worker =
      .pending rho at hp
    by_cases he : (seed.val i).tok = .E
    · simp [renewalBankInitialSite, he] at hp
    · simp [renewalBankInitialSite, he] at hp
  · exact bankWindowStartNoOrigin ring seed i p o (Or.inl hw) ho

private theorem bankWindowStartNoEmptyWait {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (root : Fin n)
    (hm : ((renewalBankStart ring seed).1 root).mode = .RWAIT)
    (hc : ((renewalBankStart ring seed).2.sites root).controller =
      .waiting []) : False := by
  change (seed.val root).mode = .RWAIT at hm
  change (renewalBankInitialSite seed.val root).controller =
    .waiting [] at hc
  by_cases hr : (seed.val root).pack.val = 0
  · simp [renewalBankInitialSite, hr, hm] at hc
  · simp [renewalBankInitialSite, hr] at hc

/-- Genuine start, not an arbitrary fabricated memory state. -/
theorem bankWindowInvStart {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring) :
    BankWindowInv ring (renewalBankStart ring seed) := by
  refine {
    frame := bankInFlightAlignedStart ring seed
    payloadShape := ?_
    phaseExcludes := ?_
    phaseComplete := ?_
    phaseUnique := ?_
    phaseFlags := ?_
    inheritedClean := ?_
    resetWait := ?_
    armed := ?_
    increment := ?_
    compare := ?_ }
  · intro i p hp _
    change p ∈ rbSiteLivePayloads
      (renewalBankInitialSite seed.val i) at hp
    have hs := bankWindowInitialLiveShape seed.val i p hp
    exact ⟨hs.2.1, hs.2.2⟩
  · intro o i p hc
    exact False.elim (bankWindowStartNoOrigin
      ring seed i p o (Or.inl hc.1) hc.2.1)
  · intro o i p hc
    exact False.elim (bankWindowStartNoOrigin
      ring seed i p o (Or.inl hc.1) hc.2.1)
  · intro o i p hc
    exact False.elim (bankWindowStartNoOrigin
      ring seed i p o (Or.inl hc.1) hc.2.1)
  · intro o i p hc
    exact False.elim (bankWindowStartNoOrigin
      ring seed i p o (Or.inl hc.1) hc.2.1)
  · intro root _ _ j
    exact bankWindowStartNoTainted ring seed
      (Counter.site ring root (j.val + 1))
  · intro root _ hm hc
    exact False.elim
      (bankWindowStartNoEmptyWait ring seed root hm hc)
  · intro root o p _ _ hc ho
    exact False.elim (bankWindowStartNoOrigin
      ring seed root p o (Or.inr hc) ho)
  · intro root o i p _ _ _ hw ho _
    exact False.elim (bankWindowStartNoOrigin
      ring seed i p o (Or.inl hw) ho)
  · intro o i p hw ho _ _
    exact False.elim (bankWindowStartNoOrigin
      ring seed i p o (Or.inl hw) ho)

/-- Every actual real edge preserves the F_tok/F_ctl component.
This includes PACK change, grant, spacer and outside edges. -/
theorem bankWindowFrameStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n)
    (h : BankWindowInv ring
      (rbRun ring (renewalBankStart ring seed) pre)) :
    BankInFlightAligned ring
      (renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e) := by
  change BankInFlightAligned ring
    (rbRun ring
      (rbRun ring (renewalBankStart ring seed) pre) [e])
  exact bankInFlightAlignedStep ring hn seed pre
    (rbRun ring (renewalBankStart ring seed) pre) e h.frame
    (rbReceiptInvBankWordOfInv ring
      (by omega : 2 ≤ n) seed hbank pre) hbank

/-- General-b literal reset launch overwrites an old worker. -/
theorem bankWindowResetLaunchErases {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b) (hx : x.pack.val = 0)
    (hy : y.pack.val = 1) (hg : x.grant = false)
    (hm : x.mode = .RESET) (p : RenewalBankPayload n) :
    (renewalBankPairMemory c m e dest x y).2.worker ≠
      .payload p := by
  exact bankRootPhaseResetLaunchDestErased
    c m e dest x y hb hx hy hg hm p

/-- General-b RR priority even when the responder has CR1. -/
theorem bankWindowRrPriority
    (b : Nat) (theta : Nat → Bool) (x y : BankCell)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (hrr : x.tok = .RR) (hcr : y.tok = .CR1) :
    (bankPair x y y.role b theta).2.tok = .RR := by
  exact bankRootPhaseRROverwritesCR
    b theta x y hx hlt hy hrr hcr

/-- Exact OPEN real reachable one-edge closure. Not an axiom. -/
def BankWindowRows {n : Nat} (ring : DirectedRing n) : Prop :=
  ∀ (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (e : Fin n),
    ReceiptInv ring seed pre
      (rbRun ring (renewalBankStart ring seed) pre) →
    BankWindowInv ring
      (rbRun ring (renewalBankStart ring seed) pre) →
    BankWindowInv ring
      (renewalBankNext ring
        (rbRun ring (renewalBankStart ring seed) pre) e)

/-- Only conditional word induction: BankWindowRows is visible. -/
theorem bankWindowInvWordOfRows {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrows : BankWindowRows ring)
    (seed : RootedSeed ring) (word : List (Fin n)) :
    BankWindowInv ring
      (rbRun ring (renewalBankStart ring seed) word) := by
  have hreverse :
      ∀ rev : List (Fin n),
        BankWindowInv ring
          (rbRun ring (renewalBankStart ring seed)
            rev.reverse) := by
    intro rev
    induction rev with
    | nil =>
        exact bankWindowInvStart ring seed
    | cons e rest ih =>
        rw [List.reverse_cons, rbRunAppend]
        change BankWindowInv ring
          (renewalBankNext ring
            (rbRun ring (renewalBankStart ring seed)
              rest.reverse) e)
        exact hrows hbank seed rest.reverse e
          (rbReceiptInvBankWordOfInv ring
            (by omega : 2 ≤ n) seed hbank rest.reverse) ih
  simpa only [List.reverse_reverse] using hreverse word.reverse

/-- A fresh CL1 cut is in the empty-wait S_cwait case. -/
private theorem bankWindowFreshWaitingEmpty {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n)
    (hcut : renewalBankCut ring r.1 r.2 e = true) :
    (r.2.sites e).controller = .waiting [] := by
  cases hc : (r.2.sites e).controller with
  | empty =>
      simp [renewalBankCut, renewalBankFreshPayer, hc] at hcut
  | active p =>
      simp [renewalBankCut, renewalBankFreshPayer, hc] at hcut
  | waiting atoms =>
      cases atoms with
      | nil => rfl
      | cons a rest =>
          cases hw : (r.2.sites (ring.rightNeighbor e)).worker <;>
            simp [renewalBankCut, renewalBankFreshPayer, hc, hw] at hcut

/-- CWAIT + CL1 fixes current bits at theta; S_cwait gives
heads = cap(K) = K, and ReceiptInv converts to rbHeadCount. -/
theorem bankCutGenuineHeadThresholdOfWindowInv {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hwords : ∀ (seed : RootedSeed ring) (pre : List (Fin n)),
      BankWindowInv ring
        (rbRun ring (renewalBankStart ring seed) pre)) :
    BankCutGenuineHeadThreshold ring hbank := by
  have hq : 3 ≤ ceilLogTwo n := by
    have hs :
        (compileAdvice (ceilLogTwo n)).useSmall =
          decide (ceilLogTwo n ≤ qStar) := rfl
    rw [hs] at hbank
    have hnot : ¬ ceilLogTwo n ≤ qStar :=
      of_decide_eq_false hbank
    change ¬ ceilLogTwo n ≤ 79 at hnot
    omega
  intro seed pre e p o hcut hw ho
  have hroot := bankComparatorFreshCutOwnRoot
    ring hn hbank seed pre e p o hcut hw ho
  have hguard := bankComparatorCutPhysicalGuards
    ring (rbRun ring (renewalBankStart ring seed) pre)
    e hcut
  have hmode :
      ((rbRun ring (renewalBankStart ring seed) pre).1
        o.root).mode = .CWAIT := by
    rw [hroot.1]
    exact hguard.1
  have hwait :
      ((rbRun ring (renewalBankStart ring seed) pre).2.sites
        o.root).controller = .waiting [] := by
    rw [hroot.1]
    exact bankWindowFreshWaitingEmpty
      ring (rbRun ring (renewalBankStart ring seed) pre)
      e hcut
  have hcmp :
      BankComparatorOriginWorker ring
        (rbRun ring (renewalBankStart ring seed) pre)
        o (ring.rightNeighbor e) p := by
    refine ⟨hw, ho, ?_⟩
    rw [hguard.2]
    exact Or.inr (Or.inr (Or.inr rfl))
  have hmatch := ((hwords seed pre).phaseFlags
    o (ring.rightNeighbor e) p hcmp hmode).2.2.1 hguard.2
  have hbinary := bankComparatorFullMatchBinary
    ring (rbRun ring (renewalBankStart ring seed) pre)
    o hmatch
  have hcap := (hwords seed pre).compare
    o (ring.rightNeighbor e) p hw ho hmode hwait
  have hpaid : (compileAdvice (ceilLogTwo n)).K ≤ p.heads := by
    rw [hcap.2.2]
    unfold bankWindowCap
    rw [hbinary, bankComparatorThetaIsK (ceilLogTwo n) hq]
    simp
  rw [← hroot.2]
  exact hpaid

/-- The existing R11 consumer, conditional only on the real
per-prefix I. -/
theorem bankReferenceRetryCoverageOfWindowInv {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hwords : ∀ (seed : RootedSeed ring) (pre : List (Fin n)),
      BankWindowInv ring
        (rbRun ring (renewalBankStart ring seed) pre)) :
    ReferenceRetryCoverage ring hn
      (bankValidRootedReferenceData ring hbank) := by
  exact bankReferenceRetryCoverageOfHeadThreshold
    ring hn hbank
    (bankCutGenuineHeadThresholdOfWindowInv
      ring hn hbank hwords)

/-- Conditional R11 with the missing row table explicit. -/
theorem bankReferenceRetryCoverageOfWindowRows {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrows : BankWindowRows ring) :
    ReferenceRetryCoverage ring hn
      (bankValidRootedReferenceData ring hbank) := by
  apply bankReferenceRetryCoverageOfWindowInv ring hn hbank
  intro seed pre
  exact bankWindowInvWordOfRows
    ring hn hbank hrows seed pre

end L3.BankWindow

#print axioms L3.BankWindow.bankWindowInvStart
#print axioms L3.BankWindow.bankWindowFrameStep
#print axioms L3.BankWindow.bankCutGenuineHeadThresholdOfWindowInv
#print axioms L3.BankWindow.bankReferenceRetryCoverageOfWindowRows
