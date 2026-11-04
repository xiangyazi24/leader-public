import Leader.L3.Bank.Counter
import Leader.L3.Bank.PairNonroot
import Leader.L3.Bank.PairRoot

/-!
Arbitrary-scratch entry for the physical spatial counter.

The cold-stage carrier imposes no restrictions on mode, bit, worker,
or lease fields. A supported PACK defect is a distinct terminal exit.
The stochastic C.3 charge is declared as a Prop, not assumed or proved.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Complete and grant-free, with otherwise arbitrary physical scratch. -/
abbrev ResetClockBankColdCarrier {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :=
  { C : Config q n // Complete ring C root ∧ GrantFree C root }

/-- Stage one shares the actual recovery and terminal states of C.2. -/
abbrev ResetClockBankColdState {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :=
  ResetClockBankColdCarrier (q := q) ring root ⊕
    ResetClockBankRenewalState (q := q) ring root

def resetClockBankColdConfig {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ResetClockBankColdState (q := q) ring root → Config q n
  | .inl x => x.val
  | .inr y => resetClockBankRenewalConfig ring root y

/-- The first-stage target includes every entry to the renewal side.
A RESET-mode cold record is also already at its first-stage target. -/
def resetClockBankColdPhaseTarget {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ResetClockBankColdState (q := q) ring root → Prop
  | .inl x => (x.val root).mode = .RESET
  | .inr _ => True

/-- This subset of the first-stage target is an authentic C.2 handoff. -/
def resetClockBankColdRecoveryCut {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ResetClockBankColdState (q := q) ring root → Prop
  | .inr (.inl (.inr _)) => True
  | _ => False

def resetClockBankColdTerminal {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ResetClockBankColdState (q := q) ring root → Prop
  | .inl _ => False
  | .inr y => resetClockBankRenewalTarget ring root y

/-- The pre-existing defect classifier certifies every protected role. -/
theorem resetClockBankColdCompleteStep {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : ResetClockBankColdCarrier (q := q) ring root)
    (e : Fin n)
    (hno : ¬ ResetClockBankDefectEntry ring x.val root e) :
    Complete ring ((protocol q).step ring x.val e) root := by
  intro j hj
  have hs := resetClockBankStableOfNoDefect ring x.val root e hno
  have hv := congrArg Fin.val (hs j hj)
  change
    (((protocol q).step ring x.val e) (site ring root j)).pack.val =
      (x.val (site ring root j)).pack.val at hv
  rw [hv]
  exact x.property.1 j hj

/-- Zero-time injection when the old or new root is already RESET. -/
noncomputable def resetClockBankColdLift {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : Complete ring C root) (hg : GrantFree C root) :
    ResetClockBankColdState (q := q) ring root :=
  if hm : (C root).mode = .RESET then
    .inr (.inl (.inr ⟨C, ⟨hc, hg, hm⟩⟩))
  else
    .inl ⟨C, ⟨hc, hg⟩⟩

theorem resetClockBankColdLiftReset {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : Complete ring C root) (hg : GrantFree C root)
    (hm : (C root).mode = .RESET) :
    resetClockBankColdLift ring root C hc hg =
      .inr (.inl (.inr ⟨C, ⟨hc, hg, hm⟩⟩)) := by
  simp only [resetClockBankColdLift, dif_pos hm]

theorem resetClockBankColdLiftPhysical {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : Complete ring C root) (hg : GrantFree C root) :
    resetClockBankColdConfig ring root
      (resetClockBankColdLift ring root C hc hg) = C := by
  by_cases hm : (C root).mode = .RESET
  · rw [resetClockBankColdLiftReset ring root C hc hg hm]
    rfl
  · simp only [resetClockBankColdLift, dif_neg hm,
      resetClockBankColdConfig]

noncomputable def resetClockBankColdStart {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : ResetClockBankColdCarrier (q := q) ring root) :
    ResetClockBankColdState (q := q) ring root :=
  resetClockBankColdLift ring root x.val x.property.1 x.property.2

theorem resetClockBankColdStartPhysical {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : ResetClockBankColdCarrier (q := q) ring root) :
    resetClockBankColdConfig ring root
      (resetClockBankColdStart ring root x) = x.val := by
  exact resetClockBankColdLiftPhysical ring root
    x.val x.property.1 x.property.2

theorem resetClockBankColdStartReset {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : ResetClockBankColdCarrier (q := q) ring root)
    (hm : (x.val root).mode = .RESET) :
    resetClockBankColdRecoveryCut ring root
      (resetClockBankColdStart ring root x) := by
  change resetClockBankColdRecoveryCut ring root
    (resetClockBankColdLift ring root x.val
      x.property.1 x.property.2)
  rw [resetClockBankColdLiftReset ring root
    x.val x.property.1 x.property.2 hm]
  exact True.intro

/-- One real selected edge. Priority is defect, new grant, RESET,
or continued cold scratch; renewal uses its existing physical kernel. -/
noncomputable def resetClockBankColdNext {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false) :
    ResetClockBankColdState (q := q) ring root → Fin n →
      ResetClockBankColdState (q := q) ring root
  | .inl x, e =>
      if hd : ResetClockBankDefectEntry ring x.val root e then
        .inr (.inr ((protocol q).step ring x.val e, .defect))
      else if hg : GrantFree ((protocol q).step ring x.val e) root then
        resetClockBankColdLift ring root
          ((protocol q).step ring x.val e)
          (resetClockBankColdCompleteStep ring root x e hd) hg
      else
        .inr (.inr ((protocol q).step ring x.val e, .grant))
  | .inr y, e =>
      .inr (resetClockBankRenewalNext ring root hsp y e)

theorem resetClockBankColdNextDefect {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankColdCarrier (q := q) ring root)
    (e : Fin n)
    (hd : ResetClockBankDefectEntry ring x.val root e) :
    resetClockBankColdNext ring root hsp (.inl x) e =
      .inr (.inr ((protocol q).step ring x.val e, .defect)) := by
  simp only [resetClockBankColdNext, dif_pos hd]

theorem resetClockBankColdNextGrant {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankColdCarrier (q := q) ring root)
    (e : Fin n)
    (hd : ¬ ResetClockBankDefectEntry ring x.val root e)
    (hg : ¬ GrantFree ((protocol q).step ring x.val e) root) :
    resetClockBankColdNext ring root hsp (.inl x) e =
      .inr (.inr ((protocol q).step ring x.val e, .grant)) := by
  simp only [resetClockBankColdNext, dif_neg hd, dif_neg hg]

theorem resetClockBankColdNextContinue {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankColdCarrier (q := q) ring root)
    (e : Fin n)
    (hd : ¬ ResetClockBankDefectEntry ring x.val root e)
    (hg : GrantFree ((protocol q).step ring x.val e) root) :
    resetClockBankColdNext ring root hsp (.inl x) e =
      resetClockBankColdLift ring root
        ((protocol q).step ring x.val e)
        (resetClockBankColdCompleteStep ring root x e hd) hg := by
  simp only [resetClockBankColdNext, dif_neg hd, dif_pos hg]

/-- The first new RESET is handed to a genuine Recovery subtype. -/
theorem resetClockBankColdNextReset {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankColdCarrier (q := q) ring root)
    (e : Fin n)
    (hd : ¬ ResetClockBankDefectEntry ring x.val root e)
    (hg : GrantFree ((protocol q).step ring x.val e) root)
    (hm : (((protocol q).step ring x.val e) root).mode = .RESET) :
    resetClockBankColdRecoveryCut ring root
      (resetClockBankColdNext ring root hsp (.inl x) e) := by
  rw [resetClockBankColdNextContinue ring root hsp x e hd hg]
  rw [resetClockBankColdLiftReset ring root
    ((protocol q).step ring x.val e)
    (resetClockBankColdCompleteStep ring root x e hd) hg hm]
  exact True.intro

theorem resetClockBankColdNextDefectStop {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankColdCarrier (q := q) ring root)
    (e : Fin n)
    (hd : ResetClockBankDefectEntry ring x.val root e) :
    resetClockBankColdTerminal ring root
      (resetClockBankColdNext ring root hsp (.inl x) e) := by
  rw [resetClockBankColdNextDefect ring root hsp x e hd]
  exact True.intro

theorem resetClockBankColdNextGrantStop {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankColdCarrier (q := q) ring root)
    (e : Fin n)
    (hd : ¬ ResetClockBankDefectEntry ring x.val root e)
    (hg : ¬ GrantFree ((protocol q).step ring x.val e) root) :
    resetClockBankColdTerminal ring root
      (resetClockBankColdNext ring root hsp (.inl x) e) := by
  rw [resetClockBankColdNextGrant ring root hsp x e hd hg]
  exact True.intro

/-- Until a terminal cut, every scheduler letter is the real protocol. -/
theorem resetClockBankColdPhysical {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (z : ResetClockBankColdState (q := q) ring root)
    (hz : ¬ resetClockBankColdTerminal ring root z)
    (e : Fin n) :
    resetClockBankColdConfig ring root
      (resetClockBankColdNext ring root hsp z e) =
      (protocol q).step ring
        (resetClockBankColdConfig ring root z) e := by
  cases z with
  | inl x =>
      change resetClockBankColdConfig ring root
        (resetClockBankColdNext ring root hsp (.inl x) e) =
        (protocol q).step ring x.val e
      by_cases hd : ResetClockBankDefectEntry ring x.val root e
      · rw [resetClockBankColdNextDefect ring root hsp x e hd]
        rfl
      · by_cases hg : GrantFree ((protocol q).step ring x.val e) root
        · rw [resetClockBankColdNextContinue ring root hsp x e hd hg]
          exact resetClockBankColdLiftPhysical ring root
            ((protocol q).step ring x.val e)
            (resetClockBankColdCompleteStep ring root x e hd) hg
        · rw [resetClockBankColdNextGrant ring root hsp x e hd hg]
          rfl
  | inr y =>
      have hy : ¬ resetClockBankRenewalTarget ring root y := by
        intro h
        exact hz h
      change resetClockBankRenewalConfig ring root
          (resetClockBankRenewalNext ring root hsp y e) =
        (protocol q).step ring
          (resetClockBankRenewalConfig ring root y) e
      exact resetClockBankRenewalPhysical ring root hsp y hy e

/-- Exact missing C.3 Bellman certificate. This is a definition,
not a hypothesis inserted into the protocol or an asserted theorem. -/
def ResetClockBankColdCharge {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false) : Prop :=
  ∃ Φ : ResetClockBankColdState (q := q) ring root → Nat,
    (∀ z, ¬ resetClockBankColdPhaseTarget ring root z →
      n + (List.ofFn (fun e : Fin n =>
        Φ (resetClockBankColdNext ring root hsp z e))).sum ≤
        n * Φ z) ∧
    (∀ x : ResetClockBankColdCarrier (q := q) ring root,
      Φ (resetClockBankColdStart ring root x) ≤
        (2 * (compileAdvice q).bankLeaseCap +
          (compileAdvice q).b + 7) * n)

/-- Conditional C.3 first-stage bound: no existence assertion for Φ. -/
theorem resetClockBankColdFirstCostOfCharge {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hcharge : ResetClockBankColdCharge ring root hsp)
    (x : ResetClockBankColdCarrier (q := q) ring root)
    (T : Nat) :
    costNumerator (resetClockBankColdNext ring root hsp)
      (resetClockBankColdPhaseTarget ring root)
      (resetClockBankColdStart ring root x) T ≤
      n ^ T * ((2 * (compileAdvice q).bankLeaseCap +
        (compileAdvice q).b + 7) * n) := by
  obtain ⟨Φ, hdrift, hstart⟩ := hcharge
  exact Nat.le_trans
    (Prob.costNumerator_le_of_potential
      (resetClockBankColdNext ring root hsp)
      (resetClockBankColdPhaseTarget ring root)
      Φ hdrift (resetClockBankColdStart ring root x) T)
    (Nat.mul_le_mul_left (n ^ T) (hstart x))

/-- Exact coefficient arithmetic needed when C.2 is composed with C.3. -/
theorem resetClockBankColdCompositionCoefficient
    (n lease b : Nat) :
    ((2 * lease + b + 7) * n) +
      ((4 * b + 6) * n) =
        (2 * lease + 5 * b + 13) * n := by
  have hcoef :
      (2 * lease + b + 7) + (4 * b + 6) =
        2 * lease + 5 * b + 13 := by omega
  calc
    ((2 * lease + b + 7) * n) +
        ((4 * b + 6) * n) =
      ((2 * lease + b + 7) + (4 * b + 6)) * n :=
        (Nat.add_mul _ _ _).symm
    _ = (2 * lease + 5 * b + 13) * n := by rw [hcoef]

end Counter
end L3


/-!
Root-mode row audit and worker-count observables.

These lemmas do not claim the C.3 potential. The first outstanding
row certificate is the nonroot worker monotonicity.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open K2ArbitraryElimination.FiniteAccounting

/-- On an unchanged incoming root role, the literal ARMED row
preempts to RESET. Any PACK defect is handled by the stopped kernel. -/
theorem resetColdIncomingArmedBank
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : x.role ≠ 0)
    (hy : y.role = 0)
    (hg : y.grant = false)
    (hm : y.mode = .ARMED) :
    (bankPair x y 0 b theta).2.mode = .RESET := by
  simp [bankPair, hx, hy, hg, hm, isWaitMode] <;>
    repeat (first | rfl | split)

/-- In CSTART an OLD RL at digit one is not a comparator launch:
it is consumed and leaves the root in CSTART. This is the row
that prevents a drift certificate based only on mode and lease. -/
theorem resetColdComparatorReturnObstruction
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hr : x.role = 0)
    (hg : x.grant = false)
    (hy : y.role = 1)
    (hm : x.mode = .CSTART)
    (ht : y.tok = .RL)
    (hb : 1 ≤ b) :
    (bankPair x y 1 b theta).1.mode = .CSTART ∧
      (bankPair x y 1 b theta).2.tok = .E := by
  simp [bankPair, hr, hg, hy, hm, ht, hb,
    isRetTok, isWaitMode]

/-- A service with neither endpoint at the root cannot change its
BANK mode. This is a full-Agent protocol-step fact, not a replacement
BANK-only scheduler. -/
theorem resetColdNonincidentRootMode {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (he : e ≠ root)
    (hpred : ring.rightNeighbor e ≠ root) :
    (((protocol q).step ring C e) root).mode =
      (C root).mode := by
  exact congrArg (fun a : Agent (compileAdvice q) => a.mode)
    (step_frame ring C e root (Ne.symm he) (Ne.symm hpred))

/-- Observable number of nonempty worker slots on digits 1 through b.
It does not identify a token's origin or certify any worker history. -/
def resetColdWorkerCount {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) : Nat :=
  ((List.range (compileAdvice q).b).map (fun i =>
    if (C (site ring root (i + 1))).tok = .E then 0 else 1)).sum

private theorem resetColdIndicatorSumLeLength
    (xs : List Nat) (f : Nat → Nat)
    (hf : ∀ i : Nat, f i ≤ 1) :
    (xs.map f).sum ≤ xs.length := by
  induction xs with
  | nil =>
      simp
  | cons i tail ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hi : f i ≤ 1 := hf i
      omega

/-- At every physical snapshot there are at most b occupied
digit slots, including at completely arbitrary cold scratch. -/
theorem resetColdWorkerCountLe {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) :
    resetColdWorkerCount ring C root ≤ (compileAdvice q).b := by
  have hterm : ∀ i : Nat,
      (if (C (site ring root (i + 1))).tok = .E
        then 0 else 1) ≤ 1 := by
    intro i
    split <;> omega
  have hh := resetColdIndicatorSumLeLength
    (List.range (compileAdvice q).b)
    (fun i => if (C (site ring root (i + 1))).tok = .E
      then 0 else 1) hterm
  simpa [resetColdWorkerCount] using hh

/-- The bound is valid on the existing arbitrary-scratch carrier. -/
theorem resetColdCarrierWorkerCountLe {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : ResetClockBankColdCarrier (q := q) ring root) :
    resetColdWorkerCount ring x.val root ≤ (compileAdvice q).b := by
  exact resetColdWorkerCountLe ring x.val root

end Counter
end L3


/-!
BANK digit-slot accounting.
All statements use the literal Base.bankPair and the existing physical
projection; no auxiliary transition system or history axiom is added.

The literal non-root arms (Base.lean, bankPair) are, in priority order:
  changed responder role -> erase its token;
  sanitize nonworker roles -> E;
  top IR at source/responder -> E;
  source RR -> (E,RR);
  top responder RR -> (RL,E);
  responder RL -> (RL,E);
  two occupied slots -> (E,E);
  top responder CR0/CR1 -> (CL0/CL1,E);
  responder AL/CL0/CL1 -> (that return,E);
  source IR -> (E,IR/AL);
  source CR0/CR1 -> (E,CR0/CR1);
  otherwise retain the two tokens.
The incoming root seam is a non-root source edge; the root's own
token is not part of resetColdWorkerCount.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open K2ArbitraryElimination.FiniteAccounting

/-- A token uses either zero or one digit worker slot. -/
def resetColdTokenOccupied (t : BTok) : Nat :=
  if t = .E then 0 else 1

theorem resetColdTokenOccupiedLeOne (t : BTok) :
    resetColdTokenOccupied t ≤ 1 := by
  unfold resetColdTokenOccupied
  split <;> omega

theorem resetColdTokenOccupiedEmpty :
    resetColdTokenOccupied .E = 0 := by
  rfl

theorem resetColdTokenOccupiedNonempty
    (t : BTok) (ht : t ≠ .E) :
    resetColdTokenOccupied t = 1 := by
  simp [resetColdTokenOccupied, ht]

/-- The pair-count before and after a BANK edge. -/
def resetColdPairOccupied (x y : BankCell) : Nat :=
  resetColdTokenOccupied x.tok + resetColdTokenOccupied y.tok

/-- Exact unguarded-bit RR advance: the source is erased, and a
destination worker, if any, is overwritten instead of duplicated. -/
theorem resetColdBankForwardTokens
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (htx : x.tok = .RR) :
    (bankPair x y y.role b theta).1.tok = .E ∧
      (bankPair x y y.role b theta).2.tok = .RR := by
  have hxne : x.role ≠ 0 := by omega
  have hyne : y.role ≠ 0 := by omega
  have hxb : x.role ≠ b := by omega
  have hxle : x.role ≤ b := by omega
  have hyle : y.role ≤ b := by omega
  have hypos : 1 ≤ y.role := by omega
  by_cases htop : y.role = b
  · by_cases hir : y.tok = .IR
    · simp [bankPair, hxne, hyne, hx, hlt, hxle,
        hy, hyle, hypos, hxb, htx, htop, hir]
    · simp [bankPair, hxne, hyne, hx, hlt, hxle,
        hy, hyle, hypos, hxb, htx, htop, hir]
  · simp [bankPair, hxne, hyne, hx, hlt, hxle,
      hy, hyle, hypos, hxb, htx, htop]

/-- IR propagation/turnaround is exactly the existing row,
with no restriction on inherited digit bits. -/
theorem resetColdBankIncrementTokens
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (htx : x.tok = .IR) (hty : y.tok = .E) :
    (bankPair x y y.role b theta).1.tok = .E ∧
      (bankPair x y y.role b theta).2.tok =
        (if y.bit then .IR else .AL) := by
  have hh := resetBankIncrementToggleSymbolic
    x y b theta hx hlt hy htx hty
  exact ⟨hh.1, hh.2.2⟩

/-- A restricted, previously verified top turnaround is already
enough to certify a genuine RR worker does not split at the top. -/
theorem resetColdBankTopTurnTokens
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (htop : y.role = b)
    (htx : x.tok = .E) (hty : y.tok = .RR)
    (hby : y.bit = false) :
    (bankPair x y y.role b theta).1.tok = .RL ∧
      (bankPair x y y.role b theta).2.tok = .E := by
  have hh := resetTrialBankTopTurnSymbolic
    x y b theta hx hlt hy htop htx hty hby
  exact ⟨hh.1, hh.2.2.1⟩

/-- A restricted, previously verified RL retreat consumes the
source token instead of preserving two copies. -/
theorem resetColdBankRetreatTokens
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (htx : x.tok = .E) (hty : y.tok = .RL)
    (hby : y.bit = false) :
    (bankPair x y y.role b theta).1.tok = .RL ∧
      (bankPair x y y.role b theta).2.tok = .E := by
  have hh := resetTrialBankRetreatSymbolic
    x y b theta hx hlt hy htx hty hby
  exact ⟨hh.1, hh.2.2.1⟩

/-- First-match enumeration for all inherited token values in an
unchanged consecutive non-root digit pair. The top-IR sanitizer is
split before evaluating the source worker; the remaining branches
cover RR, IR, CR0/CR1, all four return tokens, collisions, and E/E.
No bit-clear or authentic-worker hypothesis is used. -/
theorem resetColdBankInteriorTwoSlotBound
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1) :
    resetColdPairOccupied
      (bankPair x y y.role b theta).1
      (bankPair x y y.role b theta).2 ≤
        resetColdPairOccupied x y := by
  have hxne : x.role ≠ 0 := by omega
  have hyne : y.role ≠ 0 := by omega
  have hxb : x.role ≠ b := by omega
  have hxle : x.role ≤ b := by omega
  have hyle : y.role ≤ b := by omega
  have hypos : 1 ≤ y.role := by omega
  have hnlt : ¬ b < x.role + 1 := by omega
  rw [bankPair_nonroot x y y.role b theta hxne]
  by_cases htop : y.role = b
  · simp [resetColdPairOccupied, resetColdTokenOccupied, bankPairNR, hxne, hyne, hx, hlt, hxle, hy, hyle, hypos, hxb, hnlt, htop, apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd, apply_ite BankCell.tok, ite_self]
    all_goals (cases hxt : x.tok <;> cases hyt : y.tok <;>
      simp [resetColdPairOccupied, resetColdTokenOccupied, bankPairNR, hxne, hyne, hx, hlt, hxle, hy, hyle, hypos, hxb, hnlt, htop, hxt, hyt, apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd, apply_ite BankCell.tok, ite_self] <;>
      repeat (first | omega | (split <;> simp [resetColdTokenOccupied])))
  · simp [resetColdPairOccupied, resetColdTokenOccupied, bankPairNR, hxne, hyne, hx, hlt, hxle, hy, hyle, hypos, hxb, hnlt, htop, apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd, apply_ite BankCell.tok, ite_self]
    all_goals (cases hxt : x.tok <;> cases hyt : y.tok <;>
      simp [resetColdPairOccupied, resetColdTokenOccupied, bankPairNR, hxne, hyne, hx, hlt, hxle, hy, hyle, hypos, hxb, hnlt, htop, hxt, hyt, apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd, apply_ite BankCell.tok, ite_self] <;>
      repeat (first | omega | (split <;> simp [resetColdTokenOccupied])))

/-- The CR0/CR1 forward family is included with arbitrary bits. -/
theorem resetColdBankComparisonFamilyBound
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (ht : x.tok = .CR0 ∨ x.tok = .CR1) :
    resetColdPairOccupied
      (bankPair x y y.role b theta).1
      (bankPair x y y.role b theta).2 ≤
        resetColdPairOccupied x y := by
  exact resetColdBankInteriorTwoSlotBound x y b theta hx hlt hy

/-- RL, AL, CL0 and CL1 return-token family. -/
theorem resetColdBankReturnFamilyBound
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (ht : y.tok = .RL ∨ y.tok = .AL ∨
      y.tok = .CL0 ∨ y.tok = .CL1) :
    resetColdPairOccupied
      (bankPair x y y.role b theta).1
      (bankPair x y y.role b theta).2 ≤
        resetColdPairOccupied x y := by
  exact resetColdBankInteriorTwoSlotBound x y b theta hx hlt hy

/-- The occupied/occupied collision family cannot increase the
number of occupied endpoints, even at the top sanitizer. -/
theorem resetColdBankCollisionFamilyBound
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (htx : x.tok ≠ .E) (hty : y.tok ≠ .E) :
    resetColdPairOccupied
      (bankPair x y y.role b theta).1
      (bankPair x y y.role b theta).2 ≤
        resetColdPairOccupied x y := by
  exact resetColdBankInteriorTwoSlotBound x y b theta hx hlt hy

/-- At an incoming-root seam from outside the protected digits,
every digit token is framed. When its source is the last digit,
the top-one-slot lemma, not this outside-source lemma, applies. -/
theorem resetColdBankIncomingSeamFrame {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hc : Complete ring C root)
    (hpred : ring.rightNeighbor e = root)
    (hout : ∀ j : Nat, 1 ≤ j → j ≤ (compileAdvice q).b →
      e ≠ site ring root j)
    (j : Nat) (hj : 1 ≤ j) (hjb : j ≤ (compileAdvice q).b) :
    (((protocol q).step ring C e)
      (site ring root j)).tok =
        (C (site ring root j)).tok := by
  have hdiff : site ring root j ≠ root :=
    resetCompleteSitesDifferent ring C root hc j 0 hjb
      (Nat.zero_le _) (by omega)
  have hframe := step_frame ring C e
    (site ring root j) (Ne.symm (hout j hj hjb))
    (by rw [hpred]; exact hdiff)
  exact congrArg (fun a : Agent (compileAdvice q) => a.tok)
    hframe

end Counter
end L3


/-!
Top source BANK token retention.

Important literal first-match detail in Base.bankPair:
the changed-responder-role branch returns BEFORE the top-source IR
eraser. Thus for x.role = b > 0, source IR is erased only if
postRole = y.role. The unconditional formula without that condition
is false, although the occupied-slot inequality remains valid.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical

/-- Exact top-source token formula, including the early return on
a responder PACK-role change. The source is never a root, and the
interior forwarding branch is disabled by x.role = b. -/
theorem resetColdBankTopSourceToken
    (x y : BankCell) (postRole b : Nat) (theta : Nat → Bool)
    (hx : x.role = b) (hb : 0 < b) :
    (bankPair x y postRole b theta).1.tok =
      (if postRole = y.role then
        (if x.tok = .IR then .E else x.tok)
      else x.tok) := by
  obtain ⟨xr, xm, xb, xt, xl, xg⟩ := x
  obtain ⟨yr, ym, yb, yt, yl, yg⟩ := y
  change xr = b at hx
  subst xr
  have hb0 : b ≠ 0 := by omega
  have hbge : 1 ≤ b := by omega
  have hnlt : ¬ b < b := by omega
  rw [bankPair_nonroot ⟨b, xm, xb, xt, xl, xg⟩ ⟨yr, ym, yb, yt, yl, yg⟩ postRole b theta hb0]
  by_cases hsame : postRole = yr
  · subst postRole
    cases xt <;>
      simp [bankPairNR, hb0, hbge, hnlt, isWaitMode, apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd, apply_ite BankCell.tok, apply_ite BankCell.role, apply_ite BankCell.bit, ite_self] <;>
      (repeat' split) <;> first | rfl | (simp_all [Id.run]) | omega
  · cases xt <;>
      simp [bankPairNR, hb0, hbge, hnlt, hsame, isWaitMode, apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd, apply_ite BankCell.tok, apply_ite BankCell.role, apply_ite BankCell.bit, ite_self] <;>
      (repeat' split) <;> first | rfl | (simp_all [Id.run]) | omega

/-- At the final digit, the initiator's worker slot can only be
retained or erased, even if the responder changes PACK role. -/
theorem resetColdBankTopOneSlotBound
    (x y : BankCell) (postRole b : Nat) (theta : Nat → Bool)
    (hx : x.role = b) (hb : 0 < b) :
    resetColdTokenOccupied
      (bankPair x y postRole b theta).1.tok ≤
        resetColdTokenOccupied x.tok := by
  by_cases he : x.tok = .E
  · rw [resetColdBankTopSourceToken x y postRole b theta hx hb]
    simp [resetColdTokenOccupied, he]
  · rw [resetColdTokenOccupiedNonempty x.tok he]
    exact resetColdTokenOccupiedLeOne _

end Counter
end L3


/-!
Explicit cold-stage BANK credit and finite-row obligations.

This section does NOT assert ResetClockBankColdCharge. The capped
credit has an unconditional initial bound, but its physical drift is
NOT proved. In particular, clipping can destroy strict drift when
an odd-n initial scratch carries a saturated IWAIT lease.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

/-- One incident service costs n/2 in the exact two-port race.
The ceiling is needed for an integer Nat-valued Bellman certificate. -/
def resetColdHalfClock (n : Nat) : Nat :=
  (n + 1) / 2

/-- ARMED pays for the fair incoming-reset / outgoing-head race. -/
def resetColdArmedCredit (n cap : Nat) : Nat :=
  2 * (resetColdHalfClock n * cap) + 4 * n

/-- CSTART pays for a whole CWAIT launch plus the created worker. -/
def resetColdComparatorCredit (n cap : Nat) : Nat :=
  resetColdArmedCredit n cap +
    resetColdHalfClock n * cap + 2 * n

/-- Scalar root-mode and lease credit. Worker slots are accounted for
separately; a raw return is not treated as an authenticated worker. -/
def resetColdModeCredit (n cap : Nat) (m : Mode) (lease : Nat) : Nat :=
  match m with
  | .RESET => 0
  | .ARMED => resetColdArmedCredit n cap
  | .RWAIT =>
      resetColdArmedCredit n cap + resetColdHalfClock n * lease
  | .IWAIT =>
      resetColdComparatorCredit n cap + resetColdHalfClock n * lease
  | .CSTART => resetColdComparatorCredit n cap
  | .CWAIT =>
      resetColdArmedCredit n cap + resetColdHalfClock n * lease

/-- The uncapped mode/lease and occupied-worker proposal.
Renewal, grant and defect cuts have zero first-stage credit. -/
def resetColdUncappedCredit {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ResetClockBankColdState (q := q) ring root → Nat
  | .inl x =>
      resetColdModeCredit n (compileAdvice q).bankLeaseCap
        (x.val root).mode (x.val root).lease.val +
        n * resetColdWorkerCount ring x.val root
  | .inr _ => 0

/-- Capping gives an initial bound for every n and arbitrary cold
scratch. This cap alone does NOT establish a Bellman drift. -/
def resetColdCappedCredit {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : ResetClockBankColdState (q := q) ring root) : Nat :=
  Nat.min (resetColdUncappedCredit ring root z)
    ((2 * (compileAdvice q).bankLeaseCap +
      (compileAdvice q).b + 7) * n)

theorem resetColdCappedCredit_start {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : ResetClockBankColdCarrier (q := q) ring root) :
    resetColdCappedCredit ring root
      (resetClockBankColdStart ring root x) ≤
        (2 * (compileAdvice q).bankLeaseCap +
          (compileAdvice q).b + 7) * n := by
  unfold resetColdCappedCredit
  exact Nat.min_le_right _ _

theorem resetColdCappedCredit_cut {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (y : ResetClockBankRenewalState (q := q) ring root) :
    resetColdCappedCredit ring root (.inr y) = 0 := by
  simp [resetColdCappedCredit, resetColdUncappedCredit]

/-! Initial arithmetic of the uncapped proposal. -/

private theorem resetColdModeCredit_le
    (n cap lease : Nat) (m : Mode) (hlease : lease ≤ cap) :
    resetColdModeCredit n cap m lease ≤
      4 * (resetColdHalfClock n * cap) + 6 * n := by
  have hw :
      resetColdHalfClock n * lease ≤
        resetColdHalfClock n * cap :=
    Nat.mul_le_mul_left _ hlease
  cases m <;>
    simp only [resetColdModeCredit, resetColdArmedCredit,
      resetColdComparatorCredit] <;> omega

theorem resetColdUncappedCredit_carrier_le {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : ResetClockBankColdCarrier (q := q) ring root) :
    resetColdUncappedCredit ring root (.inl x) ≤
      4 * (resetColdHalfClock n * (compileAdvice q).bankLeaseCap) +
        ((compileAdvice q).b + 6) * n := by
  have hlease :
      (x.val root).lease.val ≤ (compileAdvice q).bankLeaseCap := by
    have hh := (x.val root).lease.isLt
    omega
  have hm := resetColdModeCredit_le n
    (compileAdvice q).bankLeaseCap
    (x.val root).lease.val (x.val root).mode hlease
  have hw := Nat.mul_le_mul_left n
    (resetColdCarrierWorkerCountLe ring root x)
  change
    resetColdModeCredit n (compileAdvice q).bankLeaseCap
        (x.val root).mode (x.val root).lease.val +
      n * resetColdWorkerCount ring x.val root ≤ _
  calc
    _ ≤
        (4 * (resetColdHalfClock n *
          (compileAdvice q).bankLeaseCap) + 6 * n) +
          n * (compileAdvice q).b := Nat.add_le_add hm hw
    _ = 4 * (resetColdHalfClock n *
          (compileAdvice q).bankLeaseCap) +
          ((compileAdvice q).b + 6) * n := by
        rw [Nat.add_mul]
        ac_rfl

/-- The paper coefficient pays the uncapped proposal whenever
2*ceil(n/2) ≤ n, in particular on the actual even cycle sizes.
There is no such parity/size premise in ResetClockBankColdCharge. -/
theorem resetColdUncappedCredit_carrier_le_of_half {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hhalf : 2 * resetColdHalfClock n ≤ n)
    (x : ResetClockBankColdCarrier (q := q) ring root) :
    resetColdUncappedCredit ring root (.inl x) ≤
      (2 * (compileAdvice q).bankLeaseCap +
        (compileAdvice q).b + 7) * n := by
  have hp := resetColdUncappedCredit_carrier_le ring root x
  have hmul := Nat.mul_le_mul_right
    (2 * (compileAdvice q).bankLeaseCap) hhalf
  have hscale :
      4 * (resetColdHalfClock n *
        (compileAdvice q).bankLeaseCap) ≤
          (2 * (compileAdvice q).bankLeaseCap) * n := by
    calc
      _ = (2 * resetColdHalfClock n) *
          (2 * (compileAdvice q).bankLeaseCap) := by ac_rfl
      _ ≤ n * (2 * (compileAdvice q).bankLeaseCap) := hmul
      _ = (2 * (compileAdvice q).bankLeaseCap) * n := by ac_rfl
  have he :
      (2 * (compileAdvice q).bankLeaseCap +
        (compileAdvice q).b + 7) * n =
      (2 * (compileAdvice q).bankLeaseCap) * n +
        ((compileAdvice q).b + 7) * n := by
    rw [show 2 * (compileAdvice q).bankLeaseCap +
      (compileAdvice q).b + 7 =
      2 * (compileAdvice q).bankLeaseCap +
        ((compileAdvice q).b + 7) by omega, Nat.add_mul]
  calc
    _ ≤
      4 * (resetColdHalfClock n *
        (compileAdvice q).bankLeaseCap) +
        ((compileAdvice q).b + 6) * n := hp
    _ ≤ (2 * (compileAdvice q).bankLeaseCap) * n +
        ((compileAdvice q).b + 6) * n :=
      Nat.add_le_add_right hscale _
    _ ≤ (2 * (compileAdvice q).bankLeaseCap) * n +
        ((compileAdvice q).b + 7) * n :=
      Nat.add_le_add_left
        (Nat.mul_le_mul_right n (by omega :
          (compileAdvice q).b + 6 ≤ (compileAdvice q).b + 7)) _
    _ = _ := he.symm

/-! Exact abstract mode budgets (before the physical frame lift). -/

theorem resetColdHalfClock_covers (n : Nat) :
    n ≤ 2 * resetColdHalfClock n := by
  unfold resetColdHalfClock
  omega

theorem resetColdWaitPairBudget (n cap lease : Nat)
    (m : Mode) (hm : isWaitMode m = true)
    (hl : 0 < lease) :
    n + resetColdModeCredit n cap m (lease - 1) +
      resetColdModeCredit n cap m (lease - 1) ≤
        resetColdModeCredit n cap m lease +
          resetColdModeCredit n cap m lease := by
  have hstep :
      resetColdHalfClock n * lease =
        resetColdHalfClock n * (lease - 1) +
          resetColdHalfClock n := by
    calc
      _ = resetColdHalfClock n * ((lease - 1) + 1) := by
        congr 1
        omega
      _ = _ := by rw [Nat.mul_add, Nat.mul_one]
  have hclock := resetColdHalfClock_covers n
  cases m with
  | RESET => simp [isWaitMode] at hm
  | RWAIT =>
      simp only [resetColdModeCredit]
      omega
  | ARMED => simp [isWaitMode] at hm
  | IWAIT =>
      simp only [resetColdModeCredit]
      omega
  | CSTART => simp [isWaitMode] at hm
  | CWAIT =>
      simp only [resetColdModeCredit]
      omega

/-- When an ARMED outgoing service creates a fresh increment worker,
its maximal IWAIT cap is paid for by the two-port preemption credit. -/
theorem resetColdArmedHeadBudget (n cap : Nat) :
    n + (resetColdModeCredit n cap .IWAIT cap + n) =
      resetColdModeCredit n cap .ARMED 0 +
        resetColdModeCredit n cap .ARMED 0 := by
  simp only [resetColdModeCredit, resetColdComparatorCredit,
    resetColdArmedCredit]
  omega

/-- The CSTART empty-slot launch creates one occupied comparator token. -/
theorem resetColdComparatorLaunchBudget (n cap : Nat) :
    n + (resetColdModeCredit n cap .CWAIT cap + n) =
      resetColdModeCredit n cap .CSTART 0 := by
  simp only [resetColdModeCredit, resetColdComparatorCredit,
    resetColdArmedCredit]
  omega

/-- AL acceptance can enter CSTART because consuming AL returns
one worker-slot credit; no forged-AL authentication is assumed. -/
theorem resetColdIncrementReturnBudget (n cap lease : Nat) :
    n + resetColdModeCredit n cap .CSTART 0 ≤
      resetColdModeCredit n cap .IWAIT lease + n := by
  simp only [resetColdModeCredit]
  omega

/-- RL and CL0 acceptance may rearm: their consumed slot pays the
one incident charge, while their waiting-mode reserve is retained. -/
theorem resetColdReturnRearmBudget (n cap lease : Nat) :
    n + resetColdModeCredit n cap .ARMED 0 ≤
      resetColdModeCredit n cap .RWAIT lease + n ∧
    n + resetColdModeCredit n cap .ARMED 0 ≤
      resetColdModeCredit n cap .CWAIT lease + n := by
  simp only [resetColdModeCredit]
  omega

/-! Literal BANK row checks, with inherited scratch admitted. -/

/-- Incoming root service does not alter CSTART when no grant exists.
This is the unchanged-role branch; a defect exits the cold kernel. -/
theorem resetColdIncomingCStartBank
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : x.role ≠ 0) (hy : y.role = 0)
    (hg : y.grant = false) (hm : y.mode = .CSTART) :
    (bankPair x y 0 b theta).2.mode = .CSTART := by
  simp [bankPair, hx, hy, hg, hm, isWaitMode] <;>
    repeat (first | rfl | split)

/-- The known OLD-RL obstruction is paid for exactly by consuming
one occupied slot; no root-only rank would pay this service. -/
theorem resetColdCStartConsumesReturnCredit
    (n cap : Nat) (x y : BankCell) (b : Nat)
    (theta : Nat → Bool)
    (hr : x.role = 0) (hg : x.grant = false)
    (hy : y.role = 1) (hm : x.mode = .CSTART)
    (ht : y.tok = .RL) (hb : 1 ≤ b) :
    n + resetColdModeCredit n cap
        (bankPair x y 1 b theta).1.mode
        (bankPair x y 1 b theta).1.lease +
      n * resetColdTokenOccupied (bankPair x y 1 b theta).2.tok =
    resetColdModeCredit n cap x.mode x.lease +
      n * resetColdTokenOccupied y.tok := by
  have hh := resetColdComparatorReturnObstruction
    x y b theta hr hg hy hm ht hb
  rw [hh.1, hh.2, hm, ht]
  simp [resetColdModeCredit, resetColdTokenOccupied]
  omega

end Counter
end L3


/-!
Continuation of the cold BANK Bellman
certificate. The uncapped credit is retained; the capped credit is NOT used
for any drift assertion.

Proved below:
* exact two-site list-sum comparison,
* global worker-slot monotonicity for a physical INTERNAL digit edge,
* monotonicity of the uncapped stopped cold credit on such an edge,
* initial credit bound from hlarge,
* hlarge for q = ceilLogTwo n on the spatial compiler branch.

Not claimed: the full two-root-incident aggregate, top-boundary
aggregation, or ResetClockBankColdCharge_holds.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open K2ArbitraryElimination.FiniteAccounting

/-! A finite-range sum can be compared after changes at two indices. -/

private theorem resetColdRangeMapAdd (m : Nat) (f g : Nat → Nat) :
    ((List.range m).map (fun i => f i + g i)).sum =
      ((List.range m).map f).sum +
        ((List.range m).map g).sum := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [List.range_succ, List.map_append, List.sum_append,
        List.map_singleton, List.sum_cons, List.sum_nil, Nat.add_zero]
      rw [ih]
      omega

private theorem resetColdRangeMapSpike (m a v : Nat) :
    ((List.range m).map (fun i => if i = a then v else 0)).sum =
      if a < m then v else 0 := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      simp only [List.range_succ, List.map_append, List.sum_append,
        List.map_singleton, List.sum_cons, List.sum_nil, Nat.add_zero]
      rw [ih]
      by_cases ha : a < m
      · have hne : m ≠ a := by omega
        have hs : a < m + 1 := by omega
        simp [ha, hne, hs]
      · by_cases he : m = a
        · have hs : a < m + 1 := by omega
          simp [ha, he, hs]
        · have hs : ¬ a < m + 1 := by omega
          simp [ha, he, hs]

/-- A two-site conservation inequality plus pointwise framing
implies a global range-sum inequality. Neither pointwise inequality
at either of the selected positions is needed. -/
private theorem resetColdRangePairLe
    (m a c : Nat) (f g : Nat → Nat)
    (ha : a < m) (hc : c < m) (hac : a ≠ c)
    (hpair : f a + f c ≤ g a + g c)
    (hrest : ∀ i, i < m → i ≠ a → i ≠ c → f i = g i) :
    ((List.range m).map f).sum ≤
      ((List.range m).map g).sum := by
  have hrow (i : Nat) (hi : i < m) :
      (f i + (if i = a then g a else 0)) +
          (if i = c then g c else 0) =
        (g i + (if i = a then f a else 0)) +
          (if i = c then f c else 0) := by
    by_cases hia : i = a
    · subst i
      simp [hac, Nat.add_comm]
    · by_cases hic : i = c
      · subst i
        have hca : c ≠ a := Ne.symm hac
        simp [hca, Nat.add_comm]
      · simp [hia, hic, hrest i hi hia hic]
  have heq :
      ((List.range m).map (fun i =>
        (f i + (if i = a then g a else 0)) +
          (if i = c then g c else 0))).sum =
      ((List.range m).map (fun i =>
        (g i + (if i = a then f a else 0)) +
          (if i = c then f c else 0))).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro i hi
    exact hrow i (by simpa only [List.mem_range] using hi)
  have hsum :
      (((List.range m).map f).sum + g a) + g c =
        (((List.range m).map g).sum + f a) + f c := by
    simpa only [resetColdRangeMapAdd, resetColdRangeMapSpike,
      if_pos ha, if_pos hc] using heq
  omega

/-! Local BANK two-slot inequality lifted to the real global count. -/

/-- All digit slots outside a selected internal pair are framed
by the full physical protocol, and the two selected slot values
satisfy the BANK two-slot bound. This establishes a genuinely
GLOBAL, not merely pairwise, worker-count inequality. -/
theorem resetColdWorkerCountInternalPhysicalLe {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (j : Nat)
    (hc : Complete ring C root)
    (hj : 1 ≤ j) (hjlt : j < (compileAdvice q).b)
    (hsp : (compileAdvice q).useSmall = false) :
    resetColdWorkerCount ring
      ((protocol q).step ring C (site ring root j)) root ≤
        resetColdWorkerCount ring C root := by
  have hsite : site ring root (j + 1) ≠ site ring root j :=
    resetCompleteSitesDifferent ring C root hc
      (j + 1) j (by omega) (by omega) (by omega)
  have hn : 2 ≤ n := by
    by_cases htwo : 2 ≤ n
    · exact htwo
    · have hsmall : n = 1 := by
        have hh := ring.hn
        omega
      have heq : site ring root (j + 1) = site ring root j := by
        apply Fin.ext
        have ha := (site ring root (j + 1)).isLt
        have hb := (site ring root j).isLt
        omega
      exact False.elim (hsite heq)
  have hne : ring.rightNeighbor (site ring root j) ≠
      site ring root j := by
    change site ring root (j + 1) ≠ site ring root j
    exact hsite
  have hrole :
      (C (site ring root j)).pack.val = j :=
    hc j (by omega)
  have hroleNext :
      (C (site ring root (j + 1))).pack.val = j + 1 :=
    hc (j + 1) (by omega)
  have hpost :
      packNext (C (site ring root j)).pack.val
        (C (site ring root (j + 1))).pack.val
        (compileAdvice q).b = j + 1 := by
    rw [hrole, hroleNext]
    simp [packNext, hjlt]
  have hx :
      1 ≤ (bankCell (C (site ring root j))
        (C (site ring root j)).pack.val).role := by
    change 1 ≤ (C (site ring root j)).pack.val
    rw [hrole]
    exact hj
  have hxlt :
      (bankCell (C (site ring root j))
        (C (site ring root j)).pack.val).role <
        (compileAdvice q).b := by
    change (C (site ring root j)).pack.val <
      (compileAdvice q).b
    rw [hrole]
    exact hjlt
  have hy :
      (bankCell (C (site ring root (j + 1)))
        (C (site ring root (j + 1))).pack.val).role =
        (bankCell (C (site ring root j))
          (C (site ring root j)).pack.val).role + 1 := by
    change (C (site ring root (j + 1))).pack.val =
      (C (site ring root j)).pack.val + 1
    rw [hrole, hroleNext]
  have hbank :
      resetColdPairOccupied
        (resetBankOld (C (site ring root j))
          (C (site ring root (j + 1)))).1
        (resetBankOld (C (site ring root j))
          (C (site ring root (j + 1)))).2 ≤
      resetColdPairOccupied
        (bankCell (C (site ring root j))
          (C (site ring root j)).pack.val)
        (bankCell (C (site ring root (j + 1)))
          (C (site ring root (j + 1))).pack.val) := by
    have hyr :
        (bankCell (C (site ring root (j + 1)))
          (C (site ring root (j + 1))).pack.val).role = j + 1 := by
      change (C (site ring root (j + 1))).pack.val = j + 1
      exact hroleNext
    simpa only [resetBankOld, hpost, hyr] using
      (resetColdBankInteriorTwoSlotBound
        (bankCell (C (site ring root j))
          (C (site ring root j)).pack.val)
        (bankCell (C (site ring root (j + 1)))
          (C (site ring root (j + 1))).pack.val)
        (compileAdvice q).b (compileAdvice q).theta
        hx hxlt hy)
  have htrip := resetPhysicalEdgeBankTrip ring C
    (site ring root j) hne hsp
  have htokSource :
      (((protocol q).step ring C (site ring root j))
        (site ring root j)).tok =
      (resetBankOld (C (site ring root j))
        (C (site ring root (j + 1)))).1.tok := by
    exact congrArg (fun z : Mode × Bool × BTok => z.2.2) htrip.1
  have htokTarget :
      (((protocol q).step ring C (site ring root j))
        (site ring root (j + 1))).tok =
      (resetBankOld (C (site ring root j))
        (C (site ring root (j + 1)))).2.tok := by
    exact congrArg (fun z : Mode × Bool × BTok => z.2.2) htrip.2
  have hpair :
      resetColdTokenOccupied
        (((protocol q).step ring C (site ring root j))
          (site ring root j)).tok +
      resetColdTokenOccupied
        (((protocol q).step ring C (site ring root j))
          (site ring root (j + 1))).tok ≤
      resetColdTokenOccupied (C (site ring root j)).tok +
        resetColdTokenOccupied (C (site ring root (j + 1))).tok := by
    rw [htokSource, htokTarget]
    exact hbank
  have hframe (i : Nat)
      (hi : i < (compileAdvice q).b)
      (hleft : i ≠ j - 1) (hright : i ≠ j) :
      resetColdTokenOccupied
        (((protocol q).step ring C (site ring root j))
          (site ring root (i + 1))).tok =
      resetColdTokenOccupied (C (site ring root (i + 1))).tok := by
    have hfrom : site ring root (i + 1) ≠ site ring root j :=
      resetCompleteSitesDifferent ring C root hc
        (i + 1) j (by omega) (by omega) (by omega)
    have hto : site ring root (i + 1) ≠
        site ring root (j + 1) :=
      resetCompleteSitesDifferent ring C root hc
        (i + 1) (j + 1) (by omega) (by omega) (by omega)
    exact congrArg
      (fun a : Agent (compileAdvice q) =>
        resetColdTokenOccupied a.tok)
      (step_frame ring C (site ring root j)
        (site ring root (i + 1)) hfrom (by
          change site ring root (i + 1) ≠ site ring root (j + 1)
          exact hto))
  have hindex : j - 1 + 1 = j := by omega
  have hrange := resetColdRangePairLe
    (compileAdvice q).b (j - 1) j
    (fun i => resetColdTokenOccupied
      (((protocol q).step ring C (site ring root j))
        (site ring root (i + 1))).tok)
    (fun i => resetColdTokenOccupied
      (C (site ring root (i + 1))).tok)
    (by omega) hjlt (by omega)
    (by simpa only [hindex] using hpair)
    hframe
  simpa only [resetColdWorkerCount, resetColdTokenOccupied] using hrange

/-- On any internal digit service the physical root Agent is framed
and global occupied slots do not increase. The stopped cold kernel
also maps defect/grant/RESET exits to zero credit. -/
theorem resetColdUncappedCreditInternalNextLe {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankColdCarrier (q := q) ring root)
    (j : Nat) (hj : 1 ≤ j)
    (hjlt : j < (compileAdvice q).b) :
    resetColdUncappedCredit ring root
        (resetClockBankColdNext ring root hsp
          (.inl x) (site ring root j)) ≤
      resetColdUncappedCredit ring root (.inl x) := by
  classical
  have hrootSource : root ≠ site ring root j := by
    change site ring root 0 ≠ site ring root j
    exact resetCompleteSitesDifferent ring x.val root
      x.property.1 0 j (by omega) (by omega) (by omega)
  have hrootTarget :
      root ≠ ring.rightNeighbor (site ring root j) := by
    change site ring root 0 ≠ site ring root (j + 1)
    exact resetCompleteSitesDifferent ring x.val root
      x.property.1 0 (j + 1)
      (by omega) (by omega) (by omega)
  have hroot :
      (((protocol q).step ring x.val (site ring root j)) root) =
        x.val root :=
    step_frame ring x.val (site ring root j) root
      hrootSource hrootTarget
  have hw := resetColdWorkerCountInternalPhysicalLe
    ring x.val root j x.property.1 hj hjlt hsp
  have hbase :
      resetColdModeCredit n (compileAdvice q).bankLeaseCap
        ((((protocol q).step ring x.val (site ring root j)) root).mode)
        ((((protocol q).step ring x.val (site ring root j)) root).lease.val) +
        n * resetColdWorkerCount ring
          ((protocol q).step ring x.val (site ring root j)) root ≤
      resetColdModeCredit n (compileAdvice q).bankLeaseCap
        (x.val root).mode (x.val root).lease.val +
        n * resetColdWorkerCount ring x.val root := by
    rw [hroot]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left n hw) _
  by_cases hd :
      ResetClockBankDefectEntry ring x.val root (site ring root j)
  · rw [resetClockBankColdNextDefect ring root hsp x
        (site ring root j) hd]
    change 0 ≤ _
    exact Nat.zero_le _
  · by_cases hg :
      GrantFree ((protocol q).step ring x.val
        (site ring root j)) root
    · rw [resetClockBankColdNextContinue ring root hsp x
          (site ring root j) hd hg]
      unfold resetClockBankColdLift
      split
      · change 0 ≤ _
        exact Nat.zero_le _
      · change
          resetColdModeCredit n (compileAdvice q).bankLeaseCap
            ((((protocol q).step ring x.val
              (site ring root j)) root).mode)
            ((((protocol q).step ring x.val
              (site ring root j)) root).lease.val) +
            n * resetColdWorkerCount ring
              ((protocol q).step ring x.val
                (site ring root j)) root ≤
          resetColdModeCredit n (compileAdvice q).bankLeaseCap
            (x.val root).mode (x.val root).lease.val +
            n * resetColdWorkerCount ring x.val root
        exact hbase
    · rw [resetClockBankColdNextGrant ring root hsp x
          (site ring root j) hd hg]
      change 0 ≤ _
      exact Nat.zero_le _

/-! The arithmetic size condition is enough to pay rounding. -/

theorem resetColdHalfClock_upper (n : Nat) :
    2 * resetColdHalfClock n ≤ n + 1 := by
  unfold resetColdHalfClock
  have hdiv := Nat.div_add_mod (n + 1) 2
  have hmod := Nat.mod_lt (n + 1) (by decide : 0 < (2 : Nat))
  omega

theorem resetColdUncappedCredit_carrier_le_of_large {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (x : ResetClockBankColdCarrier (q := q) ring root) :
    resetColdUncappedCredit ring root (.inl x) ≤
      (2 * (compileAdvice q).bankLeaseCap +
        (compileAdvice q).b + 7) * n := by
  have hhalf := resetColdHalfClock_upper n
  have hmul := Nat.mul_le_mul_right
    (2 * (compileAdvice q).bankLeaseCap) hhalf
  have hround :
      4 * (resetColdHalfClock n *
        (compileAdvice q).bankLeaseCap) ≤
      (2 * (compileAdvice q).bankLeaseCap) * n + n := by
    calc
      _ = (2 * resetColdHalfClock n) *
          (2 * (compileAdvice q).bankLeaseCap) := by ac_rfl
      _ ≤ (n + 1) * (2 * (compileAdvice q).bankLeaseCap) := hmul
      _ = (2 * (compileAdvice q).bankLeaseCap) * n +
          2 * (compileAdvice q).bankLeaseCap := by
            rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm n]
      _ ≤ (2 * (compileAdvice q).bankLeaseCap) * n + n :=
          Nat.add_le_add_left hlarge _
  calc
    _ ≤ 4 * (resetColdHalfClock n *
          (compileAdvice q).bankLeaseCap) +
          ((compileAdvice q).b + 6) * n :=
      resetColdUncappedCredit_carrier_le ring root x
    _ ≤ ((2 * (compileAdvice q).bankLeaseCap) * n + n) +
          ((compileAdvice q).b + 6) * n :=
      Nat.add_le_add_right hround _
    _ = (2 * (compileAdvice q).bankLeaseCap +
          (compileAdvice q).b + 7) * n := by
      rw [show
        2 * (compileAdvice q).bankLeaseCap +
          (compileAdvice q).b + 7 =
        2 * (compileAdvice q).bankLeaseCap +
          (1 + ((compileAdvice q).b + 6)) by omega]
      simp only [Nat.add_mul, Nat.one_mul]
      omega

theorem resetColdUncappedCredit_start_le_of_large {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (x : ResetClockBankColdCarrier (q := q) ring root) :
    resetColdUncappedCredit ring root
      (resetClockBankColdStart ring root x) ≤
        (2 * (compileAdvice q).bankLeaseCap +
          (compileAdvice q).b + 7) * n := by
  by_cases hm : (x.val root).mode = .RESET
  · change
      resetColdUncappedCredit ring root
        (resetClockBankColdLift ring root
          x.val x.property.1 x.property.2) ≤ _
    rw [resetClockBankColdLiftReset ring root
      x.val x.property.1 x.property.2 hm]
    change 0 ≤ _
    exact Nat.zero_le _
  · change
      resetColdUncappedCredit ring root
        (resetClockBankColdLift ring root
          x.val x.property.1 x.property.2) ≤ _
    simp only [resetClockBankColdLift, dif_neg hm]
    exact resetColdUncappedCredit_carrier_le_of_large
      ring root hlarge x

/-! For q = ceilLogTwo n, the spatial cutoff implies hlarge. -/

private theorem resetColdCeilLogLeSelf (m : Nat) :
    ceilLogTwo m ≤ m := by
  unfold ceilLogTwo
  split
  · omega
  · have hh := Nat.log2_le_self (m - 1)
    omega

private theorem resetColdPowerLinear :
    ∀ q : Nat, 11 ≤ q → 26 * (q + 13) ≤ 2 ^ (q - 1) := by
  have hp : ∀ k : Nat,
      26 * ((11 + k) + 13) ≤ 2 ^ ((11 + k) - 1) := by
    intro k
    induction k with
    | zero =>
        decide
    | succ k ih =>
        have he :
            (11 + Nat.succ k) - 1 = ((11 + k) - 1) + 1 := by omega
        have ha :
            26 * ((11 + Nat.succ k) + 13) =
              26 * ((11 + k) + 13) + 26 := by omega
        rw [ha, he, Nat.pow_succ]
        have hsmall : 26 ≤ 26 * ((11 + k) + 13) := by omega
        omega
  intro q hq
  obtain ⟨k, hk⟩ : ∃ k : Nat, q = 11 + k :=
    ⟨q - 11, by omega⟩
  rw [hk]
  exact hp k

private theorem resetColdBankCapLinear (q : Nat) (hq : 2 ≤ q) :
    2 * (compileAdvice q).bankLeaseCap ≤ 26 * (q + 13) := by
  have hlog : ceilLogTwo q ≤ q := resetColdCeilLogLeSelf q
  have hmax : max 2 (ceilLogTwo q) ≤ q := by
    exact Nat.max_le.mpr ⟨by omega, hlog⟩
  change 2 * (13 * ((max 2 (ceilLogTwo q) + 11) + 2)) ≤
    26 * (q + 13)
  omega

/-- Exact answer to item (3): q is the ceiling binary logarithm of
the actual ring size. The spatial branch implies n >= 2 Lambda.
This result is independent of the still-open physical Bellman drift. -/
theorem resetColdLargeAtSpatialCutoff (n : Nat)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n := by
  have hq : 80 ≤ ceilLogTwo n := by
    change decide (ceilLogTwo n ≤ 79) = false at hsp
    by_cases hl : ceilLogTwo n ≤ 79
    · simp [hl] at hsp
    · omega
  have hn : 2 ≤ n := by
    by_cases hl : n ≤ 1
    · have hz : ceilLogTwo n = 0 := by
        simp [ceilLogTwo, hl]
      omega
    · omega
  have hceil : ceilLogTwo n = Nat.log2 (n - 1) + 1 := by
    simp [ceilLogTwo, show ¬ n ≤ 1 by omega]
  have hpowBase : 2 ^ Nat.log2 (n - 1) ≤ n - 1 :=
    (Nat.le_log2 (by omega : n - 1 ≠ 0)).1
      (Nat.le_refl (Nat.log2 (n - 1)))
  have hpow : 2 ^ (ceilLogTwo n - 1) ≤ n - 1 := by
    rw [hceil]
    simpa only [Nat.add_sub_cancel_right] using hpowBase
  have hcap :
      2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤
        26 * (ceilLogTwo n + 13) :=
    resetColdBankCapLinear (ceilLogTwo n) (by omega)
  have hlinear :
      26 * (ceilLogTwo n + 13) ≤
        2 ^ (ceilLogTwo n - 1) :=
    resetColdPowerLinear (ceilLogTwo n) (by omega)
  omega

end Counter
end L3


/-!
Cold root-port projection and the CSTART/E BANK row.

This block does not assert ResetClockBankColdCharge_holds.
The full stopped Bellman inequality is still missing its root-port
case aggregation and the incoming-port geometry required to frame
every active digit.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open K2ArbitraryElimination.FiniteAccounting

/-- The root and its first digit are distinct in a complete interval.
No separate assumption on n is needed: the role values 0 and 1
are already different. -/
theorem resetColdRootPortDistinct {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root) :
    ring.rightNeighbor root ≠ root := by
  change site ring root 1 ≠ site ring root 0
  exact resetCompleteSitesDifferent ring C root hc 1 0
    (by have hh := resetTrialCompiledWidth q; omega)
    (by omega) (by omega)

/-- Two endpoints of the real protocol agree with the literal
BANK pair in their modes and exact Fin-valued copied leases.
The conversion to numeric BANK leases is available whenever
the corresponding BANK lease is within the compiled cap. -/
theorem resetColdPhysicalSourceModeLease {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (e : Fin n) (hne : ring.rightNeighbor e ≠ e)
    (hsp : (compileAdvice q).useSmall = false) :
    (((protocol q).step ring C e) e).mode =
        (resetBankOld (C e) (C (ring.rightNeighbor e))).1.mode ∧
    (((protocol q).step ring C e) e).lease =
        (copyBank (C e)
          (resetBankOld (C e) (C (ring.rightNeighbor e))).1).lease := by
  have ht := resetPhysicalEdgeBankTrip ring C e hne hsp
  have hl := resetClockPhysicalEdgeLeasePair ring C e hne hsp
  exact ⟨congrArg (fun z : Mode × Bool × BTok => z.1) ht.1,
    hl.1⟩

theorem resetColdPhysicalTargetModeLease {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (e : Fin n) (hne : ring.rightNeighbor e ≠ e)
    (hsp : (compileAdvice q).useSmall = false) :
    (((protocol q).step ring C e)
        (ring.rightNeighbor e)).mode =
        (resetBankOld (C e) (C (ring.rightNeighbor e))).2.mode ∧
    (((protocol q).step ring C e)
        (ring.rightNeighbor e)).lease =
        (copyBank (C (ring.rightNeighbor e))
          (resetBankOld (C e) (C (ring.rightNeighbor e))).2).lease := by
  have ht := resetPhysicalEdgeBankTrip ring C e hne hsp
  have hl := resetClockPhysicalEdgeLeasePair ring C e hne hsp
  exact ⟨congrArg (fun z : Mode × Bool × BTok => z.1) ht.2,
    hl.2⟩

/-- The two requested specializations of the full real transition.
These retain the precise copying expression instead of assuming
all arbitrary BankCells carry in-range numeric leases. -/
theorem resetColdOutgoingRootModeLease {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false) :
    (((protocol q).step ring C root) root).mode =
        (resetBankOld (C root) (C (site ring root 1))).1.mode ∧
    (((protocol q).step ring C root) root).lease =
        (copyBank (C root)
          (resetBankOld (C root) (C (site ring root 1))).1).lease := by
  exact resetColdPhysicalSourceModeLease ring C root
    (resetColdRootPortDistinct ring C root hc) hsp

theorem resetColdIncomingRootModeLease {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n) (he : e ≠ root)
    (hpred : ring.rightNeighbor e = root)
    (hsp : (compileAdvice q).useSmall = false) :
    (((protocol q).step ring C e) root).mode =
        (resetBankOld (C e) (C root)).2.mode ∧
    (((protocol q).step ring C e) root).lease =
        (copyBank (C root)
          (resetBankOld (C e) (C root)).2).lease := by
  have hne : ring.rightNeighbor e ≠ e := by
    rw [hpred]
    exact Ne.symm he
  have hh := resetColdPhysicalTargetModeLease ring C e hne hsp
  rw [hpred] at hh
  exact hh

/-- One outgoing root service frames all digit sites j >= 2;
the first digit is its only potentially modified digit worker. -/
theorem resetColdOutgoingRootOtherDigitsFrame {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (j : Nat) (hj : 2 ≤ j)
    (hjb : j ≤ (compileAdvice q).b) :
    ((protocol q).step ring C root) (site ring root j) =
      C (site ring root j) := by
  have hs : site ring root j ≠ root := by
    change site ring root j ≠ site ring root 0
    exact resetCompleteSitesDifferent ring C root hc
      j 0 hjb (by omega) (by omega)
  have ht : site ring root j ≠ ring.rightNeighbor root := by
    change site ring root j ≠ site ring root 1
    exact resetCompleteSitesDifferent ring C root hc
      j 1 hjb (by omega) (by omega)
  exact step_frame ring C root (site ring root j) hs ht

/-- An incoming root service frames every digit if its source
is exterior to all active digits. This explicit geometric premise
must be derived before using the lemma on all incoming edges. -/
theorem resetColdIncomingRootDigitFrame {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n) (hc : Complete ring C root)
    (hpred : ring.rightNeighbor e = root)
    (hex : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b → e ≠ site ring root j)
    (j : Nat) (hj : 1 ≤ j)
    (hjb : j ≤ (compileAdvice q).b) :
    ((protocol q).step ring C e) (site ring root j) =
      C (site ring root j) := by
  have hx : site ring root j ≠ e :=
    Ne.symm (hex j hj hjb)
  have hy : site ring root j ≠ ring.rightNeighbor e := by
    rw [hpred]
    change site ring root j ≠ site ring root 0
    exact resetCompleteSitesDifferent ring C root hc
      j 0 hjb (by omega) (by omega)
  exact step_frame ring C e (site ring root j) hx hy

/-! Core finite range sum with at most one exceptional index. -/

private theorem resetColdRangePointwiseLe (f g : Nat → Nat) :
    ∀ m : Nat, (∀ i, i < m → f i ≤ g i) →
      ((List.range m).map f).sum ≤
        ((List.range m).map g).sum := by
  intro m
  induction m with
  | zero =>
      intro h
      exact Nat.le_refl _
  | succ m ih =>
      intro h
      simp only [List.range_succ, List.map_append,
        List.sum_append, List.map_singleton, List.sum_cons,
        List.sum_nil, Nat.add_zero]
      exact Nat.add_le_add
        (ih (fun i hi => h i (by omega)))
        (h m (by omega))

private theorem resetColdRangeOneLe
    (m a : Nat) (f g : Nat → Nat)
    (ha : a < m) (hat : f a ≤ g a + 1)
    (hframe : ∀ i, i < m → i ≠ a → f i = g i) :
    ((List.range m).map f).sum ≤
      ((List.range m).map g).sum + 1 := by
  have hpoint : ∀ i, i < m →
      f i ≤ g i + (if i = a then 1 else 0) := by
    intro i hi
    by_cases he : i = a
    · subst i
      simpa using hat
    · simp only [if_neg he, Nat.add_zero]
      exact Nat.le_of_eq (hframe i hi he)
  have hsum := resetColdRangePointwiseLe f
    (fun i => g i + (if i = a then 1 else 0))
    m hpoint
  rw [resetColdRangeMapAdd, resetColdRangeMapSpike m a 1,
    if_pos ha] at hsum
  exact hsum

/-- The full physical outgoing-root service can add at most
one digit worker, since every digit j >= 2 is framed. -/
theorem resetColdWorkerCountOutgoingRootLe {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root) :
    resetColdWorkerCount ring
      ((protocol q).step ring C root) root ≤
        resetColdWorkerCount ring C root + 1 := by
  have hb : 0 < (compileAdvice q).b := by
    have hh := resetTrialCompiledWidth q
    omega
  have hf :
      resetColdTokenOccupied
        (((protocol q).step ring C root) (site ring root 1)).tok ≤
      resetColdTokenOccupied (C (site ring root 1)).tok + 1 := by
    have ht := resetColdTokenOccupiedLeOne
      (((protocol q).step ring C root) (site ring root 1)).tok
    omega
  have hr (i : Nat) (hi : i < (compileAdvice q).b)
      (hne : i ≠ 0) :
      resetColdTokenOccupied
        (((protocol q).step ring C root) (site ring root (i + 1))).tok =
      resetColdTokenOccupied (C (site ring root (i + 1))).tok := by
    rw [resetColdOutgoingRootOtherDigitsFrame ring C root hc
      (i + 1) (by omega) (by omega)]
  have hsum := resetColdRangeOneLe
    (compileAdvice q).b 0
    (fun i => resetColdTokenOccupied
      (((protocol q).step ring C root) (site ring root (i + 1))).tok)
    (fun i => resetColdTokenOccupied
      (C (site ring root (i + 1))).tok)
    hb (by simpa only [Nat.zero_add] using hf) hr
  simpa only [resetColdWorkerCount, resetColdTokenOccupied] using hsum

/-- The incoming-root exterior service preserves the global number
of occupied active digit worker slots exactly. -/
theorem resetColdWorkerCountIncomingRootEq {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n) (hc : Complete ring C root)
    (hpred : ring.rightNeighbor e = root)
    (hex : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b → e ≠ site ring root j) :
    resetColdWorkerCount ring ((protocol q).step ring C e) root =
      resetColdWorkerCount ring C root := by
  unfold resetColdWorkerCount
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have hj : i < (compileAdvice q).b := by
    simpa only [List.mem_range] using hi
  rw [resetColdIncomingRootDigitFrame ring C root e hc hpred hex
    (i + 1) (by omega) (by omega)]

/-! Two literal CSTART BANK rows. -/

/-- The empty first-worker CSTART row starts a comparator.
It raises the root from CSTART to CWAIT, resets the lease to the
full cap, and creates exactly one nonempty comparator worker. -/
theorem resetColdCStartEmptyBankLaunch
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hr : x.role = 0) (hg : x.grant = false)
    (hy : y.role = 1) (hm : x.mode = .CSTART)
    (ht : y.tok = .E) (hb : 0 < b) :
    (bankPair x y 1 b theta).1.mode = .CWAIT ∧
    (bankPair x y 1 b theta).1.lease = 13 * (b + 2) ∧
    (bankPair x y 1 b theta).2.tok ≠ .E := by
  constructor
  · simp [bankPair, hr, hg, hy, hm, ht, hb, isRetTok,
      isWaitMode]
  constructor
  · simp [bankPair, hr, hg, hy, hm, ht, hb, isRetTok,
      isWaitMode]
  · simp [bankPair, hr, hg, hy, hm, ht, hb, isRetTok,
      isWaitMode]
    split <;> simp

/-- An unchanged incoming nonroot-to-root edge does not alter
the CSTART root lease (nor its mode). -/
theorem resetColdIncomingCStartFieldsBank
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : x.role ≠ 0) (hy : y.role = 0)
    (hg : y.grant = false) (hm : y.mode = .CSTART) :
    (bankPair x y 0 b theta).2.mode = .CSTART ∧
      (bankPair x y 0 b theta).2.lease = y.lease := by
  constructor
  · exact resetColdIncomingCStartBank x y b theta hx hy hg hm
  · simp [bankPair, hx, hy, hg, hm, isWaitMode] <;>
      repeat (first | rfl | split)

/-- The two-root-edge CSTART/E Bellman arithmetic, including the
additional occupied first-digit worker after comparator launch.
This is the numerical ledger, not yet the full stopped kernel. -/
theorem resetColdCStartEmptyPairBudget
    (n cap occupied : Nat) :
    n +
      (resetColdModeCredit n cap .CWAIT cap +
        n * (occupied + 1)) +
      (resetColdModeCredit n cap .CSTART 0 +
        n * occupied) =
      2 * (resetColdModeCredit n cap .CSTART 0 +
        n * occupied) := by
  have hb := resetColdComparatorLaunchBudget n cap
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- Exact physical projection of the CSTART/E outgoing root row.
The copyBank lease carrier is handled with the existing range lemma,
so the numeric output is the actual bankLeaseCap. -/
theorem resetColdPhysicalCStartEmptyLaunch {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hm : (C root).mode = .CSTART)
    (ht : (C (site ring root 1)).tok = .E) :
    (((protocol q).step ring C root) root).mode = .CWAIT ∧
    (((protocol q).step ring C root) root).lease.val =
      (compileAdvice q).bankLeaseCap ∧
    (((protocol q).step ring C root)
      (site ring root 1)).tok ≠ .E := by
  have hroot : (C root).pack.val = 0 := by
    simpa only [site] using hc 0 (by omega)
  have hfirst : (C (site ring root 1)).pack.val = 1 :=
    hc 1 (by have hh := resetTrialCompiledWidth q; omega)
  have hb : 0 < (compileAdvice q).b := by
    have hh := resetTrialCompiledWidth q
    omega
  have hpost :
      packNext (C root).pack.val
        (C (site ring root 1)).pack.val
        (compileAdvice q).b = 1 := by
    rw [hroot, hfirst]
    simp [packNext, hb]
  have hrow :
      (resetBankOld (C root) (C (site ring root 1))).1.mode =
        .CWAIT ∧
      (resetBankOld (C root) (C (site ring root 1))).1.lease =
        (compileAdvice q).bankLeaseCap ∧
      (resetBankOld (C root) (C (site ring root 1))).2.tok ≠ .E := by
    simpa only [resetBankOld, hpost, Compiled.bankLeaseCap] using
      (resetColdCStartEmptyBankLaunch
        (bankCell (C root) (C root).pack.val)
        (bankCell (C (site ring root 1))
          (C (site ring root 1)).pack.val)
        (compileAdvice q).b (compileAdvice q).theta
        (by change (C root).pack.val = 0; exact hroot)
        (by change (C root).grant = false; exact hg)
        (by change (C (site ring root 1)).pack.val = 1; exact hfirst)
        hm ht hb)
  have hphysical := resetColdOutgoingRootModeLease
    ring C root hc hsp
  have hfit :
      (resetBankOld (C root)
        (C (site ring root 1))).1.lease <
      (compileAdvice q).bankLeaseCap + 1 := by
    rw [hrow.2.1]
    omega
  have hlease :
      (((protocol q).step ring C root) root).lease.val =
        (compileAdvice q).bankLeaseCap := by
    have hh := congrArg Fin.val hphysical.2
    rw [resetClockCopyBankLeaseExact
      (C root)
      (resetBankOld (C root) (C (site ring root 1))).1 hfit] at hh
    exact hh.trans hrow.2.1
  have htrip := resetPhysicalEdgeBankTrip ring C root
    (resetColdRootPortDistinct ring C root hc) hsp
  have htok :
      (((protocol q).step ring C root)
        (site ring root 1)).tok =
      (resetBankOld (C root) (C (site ring root 1))).2.tok :=
    congrArg (fun z : Mode × Bool × BTok => z.2.2) htrip.2
  refine ⟨hphysical.1.trans hrow.1, hlease, ?_⟩
  rw [htok]
  exact hrow.2.2

end Counter
end L3


/-!
Incoming-root defect/role classification and stopped credit.

The full C.3 charge is NOT asserted here. The first two-root-edge
CSTART/E case is completed; the next outstanding case is CSTART
with a nonempty first worker, followed by the other four root modes.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open K2ArbitraryElimination.FiniteAccounting

/-- An incoming-root edge is either already a stopped PACK defect
or its old source has one of the two legal predecessor roles.
No assumption on the source's BANK scratch is made. -/
theorem resetColdIncomingDefectOrRole {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hc : Complete ring C root)
    (hpred : ring.rightNeighbor e = root) :
    ResetClockBankDefectEntry ring C root e ∨
      (C e).pack.val = (compileAdvice q).b ∨
        (C e).pack.val = (compileAdvice q).b + 1 := by
  classical
  by_cases hd : ResetClockBankDefectEntry ring C root e
  · exact Or.inl hd
  · right
    have hroot : (C root).pack.val = 0 := by
      simpa only [site] using hc 0 (by omega)
    have hgood :
        goodPair (compileAdvice q).b
          (C e).pack (C root).pack = true := by
      cases h : goodPair (compileAdvice q).b
          (C e).pack (C root).pack with
      | true => rfl
      | false =>
          have hf : ResetClockBankDefectEntry ring C root e :=
            ⟨Or.inl hpred, Or.inl (by
              simpa only [hpred] using h)⟩
          exact False.elim (hd hf)
    rcases (goodPair_iff (compileAdvice q).b
      (C e).pack (C root).pack).mp hgood with
      hfirst | hmiddle | hlast
    · have hf : (C e).pack.val + 1 = 0 := by
        rw [← hroot]
        exact hfirst.2.symm
      omega
    · exact Or.inl hmiddle.1
    · exact Or.inr hlast.1

/-- The role classification as a non-defect implication, convenient
when invoking the incoming BANK row. -/
theorem resetColdIncomingRoleOfNoDefect {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hc : Complete ring C root)
    (hpred : ring.rightNeighbor e = root)
    (hno : ¬ ResetClockBankDefectEntry ring C root e) :
    (C e).pack.val = (compileAdvice q).b ∨
      (C e).pack.val = (compileAdvice q).b + 1 := by
  rcases resetColdIncomingDefectOrRole ring C root e hc hpred with
    hd | hr
  · exact False.elim (hno hd)
  · exact hr

/-! The large spatial ring cannot wrap from the last digit
directly to the root. This is stronger than merely knowing
that the incoming PACK role is legal. -/

private theorem resetColdSiteVal {n : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ j : Nat,
      (site ring root j).val = (root.val + j) % n := by
  intro j
  induction j with
  | zero =>
      change root.val = (root.val + 0) % n
      simpa only [Nat.add_zero] using
        (Nat.mod_eq_of_lt root.isLt).symm
  | succ j ih =>
      change ((site ring root j).val + 1) % n =
        (root.val + (j + 1)) % n
      rw [ih, Nat.mod_add_mod]
      congr 1

private theorem resetColdSiteShortNoReturn {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (j : Nat) (hj : 0 < j) (hjn : j < n) :
    site ring root j ≠ root := by
  intro he
  have hv := congrArg Fin.val he
  rw [resetColdSiteVal ring root j] at hv
  by_cases hsum : root.val + j < n
  · rw [Nat.mod_eq_of_lt hsum] at hv
    omega
  · have hge : n ≤ root.val + j := by omega
    have hsub : root.val + j - n < n := by
      have hr := root.isLt
      omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsub] at hv
    omega

/-- Under hlarge, the source of an incoming-root edge is outside
every active digit. This excludes the otherwise possible n=b+1
wraparound, where the source could be the final digit. -/
theorem resetColdIncomingExteriorOfLarge {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hc : Complete ring C root)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hpred : ring.rightNeighbor e = root) :
    ∀ j : Nat, 1 ≤ j → j ≤ (compileAdvice q).b →
      e ≠ site ring root j := by
  have hsize : (compileAdvice q).b + 1 < n := by
    have hh : 2 * (13 * ((compileAdvice q).b + 2)) ≤ n := by
      simpa only [Compiled.bankLeaseCap] using hlarge
    omega
  intro j hj hjb he
  have hcycle : site ring root (j + 1) = root := by
    calc
      site ring root (j + 1) =
          ring.rightNeighbor (site ring root j) := rfl
      _ = ring.rightNeighbor e := by rw [he]
      _ = root := hpred
  by_cases hbefore : j < (compileAdvice q).b
  · have hne := resetCompleteSitesDifferent
      ring C root hc (j + 1) 0
      (by omega) (by omega) (by omega)
    exact hne (by simpa only [site] using hcycle)
  · have hlast : j = (compileAdvice q).b := by omega
    rw [hlast] at hcycle
    exact (resetColdSiteShortNoReturn ring root
      ((compileAdvice q).b + 1) (by omega) hsize) hcycle

/-- The stopped kernel never charges more than the physical
endpoint's uncapped root+digit credit. Defect, grant and RESET
exits are zero, without assuming any BANK row property. -/
theorem resetColdNextCreditLePhysical {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankColdCarrier (q := q) ring root)
    (e : Fin n) :
    resetColdUncappedCredit ring root
        (resetClockBankColdNext ring root hsp (.inl x) e) ≤
      resetColdModeCredit n (compileAdvice q).bankLeaseCap
        (((protocol q).step ring x.val e) root).mode
        (((protocol q).step ring x.val e) root).lease.val +
      n * resetColdWorkerCount ring
        ((protocol q).step ring x.val e) root := by
  classical
  by_cases hd : ResetClockBankDefectEntry ring x.val root e
  · rw [resetClockBankColdNextDefect ring root hsp x e hd]
    change 0 ≤ _
    exact Nat.zero_le _
  · by_cases hg : GrantFree ((protocol q).step ring x.val e) root
    · rw [resetClockBankColdNextContinue ring root hsp x e hd hg]
      unfold resetClockBankColdLift
      split
      · change 0 ≤ _
        exact Nat.zero_le _
      · exact Nat.le_refl _
    · rw [resetClockBankColdNextGrant ring root hsp x e hd hg]
      change 0 ≤ _
      exact Nat.zero_le _

/-- Exact full-protocol incoming-root CSTART/lease projection,
assuming one of the two legally classified source roles. -/
theorem resetColdPhysicalIncomingCStart {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hpred : ring.rightNeighbor e = root)
    (hrole : (C e).pack.val = (compileAdvice q).b ∨
      (C e).pack.val = (compileAdvice q).b + 1)
    (hm : (C root).mode = .CSTART) :
    (((protocol q).step ring C e) root).mode = .CSTART ∧
    (((protocol q).step ring C e) root).lease.val =
      (C root).lease.val := by
  have hroot : (C root).pack.val = 0 := by
    simpa only [site] using hc 0 (by omega)
  have hb : 0 < (compileAdvice q).b := by
    have hh := resetTrialCompiledWidth q
    omega
  have hpost :
      packNext (C e).pack.val (C root).pack.val
        (compileAdvice q).b = 0 := by
    rcases hrole with hr | hr
    · rw [hr, hroot]
      simp [packNext]
    · rw [hr, hroot]
      simp [packNext]
  have hs : e ≠ root := by
    intro he
    subst e
    have hneq := resetColdRootPortDistinct ring C root hc
    exact hneq hpred
  have hrow :
      (resetBankOld (C e) (C root)).2.mode = .CSTART ∧
      (resetBankOld (C e) (C root)).2.lease =
        (C root).lease.val := by
    have hsource : (C e).pack.val ≠ 0 := by
      have hwidth := resetTrialCompiledWidth q
      rcases hrole with hr | hr <;> omega
    simpa only [resetBankOld, hpost, bankCell] using
      (resetColdIncomingCStartFieldsBank
        (bankCell (C e) (C e).pack.val)
        (bankCell (C root) (C root).pack.val)
        (compileAdvice q).b (compileAdvice q).theta
        (by change (C e).pack.val ≠ 0; exact hsource)
        (by change (C root).pack.val = 0; exact hroot)
        (by change (C root).grant = false; exact hg)
        (by change (C root).mode = .CSTART; exact hm))
  have hphys := resetColdIncomingRootModeLease
    ring C root e hs hpred hsp
  have hfit :
      (resetBankOld (C e) (C root)).2.lease <
        (compileAdvice q).bankLeaseCap + 1 := by
    rw [hrow.2]
    exact (C root).lease.isLt
  have hlease :
      (((protocol q).step ring C e) root).lease.val =
        (C root).lease.val := by
    have hh := congrArg Fin.val hphys.2
    rw [resetClockCopyBankLeaseExact
      (C root) (resetBankOld (C e) (C root)).2 hfit] at hh
    exact hh.trans hrow.2
  exact ⟨hphys.1.trans hrow.1, hlease⟩

/-- A CSTART incoming service in the large spatial ring has
no more uncapped stopped credit than the current state, including
both defect exits and every allowed role. -/
theorem resetColdIncomingCStartNextLe {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (x : ResetClockBankColdCarrier (q := q) ring root)
    (e : Fin n) (hpred : ring.rightNeighbor e = root)
    (hm : (x.val root).mode = .CSTART) :
    resetColdUncappedCredit ring root
      (resetClockBankColdNext ring root hsp (.inl x) e) ≤
        resetColdUncappedCredit ring root (.inl x) := by
  rcases resetColdIncomingDefectOrRole
    ring x.val root e x.property.1 hpred with hd | hrole
  · rw [resetClockBankColdNextDefect ring root hsp x e hd]
    change 0 ≤ _
    exact Nat.zero_le _
  · have hfields := resetColdPhysicalIncomingCStart
      ring x.val root e x.property.1 x.property.2 hsp
      hpred hrole hm
    have hw := resetColdWorkerCountIncomingRootEq
      ring x.val root e x.property.1 hpred
      (resetColdIncomingExteriorOfLarge
        ring x.val root e x.property.1 hlarge hpred)
    have hb := resetColdNextCreditLePhysical ring root hsp x e
    calc
      _ ≤
        resetColdModeCredit n (compileAdvice q).bankLeaseCap
          (((protocol q).step ring x.val e) root).mode
          (((protocol q).step ring x.val e) root).lease.val +
          n * resetColdWorkerCount ring
            ((protocol q).step ring x.val e) root := hb
      _ = resetColdUncappedCredit ring root (.inl x) := by
        rw [hfields.1, hfields.2, hw]
        simp only [resetColdUncappedCredit, hm]

/-- CSTART with an empty first digit slot launches a real
comparator, with no more than one new occupied digit slot. -/
theorem resetColdOutgoingCStartEmptyNextLe {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankColdCarrier (q := q) ring root)
    (hm : (x.val root).mode = .CSTART)
    (ht : (x.val (site ring root 1)).tok = .E) :
    resetColdUncappedCredit ring root
        (resetClockBankColdNext ring root hsp (.inl x) root) ≤
      resetColdModeCredit n (compileAdvice q).bankLeaseCap
        .CWAIT (compileAdvice q).bankLeaseCap +
      n * (resetColdWorkerCount ring x.val root + 1) := by
  have hf := resetColdPhysicalCStartEmptyLaunch
    ring x.val root x.property.1 x.property.2 hsp hm ht
  have hw := resetColdWorkerCountOutgoingRootLe
    ring x.val root x.property.1
  calc
    _ ≤
      resetColdModeCredit n (compileAdvice q).bankLeaseCap
        (((protocol q).step ring x.val root) root).mode
        (((protocol q).step ring x.val root) root).lease.val +
      n * resetColdWorkerCount ring
        ((protocol q).step ring x.val root) root :=
      resetColdNextCreditLePhysical ring root hsp x root
    _ ≤
      resetColdModeCredit n (compileAdvice q).bankLeaseCap
        .CWAIT (compileAdvice q).bankLeaseCap +
      n * (resetColdWorkerCount ring x.val root + 1) := by
        rw [hf.1, hf.2.1]
        exact Nat.add_le_add_left (Nat.mul_le_mul_left n hw) _

/-- Closed two-root-edge CSTART/E numerical Bellman row,
including actual defect/grant/RESET terminal cuts.
This is only one of the five non-RESET root modes. -/
theorem resetColdCStartEmptyTwoPortDrift {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (x : ResetClockBankColdCarrier (q := q) ring root)
    (hpred : ring.rightNeighbor e = root)
    (hm : (x.val root).mode = .CSTART)
    (ht : (x.val (site ring root 1)).tok = .E) :
    n +
      resetColdUncappedCredit ring root
        (resetClockBankColdNext ring root hsp (.inl x) root) +
      resetColdUncappedCredit ring root
        (resetClockBankColdNext ring root hsp (.inl x) e) ≤
      2 * resetColdUncappedCredit ring root (.inl x) := by
  have ho := resetColdOutgoingCStartEmptyNextLe
    ring root hsp x hm ht
  have hi := resetColdIncomingCStartNextLe
    ring root hsp hlarge x e hpred hm
  have hbudget := resetColdCStartEmptyPairBudget
    n (compileAdvice q).bankLeaseCap
      (resetColdWorkerCount ring x.val root)
  calc
    _ ≤
        n +
          (resetColdModeCredit n (compileAdvice q).bankLeaseCap
            .CWAIT (compileAdvice q).bankLeaseCap +
            n * (resetColdWorkerCount ring x.val root + 1)) +
          resetColdUncappedCredit ring root (.inl x) :=
      Nat.add_le_add
        (Nat.add_le_add_left ho n) hi
    _ = 2 * resetColdUncappedCredit ring root (.inl x) := by
      simpa only [resetColdUncappedCredit, hm, resetColdModeCredit]
        using hbudget

end Counter
end L3


/-!
CSTART nonempty and ARMED two-root-edge Bellman certificates.

This section proves the
next two mode families by combining literal BANK rows with actual
protocol endpoint projections, worker counts and stopped cuts.

The remaining first unclosed mode is WAIT (RWAIT, IWAIT, CWAIT).
No ResetClockBankColdCharge_holds declaration is made here.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open K2ArbitraryElimination.FiniteAccounting

/-! A consumed digit-one worker pays exactly one root service. -/

/-- If the outgoing root step empties an occupied digit-one slot,
all remaining digit slots are framed; their global count drops by one. -/
theorem resetColdWorkerCountOutgoingRootDrop {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (ht : (C (site ring root 1)).tok ≠ .E)
    (hnew :
      (((protocol q).step ring C root)
        (site ring root 1)).tok = .E) :
    resetColdWorkerCount ring
        ((protocol q).step ring C root) root + 1 ≤
      resetColdWorkerCount ring C root := by
  have hb : 0 < (compileAdvice q).b := by
    have hh := resetTrialCompiledWidth q
    omega
  have hfirst :
      resetColdTokenOccupied
          (((protocol q).step ring C root)
            (site ring root 1)).tok + 1 ≤
        resetColdTokenOccupied (C (site ring root 1)).tok := by
    rw [hnew, resetColdTokenOccupiedEmpty,
      resetColdTokenOccupiedNonempty _ ht]
    exact Nat.le_refl _
  have hpoint (i : Nat) (hi : i < (compileAdvice q).b) :
      resetColdTokenOccupied
          (((protocol q).step ring C root)
            (site ring root (i + 1))).tok +
        (if i = 0 then 1 else 0) ≤
      resetColdTokenOccupied
        (C (site ring root (i + 1))).tok := by
    by_cases hz : i = 0
    · subst i
      simpa only [Nat.zero_add, ite_true, ↓reduceIte] using hfirst
    · have hf := resetColdOutgoingRootOtherDigitsFrame
        ring C root hc (i + 1) (by omega) (by omega)
      have he := congrArg
        (fun a : Agent (compileAdvice q) =>
          resetColdTokenOccupied a.tok) hf
      simpa only [if_neg hz, Nat.add_zero] using
        (Nat.le_of_eq he)
  have hsum := resetColdRangePointwiseLe
    (fun i =>
      resetColdTokenOccupied
        (((protocol q).step ring C root)
          (site ring root (i + 1))).tok +
        (if i = 0 then 1 else 0))
    (fun i => resetColdTokenOccupied
      (C (site ring root (i + 1))).tok)
    (compileAdvice q).b hpoint
  rw [resetColdRangeMapAdd,
    resetColdRangeMapSpike (compileAdvice q).b 0 1,
    if_pos hb] at hsum
  simpa only [resetColdWorkerCount, resetColdTokenOccupied] using hsum

/-- A physical RESET at the root is already a terminal first-stage
handoff: a defect or new grant also has exactly zero cold credit. -/
theorem resetColdNextResetCreditZero {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankColdCarrier (q := q) ring root)
    (e : Fin n)
    (hm : (((protocol q).step ring x.val e) root).mode = .RESET) :
    resetColdUncappedCredit ring root
        (resetClockBankColdNext ring root hsp (.inl x) e) = 0 := by
  classical
  by_cases hd : ResetClockBankDefectEntry ring x.val root e
  · rw [resetClockBankColdNextDefect ring root hsp x e hd]
    rfl
  · by_cases hg : GrantFree ((protocol q).step ring x.val e) root
    · rw [resetClockBankColdNextContinue ring root hsp x e hd hg]
      rw [resetClockBankColdLiftReset ring root
        ((protocol q).step ring x.val e)
        (resetClockBankColdCompleteStep ring root x e hd) hg hm]
      rfl
    · rw [resetClockBankColdNextGrant ring root hsp x e hd hg]
      rfl

/-! CSTART with any nonempty digit-one worker. -/

/-- Every nonempty first-digit token is consumed by CSTART.
A return token leaves the root in CSTART; each nonreturn token
causes RESET. This is a literal bankPair fact with arbitrary bits. -/
theorem resetColdCStartNonemptyBankRow
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hr : x.role = 0) (hg : x.grant = false)
    (hy : y.role = 1) (hm : x.mode = .CSTART)
    (hb : 0 < b) (ht : y.tok ≠ .E) :
    (bankPair x y 1 b theta).2.tok = .E ∧
      ((bankPair x y 1 b theta).1.mode = .CSTART ∨
        (bankPair x y 1 b theta).1.mode = .RESET) := by
  have hbge : 1 ≤ b := by omega
  cases htok : y.tok with
  | E => exact False.elim (ht htok)
  | RR =>
      simp [bankPair, hr, hg, hy, hm, htok,
        hbge, isRetTok, isWaitMode]
  | RL =>
      simp [bankPair, hr, hg, hy, hm, htok,
        hbge, isRetTok, isWaitMode]
  | IR =>
      simp [bankPair, hr, hg, hy, hm, htok,
        hbge, isRetTok, isWaitMode]
  | AL =>
      simp [bankPair, hr, hg, hy, hm, htok,
        hbge, isRetTok, isWaitMode]
  | CR0 =>
      simp [bankPair, hr, hg, hy, hm, htok,
        hbge, isRetTok, isWaitMode]
  | CR1 =>
      simp [bankPair, hr, hg, hy, hm, htok,
        hbge, isRetTok, isWaitMode]
  | CL0 =>
      simp [bankPair, hr, hg, hy, hm, htok,
        hbge, isRetTok, isWaitMode]
  | CL1 =>
      simp [bankPair, hr, hg, hy, hm, htok,
        hbge, isRetTok, isWaitMode]

/-- Real root and first-digit projections for CSTART and an
inherited nonempty first-digit token, with no worker provenance. -/
theorem resetColdPhysicalCStartNonempty {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hm : (C root).mode = .CSTART)
    (ht : (C (site ring root 1)).tok ≠ .E) :
    (((protocol q).step ring C root)
        (site ring root 1)).tok = .E ∧
      ((((protocol q).step ring C root) root).mode = .CSTART ∨
        (((protocol q).step ring C root) root).mode = .RESET) := by
  have hroot : (C root).pack.val = 0 := by
    simpa only [site] using hc 0 (by omega)
  have hone : (C (site ring root 1)).pack.val = 1 :=
    hc 1 (by have hh := resetTrialCompiledWidth q; omega)
  have hb : 0 < (compileAdvice q).b := by
    have hh := resetTrialCompiledWidth q
    omega
  have hpost :
      packNext (C root).pack.val
        (C (site ring root 1)).pack.val
        (compileAdvice q).b = 1 := by
    rw [hroot, hone]
    simp [packNext, hb]
  have hrow :
      (resetBankOld (C root) (C (site ring root 1))).2.tok =
        .E ∧
      ((resetBankOld (C root)
          (C (site ring root 1))).1.mode = .CSTART ∨
        (resetBankOld (C root)
          (C (site ring root 1))).1.mode = .RESET) := by
    simpa only [resetBankOld, hpost, bankCell] using
      (resetColdCStartNonemptyBankRow
        (bankCell (C root) (C root).pack.val)
        (bankCell (C (site ring root 1))
          (C (site ring root 1)).pack.val)
        (compileAdvice q).b (compileAdvice q).theta
        (by change (C root).pack.val = 0; exact hroot)
        (by change (C root).grant = false; exact hg)
        (by change (C (site ring root 1)).pack.val = 1; exact hone)
        hm hb ht)
  have htrip := resetPhysicalEdgeBankTrip ring C root
    (resetColdRootPortDistinct ring C root hc) hsp
  have htokeq :
      (((protocol q).step ring C root)
        (site ring root 1)).tok =
      (resetBankOld (C root)
        (C (site ring root 1))).2.tok :=
    congrArg (fun z : Mode × Bool × BTok => z.2.2) htrip.2
  have hmode := (resetColdOutgoingRootModeLease
    ring C root hc hsp).1
  constructor
  · exact htokeq.trans hrow.1
  · rcases hrow.2 with hcstart | hreset
    · exact Or.inl (hmode.trans hcstart)
    · exact Or.inr (hmode.trans hreset)

/-- The outgoing nonempty CSTART service consumes one worker-slot
credit and therefore pays its full n-unit service charge. -/
theorem resetColdCStartNonemptyOutgoingCharge {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankColdCarrier (q := q) ring root)
    (hm : (x.val root).mode = .CSTART)
    (ht : (x.val (site ring root 1)).tok ≠ .E) :
    n + resetColdUncappedCredit ring root
        (resetClockBankColdNext ring root hsp (.inl x) root) ≤
      resetColdUncappedCredit ring root (.inl x) := by
  have hf := resetColdPhysicalCStartNonempty
    ring x.val root x.property.1 x.property.2 hsp hm ht
  have hw := resetColdWorkerCountOutgoingRootDrop
    ring x.val root x.property.1 ht hf.1
  have hmul :
      n * resetColdWorkerCount ring
          ((protocol q).step ring x.val root) root + n ≤
        n * resetColdWorkerCount ring x.val root := by
    have hh := Nat.mul_le_mul_left n hw
    simpa only [Nat.mul_add, Nat.mul_one] using hh
  have hmode :
      resetColdModeCredit n (compileAdvice q).bankLeaseCap
        (((protocol q).step ring x.val root) root).mode
        (((protocol q).step ring x.val root) root).lease.val ≤
      resetColdModeCredit n (compileAdvice q).bankLeaseCap
        .CSTART 0 := by
    rcases hf.2 with hcstart | hreset
    · rw [hcstart]
      exact Nat.le_refl _
    · rw [hreset]
      change 0 ≤ _
      exact Nat.zero_le _
  calc
    n + resetColdUncappedCredit ring root
        (resetClockBankColdNext ring root hsp (.inl x) root) ≤
      n + (resetColdModeCredit n
          (compileAdvice q).bankLeaseCap
          (((protocol q).step ring x.val root) root).mode
          (((protocol q).step ring x.val root) root).lease.val +
        n * resetColdWorkerCount ring
          ((protocol q).step ring x.val root) root) :=
      Nat.add_le_add_left
        (resetColdNextCreditLePhysical ring root hsp x root) n
    _ ≤ resetColdUncappedCredit ring root (.inl x) := by
      have hc0 :
          resetColdModeCredit n (compileAdvice q).bankLeaseCap
            .CSTART (x.val root).lease.val =
          resetColdModeCredit n (compileAdvice q).bankLeaseCap
            .CSTART 0 := rfl
      simp only [resetColdUncappedCredit, hm]
      omega

/-- Completes the second CSTART case: RL/AL/CL0/CL1 disappear
in CSTART; RR/IR/CR0/CR1 abort. The incoming service is
unchanged unless it is already a stopped defect. -/
theorem resetColdCStartTokenTwoPortDrift {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (x : ResetClockBankColdCarrier (q := q) ring root)
    (hpred : ring.rightNeighbor e = root)
    (hm : (x.val root).mode = .CSTART)
    (ht : (x.val (site ring root 1)).tok ≠ .E) :
    n +
      resetColdUncappedCredit ring root
        (resetClockBankColdNext ring root hsp (.inl x) root) +
      resetColdUncappedCredit ring root
        (resetClockBankColdNext ring root hsp (.inl x) e) ≤
      2 * resetColdUncappedCredit ring root (.inl x) := by
  have ho := resetColdCStartNonemptyOutgoingCharge
    ring root hsp x hm ht
  have hi := resetColdIncomingCStartNextLe
    ring root hsp hlarge x e hpred hm
  calc
    _ ≤ resetColdUncappedCredit ring root (.inl x) +
        resetColdUncappedCredit ring root (.inl x) :=
      Nat.add_le_add ho hi
    _ = 2 * resetColdUncappedCredit ring root (.inl x) := by omega

/-! ARMED: incoming preemption, outgoing maximum IR-head budget. -/

/-- A stopped successor whose root reaches RESET carries zero
credit; the incoming-root ARMED row is such a successor. -/
theorem resetColdPhysicalIncomingArmed {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hpred : ring.rightNeighbor e = root)
    (hrole : (C e).pack.val = (compileAdvice q).b ∨
      (C e).pack.val = (compileAdvice q).b + 1)
    (hm : (C root).mode = .ARMED) :
    (((protocol q).step ring C e) root).mode = .RESET := by
  have hroot : (C root).pack.val = 0 := by
    simpa only [site] using hc 0 (by omega)
  have hpost :
      packNext (C e).pack.val (C root).pack.val
        (compileAdvice q).b = 0 := by
    rcases hrole with hr | hr
    · rw [hr, hroot]
      simp [packNext]
    · rw [hr, hroot]
      simp [packNext]
  have hs : e ≠ root := by
    intro he
    subst e
    have hneq := resetColdRootPortDistinct ring C root hc
    exact hneq hpred
  have hrow :
      (resetBankOld (C e) (C root)).2.mode = .RESET := by
    have hsource : (C e).pack.val ≠ 0 := by
      have hwidth := resetTrialCompiledWidth q
      rcases hrole with hr | hr <;> omega
    simpa only [resetBankOld, hpost, bankCell] using
      (resetColdIncomingArmedBank
        (bankCell (C e) (C e).pack.val)
        (bankCell (C root) (C root).pack.val)
        (compileAdvice q).b (compileAdvice q).theta
        (by change (C e).pack.val ≠ 0; exact hsource)
        (by change (C root).pack.val = 0; exact hroot)
        (by change (C root).grant = false; exact hg)
        hm)
  exact (resetColdIncomingRootModeLease
    ring C root e hs hpred hsp).1.trans hrow

theorem resetColdIncomingArmedNextZero {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankColdCarrier (q := q) ring root)
    (hpred : ring.rightNeighbor e = root)
    (hm : (x.val root).mode = .ARMED) :
    resetColdUncappedCredit ring root
      (resetClockBankColdNext ring root hsp (.inl x) e) = 0 := by
  rcases resetColdIncomingDefectOrRole
    ring x.val root e x.property.1 hpred with hd | hrole
  · rw [resetClockBankColdNextDefect ring root hsp x e hd]
    rfl
  · exact resetColdNextResetCreditZero ring root hsp x e
      (resetColdPhysicalIncomingArmed
        ring x.val root e x.property.1 x.property.2
        hsp hpred hrole hm)

/-- For an ARMED source the outgoing root BANK mode is one of:
RESET (abort), ARMED (return-token consumed), CSTART (head bit zero),
or IWAIT (head bit one). No outgoing outcome is a waiting reset phase. -/
theorem resetColdArmedBankOutModes
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hr : x.role = 0) (hg : x.grant = false)
    (hy : y.role = 1) (hm : x.mode = .ARMED)
    (hb : 0 < b) :
    (bankPair x y 1 b theta).1.mode = .RESET ∨
      (bankPair x y 1 b theta).1.mode = .ARMED ∨
      (bankPair x y 1 b theta).1.mode = .CSTART ∨
      (bankPair x y 1 b theta).1.mode = .IWAIT := by
  have hbge : 1 ≤ b := by omega
  cases ht : y.tok <;> cases hbit : y.bit <;>
    simp [bankPair, hr, hg, hy, hm,
      ht, hbit, hbge, isRetTok, isWaitMode]

theorem resetColdPhysicalArmedOutModes {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hm : (C root).mode = .ARMED) :
    (((protocol q).step ring C root) root).mode = .RESET ∨
      (((protocol q).step ring C root) root).mode = .ARMED ∨
      (((protocol q).step ring C root) root).mode = .CSTART ∨
      (((protocol q).step ring C root) root).mode = .IWAIT := by
  have hroot : (C root).pack.val = 0 := by
    simpa only [site] using hc 0 (by omega)
  have hone : (C (site ring root 1)).pack.val = 1 :=
    hc 1 (by have hh := resetTrialCompiledWidth q; omega)
  have hb : 0 < (compileAdvice q).b := by
    have hh := resetTrialCompiledWidth q
    omega
  have hpost :
      packNext (C root).pack.val
        (C (site ring root 1)).pack.val
        (compileAdvice q).b = 1 := by
    rw [hroot, hone]
    simp [packNext, hb]
  have hrow :
      (resetBankOld (C root) (C (site ring root 1))).1.mode =
        .RESET ∨
      (resetBankOld (C root) (C (site ring root 1))).1.mode =
        .ARMED ∨
      (resetBankOld (C root) (C (site ring root 1))).1.mode =
        .CSTART ∨
      (resetBankOld (C root) (C (site ring root 1))).1.mode =
        .IWAIT := by
    simpa only [resetBankOld, hpost, bankCell] using
      (resetColdArmedBankOutModes
        (bankCell (C root) (C root).pack.val)
        (bankCell (C (site ring root 1))
          (C (site ring root 1)).pack.val)
        (compileAdvice q).b (compileAdvice q).theta
        (by change (C root).pack.val = 0; exact hroot)
        (by change (C root).grant = false; exact hg)
        (by change (C (site ring root 1)).pack.val = 1; exact hone)
        hm hb)
  have hrootMode := (resetColdOutgoingRootModeLease
    ring C root hc hsp).1
  rcases hrow with hreset | harm | hcstart | hiwait
  · exact Or.inl (hrootMode.trans hreset)
  · exact Or.inr (Or.inl (hrootMode.trans harm))
  · exact Or.inr (Or.inr (Or.inl (hrootMode.trans hcstart)))
  · exact Or.inr (Or.inr (Or.inr (hrootMode.trans hiwait)))

/-- Even after discarding all information about the first digit,
IWAIT with full lease is the largest of the possible ARMED
outgoing root-mode credits. -/
theorem resetColdArmedModeCreditUpper (n cap lease : Nat)
    (hl : lease ≤ cap) (m : Mode)
    (hm : m = .RESET ∨ m = .ARMED ∨
      m = .CSTART ∨ m = .IWAIT) :
    resetColdModeCredit n cap m lease ≤
      resetColdModeCredit n cap .IWAIT cap := by
  rcases hm with hreset | harm | hcstart | hiwait
  · rw [hreset]
    change 0 ≤ _
    exact Nat.zero_le _
  · rw [harm]
    change resetColdArmedCredit n cap ≤
      resetColdComparatorCredit n cap +
        resetColdHalfClock n * cap
    unfold resetColdComparatorCredit
    omega
  · rw [hcstart]
    change resetColdComparatorCredit n cap ≤
      resetColdComparatorCredit n cap +
        resetColdHalfClock n * cap
    exact Nat.le_add_right _ _
  · rw [hiwait]
    change resetColdComparatorCredit n cap +
        resetColdHalfClock n * lease ≤
      resetColdComparatorCredit n cap +
        resetColdHalfClock n * cap
    exact Nat.add_le_add_left
      (Nat.mul_le_mul_left _ hl) _

theorem resetColdArmedOutgoingNextLe {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankColdCarrier (q := q) ring root)
    (hm : (x.val root).mode = .ARMED) :
    resetColdUncappedCredit ring root
        (resetClockBankColdNext ring root hsp (.inl x) root) ≤
      resetColdModeCredit n (compileAdvice q).bankLeaseCap
        .IWAIT (compileAdvice q).bankLeaseCap +
      n * (resetColdWorkerCount ring x.val root + 1) := by
  have hmode := resetColdPhysicalArmedOutModes
    ring x.val root x.property.1 x.property.2 hsp hm
  have hl :
      (((protocol q).step ring x.val root) root).lease.val ≤
        (compileAdvice q).bankLeaseCap := by
    have hh := (((protocol q).step ring x.val root) root).lease.isLt
    omega
  have hu := resetColdArmedModeCreditUpper n
    (compileAdvice q).bankLeaseCap
    (((protocol q).step ring x.val root) root).lease.val
    hl (((protocol q).step ring x.val root) root).mode hmode
  have hw := resetColdWorkerCountOutgoingRootLe
    ring x.val root x.property.1
  calc
    _ ≤ resetColdModeCredit n (compileAdvice q).bankLeaseCap
          (((protocol q).step ring x.val root) root).mode
          (((protocol q).step ring x.val root) root).lease.val +
        n * resetColdWorkerCount ring
          ((protocol q).step ring x.val root) root :=
      resetColdNextCreditLePhysical ring root hsp x root
    _ ≤ resetColdModeCredit n (compileAdvice q).bankLeaseCap
          .IWAIT (compileAdvice q).bankLeaseCap +
        n * (resetColdWorkerCount ring x.val root + 1) :=
      Nat.add_le_add hu (Nat.mul_le_mul_left n hw)

/-- The worst outgoing ARMED head spends all the available
two-port budget; all non-head rows are cheaper. -/
theorem resetColdArmedAllSlotBudget (n cap occupied : Nat) :
    n + (resetColdModeCredit n cap .IWAIT cap +
      n * (occupied + 1)) ≤
      2 * (resetColdModeCredit n cap .ARMED 0 +
        n * occupied) := by
  have hh := resetColdArmedHeadBudget n cap
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- Completes ARMED for arbitrary first-digit scratch and
all actual stopped outcomes: incoming preempts to RESET and
outgoing is dominated by the full-lease increment head. -/
theorem resetColdArmedTwoPortDrift {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankColdCarrier (q := q) ring root)
    (hpred : ring.rightNeighbor e = root)
    (hm : (x.val root).mode = .ARMED) :
    n +
      resetColdUncappedCredit ring root
        (resetClockBankColdNext ring root hsp (.inl x) root) +
      resetColdUncappedCredit ring root
        (resetClockBankColdNext ring root hsp (.inl x) e) ≤
      2 * resetColdUncappedCredit ring root (.inl x) := by
  have hi := resetColdIncomingArmedNextZero
    ring root e hsp x hpred hm
  have ho := resetColdArmedOutgoingNextLe
    ring root hsp x hm
  have hb := resetColdArmedAllSlotBudget
    n (compileAdvice q).bankLeaseCap
      (resetColdWorkerCount ring x.val root)
  rw [hi, Nat.add_zero]
  calc
    _ ≤ n + (resetColdModeCredit n (compileAdvice q).bankLeaseCap
          .IWAIT (compileAdvice q).bankLeaseCap +
        n * (resetColdWorkerCount ring x.val root + 1)) :=
      Nat.add_le_add_left ho n
    _ ≤ 2 * resetColdUncappedCredit ring root (.inl x) := by
      simpa only [resetColdUncappedCredit, hm,
        resetColdModeCredit] using hb

end Counter
end L3


/-!
Literal WAIT-mode root-edge accounting.

All credit statements use the uncapped physical cold potential.
The remaining top-edge and scheduler sum are recorded after the code.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open K2ArbitraryElimination.FiniteAccounting

/-- The common watchdog service on all three waiting modes. -/
def resetColdWaitTickMode (m : Mode) (lease : Nat) : Mode :=
  if 1 < lease then m else .RESET

def resetColdWaitTickLease (lease : Nat) : Nat :=
  if 1 < lease then lease - 1 else 0

theorem resetColdWaitTickLeaseLe (lease : Nat) :
    resetColdWaitTickLease lease ≤ lease := by
  unfold resetColdWaitTickLease
  split <;> omega

theorem resetColdWaitTickCreditLe (n cap lease : Nat)
    (m : Mode) (hm : isWaitMode m = true) :
    resetColdModeCredit n cap
        (resetColdWaitTickMode m lease)
        (resetColdWaitTickLease lease) ≤
      resetColdModeCredit n cap m lease := by
  have hmul :
      resetColdHalfClock n * (lease - 1) ≤
        resetColdHalfClock n * lease :=
    Nat.mul_le_mul_left _ (Nat.sub_le lease 1)
  by_cases hl : 1 < lease
  · cases m with
    | RESET => simp [isWaitMode] at hm
    | RWAIT =>
        simp only [resetColdWaitTickMode, if_pos hl,
          resetColdWaitTickLease, if_pos hl, resetColdModeCredit]
        omega
    | ARMED => simp [isWaitMode] at hm
    | IWAIT =>
        simp only [resetColdWaitTickMode, if_pos hl,
          resetColdWaitTickLease, if_pos hl, resetColdModeCredit]
        omega
    | CSTART => simp [isWaitMode] at hm
    | CWAIT =>
        simp only [resetColdWaitTickMode, if_pos hl,
          resetColdWaitTickLease, if_pos hl, resetColdModeCredit]
        omega
  · simp [resetColdWaitTickMode, hl, resetColdModeCredit]

private theorem resetColdWaitCreditPaysService
    (n cap lease : Nat) (m : Mode)
    (hm : isWaitMode m = true) :
    n ≤ 2 * resetColdModeCredit n cap m lease := by
  cases m with
  | RESET => simp [isWaitMode] at hm
  | RWAIT =>
      simp [resetColdModeCredit, resetColdArmedCredit]
      omega
  | ARMED => simp [isWaitMode] at hm
  | IWAIT =>
      simp [resetColdModeCredit, resetColdComparatorCredit,
        resetColdArmedCredit]
      omega
  | CSTART => simp [isWaitMode] at hm
  | CWAIT =>
      simp [resetColdModeCredit, resetColdArmedCredit]
      omega

/-- With no return byte, both root orientations spend their
watchdog lease (or both stop at RESET). This pays one service. -/
theorem resetColdWaitTickPairBudget
    (n cap lease : Nat) (m : Mode)
    (hm : isWaitMode m = true) :
    n + 2 * resetColdModeCredit n cap
        (resetColdWaitTickMode m lease)
        (resetColdWaitTickLease lease) ≤
      2 * resetColdModeCredit n cap m lease := by
  by_cases hl : 1 < lease
  · have hp : 0 < lease := by omega
    have hh := resetColdWaitPairBudget n cap lease m hm hp
    have heMode : resetColdWaitTickMode m lease = m := by
      simp [resetColdWaitTickMode, hl]
    have heLease : resetColdWaitTickLease lease = lease - 1 := by
      simp [resetColdWaitTickLease, hl]
    rw [heMode, heLease]
    omega
  · have hzero : resetColdWaitTickMode m lease = .RESET := by
      simp [resetColdWaitTickMode, hl]
    rw [hzero]
    have hpay := resetColdWaitCreditPaysService n cap lease m hm
    simp only [resetColdModeCredit, Nat.mul_zero, Nat.add_zero]
    exact hpay

/-! Full literal BANK row, before lifting into the real physical step. -/

/-- Incoming-root BANK is a uniform watchdog tick on RWAIT,
IWAIT and CWAIT, independently of the predecessor's worker. -/
theorem resetColdWaitIncomingBankRow
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : x.role ≠ 0) (hy : y.role = 0)
    (hg : y.grant = false)
    (hm : isWaitMode y.mode = true) :
    (bankPair x y 0 b theta).2.mode =
        resetColdWaitTickMode y.mode y.lease ∧
      (bankPair x y 0 b theta).2.lease =
        resetColdWaitTickLease y.lease := by
  cases hmode : y.mode <;>
    simp [isWaitMode, hmode] at hm <;>
    by_cases hlease : 1 < y.lease <;>
    simp [bankPair, hx, hy, hg, hmode, hlease,
      resetColdWaitTickMode, resetColdWaitTickLease,
      isWaitMode, Id.run_pure, Id.run_bind] <;>
    repeat (first | rfl | omega |
      (split <;> simp [Id.run_pure, Id.run_bind]))
  all_goals (refine And.intro ?_ ?_ <;> (split <;> (try split) <;> rfl))
/-- Nonreturn first-digit bytes do not modify the digit slot.
All waiting modes execute the same watchdog tick. The b>1
hypothesis excludes the special b=1 single-digit turn. -/
theorem resetColdWaitNonreturnBankRow
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false) (hb : 1 < b)
    (hm : isWaitMode x.mode = true)
    (ht : isRetTok y.tok = false) :
    (bankPair x y 1 b theta).1.mode =
        resetColdWaitTickMode x.mode x.lease ∧
      (bankPair x y 1 b theta).1.lease =
        resetColdWaitTickLease x.lease ∧
      (bankPair x y 1 b theta).2.tok = y.tok := by
  have hbge : 1 ≤ b := by omega
  have hbne : b ≠ 1 := by omega
  cases hmode : x.mode <;> cases htok : y.tok <;>
    simp [isWaitMode, hmode] at hm <;>
    simp [isRetTok, htok] at ht <;>
    by_cases hlease : 1 < x.lease <;>
    simp [bankPair, hx, hy, hg, hbge, hbne, hmode,
      htok, hlease, resetColdWaitTickMode,
      resetColdWaitTickLease, isWaitMode, isRetTok,
      Id.run_pure, Id.run_bind] <;>
    repeat (first | rfl | omega |
      (split <;> simp [Id.run_pure, Id.run_bind]))
/-- Every return byte is consumed in a waiting mode.
The outgoing root credit never exceeds its old mode+lease
credit, and the numeric lease never increases. -/
theorem resetColdWaitReturnBankCredit
    (n cap : Nat) (x y : BankCell)
    (b : Nat) (theta : Nat → Bool)
    (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false)
    (hm : isWaitMode x.mode = true)
    (ht : isRetTok y.tok = true) :
    (bankPair x y 1 b theta).2.tok = .E ∧
      resetColdModeCredit n cap
          (bankPair x y 1 b theta).1.mode
          (bankPair x y 1 b theta).1.lease ≤
        resetColdModeCredit n cap x.mode x.lease ∧
      (bankPair x y 1 b theta).1.lease ≤ x.lease := by
  have hmul :
      resetColdHalfClock n * (x.lease - 1) ≤
        resetColdHalfClock n * x.lease :=
    Nat.mul_le_mul_left _ (Nat.sub_le x.lease 1)
  cases hmode : x.mode <;> cases htok : y.tok <;>
    simp [isWaitMode, hmode] at hm <;>
    simp [isRetTok, htok] at ht <;>
    by_cases hbzero : b = 0 <;>
    by_cases hlease : 1 < x.lease <;>
    simp [bankPair, hx, hy, hg, hmode, htok,
      hbzero, hlease, isWaitMode, isRetTok,
      resetColdModeCredit, resetColdArmedCredit,
      resetColdComparatorCredit,
      Id.run_pure, Id.run_bind] <;>
    repeat (first | rfl | omega |
      (split <;> simp [Id.run_pure, Id.run_bind]))
/-! Physically observed outgoing root WAIT rows. -/

/-- The complete outgoing mode, lease, and first-digit token
are obtained from the literal BANK row, not a surrogate step. -/
theorem resetColdPhysicalWaitNonreturn {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hm : isWaitMode (C root).mode = true)
    (ht : isRetTok (C (site ring root 1)).tok = false) :
    (((protocol q).step ring C root) root).mode =
        resetColdWaitTickMode (C root).mode (C root).lease.val ∧
      (((protocol q).step ring C root) root).lease.val =
        resetColdWaitTickLease (C root).lease.val ∧
      (((protocol q).step ring C root)
        (site ring root 1)).tok =
        (C (site ring root 1)).tok := by
  have hroot : (C root).pack.val = 0 := by
    simpa only [site] using hc 0 (by omega)
  have hone : (C (site ring root 1)).pack.val = 1 :=
    hc 1 (by have hh := resetTrialCompiledWidth q; omega)
  have hb : 1 < (compileAdvice q).b := resetTrialCompiledWidth q
  have hpost :
      packNext (C root).pack.val
        (C (site ring root 1)).pack.val
        (compileAdvice q).b = 1 := by
    rw [hroot, hone]
    have hbpos : 0 < (compileAdvice q).b := by omega
    simp [packNext, hbpos]
  have hrow :
      (resetBankOld (C root) (C (site ring root 1))).1.mode =
        resetColdWaitTickMode (C root).mode (C root).lease.val ∧
      (resetBankOld (C root) (C (site ring root 1))).1.lease =
        resetColdWaitTickLease (C root).lease.val ∧
      (resetBankOld (C root) (C (site ring root 1))).2.tok =
        (C (site ring root 1)).tok := by
    simpa only [resetBankOld, hpost, bankCell] using
      (resetColdWaitNonreturnBankRow
        (bankCell (C root) (C root).pack.val)
        (bankCell (C (site ring root 1))
          (C (site ring root 1)).pack.val)
        (compileAdvice q).b (compileAdvice q).theta
        (by change (C root).pack.val = 0; exact hroot)
        (by change (C (site ring root 1)).pack.val = 1; exact hone)
        (by change (C root).grant = false; exact hg)
        hb hm ht)
  have hmodeLease := resetColdOutgoingRootModeLease
    ring C root hc hsp
  have hfit :
      (resetBankOld (C root)
        (C (site ring root 1))).1.lease <
      (compileAdvice q).bankLeaseCap + 1 := by
    rw [hrow.2.1]
    exact Nat.lt_of_le_of_lt
      (resetColdWaitTickLeaseLe (C root).lease.val)
      (C root).lease.isLt
  have hlease :
      (((protocol q).step ring C root) root).lease.val =
        resetColdWaitTickLease (C root).lease.val := by
    have hh := congrArg Fin.val hmodeLease.2
    rw [resetClockCopyBankLeaseExact
      (C root)
      (resetBankOld (C root) (C (site ring root 1))).1
      hfit] at hh
    exact hh.trans hrow.2.1
  have htrip := resetPhysicalEdgeBankTrip ring C root
    (resetColdRootPortDistinct ring C root hc) hsp
  have htok :
      (((protocol q).step ring C root)
        (site ring root 1)).tok =
      (resetBankOld (C root)
        (C (site ring root 1))).2.tok :=
    congrArg (fun z : Mode × Bool × BTok => z.2.2) htrip.2
  exact ⟨hmodeLease.1.trans hrow.1,
    hlease, htok.trans hrow.2.2⟩

/-- A return byte in RWAIT/IWAIT/CWAIT always erases the
first worker and never increases the root's numerical credit. -/
theorem resetColdPhysicalWaitReturn {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hm : isWaitMode (C root).mode = true)
    (ht : isRetTok (C (site ring root 1)).tok = true) :
    (((protocol q).step ring C root)
        (site ring root 1)).tok = .E ∧
      resetColdModeCredit n (compileAdvice q).bankLeaseCap
        (((protocol q).step ring C root) root).mode
        (((protocol q).step ring C root) root).lease.val ≤
      resetColdModeCredit n (compileAdvice q).bankLeaseCap
        (C root).mode (C root).lease.val := by
  have hroot : (C root).pack.val = 0 := by
    simpa only [site] using hc 0 (by omega)
  have hone : (C (site ring root 1)).pack.val = 1 :=
    hc 1 (by have hh := resetTrialCompiledWidth q; omega)
  have hb : 0 < (compileAdvice q).b := by
    have hh := resetTrialCompiledWidth q
    omega
  have hpost :
      packNext (C root).pack.val
        (C (site ring root 1)).pack.val
        (compileAdvice q).b = 1 := by
    rw [hroot, hone]
    simp [packNext, hb]
  have hrow :
      (resetBankOld (C root) (C (site ring root 1))).2.tok = .E ∧
      resetColdModeCredit n (compileAdvice q).bankLeaseCap
        (resetBankOld (C root)
          (C (site ring root 1))).1.mode
        (resetBankOld (C root)
          (C (site ring root 1))).1.lease ≤
      resetColdModeCredit n (compileAdvice q).bankLeaseCap
        (C root).mode (C root).lease.val ∧
      (resetBankOld (C root)
        (C (site ring root 1))).1.lease ≤ (C root).lease.val := by
    simpa only [resetBankOld, hpost, bankCell] using
      (resetColdWaitReturnBankCredit n
        (compileAdvice q).bankLeaseCap
        (bankCell (C root) (C root).pack.val)
        (bankCell (C (site ring root 1))
          (C (site ring root 1)).pack.val)
        (compileAdvice q).b (compileAdvice q).theta
        (by change (C root).pack.val = 0; exact hroot)
        (by change (C (site ring root 1)).pack.val = 1; exact hone)
        (by change (C root).grant = false; exact hg)
        hm ht)
  have hmodeLease := resetColdOutgoingRootModeLease
    ring C root hc hsp
  have hfit :
      (resetBankOld (C root)
        (C (site ring root 1))).1.lease <
      (compileAdvice q).bankLeaseCap + 1 :=
    Nat.lt_of_le_of_lt hrow.2.2 (C root).lease.isLt
  have hlease :
      (((protocol q).step ring C root) root).lease.val =
      (resetBankOld (C root)
        (C (site ring root 1))).1.lease := by
    have hh := congrArg Fin.val hmodeLease.2
    rw [resetClockCopyBankLeaseExact
      (C root)
      (resetBankOld (C root) (C (site ring root 1))).1
      hfit] at hh
    exact hh
  have htrip := resetPhysicalEdgeBankTrip ring C root
    (resetColdRootPortDistinct ring C root hc) hsp
  have htok :
      (((protocol q).step ring C root)
        (site ring root 1)).tok =
      (resetBankOld (C root)
        (C (site ring root 1))).2.tok :=
    congrArg (fun z : Mode × Bool × BTok => z.2.2) htrip.2
  constructor
  · exact htok.trans hrow.1
  · rw [hmodeLease.1, hlease]
    exact hrow.2.1

/-! The incoming root's old predecessor may be arbitrarily dirty. -/

/-- The literal predecessor-to-root BANK row is a watchdog tick,
independent of the predecessor's private worker fields. -/
theorem resetColdPhysicalIncomingWait {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hpred : ring.rightNeighbor e = root)
    (hrole : (C e).pack.val = (compileAdvice q).b ∨
      (C e).pack.val = (compileAdvice q).b + 1)
    (hm : isWaitMode (C root).mode = true) :
    (((protocol q).step ring C e) root).mode =
        resetColdWaitTickMode (C root).mode (C root).lease.val ∧
      (((protocol q).step ring C e) root).lease.val =
        resetColdWaitTickLease (C root).lease.val := by
  have hroot : (C root).pack.val = 0 := by
    simpa only [site] using hc 0 (by omega)
  have hpost :
      packNext (C e).pack.val (C root).pack.val
        (compileAdvice q).b = 0 := by
    rcases hrole with hr | hr
    · rw [hr, hroot]
      simp [packNext]
    · rw [hr, hroot]
      simp [packNext]
  have hs : e ≠ root := by
    intro he
    subst e
    exact (resetColdRootPortDistinct ring C root hc) hpred
  have hrow :
      (resetBankOld (C e) (C root)).2.mode =
        resetColdWaitTickMode (C root).mode (C root).lease.val ∧
      (resetBankOld (C e) (C root)).2.lease =
        resetColdWaitTickLease (C root).lease.val := by
    have hbpos : 0 < (compileAdvice q).b := by
      have hh := resetTrialCompiledWidth q
      omega
    have hx : (C e).pack.val ≠ 0 := by
      rcases hrole with hr | hr <;> omega
    simpa only [resetBankOld, hpost, bankCell] using
      (resetColdWaitIncomingBankRow
        (bankCell (C e) (C e).pack.val)
        (bankCell (C root) (C root).pack.val)
        (compileAdvice q).b (compileAdvice q).theta
        (by change (C e).pack.val ≠ 0; exact hx)
        (by change (C root).pack.val = 0; exact hroot)
        (by change (C root).grant = false; exact hg)
        hm)
  have hphys := resetColdIncomingRootModeLease
    ring C root e hs hpred hsp
  have hfit :
      (resetBankOld (C e) (C root)).2.lease <
        (compileAdvice q).bankLeaseCap + 1 := by
    rw [hrow.2]
    exact Nat.lt_of_le_of_lt
      (resetColdWaitTickLeaseLe (C root).lease.val)
      (C root).lease.isLt
  have hlease :
      (((protocol q).step ring C e) root).lease.val =
        resetColdWaitTickLease (C root).lease.val := by
    have hh := congrArg Fin.val hphys.2
    rw [resetClockCopyBankLeaseExact
      (C root) (resetBankOld (C e) (C root)).2 hfit] at hh
    exact hh.trans hrow.2
  exact ⟨hphys.1.trans hrow.1, hlease⟩

/-- Even with a defective source the stopped incoming root credit
is at most the ticked mode-credit plus the unchanged digit slots. -/
theorem resetColdIncomingWaitNextLe {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (x : ResetClockBankColdCarrier (q := q) ring root)
    (hpred : ring.rightNeighbor e = root)
    (hm : isWaitMode (x.val root).mode = true) :
    resetColdUncappedCredit ring root
      (resetClockBankColdNext ring root hsp (.inl x) e) ≤
      resetColdModeCredit n (compileAdvice q).bankLeaseCap
        (resetColdWaitTickMode (x.val root).mode
          (x.val root).lease.val)
        (resetColdWaitTickLease (x.val root).lease.val) +
      n * resetColdWorkerCount ring x.val root := by
  rcases resetColdIncomingDefectOrRole
    ring x.val root e x.property.1 hpred with hd | hrole
  · rw [resetClockBankColdNextDefect ring root hsp x e hd]
    change 0 ≤ _
    exact Nat.zero_le _
  · have hfields := resetColdPhysicalIncomingWait
      ring x.val root e x.property.1 x.property.2
      hsp hpred hrole hm
    have hw := resetColdWorkerCountIncomingRootEq
      ring x.val root e x.property.1 hpred
      (resetColdIncomingExteriorOfLarge ring x.val
        root e x.property.1 hlarge hpred)
    calc
      _ ≤ resetColdModeCredit n (compileAdvice q).bankLeaseCap
          (((protocol q).step ring x.val e) root).mode
          (((protocol q).step ring x.val e) root).lease.val +
        n * resetColdWorkerCount ring
          ((protocol q).step ring x.val e) root :=
        resetColdNextCreditLePhysical ring root hsp x e
      _ = _ := by rw [hfields.1, hfields.2, hw]

/-! Global worker-slot frame for an outgoing root service. -/

theorem resetColdWorkerCountOutgoingRootEqOfToken {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n) (hc : Complete ring C root)
    (ht : (((protocol q).step ring C root)
      (site ring root 1)).tok = (C (site ring root 1)).tok) :
    resetColdWorkerCount ring
      ((protocol q).step ring C root) root =
      resetColdWorkerCount ring C root := by
  unfold resetColdWorkerCount
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have hib : i < (compileAdvice q).b := by
    simpa only [List.mem_range] using hi
  by_cases hfirst : i = 0
  · subst i
    simp only [Nat.zero_add]
    rw [ht]
  · rw [resetColdOutgoingRootOtherDigitsFrame
      ring C root hc (i + 1) (by omega) (by omega)]

/-- Every outgoing WAIT service with a nonreturn digit-one byte
ticks the lease and preserves all active digit occupancy. -/
theorem resetColdWaitNonreturnOutgoingNextLe {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankColdCarrier (q := q) ring root)
    (hm : isWaitMode (x.val root).mode = true)
    (ht : isRetTok (x.val (site ring root 1)).tok = false) :
    resetColdUncappedCredit ring root
      (resetClockBankColdNext ring root hsp (.inl x) root) ≤
      resetColdModeCredit n (compileAdvice q).bankLeaseCap
        (resetColdWaitTickMode (x.val root).mode
          (x.val root).lease.val)
        (resetColdWaitTickLease (x.val root).lease.val) +
      n * resetColdWorkerCount ring x.val root := by
  have hf := resetColdPhysicalWaitNonreturn ring x.val root
    x.property.1 x.property.2 hsp hm ht
  have hw := resetColdWorkerCountOutgoingRootEqOfToken
    ring x.val root x.property.1 hf.2.2
  calc
    _ ≤ resetColdModeCredit n (compileAdvice q).bankLeaseCap
          (((protocol q).step ring x.val root) root).mode
          (((protocol q).step ring x.val root) root).lease.val +
        n * resetColdWorkerCount ring
          ((protocol q).step ring x.val root) root :=
      resetColdNextCreditLePhysical ring root hsp x root
    _ = _ := by rw [hf.1, hf.2.1, hw]

/-- Every return byte is consumed and its released slot pays n,
including forged/mismatched returning workers. The root-mode
credit is bounded by its old WAIT credit. -/
theorem resetColdWaitReturnOutgoingCharge {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankColdCarrier (q := q) ring root)
    (hm : isWaitMode (x.val root).mode = true)
    (ht : isRetTok (x.val (site ring root 1)).tok = true) :
    n + resetColdUncappedCredit ring root
        (resetClockBankColdNext ring root hsp (.inl x) root) ≤
      resetColdUncappedCredit ring root (.inl x) := by
  have hne : (x.val (site ring root 1)).tok ≠ .E := by
    intro he
    rw [he] at ht
    cases ht
  have hf := resetColdPhysicalWaitReturn
    ring x.val root x.property.1 x.property.2 hsp hm ht
  have hw := resetColdWorkerCountOutgoingRootDrop
    ring x.val root x.property.1 hne hf.1
  have hscaled :
      n * resetColdWorkerCount ring
          ((protocol q).step ring x.val root) root + n ≤
        n * resetColdWorkerCount ring x.val root := by
    have hh := Nat.mul_le_mul_left n hw
    simpa only [Nat.mul_add, Nat.mul_one] using hh
  have hendpoint := resetColdNextCreditLePhysical
    ring root hsp x root
  change n + resetColdUncappedCredit ring root
        (resetClockBankColdNext ring root hsp (.inl x) root) ≤
      resetColdModeCredit n (compileAdvice q).bankLeaseCap
        (x.val root).mode (x.val root).lease.val +
      n * resetColdWorkerCount ring x.val root
  omega

/-- All three WAIT modes satisfy the two-root-edge Bellman
inequality, with any lease 0..Lambda and arbitrary digit workers.
Return tokens consume a slot; nonreturns invoke two watchdog ticks. -/
theorem resetColdWaitTwoPortDrift {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (x : ResetClockBankColdCarrier (q := q) ring root)
    (hpred : ring.rightNeighbor e = root)
    (hm : isWaitMode (x.val root).mode = true) :
    n +
      resetColdUncappedCredit ring root
        (resetClockBankColdNext ring root hsp (.inl x) root) +
      resetColdUncappedCredit ring root
        (resetClockBankColdNext ring root hsp (.inl x) e) ≤
      2 * resetColdUncappedCredit ring root (.inl x) := by
  have hi := resetColdIncomingWaitNextLe
    ring root e hsp hlarge x hpred hm
  by_cases ht : isRetTok (x.val (site ring root 1)).tok = true
  · have ho := resetColdWaitReturnOutgoingCharge
      ring root hsp x hm ht
    have htick := resetColdWaitTickCreditLe n
      (compileAdvice q).bankLeaseCap
      (x.val root).lease.val (x.val root).mode hm
    have hiOld :
        resetColdUncappedCredit ring root
          (resetClockBankColdNext ring root hsp (.inl x) e) ≤
        resetColdUncappedCredit ring root (.inl x) := by
      change _ ≤
        resetColdModeCredit n (compileAdvice q).bankLeaseCap
          (x.val root).mode (x.val root).lease.val +
        n * resetColdWorkerCount ring x.val root
      exact Nat.le_trans hi
        (Nat.add_le_add_right htick _)
    calc
      _ ≤ resetColdUncappedCredit ring root (.inl x) +
          resetColdUncappedCredit ring root (.inl x) :=
        Nat.add_le_add ho hiOld
      _ = 2 * resetColdUncappedCredit ring root (.inl x) := by omega
  · have htfalse :
        isRetTok (x.val (site ring root 1)).tok = false := by
      cases htok : isRetTok (x.val (site ring root 1)).tok with
      | false => rfl
      | true => exact False.elim (ht htok)
    have ho := resetColdWaitNonreturnOutgoingNextLe
      ring root hsp x hm htfalse
    have hb := resetColdWaitTickPairBudget n
      (compileAdvice q).bankLeaseCap
      (x.val root).lease.val (x.val root).mode hm
    have hupper :
        n + resetColdUncappedCredit ring root
            (resetClockBankColdNext ring root hsp (.inl x) root) +
          resetColdUncappedCredit ring root
            (resetClockBankColdNext ring root hsp (.inl x) e) ≤
        n + (resetColdModeCredit n (compileAdvice q).bankLeaseCap
            (resetColdWaitTickMode (x.val root).mode
              (x.val root).lease.val)
            (resetColdWaitTickLease (x.val root).lease.val) +
          n * resetColdWorkerCount ring x.val root) +
          (resetColdModeCredit n (compileAdvice q).bankLeaseCap
            (resetColdWaitTickMode (x.val root).mode
              (x.val root).lease.val)
            (resetColdWaitTickLease (x.val root).lease.val) +
          n * resetColdWorkerCount ring x.val root) :=
      Nat.add_le_add (Nat.add_le_add_left ho n) hi
    have htarget :
        n + (resetColdModeCredit n (compileAdvice q).bankLeaseCap
            (resetColdWaitTickMode (x.val root).mode
              (x.val root).lease.val)
            (resetColdWaitTickLease (x.val root).lease.val) +
          n * resetColdWorkerCount ring x.val root) +
          (resetColdModeCredit n (compileAdvice q).bankLeaseCap
            (resetColdWaitTickMode (x.val root).mode
              (x.val root).lease.val)
            (resetColdWaitTickLease (x.val root).lease.val) +
          n * resetColdWorkerCount ring x.val root) ≤
        2 * (resetColdModeCredit n (compileAdvice q).bankLeaseCap
            (x.val root).mode (x.val root).lease.val +
          n * resetColdWorkerCount ring x.val root) := by
      omega
    exact Nat.le_trans hupper (by
      simpa only [resetColdUncappedCredit] using htarget)

end Counter
end L3


/-!
Top boundary and genuinely exterior physical edges. Their only
effect on the first-stage charge is weakly decreasing; all
defect/grant/RESET cuts are still counted as zero.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open K2ArbitraryElimination.FiniteAccounting

/-- The last digit's outgoing edge never increases the sum of
occupied active digit slots, even if the exterior PACK responder
changes role. The changed-role early return is covered by
resetColdBankTopOneSlotBound. -/
theorem resetColdWorkerCountTopPhysicalLe {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n) :
    resetColdWorkerCount ring
      ((protocol q).step ring C
        (site ring root (compileAdvice q).b)) root ≤
      resetColdWorkerCount ring C root := by
  have hb : 0 < (compileAdvice q).b := by
    have hh := resetTrialCompiledWidth q
    omega
  have hn : 2 ≤ n := by
    have hh : 2 * (13 * ((compileAdvice q).b + 2)) ≤ n := by
      simpa only [Compiled.bankLeaseCap] using hlarge
    omega
  have hne :
      ring.rightNeighbor (site ring root (compileAdvice q).b) ≠
        site ring root (compileAdvice q).b :=
    resetRootPortDistinct ring
      (site ring root (compileAdvice q).b) hn
  have hrole :
      (C (site ring root (compileAdvice q).b)).pack.val =
        (compileAdvice q).b :=
    hc (compileAdvice q).b (by omega)
  have hbank :
      resetColdTokenOccupied
        (resetBankOld
          (C (site ring root (compileAdvice q).b))
          (C (site ring root ((compileAdvice q).b + 1)))).1.tok ≤
      resetColdTokenOccupied
        (C (site ring root (compileAdvice q).b)).tok := by
    simpa only [resetBankOld, bankCell] using
      (resetColdBankTopOneSlotBound
        (bankCell (C (site ring root (compileAdvice q).b))
          (C (site ring root (compileAdvice q).b)).pack.val)
        (bankCell (C (site ring root ((compileAdvice q).b + 1)))
          (C (site ring root ((compileAdvice q).b + 1))).pack.val)
        (packNext
          (C (site ring root (compileAdvice q).b)).pack.val
          (C (site ring root ((compileAdvice q).b + 1))).pack.val
          (compileAdvice q).b)
        (compileAdvice q).b (compileAdvice q).theta
        (by exact hrole) hb)
  have htrip := resetPhysicalEdgeBankTrip ring C
    (site ring root (compileAdvice q).b) hne hsp
  have hsource :
      resetColdTokenOccupied
        (((protocol q).step ring C
          (site ring root (compileAdvice q).b))
          (site ring root (compileAdvice q).b)).tok ≤
      resetColdTokenOccupied
        (C (site ring root (compileAdvice q).b)).tok := by
    have heq :
        (((protocol q).step ring C
          (site ring root (compileAdvice q).b))
          (site ring root (compileAdvice q).b)).tok =
        (resetBankOld
          (C (site ring root (compileAdvice q).b))
          (C (site ring root ((compileAdvice q).b + 1)))).1.tok :=
      congrArg (fun z : Mode × Bool × BTok => z.2.2) htrip.1
    rw [heq]
    exact hbank
  have hpoint (i : Nat) (hi : i < (compileAdvice q).b) :
      resetColdTokenOccupied
        (((protocol q).step ring C
          (site ring root (compileAdvice q).b))
          (site ring root (i + 1))).tok ≤
      resetColdTokenOccupied (C (site ring root (i + 1))).tok := by
    by_cases htop : i + 1 = (compileAdvice q).b
    · rw [htop]
      exact hsource
    · have hs :
          site ring root (i + 1) ≠
            site ring root (compileAdvice q).b :=
        resetCompleteSitesDifferent ring C root hc
          (i + 1) (compileAdvice q).b
          (by omega) (by omega) htop
      have ht :
          site ring root (i + 1) ≠
            ring.rightNeighbor
              (site ring root (compileAdvice q).b) := by
        intro he
        have hh :
            site ring root i =
              site ring root (compileAdvice q).b :=
          resetTrialNeighborInjective ring (by
            change site ring root (i + 1) =
              site ring root ((compileAdvice q).b + 1)
            exact he)
        exact (resetCompleteSitesDifferent ring C root hc
          i (compileAdvice q).b
          (by omega) (by omega) (by omega)) hh
      have hf := step_frame ring C
        (site ring root (compileAdvice q).b)
        (site ring root (i + 1)) hs ht
      rw [hf]
      exact Nat.le_refl _
  have hsum := resetColdRangePointwiseLe
    (fun i =>
      resetColdTokenOccupied
        (((protocol q).step ring C
          (site ring root (compileAdvice q).b))
          (site ring root (i + 1))).tok)
    (fun i =>
      resetColdTokenOccupied (C (site ring root (i + 1))).tok)
    (compileAdvice q).b hpoint
  simpa only [resetColdWorkerCount,
    resetColdTokenOccupied] using hsum

/-- With hlarge the top outgoing edge cannot touch the root
by wrapping around the ring. -/
theorem resetColdTopRootPhysicalFrame {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n)
    (hc : Complete ring C root)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n) :
    ((protocol q).step ring C
        (site ring root (compileAdvice q).b)) root = C root := by
  have hb : 0 < (compileAdvice q).b := by
    have hh := resetTrialCompiledWidth q
    omega
  have hs : root ≠ site ring root (compileAdvice q).b := by
    change site ring root 0 ≠ site ring root (compileAdvice q).b
    exact resetCompleteSitesDifferent ring C root hc
      0 (compileAdvice q).b (by omega) (by omega) (by omega)
  have hsize : (compileAdvice q).b + 1 < n := by
    have hh : 2 * (13 * ((compileAdvice q).b + 2)) ≤ n := by
      simpa only [Compiled.bankLeaseCap] using hlarge
    omega
  have ht :
      root ≠ ring.rightNeighbor
        (site ring root (compileAdvice q).b) := by
    change root ≠ site ring root ((compileAdvice q).b + 1)
    exact Ne.symm (resetColdSiteShortNoReturn
      ring root ((compileAdvice q).b + 1) (by omega) hsize)
  exact step_frame ring C
    (site ring root (compileAdvice q).b) root hs ht

theorem resetColdUncappedCreditTopNextLe {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (x : ResetClockBankColdCarrier (q := q) ring root) :
    resetColdUncappedCredit ring root
      (resetClockBankColdNext ring root hsp (.inl x)
        (site ring root (compileAdvice q).b)) ≤
      resetColdUncappedCredit ring root (.inl x) := by
  have hf := resetColdTopRootPhysicalFrame
    ring x.val root x.property.1 hlarge
  have hw := resetColdWorkerCountTopPhysicalLe
    ring x.val root x.property.1 hsp hlarge
  calc
    _ ≤ resetColdModeCredit n (compileAdvice q).bankLeaseCap
          (((protocol q).step ring x.val
            (site ring root (compileAdvice q).b)) root).mode
          (((protocol q).step ring x.val
            (site ring root (compileAdvice q).b)) root).lease.val +
        n * resetColdWorkerCount ring
          ((protocol q).step ring x.val
            (site ring root (compileAdvice q).b)) root :=
      resetColdNextCreditLePhysical ring root hsp x _
    _ ≤ resetColdUncappedCredit ring root (.inl x) := by
      rw [hf]
      simpa only [resetColdUncappedCredit] using
        (Nat.add_le_add_left (Nat.mul_le_mul_left n hw)
          (resetColdModeCredit n (compileAdvice q).bankLeaseCap
            (x.val root).mode (x.val root).lease.val))

/-- Edges with both endpoints wholly outside sites zero through b
frame all fields read by the cold credit. -/
theorem resetColdUncappedCreditOutsideNextLe {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : ResetClockBankColdCarrier (q := q) ring root)
    (hout : OutsideSites q ring root e) :
    resetColdUncappedCredit ring root
        (resetClockBankColdNext ring root hsp (.inl x) e) ≤
      resetColdUncappedCredit ring root (.inl x) := by
  have hf := outside_frame ring x.val root e hout
  have hr : ((protocol q).step ring x.val e) root = x.val root := by
    simpa only [site] using hf 0 (by omega)
  have hw :
      resetColdWorkerCount ring
        ((protocol q).step ring x.val e) root =
      resetColdWorkerCount ring x.val root := by
    unfold resetColdWorkerCount
    apply congrArg List.sum
    apply List.map_congr_left
    intro i hi
    have hib : i < (compileAdvice q).b := by
      simpa only [List.mem_range] using hi
    rw [hf (i + 1) (by omega)]
  calc
    _ ≤ resetColdModeCredit n (compileAdvice q).bankLeaseCap
          (((protocol q).step ring x.val e) root).mode
          (((protocol q).step ring x.val e) root).lease.val +
        n * resetColdWorkerCount ring
          ((protocol q).step ring x.val e) root :=
      resetColdNextCreditLePhysical ring root hsp x e
    _ = resetColdUncappedCredit ring root (.inl x) := by
      rw [hr, hw]
      rfl

end Counter
end L3


/-!
The remaining exact finite-scheduler assembly. Two distinct root
ports share the single n-unit charge; all other physical rows are
nonincreasing. No Poissonization is used in the aggregation.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open FiniteUniformStoppingTree

/-- The two-port combination of the already proved CSTART/E,
CSTART/nonempty, ARMED and all WAIT cases. -/
theorem resetColdAllRootModesTwoPortDrift {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (x : ResetClockBankColdCarrier (q := q) ring root)
    (hpred : ring.rightNeighbor e = root)
    (hm : (x.val root).mode ≠ .RESET) :
    n +
      resetColdUncappedCredit ring root
        (resetClockBankColdNext ring root hsp (.inl x) root) +
      resetColdUncappedCredit ring root
        (resetClockBankColdNext ring root hsp (.inl x) e) ≤
      2 * resetColdUncappedCredit ring root (.inl x) := by
  cases hmode : (x.val root).mode with
  | RESET =>
      exact False.elim (hm hmode)
  | ARMED =>
      exact resetColdArmedTwoPortDrift ring root e hsp x
        hpred hmode
  | CSTART =>
      by_cases ht : (x.val (site ring root 1)).tok = .E
      · exact resetColdCStartEmptyTwoPortDrift ring root e
          hsp hlarge x hpred hmode ht
      · exact resetColdCStartTokenTwoPortDrift ring root e
          hsp hlarge x hpred hmode ht
  | RWAIT =>
      exact resetColdWaitTwoPortDrift ring root e
        hsp hlarge x hpred (by simp [isWaitMode, hmode])
  | IWAIT =>
      exact resetColdWaitTwoPortDrift ring root e
        hsp hlarge x hpred (by simp [isWaitMode, hmode])
  | CWAIT =>
      exact resetColdWaitTwoPortDrift ring root e
        hsp hlarge x hpred (by simp [isWaitMode, hmode])

/-- Every other edge is either an internal digit edge, the
top boundary, or completely outside the protected support.
The incoming-root edge has been separately excluded. -/
theorem resetColdOtherEdgeNextLe {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (x : ResetClockBankColdCarrier (q := q) ring root)
    (hne : e ≠ root)
    (hnotincoming : ring.rightNeighbor e ≠ root) :
    resetColdUncappedCredit ring root
        (resetClockBankColdNext ring root hsp (.inl x) e) ≤
      resetColdUncappedCredit ring root (.inl x) := by
  rcases resetTrialEdgeGeometry (q := q) ring root e with
      hsource | hincoming | houtside
  · obtain ⟨j, hjb, heq⟩ := hsource
    subst e
    by_cases hz : j = 0
    · subst j
      exact False.elim (hne rfl)
    · by_cases htop : j = (compileAdvice q).b
      · subst j
        exact resetColdUncappedCreditTopNextLe
          ring root hsp hlarge x
      · have hj : 1 ≤ j := by omega
        have hlt : j < (compileAdvice q).b := by omega
        exact resetColdUncappedCreditInternalNextLe
          ring root hsp x j hj hlt
  · exact False.elim (hnotincoming hincoming)
  · exact resetColdUncappedCreditOutsideNextLe
      ring root e hsp x houtside

/-- An exact predecessor of the root, using the actual cyclic
site constructor rather than a new scheduler edge function. -/
theorem resetColdLastSiteIncoming {n : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ring.rightNeighbor (site ring root (n - 1)) = root := by
  have hn : 0 < n := ring.hn
  have hlen : n - 1 + 1 = n := by omega
  change site ring root (n - 1 + 1) = root
  rw [hlen]
  apply Fin.ext
  rw [resetColdSiteVal ring root n]
  simp [Nat.add_mod, Nat.mod_eq_of_lt root.isLt]

/-- A finite List.ofFn over distinct edge names is Nodup. -/
private theorem resetColdOfFnNodup {k : Nat} {A : Type}
    (f : Fin k → A) (hf : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.ofFn_succ, List.nodup_cons]
      constructor
      · intro hmem
        obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
        have hh := hf hi
        cases hh
      · apply ih
        intro i j hij
        exact Fin.succ_inj.mp (hf hij)

/-- A pair of exceptional scheduler letters share one charge;
all other letters are only required to be weakly decreasing. -/
private theorem resetColdTwoPortFinSum {n : Nat}
    (a b : Fin n) (f : Fin n → Nat) (v : Nat)
    (hn : 2 ≤ n) (hab : a ≠ b)
    (hpair : n + f a + f b ≤ 2 * v)
    (hother : ∀ e : Fin n, e ≠ a → e ≠ b → f e ≤ v) :
    n + (List.ofFn f).sum ≤ n * v := by
  have hpoint (e : Fin n) :
      f e ≤ (if e = a then f a else if e = b then f b else v) := by
    by_cases hea : e = a
    · simp [hea]
    · by_cases heb : e = b
      · subst e
        simp [Ne.symm hab]
      · simpa [hea, heb] using hother e hea heb
  have hmono := ofFn_sum_le f
    (fun e : Fin n =>
      if e = a then f a else if e = b then f b else v)
    hpoint
  have hsum :
      (List.ofFn (fun e : Fin n =>
        if e = a then f a else if e = b then f b else v)).sum =
      f a + f b + (n - 2) * v := by
    have hh := sum_two_exceptions
      (List.ofFn (fun e : Fin n => e)) a b
      (fun e : Fin n =>
        if e = a then f a else if e = b then f b else v) v
      (resetColdOfFnNodup (fun e : Fin n => e)
        Function.injective_id)
      (List.mem_ofFn.mpr ⟨a, rfl⟩)
      (List.mem_ofFn.mpr ⟨b, rfl⟩) hab
      (by
        intro e _ hea heb
        simp [hea, heb])
    simpa [List.map_ofFn, Function.comp_def, hab,
      Ne.symm hab] using hh
  have hmul : 2 * v + (n - 2) * v = n * v := by
    calc
      2 * v + (n - 2) * v = (2 + (n - 2)) * v :=
        (Nat.add_mul 2 (n - 2) v).symm
      _ = n * v := by
        rw [Nat.add_comm, Nat.sub_add_cancel hn]
  calc
    n + (List.ofFn f).sum ≤
        n + (f a + f b + (n - 2) * v) :=
      Nat.add_le_add_left (Nat.le_trans hmono
        (Nat.le_of_eq hsum)) n
    _ ≤ 2 * v + (n - 2) * v := by omega
    _ = n * v := hmul

/-! The physical first-stage finite-word Bellman certificate. -/

/-- All original directed edges are represented exactly once.
The incoming root letter is site(root,n-1), not a new marked
or probabilistic transition. -/
theorem resetColdPhysicalBellmanAllEdges {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (x : ResetClockBankColdCarrier (q := q) ring root)
    (hm : (x.val root).mode ≠ .RESET) :
    n +
      (List.ofFn (fun e : Fin n =>
        resetColdUncappedCredit ring root
          (resetClockBankColdNext ring root hsp (.inl x) e))).sum ≤
      n * resetColdUncappedCredit ring root (.inl x) := by
  have hn : 2 ≤ n := by
    have hh : 2 * (13 * ((compileAdvice q).b + 2)) ≤ n := by
      simpa only [Compiled.bankLeaseCap] using hlarge
    omega
  have hpred :
      ring.rightNeighbor (site ring root (n - 1)) = root :=
    resetColdLastSiteIncoming ring root
  have hne : root ≠ site ring root (n - 1) := by
    exact Ne.symm (resetColdSiteShortNoReturn
      ring root (n - 1) (by omega) (by omega))
  have hpair := resetColdAllRootModesTwoPortDrift
    ring root (site ring root (n - 1))
    hsp hlarge x hpred hm
  have hother (e : Fin n)
      (ha : e ≠ root)
      (hb : e ≠ site ring root (n - 1)) :
      resetColdUncappedCredit ring root
        (resetClockBankColdNext ring root hsp (.inl x) e) ≤
      resetColdUncappedCredit ring root (.inl x) := by
    have hnotincoming : ring.rightNeighbor e ≠ root := by
      intro he
      have hsame : e = site ring root (n - 1) :=
        resetTrialNeighborInjective ring (by
          rw [hpred]
          exact he)
      exact hb hsame
    exact resetColdOtherEdgeNextLe
      ring root e hsp hlarge x ha hnotincoming
  exact resetColdTwoPortFinSum root
    (site ring root (n - 1))
    (fun e : Fin n =>
      resetColdUncappedCredit ring root
        (resetClockBankColdNext ring root hsp (.inl x) e))
    (resetColdUncappedCredit ring root (.inl x))
    hn hne hpair hother

/-- Nonterminal cold states are precisely non-RESET cold
carrier records. The renewal and absorbed sides are targets. -/
theorem resetColdUncappedBellman {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n) :
    ∀ z : ResetClockBankColdState (q := q) ring root,
      ¬ resetClockBankColdPhaseTarget ring root z →
      n + (List.ofFn (fun e : Fin n =>
        resetColdUncappedCredit ring root
          (resetClockBankColdNext ring root hsp z e))).sum ≤
      n * resetColdUncappedCredit ring root z := by
  intro z hz
  cases z with
  | inl x =>
      have hnot : (x.val root).mode ≠ .RESET := by
        intro hm
        exact hz hm
      exact resetColdPhysicalBellmanAllEdges
        ring root hsp hlarge x hnot
  | inr y =>
      exact False.elim (hz True.intro)

/-- C.3, cold first stage: exact finite-word Bellman certificate
with a large spatial ring. The potential is the uncapped
root mode/lease credit plus n times occupied active worker slots. -/
theorem resetClockBankColdCharge_holds {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n) :
    ResetClockBankColdCharge ring root hsp := by
  refine ⟨resetColdUncappedCredit ring root, ?_, ?_⟩
  · exact resetColdUncappedBellman ring root hsp hlarge
  · intro x
    exact resetColdUncappedCredit_start_le_of_large
      ring root hlarge x

end Counter
end L3




/-!
Spatial cutoff, unconditional C.3 first cost, and the
actual-cold-cut composition with the C.2 RESET renewal.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- C.3 from the actual cold carrier, with no separate numerical
large-ring or Bellman-potential hypothesis. The compiled spatial
branch supplies both through the preceding proved lemmas. -/
theorem resetClockBankColdFirstCost {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root) (T : Nat) :
    costNumerator (resetClockBankColdNext ring root hsp)
      (resetClockBankColdPhaseTarget ring root)
      (resetClockBankColdStart ring root x) T ≤
      n ^ T *
        ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
          (compileAdvice (ceilLogTwo n)).b + 7) * n) := by
  exact resetClockBankColdFirstCostOfCharge ring root hsp
    (resetClockBankColdCharge_holds ring root hsp
      (resetColdLargeAtSpatialCutoff n hsp)) x T

theorem resetClockBankColdFirstExpected {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (resetClockBankColdNext ring root hsp)
      (resetClockBankColdPhaseTarget ring root)
      (resetClockBankColdStart ring root x)
      ((((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
        (compileAdvice (ceilLogTwo n)).b + 7) * n : Nat) : Rat)) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (resetClockBankColdNext ring root hsp)
    (resetClockBankColdPhaseTarget ring root)
    ring.hn (resetClockBankColdStart ring root x)
    ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
      (compileAdvice (ceilLogTwo n)).b + 7) * n)).2
  intro T
  exact resetClockBankColdFirstCost ring root hsp x T

/-- Only genuine cold states with a non-RESET root, or the two
types of first exit, can be seen before the C.3 handoff. This
predicate is proof-only: the runtime state remains unchanged. -/
def resetClockBankColdFirstGood {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ResetClockBankColdState (q := q) ring root → Prop
  | .inl x => (x.val root).mode ≠ .RESET
  | .inr (.inl (.inr _)) => True
  | .inr (.inr _) => True
  | _ => False

theorem resetColdFirstGoodStart {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : ResetClockBankColdCarrier (q := q) ring root) :
    resetClockBankColdFirstGood ring root
      (resetClockBankColdStart ring root x) := by
  by_cases hm : (x.val root).mode = .RESET
  · change resetClockBankColdFirstGood ring root
      (resetClockBankColdLift ring root
        x.val x.property.1 x.property.2)
    rw [resetClockBankColdLiftReset ring root
      x.val x.property.1 x.property.2 hm]
    exact True.intro
  · change resetClockBankColdFirstGood ring root
      (resetClockBankColdLift ring root
        x.val x.property.1 x.property.2)
    simpa only [resetClockBankColdLift, dif_neg hm,
      resetClockBankColdFirstGood] using hm

/-- Before the first C.3 exit, the next physical service either
remains a non-RESET cold state, hands off to actual RESET recovery,
or becomes a grant/defect terminal. -/
theorem resetColdFirstGoodStep {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (z : ResetClockBankColdState (q := q) ring root)
    (_hz : resetClockBankColdFirstGood ring root z)
    (ha : ¬ resetClockBankColdPhaseTarget ring root z)
    (e : Fin n) :
    resetClockBankColdFirstGood ring root
      (resetClockBankColdNext ring root hsp z e) := by
  cases z with
  | inl x =>
      by_cases hd : ResetClockBankDefectEntry ring x.val root e
      · rw [resetClockBankColdNextDefect ring root hsp x e hd]
        exact True.intro
      · by_cases hg :
          GrantFree ((protocol q).step ring x.val e) root
        · rw [resetClockBankColdNextContinue ring root hsp x e hd hg]
          by_cases hm :
              (((protocol q).step ring x.val e) root).mode = .RESET
          · rw [resetClockBankColdLiftReset ring root
              ((protocol q).step ring x.val e)
              (resetClockBankColdCompleteStep ring root x e hd)
              hg hm]
            exact True.intro
          · simpa only [resetClockBankColdLift, dif_neg hm,
              resetClockBankColdFirstGood] using hm
        · rw [resetClockBankColdNextGrant ring root hsp x e hd hg]
          exact True.intro
  | inr y =>
      exact False.elim (ha True.intro)

/-- Every good first-phase exit is an authentic C.2 RESET recovery
cut or a grant/defect terminal, never an arbitrary live attempt. -/
theorem resetColdFirstGoodAtPhase {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : ResetClockBankColdState (q := q) ring root)
    (hz : resetClockBankColdFirstGood ring root z)
    (ha : resetClockBankColdPhaseTarget ring root z) :
    resetClockBankColdRecoveryCut ring root z ∨
      resetClockBankColdTerminal ring root z := by
  cases z with
  | inl x =>
      exact False.elim (hz ha)
  | inr y =>
      cases y with
      | inl a =>
          cases a with
          | inl run =>
              exact False.elim hz
          | inr recovery =>
              exact Or.inl True.intro
      | inr out =>
          exact Or.inr True.intro

/-- A terminal outcome is already a first-phase exit. -/
theorem resetColdTerminalIsPhaseTarget {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : ResetClockBankColdState (q := q) ring root)
    (hz : resetClockBankColdTerminal ring root z) :
    resetClockBankColdPhaseTarget ring root z := by
  cases z with
  | inl x =>
      exact False.elim hz
  | inr y =>
      exact True.intro

/-- From a genuine C.2 observer state, the cold composite has
exactly the same physical scheduler letters and stopping cost. -/
theorem resetColdRenewalCostEq {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (y : ResetClockBankRenewalState (q := q) ring root)
    (T : Nat) :
    costNumerator (resetClockBankColdNext ring root hsp)
      (resetClockBankColdTerminal ring root) (.inr y) T =
    costNumerator (resetClockBankRenewalNext ring root hsp)
      (resetClockBankRenewalTarget ring root) y T := by
  induction T generalizing y with
  | zero =>
      rfl
  | succ T ih =>
      by_cases hy : resetClockBankRenewalTarget ring root y
      · have ht :
            resetClockBankColdTerminal ring root (.inr y) := hy
        rw [costNumerator_terminal
          (resetClockBankColdNext ring root hsp)
          (resetClockBankColdTerminal ring root) (.inr y) ht (T + 1),
          costNumerator_terminal
          (resetClockBankRenewalNext ring root hsp)
          (resetClockBankRenewalTarget ring root) y hy (T + 1)]
      · have ht :
            ¬ resetClockBankColdTerminal ring root (.inr y) := hy
        rw [costNumerator_succ
          (resetClockBankColdNext ring root hsp)
          (resetClockBankColdTerminal ring root) (.inr y) ht T,
          costNumerator_succ
          (resetClockBankRenewalNext ring root hsp)
          (resetClockBankRenewalTarget ring root) y hy T]
        have hs :
            (List.ofFn (fun e : Fin n =>
              costNumerator (resetClockBankColdNext ring root hsp)
                (resetClockBankColdTerminal ring root)
                (resetClockBankColdNext ring root hsp (.inr y) e) T)).sum =
            (List.ofFn (fun e : Fin n =>
              costNumerator (resetClockBankRenewalNext ring root hsp)
                (resetClockBankRenewalTarget ring root)
                (resetClockBankRenewalNext ring root hsp y e) T)).sum := by
          apply ofFn_sum_eq
          intro e
          change
            costNumerator (resetClockBankColdNext ring root hsp)
              (resetClockBankColdTerminal ring root)
              (.inr (resetClockBankRenewalNext ring root hsp y e)) T =
            costNumerator (resetClockBankRenewalNext ring root hsp)
              (resetClockBankRenewalTarget ring root)
              (resetClockBankRenewalNext ring root hsp y e) T
          exact ih (resetClockBankRenewalNext ring root hsp y e)
        exact congrArg (fun k : Nat => n ^ (T + 1) + k) hs

/-- At a good C.3 exit, C.2 requires at most (4b+6)n expected
services; the grant and defect exits already have zero cost. -/
theorem resetColdFirstGoodPhaseCost {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (z : ResetClockBankColdState (q := q) ring root)
    (hz : resetClockBankColdFirstGood ring root z)
    (ha : resetClockBankColdPhaseTarget ring root z)
    (T : Nat) :
    costNumerator (resetClockBankColdNext ring root hsp)
      (resetClockBankColdTerminal ring root) z T ≤
      n ^ T * ((4 * (compileAdvice q).b + 6) * n) := by
  rcases resetColdFirstGoodAtPhase ring root z hz ha with hrec | hterm
  · cases z with
    | inl x =>
        exact False.elim hrec
    | inr y =>
        cases y with
        | inl a =>
            cases a with
            | inl run =>
                exact False.elim hrec
            | inr recovery =>
                rw [resetColdRenewalCostEq ring root hsp
                  (.inl (.inr recovery)) T]
                exact resetClockBankResetRenewalCost
                  ring root hsp recovery T
        | inr out =>
            exact False.elim hrec
  · rw [costNumerator_terminal
      (resetClockBankColdNext ring root hsp)
      (resetClockBankColdTerminal ring root) z hterm T]
    exact Nat.zero_le _

/-- A restricted strong-Markov reserve: the second-stage estimate
is needed only on genuine first-phase exits. Unlike a global
stage lemma, it asks for no false C.2 bound on arbitrary run scratch. -/
private theorem resetColdGoodStageReserve {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false) :
    ∀ z : ResetClockBankColdState (q := q) ring root,
      resetClockBankColdFirstGood ring root z →
      ∀ T : Nat,
      costNumerator (resetClockBankColdNext ring root hsp)
        (resetClockBankColdTerminal ring root) z T ≤
      costNumerator (resetClockBankColdNext ring root hsp)
        (resetClockBankColdPhaseTarget ring root) z T +
          n ^ T * ((4 * (compileAdvice q).b + 6) * n) := by
  intro z hz T
  induction T generalizing z with
  | zero =>
      simp only [costNumerator_zero, Nat.zero_add]
      exact Nat.zero_le _
  | succ T ih =>
      by_cases ha : resetClockBankColdPhaseTarget ring root z
      · rw [costNumerator_terminal
          (resetClockBankColdNext ring root hsp)
          (resetClockBankColdPhaseTarget ring root) z ha (T + 1)]
        simpa only [Nat.zero_add] using
          (resetColdFirstGoodPhaseCost ring root hsp z hz ha (T + 1))
      · have hp : ¬ resetClockBankColdTerminal ring root z := by
          intro ht
          exact ha (resetColdTerminalIsPhaseTarget ring root z ht)
        rw [costNumerator_succ
          (resetClockBankColdNext ring root hsp)
          (resetClockBankColdTerminal ring root) z hp T,
          costNumerator_succ
          (resetClockBankColdNext ring root hsp)
          (resetClockBankColdPhaseTarget ring root) z ha T]
        have hs :
            (List.ofFn (fun e : Fin n =>
              costNumerator (resetClockBankColdNext ring root hsp)
                (resetClockBankColdTerminal ring root)
                (resetClockBankColdNext ring root hsp z e) T)).sum ≤
            (List.ofFn (fun e : Fin n =>
              costNumerator (resetClockBankColdNext ring root hsp)
                (resetClockBankColdPhaseTarget ring root)
                (resetClockBankColdNext ring root hsp z e) T)).sum +
              n * (n ^ T * ((4 * (compileAdvice q).b + 6) * n)) := by
          calc
            _ ≤ (List.ofFn (fun e : Fin n =>
                costNumerator (resetClockBankColdNext ring root hsp)
                  (resetClockBankColdPhaseTarget ring root)
                  (resetClockBankColdNext ring root hsp z e) T +
                n ^ T * ((4 * (compileAdvice q).b + 6) * n))).sum :=
              ofFn_sum_le _ _ (fun e =>
                ih (resetClockBankColdNext ring root hsp z e)
                  (resetColdFirstGoodStep ring root hsp z hz ha e))
            _ = (List.ofFn (fun e : Fin n =>
                costNumerator (resetClockBankColdNext ring root hsp)
                  (resetClockBankColdPhaseTarget ring root)
                  (resetClockBankColdNext ring root hsp z e) T)).sum +
                n * (n ^ T * ((4 * (compileAdvice q).b + 6) * n)) := by
              rw [ofFn_sum_add, ofFn_sum_const]
        calc
          _ ≤ n ^ (T + 1) +
              ((List.ofFn (fun e : Fin n =>
                costNumerator (resetClockBankColdNext ring root hsp)
                  (resetClockBankColdPhaseTarget ring root)
                  (resetClockBankColdNext ring root hsp z e) T)).sum +
              n * (n ^ T * ((4 * (compileAdvice q).b + 6) * n))) :=
            Nat.add_le_add_left hs _
          _ = (n ^ (T + 1) +
              (List.ofFn (fun e : Fin n =>
                costNumerator (resetClockBankColdNext ring root hsp)
                  (resetClockBankColdPhaseTarget ring root)
                  (resetClockBankColdNext ring root hsp z e) T)).sum) +
              n ^ (T + 1) * ((4 * (compileAdvice q).b + 6) * n) := by
            rw [Nat.pow_succ]
            ac_rfl

/-- The whole stopped BANK observation begins with real cold
scratch, not a forged ResetLaunchPhysical snapshot. -/
theorem resetClockBankColdStoppedCost {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root) (T : Nat) :
    costNumerator (resetClockBankColdNext ring root hsp)
      (resetClockBankColdTerminal ring root)
      (resetClockBankColdStart ring root x) T ≤
      n ^ T *
        ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
          5 * (compileAdvice (ceilLogTwo n)).b + 13) * n) := by
  have hreserve := resetColdGoodStageReserve ring root hsp
    (resetClockBankColdStart ring root x)
    (resetColdFirstGoodStart ring root x) T
  have hfirst := resetClockBankColdFirstCost ring root hsp x T
  calc
    _ ≤ costNumerator (resetClockBankColdNext ring root hsp)
          (resetClockBankColdPhaseTarget ring root)
          (resetClockBankColdStart ring root x) T +
        n ^ T * ((4 * (compileAdvice (ceilLogTwo n)).b + 6) * n) :=
      hreserve
    _ ≤ n ^ T *
          ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
            (compileAdvice (ceilLogTwo n)).b + 7) * n) +
        n ^ T * ((4 * (compileAdvice (ceilLogTwo n)).b + 6) * n) :=
      Nat.add_le_add_right hfirst _
    _ = n ^ T *
          (((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
            (compileAdvice (ceilLogTwo n)).b + 7) * n) +
            ((4 * (compileAdvice (ceilLogTwo n)).b + 6) * n)) := by
      rw [Nat.mul_add]
    _ = n ^ T *
          ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
            5 * (compileAdvice (ceilLogTwo n)).b + 13) * n) := by
      rw [resetClockBankColdCompositionCoefficient]

/-- Stopped expected cost of the actual cold-first BANK stage,
then C.2 RESET recovery or an earlier grant/defect terminal. -/
theorem resetClockBankColdStoppedExpected {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      (resetClockBankColdNext ring root hsp)
      (resetClockBankColdTerminal ring root)
      (resetClockBankColdStart ring root x)
      ((((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
        5 * (compileAdvice (ceilLogTwo n)).b + 13) * n : Nat) : Rat)) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (resetClockBankColdNext ring root hsp)
    (resetClockBankColdTerminal ring root)
    ring.hn (resetClockBankColdStart ring root x)
    ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
      5 * (compileAdvice (ceilLogTwo n)).b + 13) * n)).2
  intro T
  exact resetClockBankColdStoppedCost ring root hsp x T

end Counter
end L3



/-!
Terminal-observer custody and export of the C.3/C.2 cold
BANK first-hit bound to the actual physical protocol step.

The defect exit remembers an
OLD-edge predicate, so its physical target uses an existential real
predecessor-edge witness; no successor incompleteness is assumed.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Meaning of each reason using only real configurations and real
protocol services. A defect is an OLD-edge event, not necessarily a
bad PACK role in the successor snapshot. -/
def resetColdPhysicalStopReason {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) (D : Config q n) :
    ResetClockBankStop → Prop
  | .clean => ResetClockBankClean ring D root
  | .grant => (D root).grant = true
  | .defect =>
      ∃ Cbefore : Config q n, ∃ e : Fin n,
        ResetClockBankDefectEntry ring Cbefore root e ∧
          D = (protocol q).step ring Cbefore e

/-- The genuine physical exit target. The third disjunct is an
existential predecessor property of D, so it is a predicate on D;
it does not assert that D itself fails Complete. -/
def resetColdPhysicalExit {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (D : Config q n) : Prop :=
  ResetClockBankClean ring D root ∨
    (∃ s : Fin n, (D s).grant = true) ∨
      ∃ Cbefore : Config q n, ∃ e : Fin n,
        ResetClockBankDefectEntry ring Cbefore root e ∧
          D = (protocol q).step ring Cbefore e

/-- Clean means a complete physical PACK interval, an ARMED
root, and zero bits/empty tokens in every digit slot. -/
theorem resetColdCleanObserverMeaning {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) (D : Config q n)
    (h : resetColdPhysicalStopReason ring root D .clean) :
    ResetClockBankClean ring D root := by
  exact h

/-- A grant-labelled exit witnesses a true grant at the root,
which in particular is a real site with an active grant. -/
theorem resetColdGrantObserverMeaning {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) (D : Config q n)
    (h : resetColdPhysicalStopReason ring root D .grant) :
    ∃ s : Fin n, (D s).grant = true := by
  exact ⟨root, h⟩

/-- Defect records genuinely come from a selected OLD supported
bad-pair/role-unstable service. Nothing here claims a persistent
bad role in the POST configuration. -/
theorem resetColdDefectObserverMeaning {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) (D : Config q n)
    (h : resetColdPhysicalStopReason ring root D .defect) :
    ∃ Cbefore : Config q n, ∃ e : Fin n,
      ResetClockBankDefectEntry ring Cbefore root e ∧
        D = (protocol q).step ring Cbefore e := by
  exact h

/-- Terminal labels are trusted only if created by an actual
one-edge observer transition. Arbitrary forged .stop nodes do not
satisfy this invariant automatically. -/
def resetColdObserverSound {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ResetClockBankColdState (q := q) ring root → Prop
  | .inr (.inr (D, reason)) =>
      resetColdPhysicalStopReason ring root D reason
  | _ => True

/-- The existing C.2 one-step stop soundness and full physical
observer identity certify all three new real stop meanings. -/
theorem resetColdRenewalServiceSound {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (a : ResetClockBankAttempt (q := q) ring root)
    (e : Fin n) (D : Config q n)
    (reason : ResetClockBankStop)
    (hservice : resetClockBankAttemptService ring root hsp a e =
      .stop D reason) :
    resetColdPhysicalStopReason ring root D reason := by
  have hmeaning := resetClockBankServiceStopSound
    ring root hsp a e D reason hservice
  have hphysical := resetClockBankServicePhysical
    ring root hsp a e
  rw [hservice] at hphysical
  change D = (protocol q).step ring
    (resetClockBankAttemptConfig ring root a) e at hphysical
  cases reason with
  | clean =>
      change ResetClockBankClean ring D root
      change ResetClockBankClean ring
        ((protocol q).step ring
          (resetClockBankAttemptConfig ring root a) e) root at hmeaning
      rw [hphysical]
      exact hmeaning
  | grant =>
      change (D root).grant = true
      change ¬ GrantFree ((protocol q).step ring
        (resetClockBankAttemptConfig ring root a) e) root at hmeaning
      rw [← hphysical] at hmeaning
      change ¬ (D root).grant = false at hmeaning
      cases hg : (D root).grant with
      | false =>
          exact False.elim (hmeaning hg)
      | true =>
          rfl
  | defect =>
      change ∃ Cbefore : Config q n, ∃ edge : Fin n,
        ResetClockBankDefectEntry ring Cbefore root edge ∧
          D = (protocol q).step ring Cbefore edge
      change ResetClockBankDefectEntry ring
        (resetClockBankAttemptConfig ring root a) root e at hmeaning
      exact ⟨resetClockBankAttemptConfig ring root a,
        e, hmeaning, hphysical⟩

/-- A real attempt, including an authentic retry, creates only
sound observer states. The stop clause is the preceding theorem. -/
theorem resetColdRenewalObserverSound {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (a : ResetClockBankAttempt (q := q) ring root)
    (e : Fin n) :
    resetColdObserverSound ring root
      (.inr (resetClockBankResultObserve ring root
        (resetClockBankAttemptService ring root hsp a e))) := by
  cases hservice : resetClockBankAttemptService
      ring root hsp a e with
  | active a' =>
      exact True.intro
  | retry seed =>
      exact True.intro
  | stop D reason =>
      exact resetColdRenewalServiceSound
        ring root hsp a e D reason hservice

/-- Every initial real cold carrier has sound observer custody. -/
theorem resetColdObserverSoundStart {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : ResetClockBankColdCarrier (q := q) ring root) :
    resetColdObserverSound ring root
      (resetClockBankColdStart ring root x) := by
  by_cases hm : (x.val root).mode = .RESET
  · change resetColdObserverSound ring root
      (resetClockBankColdLift ring root
        x.val x.property.1 x.property.2)
    rw [resetClockBankColdLiftReset ring root
      x.val x.property.1 x.property.2 hm]
    exact True.intro
  · change resetColdObserverSound ring root
      (resetClockBankColdLift ring root
        x.val x.property.1 x.property.2)
    simp only [resetClockBankColdLift, dif_neg hm,
      resetColdObserverSound]

/-- The soundness invariant survives every real selected edge.
The initial cold DCC and subsequent C.2 observer share the same
real physical transition, including direct grant and defect exits. -/
theorem resetColdObserverSoundStep {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (z : ResetClockBankColdState (q := q) ring root)
    (hz : resetColdObserverSound ring root z)
    (e : Fin n) :
    resetColdObserverSound ring root
      (resetClockBankColdNext ring root hsp z e) := by
  cases z with
  | inl x =>
      by_cases hd : ResetClockBankDefectEntry ring x.val root e
      · rw [resetClockBankColdNextDefect ring root hsp x e hd]
        change ∃ Cbefore : Config q n, ∃ edge : Fin n,
          ResetClockBankDefectEntry ring Cbefore root edge ∧
            (protocol q).step ring x.val e =
              (protocol q).step ring Cbefore edge
        exact ⟨x.val, e, hd, rfl⟩
      · by_cases hg :
          GrantFree ((protocol q).step ring x.val e) root
        · rw [resetClockBankColdNextContinue ring root hsp x e hd hg]
          by_cases hm :
              (((protocol q).step ring x.val e) root).mode = .RESET
          · rw [resetClockBankColdLiftReset ring root
              ((protocol q).step ring x.val e)
              (resetClockBankColdCompleteStep ring root x e hd)
              hg hm]
            exact True.intro
          · simp only [resetClockBankColdLift, dif_neg hm,
              resetColdObserverSound]
        · rw [resetClockBankColdNextGrant ring root hsp x e hd hg]
          change (((protocol q).step ring x.val e) root).grant = true
          change ¬ ((((protocol q).step ring x.val e) root).grant = false) at hg
          cases hv : (((protocol q).step ring x.val e) root).grant with
          | false =>
              exact False.elim (hg hv)
          | true =>
              rfl
  | inr y =>
      cases y with
      | inl a =>
          change resetColdObserverSound ring root
            (.inr (resetClockBankResultObserve ring root
              (resetClockBankAttemptService ring root hsp a e)))
          exact resetColdRenewalObserverSound ring root hsp a e
      | inr out =>
          change resetColdObserverSound ring root (.inr (.inr out))
          exact hz

/-- Every sound terminal state represents a real physical exit.
This is the exact terminal-to-real-target witness used below. -/
theorem resetColdTerminalPhysicalExit {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : ResetClockBankColdState (q := q) ring root)
    (hz : resetColdObserverSound ring root z)
    (ht : resetClockBankColdTerminal ring root z) :
    resetColdPhysicalExit ring root
      (resetClockBankColdConfig ring root z) := by
  cases z with
  | inl x =>
      exact False.elim ht
  | inr y =>
      cases y with
      | inl a =>
          exact False.elim ht
      | inr out =>
          rcases out with ⟨D, reason⟩
          cases reason with
          | clean =>
              change ResetClockBankClean ring D root at hz
              exact Or.inl hz
          | grant =>
              change (D root).grant = true at hz
              exact Or.inr (Or.inl ⟨root, hz⟩)
          | defect =>
              change ∃ Cbefore : Config q n, ∃ e : Fin n,
                ResetClockBankDefectEntry ring Cbefore root e ∧
                  D = (protocol q).step ring Cbefore e at hz
              exact Or.inr (Or.inr hz)

/-- Proof-only projection through the real physical observer,
with a stopping-time target only on actual physical configurations.
Terminal soundness is required because arbitrary forged observer
stops need not represent a physical exit. -/
theorem resetColdPhysicalCostLe {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false) :
    ∀ (z : ResetClockBankColdState (q := q) ring root),
      resetColdObserverSound ring root z →
      ∀ T : Nat,
        costNumerator ((protocol q).step ring)
          (resetColdPhysicalExit ring root)
          (resetClockBankColdConfig ring root z) T ≤
        costNumerator (resetClockBankColdNext ring root hsp)
          (resetClockBankColdTerminal ring root) z T := by
  intro z hz T
  induction T generalizing z with
  | zero =>
      exact Nat.le_refl 0
  | succ T ih =>
      by_cases ht : resetClockBankColdTerminal ring root z
      · have he := resetColdTerminalPhysicalExit ring root z hz ht
        rw [costNumerator_terminal
          ((protocol q).step ring)
          (resetColdPhysicalExit ring root)
          (resetClockBankColdConfig ring root z) he (T + 1),
          costNumerator_terminal
          (resetClockBankColdNext ring root hsp)
          (resetClockBankColdTerminal ring root) z ht (T + 1)]
        exact Nat.le_refl 0
      · by_cases he : resetColdPhysicalExit ring root
            (resetClockBankColdConfig ring root z)
        · rw [costNumerator_terminal
            ((protocol q).step ring)
            (resetColdPhysicalExit ring root)
            (resetClockBankColdConfig ring root z) he (T + 1)]
          exact Nat.zero_le _
        · rw [costNumerator_succ
            ((protocol q).step ring)
            (resetColdPhysicalExit ring root)
            (resetClockBankColdConfig ring root z) he T,
            costNumerator_succ
            (resetClockBankColdNext ring root hsp)
            (resetClockBankColdTerminal ring root) z ht T]
          have hsum :
              (List.ofFn (fun e : Fin n =>
                costNumerator ((protocol q).step ring)
                  (resetColdPhysicalExit ring root)
                  ((protocol q).step ring
                    (resetClockBankColdConfig ring root z) e) T)).sum ≤
              (List.ofFn (fun e : Fin n =>
                costNumerator (resetClockBankColdNext ring root hsp)
                  (resetClockBankColdTerminal ring root)
                  (resetClockBankColdNext ring root hsp z e) T)).sum := by
            apply ofFn_sum_le
            intro e
            have hh := ih (resetClockBankColdNext ring root hsp z e)
              (resetColdObserverSoundStep ring root hsp z hz e)
            have hp := resetClockBankColdPhysical
              ring root hsp z ht e
            rw [hp] at hh
            exact hh
          exact Nat.add_le_add_left hsum _

/-- Real protocol expected cost of reaching one of the three
physical exit predicates. The start carries only Complete/GrantFree,
not a forged ResetLaunchPhysical snapshot. -/
theorem resetColdProtocolExpected {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (C : Config (ceilLogTwo n) n)
    (hc : Complete ring C root)
    (hg : GrantFree C root) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      ((protocol (ceilLogTwo n)).step ring)
      (resetColdPhysicalExit ring root) C
      ((((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
        5 * (compileAdvice (ceilLogTwo n)).b + 13) * n : Nat) : Rat)) := by
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    ((protocol (ceilLogTwo n)).step ring)
    (resetColdPhysicalExit ring root)
    ring.hn C
    ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
      5 * (compileAdvice (ceilLogTwo n)).b + 13) * n)).2
  intro T
  have hp := resetColdPhysicalCostLe ring root hsp
    (resetClockBankColdStart ring root ⟨C, ⟨hc, hg⟩⟩)
    (resetColdObserverSoundStart ring root ⟨C, ⟨hc, hg⟩⟩) T
  rw [resetClockBankColdStartPhysical
    ring root ⟨C, ⟨hc, hg⟩⟩] at hp
  exact Nat.le_trans hp
    (resetClockBankColdStoppedCost
      ring root hsp ⟨C, ⟨hc, hg⟩⟩ T)

/-- Export for an extensionally equal physical stepper.
The caller may supply headlinePhysicalNext in a module that imports
HeadlineAssembly: its equality with Protocol.step is definitional. -/
theorem resetColdProtocolExpectedOfNext {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (physicalNext : Config (ceilLogTwo n) n → Fin n →
      Config (ceilLogTwo n) n)
    (hnext : physicalNext = (protocol (ceilLogTwo n)).step ring)
    (C : Config (ceilLogTwo n) n)
    (hc : Complete ring C root)
    (hg : GrantFree C root) :
    UniformFirstHit.ExpectedHittingTimeAtMost
      physicalNext (resetColdPhysicalExit ring root) C
      ((((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
        5 * (compileAdvice (ceilLogTwo n)).b + 13) * n : Nat) : Rat)) := by
  subst physicalNext
  exact resetColdProtocolExpected ring root hsp C hc hg

end Counter
end L3



/-!
C.4--C.5 watchdog arithmetic and the exact C.5--C.8
trial proof obligation, on the real physical BANK step.

No new protocol row.
The arithmetic below is a theorem. The real-chain success and
conditional-duration assertions are an explicitly defined Prop,
NOT a theorem. No additional assumptions are introduced.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Numerator of 1024 U_b, with the denominator kept separate.
No natural-number division or rounding is involved. -/
def resetColdWatchdogNumerator (b : Nat) : Nat :=
  1024 * (2 ^ (b + 1) + 1) *
    2 ^ (2 * b + 2) * 4 ^ (11 * b + 24)

def resetColdWatchdogDenominator (b : Nat) : Nat :=
  5 ^ (11 * b + 24)

/-- The only closed numeric comparisons used in the large base
certificate. Their operands are at most 3125 and 2187. -/
private theorem resetColdWatchdogFiveBlock :
    3 * 4 ^ 5 ≤ 5 ^ 5 := by
  decide

private theorem resetColdWatchdogThreeBlock :
    2 ^ 11 ≤ 3 ^ 7 := by
  decide

/-- The 211-exponent base is proved by factoring into 42
five-step blocks and six seven-step blocks. In particular no
large numeral comparison is sent to decide. -/
theorem resetColdWatchdogBase :
    resetColdWatchdogNumerator 17 <
      resetColdWatchdogDenominator 17 := by
  have htwo :
      2 ^ 66 ≤ 3 ^ 42 := by
    have hh := Nat.pow_le_pow_left resetColdWatchdogThreeBlock 6
    simpa only [← Nat.pow_mul] using hh
  have hfive :
      5 * 3 ^ 42 * 4 ^ 210 ≤ 5 ^ 211 := by
    calc
      5 * 3 ^ 42 * 4 ^ 210 =
          5 * (3 * 4 ^ 5) ^ 42 := by
        rw [Nat.mul_pow, ← Nat.pow_mul]
      _ ≤ 5 * (5 ^ 5) ^ 42 :=
        Nat.mul_le_mul_left 5
          (Nat.pow_le_pow_left resetColdWatchdogFiveBlock 42)
      _ = 5 ^ 211 := by
        rw [← Nat.pow_mul]
  have hnear : 2 ^ 18 + 1 ≤ 2 ^ 19 := by
    rw [show (19 : Nat) = 18 + 1 from rfl, Nat.pow_succ]
    have hp : 0 < 2 ^ 18 := Nat.two_pow_pos _
    omega
  have hnum :
      resetColdWatchdogNumerator 17 ≤ 2 ^ 67 * 4 ^ 210 := by
    change
      1024 * (2 ^ 18 + 1) * 2 ^ 36 * 4 ^ 211 ≤
        2 ^ 67 * 4 ^ 210
    calc
      1024 * (2 ^ 18 + 1) * 2 ^ 36 * 4 ^ 211 ≤
          1024 * 2 ^ 19 * 2 ^ 36 * 4 ^ 211 :=
        Nat.mul_le_mul_right (4 ^ 211)
          (Nat.mul_le_mul_right (2 ^ 36)
            (Nat.mul_le_mul_left 1024 hnear))
      _ = (2 ^ 10 * 2 ^ 19 * 2 ^ 36 * 4) *
            4 ^ 210 := by
        change
          2 ^ 10 * 2 ^ 19 * 2 ^ 36 * 4 ^ 211 =
            (2 ^ 10 * 2 ^ 19 * 2 ^ 36 * 4) * 4 ^ 210
        have hp : 4 ^ 211 = 4 ^ 210 * 4 := by
          rw [show (211 : Nat) = 210 + 1 from rfl,
            Nat.pow_succ]
        rw [hp]
      _ = 2 ^ 67 * 4 ^ 210 := by
        congr 1
  have hstrict :
      2 ^ 67 * 4 ^ 210 <
        5 * 2 ^ 66 * 4 ^ 210 := by
    have hp : 0 < 4 ^ 210 := Nat.pow_pos (by omega)
    have hm : 2 ^ 67 < 5 * 2 ^ 66 := by
      rw [show (67 : Nat) = 66 + 1 from rfl,
        Nat.pow_succ]
      have hpositive : 0 < 2 ^ 66 := Nat.two_pow_pos _
      omega
    exact Nat.mul_lt_mul_of_pos_right hm hp
  calc
    resetColdWatchdogNumerator 17 ≤
        2 ^ 67 * 4 ^ 210 := hnum
    _ < 5 * 2 ^ 66 * 4 ^ 210 := hstrict
    _ ≤ 5 * 3 ^ 42 * 4 ^ 210 :=
      Nat.mul_le_mul_right (4 ^ 210)
        (Nat.mul_le_mul_left 5 htwo)
    _ ≤ 5 ^ 211 := hfive
    _ = resetColdWatchdogDenominator 17 := rfl

/-- The ratio of consecutive watchdog error terms is strictly
below one, because 8 * 4^11 < 5^11. This last inequality is
also obtained from the 3125-versus-3072 five-step comparison. -/
private theorem resetColdWatchdogEleven :
    8 * 4 ^ 11 < 5 ^ 11 := by
  have hp : 0 < 4 ^ 10 := Nat.pow_pos (by omega)
  have hs :
      (3 * 4 ^ 5) ^ 2 ≤ (5 ^ 5) ^ 2 :=
    Nat.pow_le_pow_left resetColdWatchdogFiveBlock 2
  calc
    8 * 4 ^ 11 = 32 * 4 ^ 10 := by
      rw [show (11 : Nat) = 10 + 1 from rfl, Nat.pow_succ]
    _ < 45 * 4 ^ 10 :=
      Nat.mul_lt_mul_of_pos_right (by decide : 32 < 45) hp
    _ = 5 * (3 * 4 ^ 5) ^ 2 := by
      rw [Nat.mul_pow, ← Nat.pow_mul]
    _ ≤ 5 * (5 ^ 5) ^ 2 :=
      Nat.mul_le_mul_left 5 hs
    _ = 5 ^ 11 := by
      rw [← Nat.pow_mul]

private theorem resetColdWatchdogRatio (b : Nat) :
    4 * (2 ^ (b + 2) + 1) * 4 ^ 11 <
      (2 ^ (b + 1) + 1) * 5 ^ 11 := by
  have hpow :
      2 ^ (b + 2) = 2 * 2 ^ (b + 1) := by
    rw [show b + 2 = (b + 1) + 1 by omega, Nat.pow_succ]
    ac_rfl
  have hcoef :
      4 * (2 ^ (b + 2) + 1) ≤
        8 * (2 ^ (b + 1) + 1) := by
    rw [hpow]
    omega
  have hpositive : 0 < 2 ^ (b + 1) + 1 := by omega
  calc
    4 * (2 ^ (b + 2) + 1) * 4 ^ 11 ≤
        (8 * (2 ^ (b + 1) + 1)) * 4 ^ 11 :=
      Nat.mul_le_mul_right (4 ^ 11) hcoef
    _ = (8 * 4 ^ 11) * (2 ^ (b + 1) + 1) := by
      ac_rfl
    _ < 5 ^ 11 * (2 ^ (b + 1) + 1) :=
      Nat.mul_lt_mul_of_pos_right
        resetColdWatchdogEleven hpositive
    _ = (2 ^ (b + 1) + 1) * 5 ^ 11 := by
      ac_rfl

/-- Exact one-step induction, with the numerator factor bounded
by the strict ratio and the denominator multiplied by 5^11. -/
private theorem resetColdWatchdogStep (b : Nat)
    (hb : resetColdWatchdogNumerator b <
      resetColdWatchdogDenominator b) :
    resetColdWatchdogNumerator (b + 1) <
      resetColdWatchdogDenominator (b + 1) := by
  have htwo :
      2 ^ (2 * (b + 1) + 2) =
        2 ^ (2 * b + 2) * 4 := by
    rw [show 2 * (b + 1) + 2 = (2 * b + 2) + 2
      by omega, Nat.pow_add]
  have hfour :
      4 ^ (11 * (b + 1) + 24) =
        4 ^ (11 * b + 24) * 4 ^ 11 := by
    rw [show 11 * (b + 1) + 24 =
      (11 * b + 24) + 11 by omega, Nat.pow_add]
  have hfive :
      5 ^ (11 * (b + 1) + 24) =
        5 ^ (11 * b + 24) * 5 ^ 11 := by
    rw [show 11 * (b + 1) + 24 =
      (11 * b + 24) + 11 by omega, Nat.pow_add]
  calc
    resetColdWatchdogNumerator (b + 1) =
        (1024 * 2 ^ (2 * b + 2) * 4 ^ (11 * b + 24)) *
          (4 * (2 ^ (b + 2) + 1) * 4 ^ 11) := by
      unfold resetColdWatchdogNumerator
      rw [htwo, hfour]
      ac_rfl
    _ ≤ (1024 * 2 ^ (2 * b + 2) * 4 ^ (11 * b + 24)) *
          ((2 ^ (b + 1) + 1) * 5 ^ 11) :=
      Nat.mul_le_mul_left _
        (Nat.le_of_lt (resetColdWatchdogRatio b))
    _ = resetColdWatchdogNumerator b * 5 ^ 11 := by
      unfold resetColdWatchdogNumerator
      ac_rfl
    _ < resetColdWatchdogDenominator b * 5 ^ 11 :=
      Nat.mul_lt_mul_of_pos_right hb (Nat.pow_pos (by omega))
    _ = resetColdWatchdogDenominator (b + 1) := by
      unfold resetColdWatchdogDenominator
      rw [hfive]

/-- Full C.4--C.5 watchdog inequality for every b >= 17.
No closed comparison involving 5^211 is evaluated by decide. -/
theorem resetColdWatchdogAll (b : Nat) (hb : 17 ≤ b) :
    resetColdWatchdogNumerator b <
      resetColdWatchdogDenominator b := by
  obtain ⟨k, hk⟩ : ∃ k : Nat, b = 17 + k :=
    ⟨b - 17, by omega⟩
  subst hk
  clear hb
  induction k with
  | zero =>
      exact resetColdWatchdogBase
  | succ k ih =>
      have hstep := resetColdWatchdogStep (17 + k) ih
      simpa only [Nat.add_succ] using hstep

/-- At q >= 80, the compiler uses s=max(2,ceilLogTwo q)
and b=s+11, so in fact b>=18. The weaker b>=17 is the
form needed for the watchdog inequality. -/
theorem resetColdWatchdogSpatialWidth (q : Nat)
    (hsp : (compileAdvice q).useSmall = false) :
    17 ≤ (compileAdvice q).b := by
  have hq : 80 ≤ q := by
    change decide (q ≤ 79) = false at hsp
    by_cases hl : q ≤ 79
    · simp [hl] at hsp
    · omega
  have hlog : 6 ≤ Nat.log2 (q - 1) :=
    (Nat.le_log2 (by omega : q - 1 ≠ 0)).2
      (by change 64 ≤ q - 1; omega)
  have hceil :
      ceilLogTwo q = Nat.log2 (q - 1) + 1 := by
    simp [ceilLogTwo, show ¬ q ≤ 1 by omega]
  change 17 ≤ max 2 (ceilLogTwo q) + 11
  rw [hceil]
  omega

/-- C.5 numeric watchdog certificate for the actual compiled
spatial branch, with no extra width assumption. -/
theorem resetColdWatchdogCompiled (q : Nat)
    (hsp : (compileAdvice q).useSmall = false) :
    1024 * (2 ^ ((compileAdvice q).b + 1) + 1) *
        2 ^ (2 * (compileAdvice q).b + 2) *
        4 ^ (11 * (compileAdvice q).b + 24) <
      5 ^ (11 * (compileAdvice q).b + 24) := by
  exact resetColdWatchdogAll (compileAdvice q).b
    (resetColdWatchdogSpatialWidth q hsp)

/-!
C.5--C.8: define the actual experiment before asserting any
probability. A trial begins at an authenticated Clean/GrantFree
cut. The waiting mode ignores unchanged Clean snapshots until
the first root-incident service. The running mode ends at the
first physical root grant, authenticated new Clean, or a selected
OLD-edge defect. Terminal outcomes are absorbing in the observer,
but the physical successor is the literal protocol step on every
nonterminal letter. Defect takes priority over a simultaneous grant,
as in the existing C.2 observer.

The complete success and duration certificate is a Prop below,
not a proved lemma. Its finite-horizon form includes unfinished
mass to avoid the false assertion of a positive success probability
at every fixed finite horizon.
-/

inductive ResetColdGenuineTrialState (q n : Nat) where
  | waiting : Config q n → ResetColdGenuineTrialState q n
  | running : Config q n → ResetColdGenuineTrialState q n
  | success : Config q n → ResetColdGenuineTrialState q n
  | failure : Config q n → ResetColdGenuineTrialState q n

def resetColdTrialConfig {n q : Nat} :
    ResetColdGenuineTrialState q n → Config q n
  | .waiting C => C
  | .running C => C
  | .success C => C
  | .failure C => C

def resetColdTrialSuccess {n q : Nat} :
    ResetColdGenuineTrialState q n → Prop
  | .success _ => True
  | _ => False

def resetColdTrialFailure {n q : Nat} :
    ResetColdGenuineTrialState q n → Prop
  | .failure _ => True
  | _ => False

def resetColdTrialActive {n q : Nat} :
    ResetColdGenuineTrialState q n → Prop
  | .waiting _ => True
  | .running _ => True
  | _ => False

def resetColdTrialTerminal {n q : Nat} :
    ResetColdGenuineTrialState q n → Prop
  | .success _ => True
  | .failure _ => True
  | _ => False

/-- One real selected edge, with no independently chosen worker
or scheduling clock. A failure after a tail is counted only when
the subsequent physical clean reset is actually reached. -/
noncomputable def resetColdTrialNext {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ResetColdGenuineTrialState q n → Fin n →
      ResetColdGenuineTrialState q n
  | .waiting C, e =>
      if ResetClockBankDefectEntry ring C root e then
        .failure ((protocol q).step ring C e)
      else if (((protocol q).step ring C e) root).grant = true then
        .success ((protocol q).step ring C e)
      else if e = root ∨ ring.rightNeighbor e = root then
        if ResetClockBankClean ring
            ((protocol q).step ring C e) root then
          .failure ((protocol q).step ring C e)
        else
          .running ((protocol q).step ring C e)
      else
        .waiting ((protocol q).step ring C e)
  | .running C, e =>
      if ResetClockBankDefectEntry ring C root e then
        .failure ((protocol q).step ring C e)
      else if (((protocol q).step ring C e) root).grant = true then
        .success ((protocol q).step ring C e)
      else if ResetClockBankClean ring
          ((protocol q).step ring C e) root then
        .failure ((protocol q).step ring C e)
      else
        .running ((protocol q).step ring C e)
  | .success C, _ => .success C
  | .failure C, _ => .failure C

/-- The observer follows exactly the physical step until its
absorbing success/failure record. -/
theorem resetColdTrialPhysicalNext {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : ResetColdGenuineTrialState q n)
    (hz : ¬ resetColdTrialTerminal z)
    (e : Fin n) :
    resetColdTrialConfig (resetColdTrialNext ring root z e) =
      (protocol q).step ring (resetColdTrialConfig z) e := by
  cases z with
  | waiting C =>
      change resetColdTrialConfig
        (resetColdTrialNext ring root (.waiting C) e) =
          (protocol q).step ring C e
      simp only [resetColdTrialNext]
      repeat' split
      all_goals rfl
  | running C =>
      change resetColdTrialConfig
        (resetColdTrialNext ring root (.running C) e) =
          (protocol q).step ring C e
      simp only [resetColdTrialNext]
      repeat' split
      all_goals rfl
  | success C =>
      exact False.elim (hz True.intro)
  | failure C =>
      exact False.elim (hz True.intro)

/-- Sum of f over all scheduler words of length T. -/
def resetColdWordSum (n : Nat) : Nat → (List (Fin n) → Nat) → Nat
  | 0, f => f []
  | T + 1, f => (List.ofFn (fun e : Fin n =>
      resetColdWordSum n T (fun w => f (e :: w)))).sum

/-- Structural recursion on a finite scheduler word. -/
noncomputable def resetColdTrialRun {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ResetColdGenuineTrialState q n → List (Fin n) →
      ResetColdGenuineTrialState q n
  | z, [] => z
  | z, e :: w =>
      resetColdTrialRun ring root (resetColdTrialNext ring root z e) w

/-- Stopped elapsed time, capped at the input word length. -/
noncomputable def resetColdTrialElapsed {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ResetColdGenuineTrialState q n → List (Fin n) → Nat
  | _, [] => 0
  | z, e :: w =>
      if resetColdTrialTerminal z then 0
      else 1 + resetColdTrialElapsed ring root
        (resetColdTrialNext ring root z e) w

/-- All masses are unnormalized integer cylinder counts with
the common denominator n^T. They count first trial outcomes
because success/failure are absorbing. -/
noncomputable def resetColdTrialSuccessMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (T : Nat) : Nat :=
  resetColdWordSum n T (fun w =>
    if resetColdTrialSuccess
        (resetColdTrialRun ring root (.waiting C) w)
    then 1 else 0)

noncomputable def resetColdTrialFailureMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (T : Nat) : Nat :=
  resetColdWordSum n T (fun w =>
    if resetColdTrialFailure
        (resetColdTrialRun ring root (.waiting C) w)
    then 1 else 0)

noncomputable def resetColdTrialActiveMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (T : Nat) : Nat :=
  resetColdWordSum n T (fun w =>
    if resetColdTrialActive
        (resetColdTrialRun ring root (.waiting C) w)
    then 1 else 0)

/-- Sum of actual stopped durations only over words that have
finished in failure by horizon T. Active paths are not treated
as failed, and success paths contribute zero. -/
noncomputable def resetColdTrialFailureCostMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (T : Nat) : Nat :=
  resetColdWordSum n T (fun w =>
    if resetColdTrialFailure
        (resetColdTrialRun ring root (.waiting C) w) then
      resetColdTrialElapsed ring root (.waiting C) w
    else 0)

/-- Exact outstanding C.5--C.8 finite-horizon obligation for all
authenticated Clean/GrantFree starts. The first conjunct states
p <= 2^(-K). The second is the lower bound
p >= (1023/1024) 2^(-K), with unresolved active paths included
as an explicit finite-horizon slack. The third is the
failure-conditioned duration bound (16b+24)n, again with
active-path slack; after almost-sure termination the slack
vanishes. A separate termination theorem is needed when
passing from these integer inequalities to rational limits.
No statement of this Prop is assumed or proved here. -/
def ResetColdGenuineTrialCertificate {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ C : Config q n,
    ResetClockBankClean ring C root →
    GrantFree C root →
    ∀ T : Nat,
      2 ^ (compileAdvice q).K *
        resetColdTrialSuccessMass ring root C T ≤ n ^ T ∧
      1023 * n ^ T ≤
        1024 * 2 ^ (compileAdvice q).K *
          (resetColdTrialSuccessMass ring root C T +
            resetColdTrialActiveMass ring root C T) ∧
      resetColdTrialFailureCostMass ring root C T ≤
        ((16 * (compileAdvice q).b + 24) * n) *
          (resetColdTrialFailureMass ring root C T +
            resetColdTrialActiveMass ring root C T)

end Counter
end L3



/-!
Negative head-invariant result for the existing C.5
real-grant trial observer. A Clean snapshot allows an inherited GRANT
at digit one. On the first outgoing root service the literal token
owner transports that grant into the root, although BANK comparison
success is false. Thus observer success does not imply K head races.

This is a genuine one-edge word, not a different stepper.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

private theorem resetColdForeignWidth :
    (compileAdvice 80).b + 2 = 20 := by
  decide +kernel

private def resetColdForeignRing : DirectedRing 20 :=
  ⟨by decide⟩

/-- All PACK roles are correct; digit bits and worker tokens are
empty, but digit one holds an inherited foreign grant. -/
private def resetColdForeignConfig : Config 80 20 :=
  fun i =>
    { Agent.blank (compileAdvice 80) with
      pack := ⟨i.val, by
        have hi := i.isLt
        simpa only [resetColdForeignWidth] using hi⟩
      mode := if i.val = 0 then .ARMED else .RESET
      grant := i.val == 1 }

private theorem resetColdForeignSiteVal (j : Nat) (hj : j < 20) :
    (site resetColdForeignRing (0 : Fin 20) j).val = j := by
  induction j with
  | zero =>
      rfl
  | succ j ih =>
      change (((site resetColdForeignRing (0 : Fin 20) j).val +
        1) % 20) = j + 1
      rw [ih (by omega)]
      exact Nat.mod_eq_of_lt hj

/-- The initial state satisfies the exact C.2 Clean predicate. -/
theorem resetColdForeignClean :
    ResetClockBankClean resetColdForeignRing
      resetColdForeignConfig (0 : Fin 20) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    have hlt : j < 20 := by
      have hw := resetColdForeignWidth
      omega
    change (site resetColdForeignRing (0 : Fin 20) j).val = j
    exact resetColdForeignSiteVal j hlt
  · rfl
  · intro j hj hb
    exact ⟨rfl, rfl⟩

theorem resetColdForeignRootFree :
    GrantFree resetColdForeignConfig (0 : Fin 20) := by
  rfl

theorem resetColdForeignDigitGrant :
    (resetColdForeignConfig (1 : Fin 20)).grant = true := by
  rfl

/-- A good OLD PACK pair makes the entire physical PACK projection
unchanged, so the selected service is not a defect entry. -/
private theorem resetColdNoDefectOfGood {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n) (C : Config q n)
    (hgood : goodPair (compileAdvice q).b
      (C e).pack (C (ring.rightNeighbor e)).pack = true) :
    ¬ ResetClockBankDefectEntry ring C root e := by
  intro hd
  rcases hd.2 with hbad | hbad
  · rw [hgood] at hbad
    cases hbad
  · have hroles :
        (fun i => (((protocol q).step ring C e) i).pack) =
          (fun i => (C i).pack) :=
      (role_step ring C e).trans
        (roleWordStep_of_good (compileAdvice q).b
          ring (fun i => (C i).pack) e hgood)
    apply hbad
    intro j hj
    exact congrFun hroles (site ring root j)

private theorem resetColdForeignOutgoingGood :
    goodPair (compileAdvice 80).b
      (resetColdForeignConfig (0 : Fin 20)).pack
      (resetColdForeignConfig
        (resetColdForeignRing.rightNeighbor (0 : Fin 20))).pack =
      true := by
  have hh := internal_good resetColdForeignRing
    resetColdForeignConfig (0 : Fin 20) 0
    resetColdForeignClean.1
    (by decide +kernel)
  change
    goodPair (compileAdvice 80).b
      (resetColdForeignConfig (0 : Fin 20)).pack
      (resetColdForeignConfig
        (resetColdForeignRing.rightNeighbor (0 : Fin 20))).pack =
      true at hh
  exact hh

private theorem resetColdForeignNoDefect :
    ¬ ResetClockBankDefectEntry resetColdForeignRing
      resetColdForeignConfig (0 : Fin 20) (0 : Fin 20) := by
  exact resetColdNoDefectOfGood resetColdForeignRing
    (0 : Fin 20) (0 : Fin 20) resetColdForeignConfig
    resetColdForeignOutgoingGood

/-- Literal owner rows: BANK does not generate a permit
(old root is ARMED, not CWAIT), but the final GRANT transport
moves old responder.grant from site one to root zero. -/
theorem resetColdForeignPairRow :
    bankSuccess
      (bankCell (resetColdForeignConfig (0 : Fin 20)) 0)
      (bankCell (resetColdForeignConfig (1 : Fin 20)) 1)
      1 (compileAdvice 80).b = false ∧
    (transition (compileAdvice 80)
      (resetColdForeignConfig (0 : Fin 20))
      (resetColdForeignConfig (1 : Fin 20))).1.grant = true ∧
    (transition (compileAdvice 80)
      (resetColdForeignConfig (0 : Fin 20))
      (resetColdForeignConfig (1 : Fin 20))).1.mode = .CSTART := by
  decide +kernel

theorem resetColdForeignPhysicalGrant :
    (((protocol 80).step resetColdForeignRing
      resetColdForeignConfig (0 : Fin 20))
      (0 : Fin 20)).grant = true := by
  change
    (transition (compileAdvice 80)
      (resetColdForeignConfig (0 : Fin 20))
      (resetColdForeignConfig (1 : Fin 20))).1.grant = true
  exact resetColdForeignPairRow.2.1

/-- One-word success; the word is [root outgoing]. -/
theorem resetColdForeignFirstWord :
    resetColdTrialRun resetColdForeignRing (0 : Fin 20)
      (.waiting resetColdForeignConfig) [(0 : Fin 20)] =
    .success ((protocol 80).step resetColdForeignRing
      resetColdForeignConfig (0 : Fin 20)) := by
  change resetColdTrialNext resetColdForeignRing (0 : Fin 20)
      (.waiting resetColdForeignConfig) (0 : Fin 20) =
    .success ((protocol 80).step resetColdForeignRing
      resetColdForeignConfig (0 : Fin 20))
  simp only [resetColdTrialNext,
    if_neg resetColdForeignNoDefect,
    if_pos resetColdForeignPhysicalGrant]

theorem resetColdForeignThreshold :
    1 < (compileAdvice 80).K := by
  change 1 < 2 * 80 + productionKappa 80
  omega

private theorem resetColdOneTermLeOfFn :
    ∀ (m : Nat) (f : Fin m → Nat) (a : Fin m),
      f a ≤ (List.ofFn f).sum := by
  intro m
  induction m with
  | zero =>
      intro f a
      exact Fin.elim0 a
  | succ m ih =>
      intro f a
      refine Fin.cases ?_ ?_ a
      · rw [List.ofFn_succ, List.sum_cons]
        omega
      · intro i
        rw [List.ofFn_succ, List.sum_cons]
        have hh := ih (fun j : Fin m => f j.succ) i
        omega

/-- At least one of the twenty equally likely first service letters
already yields observer success. -/
theorem resetColdForeignMassPositive :
    1 ≤ resetColdTrialSuccessMass resetColdForeignRing
      (0 : Fin 20) resetColdForeignConfig 1 := by
  change 1 ≤
    (List.ofFn (fun e : Fin 20 =>
      if resetColdTrialSuccess
        (resetColdTrialRun resetColdForeignRing (0 : Fin 20)
          (.waiting resetColdForeignConfig) [e])
      then 1 else 0)).sum
  have hhit :
      resetColdTrialSuccess
        (resetColdTrialRun resetColdForeignRing (0 : Fin 20)
          (.waiting resetColdForeignConfig) [(0 : Fin 20)]) := by
    rw [resetColdForeignFirstWord]
    exact True.intro
  have hh := resetColdOneTermLeOfFn 20
    (fun e : Fin 20 =>
      if resetColdTrialSuccess
        (resetColdTrialRun resetColdForeignRing (0 : Fin 20)
          (.waiting resetColdForeignConfig) [e])
      then 1 else 0) (0 : Fin 20)
  rw [if_pos hhit] at hh
  exact hh

theorem resetColdForeignPowerLarge :
    20 < 2 ^ (compileAdvice 80).K := by
  have hk : 5 ≤ (compileAdvice 80).K := by
    change 5 ≤ 2 * 80 + productionKappa 80
    omega
  have hp : (2 : Nat) ^ 5 ≤ 2 ^ (compileAdvice 80).K :=
    Nat.pow_le_pow_right (by decide) hk
  have hs : 20 < (2 : Nat) ^ 5 := by decide
  omega

/-- The named trial certificate's FIRST conjunct is already false
at horizon one, before any question about watchdog duration. -/
theorem resetColdForeignUpperFalse :
    ¬ (2 ^ (compileAdvice 80).K *
      resetColdTrialSuccessMass resetColdForeignRing
        (0 : Fin 20) resetColdForeignConfig 1 ≤ 20 ^ 1) := by
  intro hu
  have hm := resetColdForeignMassPositive
  have hp := resetColdForeignPowerLarge
  have hmul :
      2 ^ (compileAdvice 80).K ≤
        2 ^ (compileAdvice 80).K *
          resetColdTrialSuccessMass resetColdForeignRing
            (0 : Fin 20) resetColdForeignConfig 1 := by
    simpa only [Nat.mul_one] using
      (Nat.mul_le_mul_left (2 ^ (compileAdvice 80).K) hm)
  change 2 ^ (compileAdvice 80).K *
    resetColdTrialSuccessMass resetColdForeignRing
      (0 : Fin 20) resetColdForeignConfig 1 ≤ 20 at hu
  omega

/-- Explicit negation of the current all-Cartesian C.5--C.8 Prop.
No stronger head-supermartingale theorem can prove this false
conclusion without first changing the observed success event. -/
theorem resetColdForeignCertificateFalse :
    ¬ ResetColdGenuineTrialCertificate (q := 80)
      resetColdForeignRing (0 : Fin 20) := by
  intro h
  have hu := (h resetColdForeignConfig
    resetColdForeignClean resetColdForeignRootFree 1).1
  exact resetColdForeignUpperFalse hu

end Counter
end L3



/-!
Corrected PRIVATE BANK-success trial and physical head
arithmetic. The original real-grant observer remains unchanged.
The correction observes the OLD bankSuccess predicate, not a moved
GRANT token. The authenticated worker/comparator head invariant is
not assumed as an existing fact.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Precisely the OLD-pair private BANK producer at this root.
The post-responder role matches the argument of Base.baseStep. -/
def resetColdPrivateSuccessAt {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (e : Fin n) : Prop :=
  e = root ∧
    bankSuccess
      (bankCell (C e) (C e).pack.val)
      (bankCell (C (ring.rightNeighbor e))
        (C (ring.rightNeighbor e)).pack.val)
      (packNext (C e).pack.val
        (C (ring.rightNeighbor e)).pack.val
        (compileAdvice q).b)
      (compileAdvice q).b = true

theorem resetColdPrivateSuccessOutgoing {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Config q n)
    (h : resetColdPrivateSuccessAt ring root C e) :
    e = root := by
  exact h.1

/-- In the literal BANK owner, a private success requires an
OLD CWAIT root. Importing an existing grant is not success. -/
theorem resetColdPrivateSuccessRequiresCWait {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Config q n)
    (h : resetColdPrivateSuccessAt ring root C e) :
    (C root).mode = .CWAIT := by
  obtain ⟨he, hs⟩ := h
  subst e
  by_cases hm : (C root).mode = .CWAIT
  · exact hm
  · have hf :
        bankSuccess
          (bankCell (C root) (C root).pack.val)
          (bankCell (C (ring.rightNeighbor root))
            (C (ring.rightNeighbor root)).pack.val)
          (packNext (C root).pack.val
            (C (ring.rightNeighbor root)).pack.val
            (compileAdvice q).b)
          (compileAdvice q).b = false := by
      simp [bankSuccess, bankCell, hm]
    rw [hf] at hs
    cases hs

theorem resetColdPrivateCleanNotSuccess {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Config q n)
    (hc : ResetClockBankClean ring C root) :
    ¬ resetColdPrivateSuccessAt ring root C e := by
  intro hh
  have hm := resetColdPrivateSuccessRequiresCWait
    ring root e C hh
  rw [hc.2.1] at hm
  cases hm

/-- The stronger initial domain of paper lem:bank-block.
The private predicate itself only needs a root-grant-free OLD
pair, but global grant-freedom prevents initial foreign grants
and is the domain that can feed the later spatial accounting. -/
def resetColdPrivateGlobalGrantFree {n q : Nat}
    (C : Config q n) : Prop :=
  ∀ i : Fin n, (C i).grant = false

/-- The physical trial is still stopped at the next actual Clean
or selected supported defect; no grant movement is a success.
The first incident service starts the running phase. -/
noncomputable def resetColdPrivateTrialNext {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ResetColdGenuineTrialState q n → Fin n →
      ResetColdGenuineTrialState q n
  | .waiting C, e =>
      if ResetClockBankDefectEntry ring C root e then
        .failure ((protocol q).step ring C e)
      else if resetColdPrivateSuccessAt ring root C e then
        .success ((protocol q).step ring C e)
      else if e = root ∨ ring.rightNeighbor e = root then
        if ResetClockBankClean ring
            ((protocol q).step ring C e) root then
          .failure ((protocol q).step ring C e)
        else
          .running ((protocol q).step ring C e)
      else
        .waiting ((protocol q).step ring C e)
  | .running C, e =>
      if ResetClockBankDefectEntry ring C root e then
        .failure ((protocol q).step ring C e)
      else if resetColdPrivateSuccessAt ring root C e then
        .success ((protocol q).step ring C e)
      else if ResetClockBankClean ring
          ((protocol q).step ring C e) root then
        .failure ((protocol q).step ring C e)
      else
        .running ((protocol q).step ring C e)
  | .success C, _ => .success C
  | .failure C, _ => .failure C

/-- One genuine protocol service on every nonterminal letter,
with no independent counter-only or HEAD/TAIL scheduler. -/
theorem resetColdPrivateTrialPhysicalNext {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : ResetColdGenuineTrialState q n)
    (hz : ¬ resetColdTrialTerminal z)
    (e : Fin n) :
    resetColdTrialConfig (resetColdPrivateTrialNext ring root z e) =
      (protocol q).step ring (resetColdTrialConfig z) e := by
  cases z with
  | waiting C =>
      change resetColdTrialConfig
        (resetColdPrivateTrialNext ring root (.waiting C) e) =
          (protocol q).step ring C e
      simp only [resetColdPrivateTrialNext]
      repeat' split
      all_goals rfl
  | running C =>
      change resetColdTrialConfig
        (resetColdPrivateTrialNext ring root (.running C) e) =
          (protocol q).step ring C e
      simp only [resetColdPrivateTrialNext]
      repeat' split
      all_goals rfl
  | success C =>
      exact False.elim (hz True.intro)
  | failure C =>
      exact False.elim (hz True.intro)

noncomputable def resetColdPrivateTrialRun {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ResetColdGenuineTrialState q n → List (Fin n) →
      ResetColdGenuineTrialState q n
  | z, [] => z
  | z, e :: w =>
      resetColdPrivateTrialRun ring root
        (resetColdPrivateTrialNext ring root z e) w

noncomputable def resetColdPrivateTrialElapsed {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ResetColdGenuineTrialState q n → List (Fin n) → Nat
  | _, [] => 0
  | z, e :: w =>
      if resetColdTrialTerminal z then 0
      else 1 + resetColdPrivateTrialElapsed ring root
        (resetColdPrivateTrialNext ring root z e) w

noncomputable def resetColdPrivateSuccessMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (T : Nat) : Nat :=
  resetColdWordSum n T (fun w =>
    if resetColdTrialSuccess
        (resetColdPrivateTrialRun ring root (.waiting C) w)
    then 1 else 0)

noncomputable def resetColdPrivateFailureMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (T : Nat) : Nat :=
  resetColdWordSum n T (fun w =>
    if resetColdTrialFailure
        (resetColdPrivateTrialRun ring root (.waiting C) w)
    then 1 else 0)

noncomputable def resetColdPrivateActiveMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (T : Nat) : Nat :=
  resetColdWordSum n T (fun w =>
    if resetColdTrialActive
        (resetColdPrivateTrialRun ring root (.waiting C) w)
    then 1 else 0)

noncomputable def resetColdPrivateFailureCostMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (T : Nat) : Nat :=
  resetColdWordSum n T (fun w =>
    if resetColdTrialFailure
        (resetColdPrivateTrialRun ring root (.waiting C) w) then
      resetColdPrivateTrialElapsed ring root (.waiting C) w
    else 0)

/-- The same three finite-horizon rational mass requirements,
with private success and the globally grant-free paper domain.
This is an UNPROVED PROP, not an extra model assumption. -/
def ResetColdPrivateTrialCertificate {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ C : Config q n,
    ResetClockBankClean ring C root →
    resetColdPrivateGlobalGrantFree C →
    ∀ T : Nat,
      2 ^ (compileAdvice q).K *
        resetColdPrivateSuccessMass ring root C T ≤ n ^ T ∧
      1023 * n ^ T ≤
        1024 * 2 ^ (compileAdvice q).K *
          (resetColdPrivateSuccessMass ring root C T +
            resetColdPrivateActiveMass ring root C T) ∧
      resetColdPrivateFailureCostMass ring root C T ≤
        ((16 * (compileAdvice q).b + 24) * n) *
          (resetColdPrivateFailureMass ring root C T +
            resetColdPrivateActiveMass ring root C T)

/-- Candidate physical completed-head index: binary digits plus
the outstanding IR carry of weight 2^j in digit j. Its value is
proved zero at Clean. Full reachability/authentication remains
an independent BANK row induction. -/
def resetColdPrivateBitValue {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) : Nat :=
  (List.ofFn (fun j : Fin (compileAdvice q).b =>
    if (C (site ring root (j.val + 1))).bit = true
    then 2 ^ j.val else 0)).sum

def resetColdPrivateCarryValue {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) : Nat :=
  (List.ofFn (fun j : Fin (compileAdvice q).b =>
    if (C (site ring root (j.val + 1))).tok = .IR
    then 2 ^ (j.val + 1) else 0)).sum

def resetColdPrivateHeadValue {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) : Nat :=
  resetColdPrivateBitValue ring root C +
    resetColdPrivateCarryValue ring root C

private theorem resetColdPrivateZeroSum {m : Nat}
    (f : Fin m → Nat) (hf : ∀ j, f j = 0) :
    (List.ofFn f).sum = 0 := by
  calc
    (List.ofFn f).sum =
        (List.ofFn (fun _ : Fin m => 0)).sum :=
      ofFn_sum_eq _ _ hf
    _ = 0 := by simp only [ofFn_sum_const, Nat.mul_zero]

theorem resetColdPrivateBitValueClean {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : ResetClockBankClean ring C root) :
    resetColdPrivateBitValue ring root C = 0 := by
  unfold resetColdPrivateBitValue
  apply resetColdPrivateZeroSum
  intro j
  have hj : j.val + 1 ≤ (compileAdvice q).b := by
    have hh := j.isLt
    omega
  have hv := hc.2.2 (j.val + 1) (by omega) hj
  simp [hv.1]

theorem resetColdPrivateCarryValueClean {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : ResetClockBankClean ring C root) :
    resetColdPrivateCarryValue ring root C = 0 := by
  unfold resetColdPrivateCarryValue
  apply resetColdPrivateZeroSum
  intro j
  have hj : j.val + 1 ≤ (compileAdvice q).b := by
    have hh := j.isLt
    omega
  have hv := hc.2.2 (j.val + 1) (by omega) hj
  simp [hv.2]

theorem resetColdPrivateHeadValueClean {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : ResetClockBankClean ring C root) :
    resetColdPrivateHeadValue ring root C = 0 := by
  unfold resetColdPrivateHeadValue
  rw [resetColdPrivateBitValueClean ring root C hc,
    resetColdPrivateCarryValueClean ring root C hc]

/-- The actual incoming-ARMED BANK row is a tail: the root enters
RESET, rather than earning an increment from an imported token. -/
theorem resetColdPrivateIncomingArmedTail {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hpred : ring.rightNeighbor e = root)
    (hrole : (C e).pack.val = (compileAdvice q).b ∨
      (C e).pack.val = (compileAdvice q).b + 1)
    (hm : (C root).mode = .ARMED) :
    (((protocol q).step ring C e) root).mode = .RESET := by
  exact resetColdPhysicalIncomingArmed
    ring C root e hc hg hsp hpred hrole hm

/-- Proposed live 2^h capital: the pending reset after a tail is
still classified running here, so a global drift is NOT claimed. -/
def resetColdPrivatePotential {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ResetColdGenuineTrialState q n → Nat
  | .waiting C => 2 ^ resetColdPrivateHeadValue ring root C
  | .running C => 2 ^ resetColdPrivateHeadValue ring root C
  | .success _ => 2 ^ (compileAdvice q).K
  | .failure _ => 0

theorem resetColdPrivatePotentialClean {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : ResetClockBankClean ring C root) :
    resetColdPrivatePotential ring root (.waiting C) = 1 := by
  change 2 ^ resetColdPrivateHeadValue ring root C = 1
  rw [resetColdPrivateHeadValueClean ring root C hc]

/-!
A finite-word upper-mass statement follows formally from the
corresponding one-step potential drift. The required real-machine
drift hypothesis is NOT established: the observer does not latch
an incoming ARMED tail until its later Clean endpoint.
-/

private noncomputable def resetColdPrivateSuccessMassFrom {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : ResetColdGenuineTrialState q n) (T : Nat) : Nat :=
  resetColdWordSum n T (fun w =>
    if resetColdTrialSuccess
        (resetColdPrivateTrialRun ring root z w)
    then 1 else 0)

private theorem resetColdPrivateSuccessMassFromSucc {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : ResetColdGenuineTrialState q n) (T : Nat) :
    resetColdPrivateSuccessMassFrom ring root z (T + 1) =
      (List.ofFn (fun e : Fin n =>
        resetColdPrivateSuccessMassFrom ring root
          (resetColdPrivateTrialNext ring root z e) T)).sum := by
  rfl

private theorem resetColdPrivateMassFromDrift {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hdrift : ∀ z : ResetColdGenuineTrialState q n,
      (List.ofFn (fun e : Fin n =>
        resetColdPrivatePotential ring root
          (resetColdPrivateTrialNext ring root z e))).sum ≤
        n * resetColdPrivatePotential ring root z) :
    ∀ (z : ResetColdGenuineTrialState q n) (T : Nat),
      2 ^ (compileAdvice q).K *
        resetColdPrivateSuccessMassFrom ring root z T ≤
      n ^ T * resetColdPrivatePotential ring root z := by
  intro z T
  induction T generalizing z with
  | zero =>
      cases z with
      | waiting C =>
          simp [resetColdPrivateSuccessMassFrom,
            resetColdWordSum, resetColdPrivateTrialRun,
            resetColdTrialSuccess]
      | running C =>
          simp [resetColdPrivateSuccessMassFrom,
            resetColdWordSum, resetColdPrivateTrialRun,
            resetColdTrialSuccess]
      | success C =>
          simp [resetColdPrivateSuccessMassFrom,
            resetColdWordSum, resetColdPrivateTrialRun,
            resetColdTrialSuccess, resetColdPrivatePotential]
      | failure C =>
          simp [resetColdPrivateSuccessMassFrom,
            resetColdWordSum, resetColdPrivateTrialRun,
            resetColdTrialSuccess, resetColdPrivatePotential]
  | succ T ih =>
      rw [resetColdPrivateSuccessMassFromSucc]
      have hs := ofFn_sum_le
        (fun e : Fin n =>
          2 ^ (compileAdvice q).K *
            resetColdPrivateSuccessMassFrom ring root
              (resetColdPrivateTrialNext ring root z e) T)
        (fun e : Fin n =>
          n ^ T * resetColdPrivatePotential ring root
            (resetColdPrivateTrialNext ring root z e))
        (fun e => ih (resetColdPrivateTrialNext ring root z e))
      calc
        2 ^ (compileAdvice q).K *
          (List.ofFn (fun e : Fin n =>
            resetColdPrivateSuccessMassFrom ring root
              (resetColdPrivateTrialNext ring root z e) T)).sum =
          (List.ofFn (fun e : Fin n =>
            2 ^ (compileAdvice q).K *
              resetColdPrivateSuccessMassFrom ring root
                (resetColdPrivateTrialNext ring root z e) T)).sum := by
            rw [ofFn_sum_mul_left]
        _ ≤ (List.ofFn (fun e : Fin n =>
          n ^ T * resetColdPrivatePotential ring root
            (resetColdPrivateTrialNext ring root z e))).sum := hs
        _ = n ^ T * (List.ofFn (fun e : Fin n =>
          resetColdPrivatePotential ring root
            (resetColdPrivateTrialNext ring root z e))).sum := by
            rw [ofFn_sum_mul_left]
        _ ≤ n ^ T * (n * resetColdPrivatePotential ring root z) :=
          Nat.mul_le_mul_left _ (hdrift z)
        _ = n ^ (T + 1) * resetColdPrivatePotential ring root z := by
          rw [Nat.pow_succ]
          ac_rfl

/-- An honest conditional upper bound. No theorem above asserts
hdrift for the current real BANK trial. -/
theorem resetColdPrivateUpperOfDrift {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hdrift : ∀ z : ResetColdGenuineTrialState q n,
      (List.ofFn (fun e : Fin n =>
        resetColdPrivatePotential ring root
          (resetColdPrivateTrialNext ring root z e))).sum ≤
        n * resetColdPrivatePotential ring root z)
    (C : Config q n)
    (hc : ResetClockBankClean ring C root)
    (T : Nat) :
    2 ^ (compileAdvice q).K *
      resetColdPrivateSuccessMass ring root C T ≤ n ^ T := by
  have hh := resetColdPrivateMassFromDrift
    ring root hdrift (.waiting C) T
  rw [resetColdPrivatePotentialClean ring root C hc] at hh
  change 2 ^ (compileAdvice q).K *
    resetColdPrivateSuccessMass ring root C T ≤ n ^ T * 1 at hh
  simpa only [Nat.mul_one] using hh

end Counter
end L3



/-!
Physical tail-latched private BANK trial.

LIVE is the active decision/excursion phase; its Boolean marker
distinguishes an initial Clean waiting cut from an already begun
excursion. RECOVERY is a zero-capital phase after an ARMED incoming
tail or an actual root RESET; it still consumes literal physical
services until the next authenticated Clean or supported defect.
SUCCESS records OLD-pair private bankSuccess, not a moved grant.
FAILURE and SUCCESS are absorbing only in the observer.

No new physical protocol row.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

inductive ResetColdLatchedPrivateState (q n : Nat) where
  | live : Config q n → Bool → ResetColdLatchedPrivateState q n
  | recovery : Config q n → ResetColdLatchedPrivateState q n
  | success : Config q n → ResetColdLatchedPrivateState q n
  | failure : Config q n → ResetColdLatchedPrivateState q n

def resetColdLatchedPrivateConfig {n q : Nat} :
    ResetColdLatchedPrivateState q n → Config q n
  | .live C _ => C
  | .recovery C => C
  | .success C => C
  | .failure C => C

def resetColdLatchedPrivateSuccess {n q : Nat} :
    ResetColdLatchedPrivateState q n → Prop
  | .success _ => True
  | _ => False

def resetColdLatchedPrivateFailure {n q : Nat} :
    ResetColdLatchedPrivateState q n → Prop
  | .failure _ => True
  | _ => False

def resetColdLatchedPrivateTerminal {n q : Nat} :
    ResetColdLatchedPrivateState q n → Prop
  | .success _ => True
  | .failure _ => True
  | _ => False

/-- The first root-incident service starts an excursion. -/
def resetColdLatchedIncident {n : Nat}
    (ring : DirectedRing n) (root e : Fin n) : Prop :=
  e = root ∨ ring.rightNeighbor e = root

def resetColdLatchedBegun {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (started : Bool) : Prop :=
  started = true ∨ resetColdLatchedIncident ring root e

/-- The incoming ARMED tail is immediately latched. A service
leaving the root RESET also latches an aborted excursion.
No statement of regeneration or immunity from private success is
silently bundled into this Boolean phase classifier. -/
def resetColdLatchedAbort {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (e : Fin n) : Prop :=
  ((C root).mode = .ARMED ∧ e ≠ root ∧
    ring.rightNeighbor e = root) ∨
  (((protocol q).step ring C e) root).mode = .RESET

/-- The fresh Clean cut is tested before entering RECOVERY.
The recovery branch never manufactures a private success: the
required claim that the OLD observer also cannot do so prior to
Clean remains a separate physical reachability lemma. -/
noncomputable def resetColdLatchedPrivateNext {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ResetColdLatchedPrivateState q n → Fin n →
      ResetColdLatchedPrivateState q n
  | .live C started, e =>
      if ResetClockBankDefectEntry ring C root e then
        .failure ((protocol q).step ring C e)
      else if resetColdPrivateSuccessAt ring root C e then
        .success ((protocol q).step ring C e)
      else if resetColdLatchedBegun ring root e started then
        if ResetClockBankClean ring
            ((protocol q).step ring C e) root then
          .failure ((protocol q).step ring C e)
        else if resetColdLatchedAbort ring root C e then
          .recovery ((protocol q).step ring C e)
        else
          .live ((protocol q).step ring C e) true
      else if resetColdLatchedAbort ring root C e then
        .recovery ((protocol q).step ring C e)
      else
        .live ((protocol q).step ring C e) false
  | .recovery C, e =>
      if ResetClockBankDefectEntry ring C root e then
        .failure ((protocol q).step ring C e)
      else if ResetClockBankClean ring
          ((protocol q).step ring C e) root then
        .failure ((protocol q).step ring C e)
      else
        .recovery ((protocol q).step ring C e)
  | .success C, _ => .success C
  | .failure C, _ => .failure C

/-- The observer takes the exact physical scheduler letter at
every nonterminal state, including the zero-credit recovery. -/
theorem resetColdLatchedPrivatePhysicalNext {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : ResetColdLatchedPrivateState q n)
    (hz : ¬ resetColdLatchedPrivateTerminal z)
    (e : Fin n) :
    resetColdLatchedPrivateConfig
      (resetColdLatchedPrivateNext ring root z e) =
      (protocol q).step ring (resetColdLatchedPrivateConfig z) e := by
  cases z with
  | live C started =>
      change resetColdLatchedPrivateConfig
        (resetColdLatchedPrivateNext ring root (.live C started) e) =
        (protocol q).step ring C e
      simp only [resetColdLatchedPrivateNext]
      repeat' split
      all_goals rfl
  | recovery C =>
      change resetColdLatchedPrivateConfig
        (resetColdLatchedPrivateNext ring root (.recovery C) e) =
        (protocol q).step ring C e
      simp only [resetColdLatchedPrivateNext]
      repeat' split
      all_goals rfl
  | success C =>
      exact False.elim (hz True.intro)
  | failure C =>
      exact False.elim (hz True.intro)

/-- A good incoming-root ARMED service is a genuine tail: the
previously proved BANK row makes the root RESET. Since RESET
is not Clean, the new observer enters recovery on this edge,
rather than keeping a positive live-state capital. -/
theorem resetColdLatchedPrivateIncomingTail {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Config q n) (started : Bool)
    (hsp : (compileAdvice q).useSmall = false)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hno : ¬ ResetClockBankDefectEntry ring C root e)
    (hpred : ring.rightNeighbor e = root)
    (hne : e ≠ root)
    (hm : (C root).mode = .ARMED) :
    resetColdLatchedPrivateNext ring root (.live C started) e =
      .recovery ((protocol q).step ring C e) := by
  have hrole :
      (C e).pack.val = (compileAdvice q).b ∨
        (C e).pack.val = (compileAdvice q).b + 1 := by
    rcases resetColdIncomingDefectOrRole ring C root e hc hpred with
      hbad | hrole
    · exact False.elim (hno hbad)
    · exact hrole
  have hreset := resetColdPhysicalIncomingArmed
    ring C root e hc hg hsp hpred hrole hm
  have hnotclean :
      ¬ ResetClockBankClean ring
        ((protocol q).step ring C e) root := by
    intro hclean
    rw [hclean.2.1] at hreset
    cases hreset
  have hprivate : ¬ resetColdPrivateSuccessAt ring root C e := by
    intro hs
    exact hne (resetColdPrivateSuccessOutgoing ring root e C hs)
  have hbegin : resetColdLatchedBegun ring root e started :=
    Or.inr (Or.inr hpred)
  have habort : resetColdLatchedAbort ring root C e :=
    Or.inl ⟨hm, hne, hpred⟩
  simp only [resetColdLatchedPrivateNext, if_neg hno,
    if_neg hprivate, if_pos hbegin, if_neg hnotclean,
    if_pos habort]

/-- The two literal ARMED head cases are exactly the BANK rows:
empty digit-one/false bit sets bit one and CSTART;
empty digit-one/true bit clears it, creates IR and IWAIT. -/
theorem resetColdLatchedPrivateArmedSetRow
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hr : x.role = 0) (hg : x.grant = false)
    (hy : y.role = 1) (hm : x.mode = .ARMED)
    (ht : y.tok = .E) (hbit : y.bit = false)
    (hb : 1 ≤ b) :
    (bankPair x y 1 b theta).1.mode = .CSTART ∧
      (bankPair x y 1 b theta).2.bit = true ∧
      (bankPair x y 1 b theta).2.tok = .E := by
  exact resetBankArmedSetSymbolic x y b theta
    hr hg hy hm ht hbit hb

theorem resetColdLatchedPrivateArmedCarryRow
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hr : x.role = 0) (hg : x.grant = false)
    (hy : y.role = 1) (hm : x.mode = .ARMED)
    (ht : y.tok = .E) (hbit : y.bit = true)
    (hb : 1 ≤ b) :
    (bankPair x y 1 b theta).1.mode = .IWAIT ∧
      (bankPair x y 1 b theta).2.bit = false ∧
      (bankPair x y 1 b theta).2.tok = .IR := by
  exact resetBankArmedIssueSymbolic x y b theta
    hr hg hy hm ht hbit hb

/-- The incoming IR carry row preserves the represented binary
value: if the next digit was one, its bit and the carried one
are replaced by a carry with double weight. -/
theorem resetColdLatchedPrivateIRWeight (j : Nat) (bit : Bool) :
    (if bit then 2 ^ j else 0) + 2 ^ j =
      (if !bit then 2 ^ j else 0) +
        (if bit then 2 ^ (j + 1) else 0) := by
  cases bit with
  | false =>
      simp
  | true =>
      simp [Nat.pow_succ] <;> omega

/-- No late success can be generated by the OBSERVER once it is
in recovery. This does NOT yet prove the ORIGINAL observer
also had no private success on that physical recovery path. -/
def resetColdLatchedPrivateDead {n q : Nat} :
    ResetColdLatchedPrivateState q n → Prop
  | .recovery _ => True
  | .failure _ => True
  | _ => False

theorem resetColdLatchedPrivateDeadStep {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : ResetColdLatchedPrivateState q n)
    (hz : resetColdLatchedPrivateDead z)
    (e : Fin n) :
    resetColdLatchedPrivateDead
      (resetColdLatchedPrivateNext ring root z e) := by
  cases z with
  | live C started =>
      exact False.elim hz
  | recovery C =>
      simp only [resetColdLatchedPrivateNext]
      repeat' split
      all_goals exact True.intro
  | success C =>
      exact False.elim hz
  | failure C =>
      exact True.intro

noncomputable def resetColdLatchedPrivateRun {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ResetColdLatchedPrivateState q n → List (Fin n) →
      ResetColdLatchedPrivateState q n
  | z, [] => z
  | z, e :: w =>
      resetColdLatchedPrivateRun ring root
        (resetColdLatchedPrivateNext ring root z e) w

theorem resetColdLatchedPrivateDeadWord {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : ResetColdLatchedPrivateState q n)
    (hz : resetColdLatchedPrivateDead z)
    (w : List (Fin n)) :
    resetColdLatchedPrivateDead
      (resetColdLatchedPrivateRun ring root z w) := by
  induction w generalizing z with
  | nil =>
      exact hz
  | cons e tail ih =>
      exact ih (resetColdLatchedPrivateNext ring root z e)
        (resetColdLatchedPrivateDeadStep ring root z hz e)

theorem resetColdLatchedPrivateDeadNoSuccess {n q : Nat}
    (z : ResetColdLatchedPrivateState q n)
    (hz : resetColdLatchedPrivateDead z) :
    ¬ resetColdLatchedPrivateSuccess z := by
  cases z with
  | live C started =>
      exact False.elim hz
  | recovery C =>
      intro hs
      exact hs
  | success C =>
      exact False.elim hz
  | failure C =>
      intro hs
      exact hs

theorem resetColdLatchedPrivateRecoveryNoSuccess {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (w : List (Fin n)) :
    ¬ resetColdLatchedPrivateSuccess
      (resetColdLatchedPrivateRun ring root (.recovery C) w) := by
  exact resetColdLatchedPrivateDeadNoSuccess _
    (resetColdLatchedPrivateDeadWord ring root
      (.recovery C) True.intro w)

/-- Exact finite-word success count of the tail-latched observer. -/
noncomputable def resetColdLatchedPrivateSuccessMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (T : Nat) : Nat :=
  resetColdWordSum n T (fun w =>
    if resetColdLatchedPrivateSuccess
        (resetColdLatchedPrivateRun ring root (.live C false) w)
    then 1 else 0)

/-- Reachable recovery is a physical, path-dependent property.
Its required no-private-success-before-Clean theorem is
deliberately separate from the observer's syntactic absorption. -/
def ResetColdLatchedRecoverySafe {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ Czero : Config q n,
    ResetClockBankClean ring Czero root →
    resetColdPrivateGlobalGrantFree Czero →
    ∀ w : List (Fin n), ∀ C : Config q n,
      resetColdLatchedPrivateRun ring root (.live Czero false) w =
        .recovery C →
      ∀ e : Fin n, ¬ resetColdPrivateSuccessAt ring root C e

/-- Equality with the successMass is an exact additional
wordwise obligation, not a consequence of the RECOVERY constructor
alone. It is recorded without asserting it as proved. -/
def ResetColdLatchedSuccessAgreement {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ C : Config q n,
    ResetClockBankClean ring C root →
    resetColdPrivateGlobalGrantFree C →
    ∀ T : Nat,
      resetColdLatchedPrivateSuccessMass ring root C T =
        resetColdPrivateSuccessMass ring root C T

/-- Live phase: binary digits plus outstanding IR carry;
recovery and failure have zero capital and a private success has
exactly 2^K capital. This is the proposed repaired potential. -/
def resetColdLatchedPrivatePotential {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ResetColdLatchedPrivateState q n → Nat
  | .live C _ => 2 ^ resetColdPrivateHeadValue ring root C
  | .recovery _ => 0
  | .success _ => 2 ^ (compileAdvice q).K
  | .failure _ => 0

theorem resetColdLatchedPrivateInitialCapital {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : ResetClockBankClean ring C root) :
    resetColdLatchedPrivatePotential ring root (.live C false) = 1 := by
  change 2 ^ resetColdPrivateHeadValue ring root C = 1
  rw [resetColdPrivateHeadValueClean ring root C hc]

theorem resetColdLatchedPrivateRecoveryCapitalStep {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (e : Fin n) :
    resetColdLatchedPrivatePotential ring root
      (resetColdLatchedPrivateNext ring root (.recovery C) e) = 0 := by
  simp only [resetColdLatchedPrivateNext]
  repeat' split
  all_goals rfl

/-- The missing literal-bank head certificate is explicitly scoped
to live states reachable from an authenticated, globally grant-free
Clean cut. It demands that non-head services retaining LIVE preserve
h, an ARMED root-outgoing service increases h by at most one, and
any actual private-success transition has h=K. -/
def ResetColdLatchedHeadRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) : Prop :=
  ∀ Czero : Config q n,
    ResetClockBankClean ring Czero root →
    resetColdPrivateGlobalGrantFree Czero →
    ∀ (w : List (Fin n)) (C : Config q n) (started : Bool),
      resetColdLatchedPrivateRun ring root (.live Czero false) w =
        .live C started →
      (∀ (e : Fin n) (D : Config q n) (started' : Bool),
        resetColdLatchedPrivateNext ring root (.live C started) e =
          .live D started' →
        resetColdPrivateHeadValue ring root D ≤
          resetColdPrivateHeadValue ring root C +
            (if e = root ∧ (C root).mode = .ARMED then 1 else 0)) ∧
      (∀ (e : Fin n) (D : Config q n) (started' : Bool),
        resetColdLatchedPrivateNext ring root (.live C started) e =
          .live D started' →
        (e ≠ root ∨ (C root).mode ≠ .ARMED) →
        resetColdPrivateHeadValue ring root D =
          resetColdPrivateHeadValue ring root C) ∧
      (∀ (e : Fin n) (D : Config q n),
        resetColdLatchedPrivateNext ring root (.live C started) e =
          .success D →
        resetColdPrivateHeadValue ring root C =
          (compileAdvice q).K)

/-!
The remaining probability implication is arithmetic, but its
one-step premise is deliberately not asserted without the complete
reachable-worker and comparator proof. The implication
resetColdPrivateUpperOfDrift is for the OLD two-phase stepper;
we therefore prove its exact analogue for this new four-constructor
observer rather than silently changing the earlier theorem.
-/

private noncomputable def resetColdLatchedPrivateMassFrom {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : ResetColdLatchedPrivateState q n) (T : Nat) : Nat :=
  resetColdWordSum n T (fun w =>
    if resetColdLatchedPrivateSuccess
        (resetColdLatchedPrivateRun ring root z w)
    then 1 else 0)

private theorem resetColdLatchedPrivateMassFromSucc {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : ResetColdLatchedPrivateState q n) (T : Nat) :
    resetColdLatchedPrivateMassFrom ring root z (T + 1) =
      (List.ofFn (fun e : Fin n =>
        resetColdLatchedPrivateMassFrom ring root
          (resetColdLatchedPrivateNext ring root z e) T)).sum := by
  rfl

private theorem resetColdLatchedPrivateMassOfDrift {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hdrift : ∀ z : ResetColdLatchedPrivateState q n,
      (List.ofFn (fun e : Fin n =>
        resetColdLatchedPrivatePotential ring root
          (resetColdLatchedPrivateNext ring root z e))).sum ≤
        n * resetColdLatchedPrivatePotential ring root z) :
    ∀ (z : ResetColdLatchedPrivateState q n) (T : Nat),
      2 ^ (compileAdvice q).K *
        resetColdLatchedPrivateMassFrom ring root z T ≤
      n ^ T * resetColdLatchedPrivatePotential ring root z := by
  intro z T
  induction T generalizing z with
  | zero =>
      cases z with
      | live C started =>
          simp [resetColdLatchedPrivateMassFrom,
            resetColdWordSum, resetColdLatchedPrivateRun,
            resetColdLatchedPrivateSuccess]
      | recovery C =>
          simp [resetColdLatchedPrivateMassFrom,
            resetColdWordSum, resetColdLatchedPrivateRun,
            resetColdLatchedPrivateSuccess,
            resetColdLatchedPrivatePotential]
      | success C =>
          simp [resetColdLatchedPrivateMassFrom,
            resetColdWordSum, resetColdLatchedPrivateRun,
            resetColdLatchedPrivateSuccess,
            resetColdLatchedPrivatePotential]
      | failure C =>
          simp [resetColdLatchedPrivateMassFrom,
            resetColdWordSum, resetColdLatchedPrivateRun,
            resetColdLatchedPrivateSuccess,
            resetColdLatchedPrivatePotential]
  | succ T ih =>
      rw [resetColdLatchedPrivateMassFromSucc]
      have hs := ofFn_sum_le
        (fun e : Fin n =>
          2 ^ (compileAdvice q).K *
            resetColdLatchedPrivateMassFrom ring root
              (resetColdLatchedPrivateNext ring root z e) T)
        (fun e : Fin n =>
          n ^ T * resetColdLatchedPrivatePotential ring root
            (resetColdLatchedPrivateNext ring root z e))
        (fun e => ih (resetColdLatchedPrivateNext ring root z e))
      calc
        2 ^ (compileAdvice q).K *
          (List.ofFn (fun e : Fin n =>
            resetColdLatchedPrivateMassFrom ring root
              (resetColdLatchedPrivateNext ring root z e) T)).sum =
          (List.ofFn (fun e : Fin n =>
            2 ^ (compileAdvice q).K *
              resetColdLatchedPrivateMassFrom ring root
                (resetColdLatchedPrivateNext ring root z e) T)).sum := by
            rw [ofFn_sum_mul_left]
        _ ≤ (List.ofFn (fun e : Fin n =>
          n ^ T * resetColdLatchedPrivatePotential ring root
            (resetColdLatchedPrivateNext ring root z e))).sum := hs
        _ = n ^ T * (List.ofFn (fun e : Fin n =>
          resetColdLatchedPrivatePotential ring root
            (resetColdLatchedPrivateNext ring root z e))).sum := by
            rw [ofFn_sum_mul_left]
        _ ≤ n ^ T * (n * resetColdLatchedPrivatePotential ring root z) :=
          Nat.mul_le_mul_left _ (hdrift z)
        _ = n ^ (T + 1) * resetColdLatchedPrivatePotential ring root z := by
          rw [Nat.pow_succ]
          ac_rfl

/-- Conditional C.5 upper bound for the new observer only.
The real BANK row drift and success-mass agreement
are independent unsolved obligations, not theorem assumptions
quietly disguised as a physical protocol property. -/
theorem resetColdLatchedPrivateUpperOfDrift {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hdrift : ∀ z : ResetColdLatchedPrivateState q n,
      (List.ofFn (fun e : Fin n =>
        resetColdLatchedPrivatePotential ring root
          (resetColdLatchedPrivateNext ring root z e))).sum ≤
        n * resetColdLatchedPrivatePotential ring root z)
    (C : Config q n)
    (hc : ResetClockBankClean ring C root)
    (T : Nat) :
    2 ^ (compileAdvice q).K *
      resetColdLatchedPrivateSuccessMass ring root C T ≤
      n ^ T := by
  have hh := resetColdLatchedPrivateMassOfDrift
    ring root hdrift (.live C false) T
  rw [resetColdLatchedPrivateInitialCapital ring root C hc] at hh
  change 2 ^ (compileAdvice q).K *
    resetColdLatchedPrivateSuccessMass ring root C T ≤
    n ^ T * 1 at hh
  simpa only [Nat.mul_one] using hh

end Counter
end L3

/-!
Physical RESET barrier and first-head certificate.

The two full
reachability claims (recovery cannot mask a later private success,
and live success forces the numerical head K) remain open. No theorem
below asserts either of them; every step refers to the real BANK
pair or to the physical protocol.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open K2ArbitraryElimination.FiniteAccounting

/-- Incoming RESET is a literal watchdog no-op on the root mode.
The predecessor's mode and token may be completely arbitrary. -/
theorem resetColdLatchedBankIncomingReset
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : x.role ≠ 0) (hy : y.role = 0)
    (hg : y.grant = false) (hm : y.mode = .RESET) :
    (bankPair x y 0 b theta).2.mode = .RESET := by
  simp [bankPair, hx, hy, hg, hm, isWaitMode] <;>
    repeat (first | rfl | split)

/-- Outgoing RESET starts a fresh RR sweep. It cannot directly enter
CWAIT, irrespective of the old digit-one token. -/
theorem resetColdLatchedBankOutgoingReset
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hr : x.role = 0) (hg : x.grant = false)
    (hy : y.role = 1) (hm : x.mode = .RESET)
    (hb : 0 < b) :
    (bankPair x y 1 b theta).1.mode = .RWAIT := by
  simp [bankPair, hr, hg, hy, hm, hb, isWaitMode]

/-- The actual predecessor-to-root service preserves RESET when
PACK is complete, the predecessor role is supported, and the root
is grant-free. No BANK-only surrogate is substituted for step. -/
theorem resetColdLatchedPhysicalIncomingReset {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hpred : ring.rightNeighbor e = root)
    (hrole : (C e).pack.val = (compileAdvice q).b ∨
      (C e).pack.val = (compileAdvice q).b + 1)
    (hm : (C root).mode = .RESET) :
    (((protocol q).step ring C e) root).mode = .RESET := by
  have hroot : (C root).pack.val = 0 := by
    simpa only [site] using hc 0 (by omega)
  have hpost :
      packNext (C e).pack.val (C root).pack.val
        (compileAdvice q).b = 0 := by
    rcases hrole with hr | hr
    · rw [hr, hroot]
      simp [packNext]
    · rw [hr, hroot]
      simp [packNext]
  have hs : e ≠ root := by
    intro he
    subst e
    exact (resetColdRootPortDistinct ring C root hc) hpred
  have hx : (C e).pack.val ≠ 0 := by
    have hb := resetTrialCompiledWidth q
    rcases hrole with hr | hr <;> omega
  have hbank :
      (resetBankOld (C e) (C root)).2.mode = .RESET := by
    simpa only [resetBankOld, hpost, bankCell] using
      (resetColdLatchedBankIncomingReset
        (bankCell (C e) (C e).pack.val)
        (bankCell (C root) (C root).pack.val)
        (compileAdvice q).b (compileAdvice q).theta
        (by change (C e).pack.val ≠ 0; exact hx)
        (by change (C root).pack.val = 0; exact hroot)
        (by change (C root).grant = false; exact hg)
        hm)
  exact (resetColdIncomingRootModeLease
    ring C root e hs hpred hsp).1.trans hbank

/-- An outgoing root service in RESET is physically RWAIT, not
CWAIT; this is the RR launch row of the literal protocol. -/
theorem resetColdLatchedPhysicalOutgoingReset {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hm : (C root).mode = .RESET) :
    (((protocol q).step ring C root) root).mode = .RWAIT := by
  have hroot : (C root).pack.val = 0 := by
    simpa only [site] using hc 0 (by omega)
  have hone : (C (site ring root 1)).pack.val = 1 :=
    hc 1 (by have hb := resetTrialCompiledWidth q; omega)
  have hb : 0 < (compileAdvice q).b := by
    have hh := resetTrialCompiledWidth q
    omega
  have hpost :
      packNext (C root).pack.val
        (C (site ring root 1)).pack.val
        (compileAdvice q).b = 1 := by
    rw [hroot, hone]
    simp [packNext, hb]
  have hbank :
      (resetBankOld (C root)
        (C (site ring root 1))).1.mode = .RWAIT := by
    simpa only [resetBankOld, hpost, bankCell] using
      (resetColdLatchedBankOutgoingReset
        (bankCell (C root) (C root).pack.val)
        (bankCell (C (site ring root 1))
          (C (site ring root 1)).pack.val)
        (compileAdvice q).b (compileAdvice q).theta
        (by change (C root).pack.val = 0; exact hroot)
        (by change (C root).grant = false; exact hg)
        (by change (C (site ring root 1)).pack.val = 1; exact hone)
        hm hb)
  exact (resetColdOutgoingRootModeLease
    ring C root hc hsp).1.trans hbank

/-- RESET excludes the OLD bankSuccess guard without inspecting any
worker token. This is a snapshot statement, not yet a word invariant. -/
theorem resetColdLatchedResetBlocksPrivate {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Config q n)
    (hm : (C root).mode = .RESET) :
    ¬ resetColdPrivateSuccessAt ring root C e := by
  intro hs
  have hw := resetColdPrivateSuccessRequiresCWait
    ring root e C hs
  rw [hm] at hw
  cases hw

/-- After a genuine ARMED incoming tail, the *very next* OLD-pair
success guard is false, on every scheduler letter. This does not
exclude a success after a later restart. -/
theorem resetColdLatchedTailBlocksImmediateGuard {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e f : Fin n)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hpred : ring.rightNeighbor e = root)
    (hrole : (C e).pack.val = (compileAdvice q).b ∨
      (C e).pack.val = (compileAdvice q).b + 1)
    (hm : (C root).mode = .ARMED) :
    ¬ resetColdPrivateSuccessAt ring root
      ((protocol q).step ring C e) f := by
  exact resetColdLatchedResetBlocksPrivate ring root f
    ((protocol q).step ring C e)
    (resetColdPhysicalIncomingArmed ring C root e
      hc hg hsp hpred hrole hm)

/-- One more good physical service from RESET has root mode RESET
or RWAIT, regardless of which of the n edges is scheduled. This is
the short prefix of the desired tail-exclusion induction. -/
theorem resetColdLatchedPhysicalResetNextModes {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hno : ¬ ResetClockBankDefectEntry ring C root e)
    (hm : (C root).mode = .RESET) :
    (((protocol q).step ring C e) root).mode = .RESET ∨
      (((protocol q).step ring C e) root).mode = .RWAIT := by
  by_cases he : e = root
  · subst e
    exact Or.inr (resetColdLatchedPhysicalOutgoingReset
      ring C root hc hg hsp hm)
  · by_cases hpred : ring.rightNeighbor e = root
    · rcases resetColdIncomingDefectOrRole
        ring C root e hc hpred with hbad | hrole
      · exact False.elim (hno hbad)
      · exact Or.inl (resetColdLatchedPhysicalIncomingReset
          ring C root e hc hg hsp hpred hrole hm)
    · exact Or.inl
        ((resetColdNonincidentRootMode ring C root e he hpred).trans hm)

/-- Hence the next good step from a RESET root cannot leave a
private-success guard enabled, under the stated current Complete
and GrantFree hypotheses. -/
theorem resetColdLatchedPhysicalResetNextNoPrivate {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e f : Fin n)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hno : ¬ ResetClockBankDefectEntry ring C root e)
    (hm : (C root).mode = .RESET) :
    ¬ resetColdPrivateSuccessAt ring root
      ((protocol q).step ring C e) f := by
  intro hs
  have hw := resetColdPrivateSuccessRequiresCWait
    ring root f ((protocol q).step ring C e) hs
  rcases resetColdLatchedPhysicalResetNextModes
    ring C root e hc hg hsp hno hm with hreset | hwait
  · rw [hreset] at hw
    cases hw
  · rw [hwait] at hw
    cases hw

/-- Each framed digit contributes the same bit and IR weight.
This simple global principle uses the real physical snapshots. -/
theorem resetColdLatchedPrivateHeadOfDigitFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n)
    (hframe : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      D (site ring root j) = C (site ring root j)) :
    resetColdPrivateHeadValue ring root D =
      resetColdPrivateHeadValue ring root C := by
  have hbit :
      resetColdPrivateBitValue ring root D =
        resetColdPrivateBitValue ring root C := by
    unfold resetColdPrivateBitValue
    apply FiniteUniformStoppingTree.ofFn_sum_eq
    intro j
    rw [hframe (j.val + 1)
      (by omega) (by have hj := j.isLt; omega)]
  have hcarry :
      resetColdPrivateCarryValue ring root D =
        resetColdPrivateCarryValue ring root C := by
    unfold resetColdPrivateCarryValue
    apply FiniteUniformStoppingTree.ofFn_sum_eq
    intro j
    rw [hframe (j.val + 1)
      (by omega) (by have hj := j.isLt; omega)]
  unfold resetColdPrivateHeadValue
  rw [hbit, hcarry]

/-- A scheduler edge outside every digit and its predecessor
preserves h, with no assumptions about its two BANK records. -/
theorem resetColdLatchedPrivateHeadOutside {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Config q n)
    (hsource : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b → e ≠ site ring root j)
    (htarget : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      ring.rightNeighbor e ≠ site ring root j) :
    resetColdPrivateHeadValue ring root
        ((protocol q).step ring C e) =
      resetColdPrivateHeadValue ring root C := by
  apply resetColdLatchedPrivateHeadOfDigitFrame ring root
  intro j hj hjb
  exact step_frame ring C e (site ring root j)
    (Ne.symm (hsource j hj hjb))
    (Ne.symm (htarget j hj hjb))

/-- In particular an exterior incoming-root service leaves h fixed.
The root may change its mode (including ARMED to RESET), but no
active bit or carry is touched by this selected edge. -/
theorem resetColdLatchedPrivateHeadIncomingExterior {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Config q n)
    (hc : Complete ring C root)
    (hpred : ring.rightNeighbor e = root)
    (hex : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b → e ≠ site ring root j) :
    resetColdPrivateHeadValue ring root
        ((protocol q).step ring C e) =
      resetColdPrivateHeadValue ring root C := by
  apply resetColdLatchedPrivateHeadOfDigitFrame ring root
  intro j hj hjb
  exact resetColdIncomingRootDigitFrame
    ring C root e hc hpred hex j hj hjb

/-- A finite binary digit array with only the least bit set has
numerical value one. This auxiliary identity uses no large decide. -/
private theorem resetColdLatchedSingleLowBit (m : Nat) :
    (List.ofFn (fun j : Fin (m + 1) =>
      if j.val = 0 then 1 else 0)).sum = 1 := by
  simp [List.ofFn_succ, Fin.succ_ne_zero, FiniteUniformStoppingTree.ofFn_sum_const]

/-- A first digit equal to one and all higher digits zero has exact
bit value one, for the actual compiled width. -/
theorem resetColdLatchedPrivateBitSingle {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hfirst : (C (site ring root 1)).bit = true)
    (hrest : ∀ j : Nat, 2 ≤ j →
      j ≤ (compileAdvice q).b →
      (C (site ring root j)).bit = false) :
    resetColdPrivateBitValue ring root C = 1 := by
  have hb : 0 < (compileAdvice q).b := by
    have hw := resetTrialCompiledWidth q
    omega
  unfold resetColdPrivateBitValue
  calc
    (List.ofFn (fun j : Fin (compileAdvice q).b =>
      if (C (site ring root (j.val + 1))).bit = true
      then 2 ^ j.val else 0)).sum =
        (List.ofFn (fun j : Fin (compileAdvice q).b =>
          if j.val = 0 then 1 else 0)).sum := by
            apply FiniteUniformStoppingTree.ofFn_sum_eq
            intro j
            by_cases hz : j.val = 0
            · have hj : j.val + 1 = 1 := by omega
              rw [hj, hfirst]
              simp [hz]
            · have hj : 2 ≤ j.val + 1 := by omega
              have hjb : j.val + 1 ≤ (compileAdvice q).b := by
                have hi := j.isLt
                omega
              rw [hrest (j.val + 1) hj hjb]
              simp [hz]
    _ = 1 := by
      have hw :
          (compileAdvice q).b =
            ((compileAdvice q).b - 1) + 1 := by omega
      rw [hw]
      exact resetColdLatchedSingleLowBit ((compileAdvice q).b - 1)

/-- If every worker slot is empty, there is no outstanding IR
carry, irrespective of the mode at the root. -/
theorem resetColdLatchedPrivateCarryEmpty {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hempty : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      (C (site ring root j)).tok = .E) :
    resetColdPrivateCarryValue ring root C = 0 := by
  unfold resetColdPrivateCarryValue
  apply resetColdPrivateZeroSum
  intro j
  have hjb : j.val + 1 ≤ (compileAdvice q).b := by
    have hh := j.isLt
    omega
  rw [hempty (j.val + 1) (by omega) hjb]
  simp

/-- Combined bit/carry snapshot certificate for the first head. -/
theorem resetColdLatchedPrivateHeadSingle {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hfirst : (C (site ring root 1)).bit = true)
    (hrest : ∀ j : Nat, 2 ≤ j →
      j ≤ (compileAdvice q).b →
      (C (site ring root j)).bit = false)
    (hempty : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      (C (site ring root j)).tok = .E) :
    resetColdPrivateHeadValue ring root C = 1 := by
  unfold resetColdPrivateHeadValue
  rw [resetColdLatchedPrivateBitSingle
    ring root C hfirst hrest,
    resetColdLatchedPrivateCarryEmpty ring root C hempty]

/-- Physical ARMED/E/bit-zero root edge. It changes the first digit
and the root as claimed; all other digits are framed separately. -/
theorem resetColdLatchedPhysicalArmedFirstSet {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hm : (C root).mode = .ARMED)
    (ht : (C (site ring root 1)).tok = .E)
    (hbit : (C (site ring root 1)).bit = false) :
    (((protocol q).step ring C root) root).mode = .CSTART ∧
      (((protocol q).step ring C root)
        (site ring root 1)).bit = true ∧
      (((protocol q).step ring C root)
        (site ring root 1)).tok = .E := by
  have hroot : (C root).pack.val = 0 := by
    simpa only [site] using hc 0 (by omega)
  have hone : (C (site ring root 1)).pack.val = 1 :=
    hc 1 (by have hb := resetTrialCompiledWidth q; omega)
  have hb : 1 ≤ (compileAdvice q).b := by
    have hw := resetTrialCompiledWidth q
    omega
  have hpost :
      packNext (C root).pack.val
        (C (site ring root 1)).pack.val
        (compileAdvice q).b = 1 := by
    rw [hroot, hone]
    have hpositive : 0 < (compileAdvice q).b := by omega
    simp [packNext, hpositive]
  have hbank :
      (resetBankOld (C root)
        (C (site ring root 1))).1.mode = .CSTART ∧
      (resetBankOld (C root)
        (C (site ring root 1))).2.bit = true ∧
      (resetBankOld (C root)
        (C (site ring root 1))).2.tok = .E := by
    simpa only [resetBankOld, hpost, bankCell] using
      (resetColdLatchedPrivateArmedSetRow
        (bankCell (C root) (C root).pack.val)
        (bankCell (C (site ring root 1))
          (C (site ring root 1)).pack.val)
        (compileAdvice q).b (compileAdvice q).theta
        (by change (C root).pack.val = 0; exact hroot)
        (by change (C root).grant = false; exact hg)
        (by change (C (site ring root 1)).pack.val = 1; exact hone)
        hm ht hbit hb)
  have htrip := resetPhysicalEdgeBankTrip ring C root
    (resetColdRootPortDistinct ring C root hc) hsp
  have hbitPhysical :
      (((protocol q).step ring C root)
        (site ring root 1)).bit =
      (resetBankOld (C root)
        (C (site ring root 1))).2.bit := by
    exact congrArg (fun z : Mode × Bool × BTok => z.2.1)
      htrip.2
  have htokPhysical :
      (((protocol q).step ring C root)
        (site ring root 1)).tok =
      (resetBankOld (C root)
        (C (site ring root 1))).2.tok := by
    exact congrArg (fun z : Mode × Bool × BTok => z.2.2)
      htrip.2
  exact ⟨(resetColdOutgoingRootModeLease
      ring C root hc hsp).1.trans hbank.1,
    hbitPhysical.trans hbank.2.1,
    htokPhysical.trans hbank.2.2⟩

/-- The first outgoing service from a genuinely authenticated Clean
configuration gives exactly one unit of physical head value.
This is the initial CSTART/bit-one head row, not the induction for
all later carries, AL returns, and comparator rounds. -/
theorem resetColdLatchedPhysicalFirstHead {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : ResetClockBankClean ring C root)
    (hg : resetColdPrivateGlobalGrantFree C)
    (hsp : (compileAdvice q).useSmall = false) :
    (((protocol q).step ring C root) root).mode = .CSTART ∧
      resetColdPrivateHeadValue ring root
        ((protocol q).step ring C root) = 1 := by
  have hone := hc.2.2 1
    (by omega)
    (by have hb := resetTrialCompiledWidth q; omega)
  have hrow := resetColdLatchedPhysicalArmedFirstSet
    ring C root hc.1 (hg root) hsp hc.2.1
    hone.2 hone.1
  have hrest : ∀ j : Nat, 2 ≤ j →
      j ≤ (compileAdvice q).b →
      (((protocol q).step ring C root)
        (site ring root j)).bit = false := by
    intro j hj hjb
    rw [resetColdOutgoingRootOtherDigitsFrame
      ring C root hc.1 j hj hjb]
    exact (hc.2.2 j (by omega) hjb).1
  have hempty : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      (((protocol q).step ring C root)
        (site ring root j)).tok = .E := by
    intro j hj hjb
    by_cases hfirst : j = 1
    · subst j
      exact hrow.2.2
    · rw [resetColdOutgoingRootOtherDigitsFrame
        ring C root hc.1 j (by omega) hjb]
      exact (hc.2.2 j hj hjb).2
  exact ⟨hrow.1, resetColdLatchedPrivateHeadSingle
    ring root ((protocol q).step ring C root)
    hrow.2.1 hrest hempty⟩

/-- CSTART with an empty first slot launches the comparator
without changing its first digit bit. -/
theorem resetColdLatchedComparatorLaunchBitRow
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hr : x.role = 0) (hg : x.grant = false)
    (hy : y.role = 1) (hm : x.mode = .CSTART)
    (ht : y.tok = .E) (hb : 0 < b) :
    (bankPair x y 1 b theta).1.mode = .CWAIT ∧
      (bankPair x y 1 b theta).2.bit = y.bit := by
  simp [bankPair, hr, hg, hy, hm, ht, hb,
    isRetTok, isWaitMode]

end Counter
end L3
/-!
RESET/RWAIT recovery band and the exact remaining
authenticated-return boundary.

This section does NOT assert
ResetColdLatchedRecoverySafe. The physical invariant is proved
one-step, up to the first RWAIT-to-ARMED return; proving that this
return is Clean on every Clean-reachable recovery word requires a
history/suffix certificate not present in the local root/first-digit
snapshot. No unverified word is called a counterexample.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open K2ArbitraryElimination.FiniteAccounting

/-- The local mode barrier available from RESET and RWAIT. A genuine
root grant also excludes the OLD private-success guard. -/
def resetColdRecoveryBand {n q : Nat}
    (root : Fin n) (C : Config q n) : Prop :=
  (C root).grant = true ∨
    (C root).mode = .RESET ∨
      (C root).mode = .RWAIT

/-- The private success guard sees an OLD, ungranted root. -/
theorem resetColdRecoverySuccessRequiresFree {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Config q n)
    (hs : resetColdPrivateSuccessAt ring root C e) :
    (C root).grant = false := by
  obtain ⟨he, hbank⟩ := hs
  subst e
  cases hg : (C root).grant with
  | false =>
      rfl
  | true =>
      have hfalse :
          bankSuccess
            (bankCell (C root) (C root).pack.val)
            (bankCell (C (ring.rightNeighbor root))
              (C (ring.rightNeighbor root)).pack.val)
            (packNext (C root).pack.val
              (C (ring.rightNeighbor root)).pack.val
              (compileAdvice q).b)
            (compileAdvice q).b = false := by
        simp [bankSuccess, bankCell, hg]
      rw [hfalse] at hbank
      cases hbank

/-- The band is disjoint from private success, for every scheduler
letter, with no assumptions on old digit tokens or lease fields. -/
theorem resetColdRecoveryBandNoPrivate {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Config q n)
    (hband : resetColdRecoveryBand root C) :
    ¬ resetColdPrivateSuccessAt ring root C e := by
  intro hs
  have hfree := resetColdRecoverySuccessRequiresFree
    ring root e C hs
  have hwait := resetColdPrivateSuccessRequiresCWait
    ring root e C hs
  rcases hband with hgrant | hreset | hrwait
  · rw [hgrant] at hfree
    cases hfree
  · rw [hreset] at hwait
    cases hwait
  · rw [hrwait] at hwait
    cases hwait

/-- After the ARMED incoming tail the physical snapshot satisfies
the recovery band; the conclusion is not a synthetic observer mode. -/
theorem resetColdRecoveryBandAfterTail {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hpred : ring.rightNeighbor e = root)
    (hrole : (C e).pack.val = (compileAdvice q).b ∨
      (C e).pack.val = (compileAdvice q).b + 1)
    (hm : (C root).mode = .ARMED) :
    resetColdRecoveryBand root ((protocol q).step ring C e) := by
  exact Or.inr (Or.inl
    (resetColdPhysicalIncomingArmed
      ring C root e hc hg hsp hpred hrole hm))

/-- In the literal BANK owner an OLD granted source root goes to
RESET, independently of the old mode and first-digit token. -/
theorem resetColdRecoveryBankOutgoingGranted
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = true) :
    (bankPair x y 1 b theta).1.mode = .RESET := by
  simp [bankPair, hx, hy, hg, isWaitMode]

/-- Likewise an incoming edge resets an OLD granted target root. -/
theorem resetColdRecoveryBankIncomingGranted
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : x.role ≠ 0) (hy : y.role = 0)
    (hg : y.grant = true) :
    (bankPair x y 0 b theta).2.mode = .RESET := by
  simp [bankPair, hx, hy, hg, isWaitMode] <;>
    repeat' (first | rfl | split | exact Or.inl rfl | exact Or.inr rfl |
      exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | (exfalso; omega))

/-- RESET and RWAIT are the only nonreturn modes of a target root
already in RWAIT, regardless of the predecessor's scratch. -/
theorem resetColdRecoveryBankIncomingRWait
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : x.role ≠ 0) (hy : y.role = 0)
    (hm : y.mode = .RWAIT) :
    (bankPair x y 0 b theta).2.mode = .RESET ∨
      (bankPair x y 0 b theta).2.mode = .RWAIT := by
  cases hg : y.grant <;>
    by_cases hl : 1 < y.lease <;>
    simp [bankPair, hx, hy, hm, hg, hl,
      isWaitMode, isRetTok] <;>
    repeat' (first | rfl | split | exact Or.inl rfl | exact Or.inr rfl |
      exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | (exfalso; omega))

/-- The exact RWAIT outgoing alternatives are RESET (granted or
watchdog), RWAIT (tick), and ARMED (RL return). No comparator launch
is available directly from RWAIT. -/
theorem resetColdRecoveryBankOutgoingRWait
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : x.role = 0) (hy : y.role = 1)
    (hm : x.mode = .RWAIT) (hb : 1 < b) :
    (bankPair x y 1 b theta).1.mode = .RESET ∨
      (bankPair x y 1 b theta).1.mode = .RWAIT ∨
        (bankPair x y 1 b theta).1.mode = .ARMED := by
  -- Root source, responder of PACK 1 kept: the root normal form (BankPairRoot.lean).
  rw [bankPair_rootKeep x y b theta hx hy hb]
  cases hg : x.grant <;> cases ht : y.tok <;>
    by_cases hl : 1 < x.lease <;>
    simp [bankPairRootKeep, hm, hg, ht, hl, isWaitMode, isRetTok] <;>
    repeat' (first | rfl | split | exact Or.inl rfl | exact Or.inr rfl |
      exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | (exfalso; omega))

/-- The grant guard is lifted to the selected full physical root
outgoing edge, not to a hypothetical BANK-only scheduler. -/
theorem resetColdRecoveryPhysicalOutgoingGranted {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hg : (C root).grant = true) :
    (((protocol q).step ring C root) root).mode = .RESET := by
  have hroot : (C root).pack.val = 0 := by
    simpa only [site] using hc 0 (by omega)
  have hone : (C (site ring root 1)).pack.val = 1 :=
    hc 1 (by have hb := resetTrialCompiledWidth q; omega)
  have hb : 0 < (compileAdvice q).b := by
    have hw := resetTrialCompiledWidth q
    omega
  have hpost :
      packNext (C root).pack.val
        (C (site ring root 1)).pack.val
        (compileAdvice q).b = 1 := by
    rw [hroot, hone]
    simp [packNext, hb]
  have hbank :
      (resetBankOld (C root)
        (C (site ring root 1))).1.mode = .RESET := by
    simpa only [resetBankOld, hpost, bankCell] using
      (resetColdRecoveryBankOutgoingGranted
        (bankCell (C root) (C root).pack.val)
        (bankCell (C (site ring root 1))
          (C (site ring root 1)).pack.val)
        (compileAdvice q).b (compileAdvice q).theta
        (by change (C root).pack.val = 0; exact hroot)
        (by change (C (site ring root 1)).pack.val = 1; exact hone)
        (by change (C root).grant = true; exact hg))
  exact (resetColdOutgoingRootModeLease
    ring C root hc hsp).1.trans hbank

/-- Incoming-root granted watchdog, with the actual unchanged
supported PACK role on the predecessor-to-root edge. -/
theorem resetColdRecoveryPhysicalIncomingGranted {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hpred : ring.rightNeighbor e = root)
    (hrole : (C e).pack.val = (compileAdvice q).b ∨
      (C e).pack.val = (compileAdvice q).b + 1)
    (hg : (C root).grant = true) :
    (((protocol q).step ring C e) root).mode = .RESET := by
  have hroot : (C root).pack.val = 0 := by
    simpa only [site] using hc 0 (by omega)
  have hpost :
      packNext (C e).pack.val (C root).pack.val
        (compileAdvice q).b = 0 := by
    rcases hrole with hr | hr
    · rw [hr, hroot]
      simp [packNext]
    · rw [hr, hroot]
      simp [packNext]
  have hne : e ≠ root := by
    intro he
    subst e
    exact (resetColdRootPortDistinct ring C root hc) hpred
  have hx : (C e).pack.val ≠ 0 := by
    have hw := resetTrialCompiledWidth q
    rcases hrole with hr | hr <;> omega
  have hbank :
      (resetBankOld (C e) (C root)).2.mode = .RESET := by
    simpa only [resetBankOld, hpost, bankCell] using
      (resetColdRecoveryBankIncomingGranted
        (bankCell (C e) (C e).pack.val)
        (bankCell (C root) (C root).pack.val)
        (compileAdvice q).b (compileAdvice q).theta
        (by change (C e).pack.val ≠ 0; exact hx)
        (by change (C root).pack.val = 0; exact hroot)
        (by change (C root).grant = true; exact hg))
  exact (resetColdIncomingRootModeLease
    ring C root e hne hpred hsp).1.trans hbank

/-- An OLD granted root remains protected by grant or RESET after
every good physical service. Exterior edges frame its whole Agent. -/
theorem resetColdRecoveryPhysicalGrantedNext {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hno : ¬ ResetClockBankDefectEntry ring C root e)
    (hg : (C root).grant = true) :
    ((((protocol q).step ring C e) root).grant = true) ∨
      ((((protocol q).step ring C e) root).mode = .RESET) := by
  by_cases he : e = root
  · subst e
    exact Or.inr
      (resetColdRecoveryPhysicalOutgoingGranted
        ring C root hc hsp hg)
  · by_cases hpred : ring.rightNeighbor e = root
    · rcases resetColdIncomingDefectOrRole
        ring C root e hc hpred with hbad | hrole
      · exact False.elim (hno hbad)
      · exact Or.inr
          (resetColdRecoveryPhysicalIncomingGranted
            ring C root e hc hsp hpred hrole hg)
    · have hframe :
          ((protocol q).step ring C e) root = C root :=
        step_frame ring C e root (Ne.symm he) (Ne.symm hpred)
      have hpost := congrArg
        (fun a : Agent (compileAdvice q) => a.grant) hframe
      rw [hg] at hpost
      exact Or.inl hpost

/-- Actual RWAIT outgoing edge: the three literal root modes, with
no assumption that an OLD grant is absent. -/
theorem resetColdRecoveryPhysicalOutgoingRWait {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root : Fin n)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hm : (C root).mode = .RWAIT) :
    (((protocol q).step ring C root) root).mode = .RESET ∨
      (((protocol q).step ring C root) root).mode = .RWAIT ∨
        (((protocol q).step ring C root) root).mode = .ARMED := by
  have hroot : (C root).pack.val = 0 := by
    simpa only [site] using hc 0 (by omega)
  have hone : (C (site ring root 1)).pack.val = 1 :=
    hc 1 (by have hb := resetTrialCompiledWidth q; omega)
  have hb : 1 < (compileAdvice q).b :=
    resetTrialCompiledWidth q
  have hpost :
      packNext (C root).pack.val
        (C (site ring root 1)).pack.val
        (compileAdvice q).b = 1 := by
    rw [hroot, hone]
    have hbpos : 0 < (compileAdvice q).b := by omega
    simp [packNext, hbpos]
  have hbank :
      (resetBankOld (C root)
        (C (site ring root 1))).1.mode = .RESET ∨
      (resetBankOld (C root)
        (C (site ring root 1))).1.mode = .RWAIT ∨
      (resetBankOld (C root)
        (C (site ring root 1))).1.mode = .ARMED := by
    simpa only [resetBankOld, hpost, bankCell] using
      (resetColdRecoveryBankOutgoingRWait
        (bankCell (C root) (C root).pack.val)
        (bankCell (C (site ring root 1))
          (C (site ring root 1)).pack.val)
        (compileAdvice q).b (compileAdvice q).theta
        (by change (C root).pack.val = 0; exact hroot)
        (by change (C (site ring root 1)).pack.val = 1; exact hone)
        hm hb)
  have hphys := (resetColdOutgoingRootModeLease
    ring C root hc hsp).1
  rw [hphys]
  exact hbank

/-- Actual incoming RWAIT watchdog: a supported good edge gives
RESET or RWAIT, never ARMED or CWAIT. -/
theorem resetColdRecoveryPhysicalIncomingRWait {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hpred : ring.rightNeighbor e = root)
    (hrole : (C e).pack.val = (compileAdvice q).b ∨
      (C e).pack.val = (compileAdvice q).b + 1)
    (hm : (C root).mode = .RWAIT) :
    (((protocol q).step ring C e) root).mode = .RESET ∨
      (((protocol q).step ring C e) root).mode = .RWAIT := by
  have hroot : (C root).pack.val = 0 := by
    simpa only [site] using hc 0 (by omega)
  have hpost :
      packNext (C e).pack.val (C root).pack.val
        (compileAdvice q).b = 0 := by
    rcases hrole with hr | hr
    · rw [hr, hroot]
      simp [packNext]
    · rw [hr, hroot]
      simp [packNext]
  have hne : e ≠ root := by
    intro he
    subst e
    exact (resetColdRootPortDistinct ring C root hc) hpred
  have hx : (C e).pack.val ≠ 0 := by
    have hw := resetTrialCompiledWidth q
    rcases hrole with hr | hr <;> omega
  have hbank :
      (resetBankOld (C e) (C root)).2.mode = .RESET ∨
        (resetBankOld (C e) (C root)).2.mode = .RWAIT := by
    simpa only [resetBankOld, hpost, bankCell] using
      (resetColdRecoveryBankIncomingRWait
        (bankCell (C e) (C e).pack.val)
        (bankCell (C root) (C root).pack.val)
        (compileAdvice q).b (compileAdvice q).theta
        (by change (C e).pack.val ≠ 0; exact hx)
        (by change (C root).pack.val = 0; exact hroot)
        hm)
  have hphys := (resetColdIncomingRootModeLease
    ring C root e hne hpred hsp).1
  rw [hphys]
  exact hbank

/-- All good physical RWAIT services respect the RESET/RWAIT band
or return to ARMED. The outgoing case is the ONLY one which can
return ARMED. -/
theorem resetColdRecoveryPhysicalRWaitModes {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hno : ¬ ResetClockBankDefectEntry ring C root e)
    (hm : (C root).mode = .RWAIT) :
    (((protocol q).step ring C e) root).mode = .RESET ∨
      (((protocol q).step ring C e) root).mode = .RWAIT ∨
        (((protocol q).step ring C e) root).mode = .ARMED := by
  by_cases he : e = root
  · subst e
    exact resetColdRecoveryPhysicalOutgoingRWait
      ring C root hc hsp hm
  · by_cases hpred : ring.rightNeighbor e = root
    · rcases resetColdIncomingDefectOrRole
        ring C root e hc hpred with hbad | hrole
      · exact False.elim (hno hbad)
      · rcases resetColdRecoveryPhysicalIncomingRWait
          ring C root e hc hsp hpred hrole hm with hr | hw
        · exact Or.inl hr
        · exact Or.inr (Or.inl hw)
    · have hframe := resetColdNonincidentRootMode
        ring C root e he hpred
      have hpost :
          (((protocol q).step ring C e) root).mode = .RWAIT :=
        hframe.trans hm
      exact Or.inr (Or.inl hpost)

/-- This is the unconditional one-step physical recovery invariant:
the band is preserved unless a RWAIT return creates ARMED. This
theorem DOES NOT claim that the latter snapshot is Clean. -/
theorem resetColdRecoveryBandStepUnlessArmed {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hno : ¬ ResetClockBankDefectEntry ring C root e)
    (hband : resetColdRecoveryBand root C) :
    resetColdRecoveryBand root ((protocol q).step ring C e) ∨
      (((protocol q).step ring C e) root).mode = .ARMED := by
  rcases hband with hgrant | hreset | hrwait
  · rcases resetColdRecoveryPhysicalGrantedNext
      ring C root e hc hsp hno hgrant with hg | hm
    · exact Or.inl (Or.inl hg)
    · exact Or.inl (Or.inr (Or.inl hm))
  · by_cases hgrant : (C root).grant = true
    · rcases resetColdRecoveryPhysicalGrantedNext
        ring C root e hc hsp hno hgrant with hg | hm
      · exact Or.inl (Or.inl hg)
      · exact Or.inl (Or.inr (Or.inl hm))
    · have hfree : GrantFree C root := by
        cases hg : (C root).grant with
        | false =>
            exact hg
        | true =>
            exact False.elim (hgrant hg)
      rcases resetColdLatchedPhysicalResetNextModes
        ring C root e hc hfree hsp hno hreset with hm | hw
      · exact Or.inl (Or.inr (Or.inl hm))
      · exact Or.inl (Or.inr (Or.inr hw))
  · rcases resetColdRecoveryPhysicalRWaitModes
      ring C root e hc hsp hno hrwait with hm | hw | ha
    · exact Or.inl (Or.inr (Or.inl hm))
    · exact Or.inl (Or.inr (Or.inr hw))
    · exact Or.inr ha

/-- If an authenticated RR return is supplied, the local band step
extends all the way to the next physical Clean cut. The premise
is deliberately explicit, not asserted for arbitrary dirty RWAIT
snapshots, where it is false. -/
theorem resetColdRecoveryBandStepOfReturnClean {n q : Nat}
    (ring : DirectedRing n) (C : Config q n)
    (root e : Fin n)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hno : ¬ ResetClockBankDefectEntry ring C root e)
    (hband : resetColdRecoveryBand root C)
    (hreturn : (((protocol q).step ring C e) root).mode =
      .ARMED → ResetClockBankClean ring
        ((protocol q).step ring C e) root) :
    resetColdRecoveryBand root ((protocol q).step ring C e) ∨
      ResetClockBankClean ring ((protocol q).step ring C e) root := by
  rcases resetColdRecoveryBandStepUnlessArmed
      ring C root e hc hsp hno hband with hb | ha
  · exact Or.inl hb
  · exact Or.inr (hreturn ha)

end Counter
end L3

/-!
Authenticated C.2 reset-return recovery invariant.

The invariant is the disjunction of an OLD granted root, a
grant-free RESET ready to launch, and a genuine C.2 outward/return
physical sweep. The third disjunct has a global cleared-prefix or
cleared-suffix certificate, not merely an RL byte in digit one.
C.2 classifies each trial service as live, clean, grant, defect
or watchdog reset. A successful terminal service gives a real
ResetClockBankClean, so the latched observer does not continue
through a fresh ARMED state without recognizing its Clean cut.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open K2ArbitraryElimination.FiniteAccounting

/-- Authenticated reset-recovery phase at a physical snapshot.
The last alternative imports the exact C.2 physical outward/return
sweep, with suffix and prefix invariants over ALL digit slots. -/
def resetColdRecoveryAuthenticated {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) : Prop :=
  Complete ring C root ∧
    ((C root).grant = true ∨
      (GrantFree C root ∧ (C root).mode = .RESET) ∨
      (GrantFree C root ∧ ResetTrialPhysical ring C root))

/-- A complete RESET snapshot admits the authenticated invariant
regardless of the inherited workers and regardless of its grant. -/
theorem resetColdRecoveryAuthenticatedReset {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : Complete ring C root)
    (hm : (C root).mode = .RESET) :
    resetColdRecoveryAuthenticated ring root C := by
  refine ⟨hc, ?_⟩
  cases hg : (C root).grant with
  | true =>
      exact Or.inl rfl
  | false =>
      exact Or.inr (Or.inl ⟨hg, hm⟩)

/-- An authenticated recovery state cannot satisfy the OLD private
root CWAIT/CL1 success guard. In its C.2 sweep alternative the root
is genuinely RWAIT, not merely tagged with a token byte. -/
theorem resetColdRecoveryAuthenticatedNoPrivate {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Config q n)
    (h : resetColdRecoveryAuthenticated ring root C) :
    ¬ resetColdPrivateSuccessAt ring root C e := by
  rcases h.2 with hg | hreset | htrial
  · exact resetColdRecoveryBandNoPrivate ring root e C
      (Or.inl hg)
  · exact resetColdRecoveryBandNoPrivate ring root e C
      (Or.inr (Or.inl hreset.2))
  · rcases htrial.2 with hout | hret
    · obtain ⟨j, hj⟩ := hout
      exact resetColdRecoveryBandNoPrivate ring root e C
        (Or.inr (Or.inr hj.1.1))
    · obtain ⟨j, hj⟩ := hret
      exact resetColdRecoveryBandNoPrivate ring root e C
        (Or.inr (Or.inr hj.1.1))

/-- One genuine C.2 comparison stage is either still authenticated
or has reached a physical Clean cut. In particular, the success
case reuses resetClockBankRunSuccessClean and its actual terminal
RL consumption, while waitLoss is the physical RESET recovery of C.2.
No history-free assertion about an arbitrary RWAIT/CL1 snapshot
occurs here. -/
theorem resetColdRecoveryAuthenticatedPhaseStep {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Config q n)
    (hsp : (compileAdvice q).useSmall = false)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hno : ¬ ResetClockBankDefectEntry ring C root e)
    (s : ResetClockStage)
    (hs : resetClockStageAt ring C root s) :
    resetColdRecoveryAuthenticated ring root
        ((protocol q).step ring C e) ∨
      ResetClockBankClean ring
        ((protocol q).step ring C e) root := by
  have hstable :=
    resetClockBankStableOfNoDefect ring C root e hno
  have hcnew :
      Complete ring ((protocol q).step ring C e) root := by
    intro j hj
    rw [hstable j hj]
    exact hc j hj
  rcases resetClockBankOutcomeCases ring C root hsp hc hg s hs e with
    hlive | hdefect | hsuccess | hgrant | hwait
  · have ha := (resetClockBankOutcomeLiveAllowed
      ring C root hsp hc hg s hs e hlive).1
    have hp : ResetTrialPhysical ring
        ((protocol q).step ring C e) root :=
      (resetPhysicalRowClosure (q := q) ring root)
        C e hc (resetClockStageToTrial ring C root s hs) ha
    exact Or.inl
      ⟨hcnew, Or.inr (Or.inr ⟨ha.2.2.1, hp⟩)⟩
  · exact False.elim (hno hdefect.2)
  · have hterminal := resetClockBankRunSuccessClean
      ring root hsp
      (⟨C, s, hc, hg, hs⟩ : ResetClockBankRun (q := q) ring root)
      e hsuccess.1
    exact Or.inr ⟨hcnew, hterminal.1, hterminal.2⟩
  · have hnewgrant :
        (((protocol q).step ring C e) root).grant = true := by
      cases hh : (((protocol q).step ring C e) root).grant with
      | false =>
          exact False.elim (hgrant.2 hh)
      | true =>
          rfl
    exact Or.inl ⟨hcnew, Or.inl hnewgrant⟩
  · have hreset := (resetClockBankWaitLossRootReset
        ring C root e hsp hc hg s hs hwait.1).1
    exact Or.inl
      (resetColdRecoveryAuthenticatedReset
        ring root ((protocol q).step ring C e) hcnew hreset)

/-- Every nondefective real physical service either preserves
the authenticated recovery phase or reaches the next Clean. RESET
launch uses C.2 restart machinery, active RR/RL transport uses
resetPhysicalRowClosure, and the terminal return is C.2 success. -/
theorem resetColdRecoveryAuthenticatedStep {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Config q n)
    (hsp : (compileAdvice q).useSmall = false)
    (hno : ¬ ResetClockBankDefectEntry ring C root e)
    (h : resetColdRecoveryAuthenticated ring root C) :
    resetColdRecoveryAuthenticated ring root
        ((protocol q).step ring C e) ∨
      ResetClockBankClean ring
        ((protocol q).step ring C e) root := by
  rcases h with ⟨hc, hphase⟩
  have hstable :=
    resetClockBankStableOfNoDefect ring C root e hno
  have hcnew :
      Complete ring ((protocol q).step ring C e) root := by
    intro j hj
    rw [hstable j hj]
    exact hc j hj
  rcases hphase with hgrant | hready | htrial
  · rcases resetColdRecoveryPhysicalGrantedNext
        ring C root e hc hsp hno hgrant with hnewgrant | hreset
    · exact Or.inl ⟨hcnew, Or.inl hnewgrant⟩
    · exact Or.inl
        (resetColdRecoveryAuthenticatedReset ring root
          ((protocol q).step ring C e) hcnew hreset)
  · have hrestart : ResetClockBankRestartReady ring C root :=
      ⟨hc, hready.1, hready.2⟩
    cases hgrant : (((protocol q).step ring C e) root).grant with
    | true =>
        exact Or.inl ⟨hcnew, Or.inl hgrant⟩
    | false =>
        by_cases he : e = root
        · subst e
          have hlaunch := resetClockBankRestartLaunch
            ring C root hsp hrestart hgrant
          have hp : ResetTrialPhysical ring
              ((protocol q).step ring C root) root :=
            resetTrialStartOutward ring
              ((protocol q).step ring C root) root hlaunch
          exact Or.inl ⟨hcnew, Or.inr (Or.inr ⟨hgrant, hp⟩)⟩
        · have hrestartNew := resetClockBankRestartIdle
            ring C root e hsp hrestart he hno hgrant
          exact Or.inl
            ⟨hrestartNew.1,
              Or.inr (Or.inl ⟨hrestartNew.2.1,
                hrestartNew.2.2⟩)⟩
  · rcases htrial with ⟨hg, hp⟩
    rcases hp with hout | hret
    · obtain ⟨j, hj⟩ := hout
      exact resetColdRecoveryAuthenticatedPhaseStep
        ring root e C hsp hc hg hno (.outward j) hj
    · obtain ⟨j, hj⟩ := hret
      exact resetColdRecoveryAuthenticatedPhaseStep
        ring root e C hsp hc hg hno (.returning j) hj

/-- No nondefective physical ARMED incoming tail leaves the root
outside RESET, even when an OLD root grant was received. This is
the missing implication from the observer's abort predicate to
the starting state of the C.2 recovery machine. -/
theorem resetColdRecoveryAbortRootReset {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Config q n)
    (hsp : (compileAdvice q).useSmall = false)
    (hc : Complete ring C root)
    (hno : ¬ ResetClockBankDefectEntry ring C root e)
    (h : resetColdLatchedAbort ring root C e) :
    (((protocol q).step ring C e) root).mode = .RESET := by
  rcases h with ⟨hm, he, hpred⟩ | hreset
  · rcases resetColdIncomingDefectOrRole ring C root e hc hpred with
      hdefect | hrole
    · exact False.elim (hno hdefect)
    · cases hg : (C root).grant with
      | false =>
          exact resetColdPhysicalIncomingArmed
            ring C root e hc hg hsp hpred hrole hm
      | true =>
          exact resetColdRecoveryPhysicalIncomingGranted
            ring C root e hc hsp hpred hrole hg
  · exact hreset

/-- A machine-observer word either remains in a live Complete
configuration, enters authenticated recovery, or terminates. The
inductive carrier makes the C.2 return certificate available at
EVERY recovery letter, rather than only at its initial tail. -/
def resetColdRecoveryTracked {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ResetColdLatchedPrivateState q n → Prop
  | .live C _ => Complete ring C root
  | .recovery C => resetColdRecoveryAuthenticated ring root C
  | .success _ => True
  | .failure _ => True

/-- The full physical observer's single scheduler letter preserves
the authenticated carrier. An OLD supported defect stops before
requiring further physical BANK authentication; a Clean return
is classified as failure before recovery can continue. -/
theorem resetColdRecoveryTrackedStep {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (z : ResetColdLatchedPrivateState q n)
    (hz : resetColdRecoveryTracked ring root z) :
    resetColdRecoveryTracked ring root
      (resetColdLatchedPrivateNext ring root z e) := by
  cases z with
  | live C started =>
      change Complete ring C root at hz
      by_cases hd : ResetClockBankDefectEntry ring C root e
      · simp only [resetColdLatchedPrivateNext, if_pos hd]
        exact True.intro
      · have hstable :=
          resetClockBankStableOfNoDefect ring C root e hd
        have hcnew :
            Complete ring ((protocol q).step ring C e) root := by
          intro j hj
          rw [hstable j hj]
          exact hz j hj
        have hrecover
            (ha : resetColdLatchedAbort ring root C e) :
            resetColdRecoveryAuthenticated ring root
              ((protocol q).step ring C e) := by
          exact resetColdRecoveryAuthenticatedReset ring root
            ((protocol q).step ring C e) hcnew
            (resetColdRecoveryAbortRootReset
              ring root e C hsp hz hd ha)
        by_cases hs : resetColdPrivateSuccessAt ring root C e
        · simp only [resetColdLatchedPrivateNext,
            if_neg hd, if_pos hs]
          exact True.intro
        · by_cases hb : resetColdLatchedBegun ring root e started
          · by_cases hclean : ResetClockBankClean ring
                ((protocol q).step ring C e) root
            · simp only [resetColdLatchedPrivateNext,
                if_neg hd, if_neg hs, if_pos hb, if_pos hclean]
              exact True.intro
            · by_cases ha : resetColdLatchedAbort ring root C e
              · simp only [resetColdLatchedPrivateNext,
                  if_neg hd, if_neg hs, if_pos hb,
                  if_neg hclean, if_pos ha]
                exact hrecover ha
              · simp only [resetColdLatchedPrivateNext,
                  if_neg hd, if_neg hs, if_pos hb,
                  if_neg hclean, if_neg ha]
                exact hcnew
          · by_cases ha : resetColdLatchedAbort ring root C e
            · simp only [resetColdLatchedPrivateNext,
                if_neg hd, if_neg hs, if_neg hb, if_pos ha]
              exact hrecover ha
            · simp only [resetColdLatchedPrivateNext,
                if_neg hd, if_neg hs, if_neg hb, if_neg ha]
              exact hcnew
  | recovery C =>
      change resetColdRecoveryAuthenticated ring root C at hz
      by_cases hd : ResetClockBankDefectEntry ring C root e
      · simp only [resetColdLatchedPrivateNext, if_pos hd]
        exact True.intro
      · have hstep := resetColdRecoveryAuthenticatedStep
          ring root e C hsp hd hz
        by_cases hclean : ResetClockBankClean ring
            ((protocol q).step ring C e) root
        · simp only [resetColdLatchedPrivateNext,
            if_neg hd, if_pos hclean]
          exact True.intro
        · have hremain :
              resetColdRecoveryAuthenticated ring root
                ((protocol q).step ring C e) := by
            rcases hstep with ha | hc
            · exact ha
            · exact False.elim (hclean hc)
          simp only [resetColdLatchedPrivateNext,
            if_neg hd, if_neg hclean]
          exact hremain
  | success C =>
      exact True.intro
  | failure C =>
      exact True.intro

/-- Finite-word induction of the complete physical/recovery
invariant, using precisely the latched observer's actual service
letters. No extra scheduler state or ghost edge is manufactured. -/
theorem resetColdRecoveryTrackedWord {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false) :
    ∀ (z : ResetColdLatchedPrivateState q n)
      (w : List (Fin n)),
      resetColdRecoveryTracked ring root z →
        resetColdRecoveryTracked ring root
          (resetColdLatchedPrivateRun ring root z w) := by
  intro z w
  induction w generalizing z with
  | nil =>
      intro hz
      exact hz
  | cons e tail ih =>
      intro hz
      exact ih (resetColdLatchedPrivateNext ring root z e)
        (resetColdRecoveryTrackedStep ring root e hsp z hz)

/-- C.5 recovery safety for the spatial BANK compiler:
every RECOVERY snapshot reachable from Clean has an authenticated
C.2 reset phase, and therefore excludes a private CWAIT/CL1
success before the next Clean or OLD supported defect. -/
theorem resetColdLatchedRecoverySafeSpatial {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false) :
    ResetColdLatchedRecoverySafe (q := q) ring root := by
  intro Czero hc hgrant w C hw e
  have hrun := resetColdRecoveryTrackedWord ring root hsp
    (.live Czero false) w hc.1
  rw [hw] at hrun
  exact resetColdRecoveryAuthenticatedNoPrivate ring root e C hrun

end Counter
end L3

/-!
Reachable-state potential and exact two-port accounting.

The earlier authenticated
recovery proof is unchanged. We prove an exact cancellation of
the root-outgoing doubling against the incoming ARMED tail,
CONDITIONAL on the still-unproved reachable physical HeadRows.
The missing carry/comparator provenance is not silently assumed
as a theorem.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- SUCCESS from a live record requires the OLD BANK success guard;
a later grant or a physical successor token is not enough. -/
theorem resetColdLatchedSuccessRequiresOldGuard {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C D : Config q n) (started : Bool)
    (h : resetColdLatchedPrivateNext ring root
      (.live C started) e = .success D) :
    resetColdPrivateSuccessAt ring root C e := by
  by_cases hd : ResetClockBankDefectEntry ring C root e
  · simp only [resetColdLatchedPrivateNext, if_pos hd] at h
    cases h
  · by_cases hs : resetColdPrivateSuccessAt ring root C e
    · exact hs
    · simp only [resetColdLatchedPrivateNext,
        if_neg hd, if_neg hs] at h
      repeat' split at h
      all_goals cases h

/-- For an ARMED root, the incoming service immediately receives
zero latched potential: it is either FAILURE or RECOVERY, even if
the prior first digit is not empty or the root has a grant. -/
theorem resetColdLatchedIncomingArmedPotentialZero {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Config q n) (started : Bool)
    (hne : e ≠ root)
    (hpred : ring.rightNeighbor e = root)
    (hm : (C root).mode = .ARMED) :
    resetColdLatchedPrivatePotential ring root
      (resetColdLatchedPrivateNext ring root
        (.live C started) e) = 0 := by
  have hprivate : ¬ resetColdPrivateSuccessAt ring root C e := by
    intro hs
    exact hne (resetColdPrivateSuccessOutgoing ring root e C hs)
  have hbegin : resetColdLatchedBegun ring root e started :=
    Or.inr (Or.inr hpred)
  have habort : resetColdLatchedAbort ring root C e :=
    Or.inl ⟨hm, hne, hpred⟩
  by_cases hd : ResetClockBankDefectEntry ring C root e
  · simp only [resetColdLatchedPrivateNext, if_pos hd,
      resetColdLatchedPrivatePotential]
  · by_cases hclean : ResetClockBankClean ring
        ((protocol q).step ring C e) root
    · simp only [resetColdLatchedPrivateNext, if_neg hd,
        if_neg hprivate, if_pos hbegin, if_pos hclean,
        resetColdLatchedPrivatePotential]
    · simp only [resetColdLatchedPrivateNext, if_neg hd,
        if_neg hprivate, if_pos hbegin, if_neg hclean,
        if_pos habort, resetColdLatchedPrivatePotential]

/-- The second and third HeadRows clauses imply non-head capital
nonincrease, including when success absorbs at exactly 2^K. -/
private theorem resetColdLatchedPotentialOtherLe {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Config q n) (started : Bool)
    (hfixed : ∀ (f : Fin n) (D : Config q n) (s : Bool),
      resetColdLatchedPrivateNext ring root (.live C started) f =
        .live D s →
      (f ≠ root ∨ (C root).mode ≠ .ARMED) →
      resetColdPrivateHeadValue ring root D =
        resetColdPrivateHeadValue ring root C)
    (hsuccess : ∀ (f : Fin n) (D : Config q n),
      resetColdLatchedPrivateNext ring root (.live C started) f =
        .success D →
      resetColdPrivateHeadValue ring root C =
        (compileAdvice q).K)
    (hother : e ≠ root ∨ (C root).mode ≠ .ARMED) :
    resetColdLatchedPrivatePotential ring root
      (resetColdLatchedPrivateNext ring root (.live C started) e) ≤
        2 ^ resetColdPrivateHeadValue ring root C := by
  cases hnext : resetColdLatchedPrivateNext ring root
      (.live C started) e with
  | live D s =>
      have hh := hfixed e D s hnext hother
      change 2 ^ resetColdPrivateHeadValue ring root D ≤
        2 ^ resetColdPrivateHeadValue ring root C
      rw [hh]
      exact Nat.le_refl _
  | recovery D =>
      change 0 ≤ 2 ^ resetColdPrivateHeadValue ring root C
      exact Nat.zero_le _
  | failure D =>
      change 0 ≤ 2 ^ resetColdPrivateHeadValue ring root C
      exact Nat.zero_le _
  | success D =>
      have hh := hsuccess e D hnext
      change 2 ^ (compileAdvice q).K ≤
        2 ^ resetColdPrivateHeadValue ring root C
      rw [hh]
      exact Nat.le_refl _

/-- The first HeadRows clause bounds the only increment edge by
2 * 2^h. An OLD ARMED root cannot satisfy a CWAIT success guard. -/
private theorem resetColdLatchedPotentialArmedHeadLe {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (started : Bool)
    (hm : (C root).mode = .ARMED)
    (hincrease : ∀ (e : Fin n) (D : Config q n) (s : Bool),
      resetColdLatchedPrivateNext ring root (.live C started) e =
        .live D s →
      resetColdPrivateHeadValue ring root D ≤
        resetColdPrivateHeadValue ring root C +
          (if e = root ∧ (C root).mode = .ARMED then 1 else 0)) :
    resetColdLatchedPrivatePotential ring root
      (resetColdLatchedPrivateNext ring root
        (.live C started) root) ≤
      2 * (2 ^ resetColdPrivateHeadValue ring root C) := by
  cases hnext : resetColdLatchedPrivateNext ring root
      (.live C started) root with
  | live D s =>
      have hh := hincrease root D s hnext
      have hstep :
          resetColdPrivateHeadValue ring root D ≤
            resetColdPrivateHeadValue ring root C + 1 := by
        have hcond : root = root ∧ (C root).mode = .ARMED := ⟨rfl, hm⟩
        rw [if_pos hcond] at hh
        exact hh
      change 2 ^ resetColdPrivateHeadValue ring root D ≤
        2 * (2 ^ resetColdPrivateHeadValue ring root C)
      calc
        2 ^ resetColdPrivateHeadValue ring root D ≤
            2 ^ (resetColdPrivateHeadValue ring root C + 1) :=
          Nat.pow_le_pow_right (by decide) hstep
        _ = 2 * (2 ^ resetColdPrivateHeadValue ring root C) := by
          rw [Nat.pow_succ]
          omega
  | recovery D =>
      change 0 ≤ 2 * (2 ^ resetColdPrivateHeadValue ring root C)
      exact Nat.zero_le _
  | failure D =>
      change 0 ≤ 2 * (2 ^ resetColdPrivateHeadValue ring root C)
      exact Nat.zero_le _
  | success D =>
      have hs := resetColdLatchedSuccessRequiresOldGuard
        ring root root C D started hnext
      have hw := resetColdPrivateSuccessRequiresCWait
        ring root root C hs
      rw [hm] at hw
      cases hw

/-- A scheduler pair with one head service bounded by 2A and one
tail service exactly zero balances to nA. This uses distinct
actual Fin n letters and no hypothetical additional port. -/
private theorem resetColdLatchedTwoPortCapital {n : Nat}
    (a b : Fin n) (f : Fin n → Nat) (v : Nat)
    (hn : 2 ≤ n) (hab : a ≠ b)
    (hhead : f a ≤ 2 * v)
    (htail : f b = 0)
    (hother : ∀ e : Fin n, e ≠ a → e ≠ b → f e ≤ v) :
    (List.ofFn f).sum ≤ n * v := by
  have hpoint (e : Fin n) :
      f e ≤ (if e = a then f a else if e = b then f b else v) := by
    by_cases hea : e = a
    · simp [hea]
    · by_cases heb : e = b
      · subst e
        simp [Ne.symm hab]
      · simpa [hea, heb] using hother e hea heb
  have hmono := ofFn_sum_le f
    (fun e : Fin n =>
      if e = a then f a else if e = b then f b else v)
    hpoint
  have hsum :
      (List.ofFn (fun e : Fin n =>
        if e = a then f a else if e = b then f b else v)).sum =
      f a + f b + (n - 2) * v := by
    have hh := sum_two_exceptions
      (List.ofFn (fun e : Fin n => e)) a b
      (fun e : Fin n =>
        if e = a then f a else if e = b then f b else v) v
      (resetColdOfFnNodup (fun e : Fin n => e)
        Function.injective_id)
      (List.mem_ofFn.mpr ⟨a, rfl⟩)
      (List.mem_ofFn.mpr ⟨b, rfl⟩) hab
      (by
        intro e _ hea heb
        simp [hea, heb])
    simpa [List.map_ofFn, Function.comp_def, hab,
      Ne.symm hab] using hh
  have hmul : 2 * v + (n - 2) * v = n * v := by
    calc
      2 * v + (n - 2) * v = (2 + (n - 2)) * v :=
        (Nat.add_mul 2 (n - 2) v).symm
      _ = n * v := by
        rw [Nat.add_comm, Nat.sub_add_cancel hn]
  calc
    (List.ofFn f).sum ≤
        (List.ofFn (fun e : Fin n =>
          if e = a then f a else if e = b then f b else v)).sum :=
      hmono
    _ = f a + f b + (n - 2) * v := hsum
    _ ≤ 2 * v + (n - 2) * v := by
      rw [htail, Nat.add_zero]
      exact Nat.add_le_add_right hhead _
    _ = n * v := hmul

/-- Given the local HeadRows clauses, each LIVE physical snapshot
has the required one-step drift. When ARMED the root outgoing edge
may double, but its actual predecessor-to-root service contributes
zero through the latched tail. -/
private theorem resetColdLatchedLiveDriftOfHeadRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (started : Bool)
    (hc : Complete ring C root)
    (hrows :
      (∀ (e : Fin n) (D : Config q n) (s : Bool),
        resetColdLatchedPrivateNext ring root (.live C started) e =
          .live D s →
        resetColdPrivateHeadValue ring root D ≤
          resetColdPrivateHeadValue ring root C +
            (if e = root ∧ (C root).mode = .ARMED then 1 else 0)) ∧
      (∀ (e : Fin n) (D : Config q n) (s : Bool),
        resetColdLatchedPrivateNext ring root (.live C started) e =
          .live D s →
        (e ≠ root ∨ (C root).mode ≠ .ARMED) →
        resetColdPrivateHeadValue ring root D =
          resetColdPrivateHeadValue ring root C) ∧
      (∀ (e : Fin n) (D : Config q n),
        resetColdLatchedPrivateNext ring root (.live C started) e =
          .success D →
        resetColdPrivateHeadValue ring root C =
          (compileAdvice q).K)) :
    (List.ofFn (fun e : Fin n =>
      resetColdLatchedPrivatePotential ring root
        (resetColdLatchedPrivateNext ring root
          (.live C started) e))).sum ≤
      n * resetColdLatchedPrivatePotential ring root
        (.live C started) := by
  change (List.ofFn (fun e : Fin n =>
    resetColdLatchedPrivatePotential ring root
      (resetColdLatchedPrivateNext ring root
        (.live C started) e))).sum ≤
      n * (2 ^ resetColdPrivateHeadValue ring root C)
  by_cases hm : (C root).mode = .ARMED
  · have hn : 2 ≤ n := by
      by_cases htwo : 2 ≤ n
      · exact htwo
      · have hsingle : n = 1 := by
          have hpos := ring.hn
          omega
        have hself : ring.rightNeighbor root = root := by
          apply Fin.ext
          have hx := (ring.rightNeighbor root).isLt
          have hy := root.isLt
          omega
        exact False.elim
          ((resetColdRootPortDistinct ring C root hc) hself)
    have hpred :
        ring.rightNeighbor (site ring root (n - 1)) = root :=
      resetColdLastSiteIncoming ring root
    have hne : root ≠ site ring root (n - 1) := by
      intro he
      have hh := hpred
      rw [← he] at hh
      exact (resetColdRootPortDistinct ring C root hc) hh
    have hhead := resetColdLatchedPotentialArmedHeadLe
      ring root C started hm hrows.1
    have htail := resetColdLatchedIncomingArmedPotentialZero
      ring root (site ring root (n - 1)) C started
      (Ne.symm hne) hpred hm
    have hother (e : Fin n)
        (he : e ≠ root)
        (ht : e ≠ site ring root (n - 1)) :
        resetColdLatchedPrivatePotential ring root
          (resetColdLatchedPrivateNext ring root
            (.live C started) e) ≤
        2 ^ resetColdPrivateHeadValue ring root C := by
      exact resetColdLatchedPotentialOtherLe
        ring root e C started hrows.2.1 hrows.2.2
        (Or.inl he)
    exact resetColdLatchedTwoPortCapital
      root (site ring root (n - 1))
      (fun e : Fin n =>
        resetColdLatchedPrivatePotential ring root
          (resetColdLatchedPrivateNext ring root
            (.live C started) e))
      (2 ^ resetColdPrivateHeadValue ring root C)
      hn hne hhead htail hother
  · have hpoint (e : Fin n) :
        resetColdLatchedPrivatePotential ring root
          (resetColdLatchedPrivateNext ring root
            (.live C started) e) ≤
          2 ^ resetColdPrivateHeadValue ring root C := by
      exact resetColdLatchedPotentialOtherLe
        ring root e C started hrows.2.1 hrows.2.2
        (Or.inr hm)
    calc
      (List.ofFn (fun e : Fin n =>
        resetColdLatchedPrivatePotential ring root
          (resetColdLatchedPrivateNext ring root
            (.live C started) e))).sum ≤
        (List.ofFn (fun _ : Fin n =>
          2 ^ resetColdPrivateHeadValue ring root C)).sum :=
        ofFn_sum_le _ _ hpoint
      _ = n * (2 ^ resetColdPrivateHeadValue ring root C) :=
        ofFn_sum_const n _

/-- Reachability is always from a real Clean cut with global
grant-freedom, through precisely the observer's scheduler letters. -/
def ResetColdLatchedReachable {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : ResetColdLatchedPrivateState q n) : Prop :=
  ∃ Czero : Config q n, ResetClockBankClean ring Czero root ∧
    resetColdPrivateGlobalGrantFree Czero ∧
      ∃ w : List (Fin n),
        resetColdLatchedPrivateRun ring root (.live Czero false) w = z

/-- One final scheduler letter commutes with the literal word run. -/
theorem resetColdLatchedPrivateRunAppend {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (z : ResetColdLatchedPrivateState q n)
      (w : List (Fin n)) (e : Fin n),
      resetColdLatchedPrivateRun ring root z (w ++ [e]) =
        resetColdLatchedPrivateNext ring root
          (resetColdLatchedPrivateRun ring root z w) e := by
  intro z w
  induction w generalizing z with
  | nil =>
      intro e
      rfl
  | cons f tail ih =>
      intro e
      change resetColdLatchedPrivateRun ring root
          (resetColdLatchedPrivateNext ring root z f)
          (tail ++ [e]) =
        resetColdLatchedPrivateNext ring root
          (resetColdLatchedPrivateRun ring root
            (resetColdLatchedPrivateNext ring root z f) tail) e
      exact ih (resetColdLatchedPrivateNext ring root z f) e

/-- The physical reachability predicate is closed under the same
scheduler step used for the potential and finite-word success mass. -/
theorem resetColdLatchedReachableStep {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : ResetColdLatchedPrivateState q n)
    (hz : ResetColdLatchedReachable ring root z)
    (e : Fin n) :
    ResetColdLatchedReachable ring root
      (resetColdLatchedPrivateNext ring root z e) := by
  obtain ⟨Czero, hc, hg, w, hw⟩ := hz
  refine ⟨Czero, hc, hg, w ++ [e], ?_⟩
  rw [resetColdLatchedPrivateRunAppend, hw]

/-- The drift need only hold for reachable states, not for every
arbitrary Cartesian configuration. The tracked invariant
provides Complete at LIVE states; all terminal modes are immediate. -/
theorem resetColdLatchedReachableDriftOfHeadRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hrows : ResetColdLatchedHeadRows (q := q) ring root)
    (z : ResetColdLatchedPrivateState q n)
    (hz : ResetColdLatchedReachable ring root z) :
    (List.ofFn (fun e : Fin n =>
      resetColdLatchedPrivatePotential ring root
        (resetColdLatchedPrivateNext ring root z e))).sum ≤
      n * resetColdLatchedPrivatePotential ring root z := by
  obtain ⟨Czero, hc, hg, w, hw⟩ := hz
  cases z with
  | live C started =>
      have ht := resetColdRecoveryTrackedWord
        ring root hsp (.live Czero false) w hc.1
      rw [hw] at ht
      change Complete ring C root at ht
      have hr := hrows Czero hc hg w C started hw
      exact resetColdLatchedLiveDriftOfHeadRows
        ring root C started ht hr
  | recovery C =>
      have hzero :
          (List.ofFn (fun e : Fin n =>
            resetColdLatchedPrivatePotential ring root
              (resetColdLatchedPrivateNext ring root
                (.recovery C) e))).sum = 0 := by
        apply resetColdPrivateZeroSum
        intro e
        exact resetColdLatchedPrivateRecoveryCapitalStep
          ring root C e
      change (List.ofFn (fun e : Fin n =>
        resetColdLatchedPrivatePotential ring root
          (resetColdLatchedPrivateNext ring root
            (.recovery C) e))).sum ≤ n * 0
      rw [hzero]
      exact Nat.zero_le _
  | success C =>
      change (List.ofFn (fun _ : Fin n =>
        2 ^ (compileAdvice q).K)).sum ≤
          n * (2 ^ (compileAdvice q).K)
      rw [ofFn_sum_const]
      exact Nat.le_refl _
  | failure C =>
      change (List.ofFn (fun _ : Fin n => 0)).sum ≤ n * 0
      rw [ofFn_sum_const]
      exact Nat.le_refl _

/-- Finite-word supermartingale induction using the actual reachable
hypothesis at every child. No ALL-state drift assumption is made. -/
private theorem resetColdLatchedMassOfReachableDrift {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hdrift : ∀ z : ResetColdLatchedPrivateState q n,
      ResetColdLatchedReachable ring root z →
      (List.ofFn (fun e : Fin n =>
        resetColdLatchedPrivatePotential ring root
          (resetColdLatchedPrivateNext ring root z e))).sum ≤
        n * resetColdLatchedPrivatePotential ring root z) :
    ∀ (z : ResetColdLatchedPrivateState q n) (T : Nat),
      ResetColdLatchedReachable ring root z →
      2 ^ (compileAdvice q).K *
        resetColdLatchedPrivateMassFrom ring root z T ≤
      n ^ T * resetColdLatchedPrivatePotential ring root z := by
  intro z T
  induction T generalizing z with
  | zero =>
      intro hz
      cases z with
      | live C started =>
          simp [resetColdLatchedPrivateMassFrom,
            resetColdWordSum, resetColdLatchedPrivateRun,
            resetColdLatchedPrivateSuccess]
      | recovery C =>
          simp [resetColdLatchedPrivateMassFrom,
            resetColdWordSum, resetColdLatchedPrivateRun,
            resetColdLatchedPrivateSuccess,
            resetColdLatchedPrivatePotential]
      | success C =>
          simp [resetColdLatchedPrivateMassFrom,
            resetColdWordSum, resetColdLatchedPrivateRun,
            resetColdLatchedPrivateSuccess,
            resetColdLatchedPrivatePotential]
      | failure C =>
          simp [resetColdLatchedPrivateMassFrom,
            resetColdWordSum, resetColdLatchedPrivateRun,
            resetColdLatchedPrivateSuccess,
            resetColdLatchedPrivatePotential]
  | succ T ih =>
      intro hz
      rw [resetColdLatchedPrivateMassFromSucc]
      have hs := ofFn_sum_le
        (fun e : Fin n =>
          2 ^ (compileAdvice q).K *
            resetColdLatchedPrivateMassFrom ring root
              (resetColdLatchedPrivateNext ring root z e) T)
        (fun e : Fin n =>
          n ^ T * resetColdLatchedPrivatePotential ring root
            (resetColdLatchedPrivateNext ring root z e))
        (fun e => ih (resetColdLatchedPrivateNext ring root z e)
          (resetColdLatchedReachableStep ring root z hz e))
      calc
        2 ^ (compileAdvice q).K *
          (List.ofFn (fun e : Fin n =>
            resetColdLatchedPrivateMassFrom ring root
              (resetColdLatchedPrivateNext ring root z e) T)).sum =
          (List.ofFn (fun e : Fin n =>
            2 ^ (compileAdvice q).K *
              resetColdLatchedPrivateMassFrom ring root
                (resetColdLatchedPrivateNext ring root z e) T)).sum := by
            rw [ofFn_sum_mul_left]
        _ ≤ (List.ofFn (fun e : Fin n =>
          n ^ T * resetColdLatchedPrivatePotential ring root
            (resetColdLatchedPrivateNext ring root z e))).sum := hs
        _ = n ^ T * (List.ofFn (fun e : Fin n =>
          resetColdLatchedPrivatePotential ring root
            (resetColdLatchedPrivateNext ring root z e))).sum := by
            rw [ofFn_sum_mul_left]
        _ ≤ n ^ T * (n * resetColdLatchedPrivatePotential ring root z) :=
          Nat.mul_le_mul_left _ (hdrift z hz)
        _ = n ^ (T + 1) * resetColdLatchedPrivatePotential ring root z := by
          rw [Nat.pow_succ]
          ac_rfl

/-- This is the corrected *reachable* finite-horizon success bound,
conditional on the exact missing HeadRows theorem. The earlier
all-Cartesian drift hypothesis is not invoked. -/
theorem resetColdLatchedPrivateUpperOfHeadRows {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hrows : ResetColdLatchedHeadRows (q := q) ring root)
    (Czero : Config q n)
    (hc : ResetClockBankClean ring Czero root)
    (hg : resetColdPrivateGlobalGrantFree Czero)
    (T : Nat) :
    2 ^ (compileAdvice q).K *
      resetColdLatchedPrivateSuccessMass ring root Czero T ≤
      n ^ T := by
  have hreach : ResetColdLatchedReachable ring root
      (.live Czero false) :=
    ⟨Czero, hc, hg, [], rfl⟩
  have hh := resetColdLatchedMassOfReachableDrift
    ring root
    (fun z hz =>
      resetColdLatchedReachableDriftOfHeadRows
        ring root hsp hrows z hz)
    (.live Czero false) T hreach
  rw [resetColdLatchedPrivateInitialCapital ring root
    Czero hc] at hh
  change 2 ^ (compileAdvice q).K *
    resetColdLatchedPrivateSuccessMass ring root Czero T ≤
    n ^ T * 1 at hh
  simpa only [Nat.mul_one] using hh

/-- The exact two-port balance in Nat arithmetic. -/
theorem resetColdLatchedArmedTwoPortBalance
    (n capital : Nat) (hn : 2 ≤ n) :
    (n - 2) * capital + 2 * capital = n * capital := by
  calc
    (n - 2) * capital + 2 * capital =
        ((n - 2) + 2) * capital := (Nat.add_mul _ _ _).symm
    _ = n * capital := by
      rw [Nat.sub_add_cancel hn]

end Counter
end L3

/-!
Reachable LIVE head phase seeds and literal comparator rows.

The fully authenticated IWAIT/CWAIT transport invariant (single
worker, provenance, ordered carry/comparison front, and bounded
numeric value) still requires a whole-interval word induction.
This section proves the initial Clean and CSTART phases, the
first real comparator launch, and local carry / comparator rows,
without assuming that the missing closure holds on every word.
No unconditional HeadRows or probability theorem is claimed.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open K2ArbitraryElimination.FiniteAccounting

/-- One occupied BANK worker at a specified protected digit.
This is a physical predicate, not a newly defined scheduler. -/
def resetColdPrivateOnlyWorker {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (j : Nat) (t : BTok) : Prop :=
  1 ≤ j ∧ j ≤ (compileAdvice q).b ∧
    (C (site ring root j)).tok = t ∧
    (∀ i : Nat, 1 ≤ i → i ≤ (compileAdvice q).b →
      i ≠ j → (C (site ring root i)).tok = .E)

/-- The empty-worker phase is a property of every digit, including
the highest digit, not merely the first outgoing root port. -/
def resetColdPrivateNoWorkers {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) : Prop :=
  ∀ i : Nat, 1 ≤ i → i ≤ (compileAdvice q).b →
    (C (site ring root i)).tok = .E

theorem resetColdPrivateNoWorkersClean {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : ResetClockBankClean ring C root) :
    resetColdPrivateNoWorkers ring root C := by
  intro i hi hib
  exact (hc.2.2 i hi hib).2

/-- The exact initial LIVE phase after zero scheduler letters. -/
structure ResetColdPrivateArmedSeed {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) : Prop where
  complete : Complete ring C root
  armed : (C root).mode = .ARMED
  bitsZero : ∀ i : Nat, 1 ≤ i → i ≤ (compileAdvice q).b →
    (C (site ring root i)).bit = false
  noWorkers : resetColdPrivateNoWorkers ring root C
  headZero : resetColdPrivateHeadValue ring root C = 0

theorem resetColdPrivateArmedSeedClean {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : ResetClockBankClean ring C root) :
    ResetColdPrivateArmedSeed ring root C := by
  refine ⟨hc.1, hc.2.1, ?_, ?_, ?_⟩
  · intro i hi hib
    exact (hc.2.2 i hi hib).1
  · exact resetColdPrivateNoWorkersClean ring root C hc
  · exact resetColdPrivateHeadValueClean ring root C hc

/-- An authenticated first head increment has mode CSTART, exactly
one set low bit, no live worker, and represented numerical head 1. -/
structure ResetColdPrivateCStartSeed {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) : Prop where
  complete : Complete ring C root
  cstart : (C root).mode = .CSTART
  firstBit : (C (site ring root 1)).bit = true
  higherBitsZero : ∀ i : Nat, 2 ≤ i → i ≤ (compileAdvice q).b →
    (C (site ring root i)).bit = false
  noWorkers : resetColdPrivateNoWorkers ring root C
  headOne : resetColdPrivateHeadValue ring root C = 1

/-- C.5 physical Clean -> CSTART seed, along the actual root
service, with only the ordinary supported no-defect premise needed
to preserve PACK completeness. The head value is exactly 1. -/
theorem resetColdPrivateCStartSeedAfterClean {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : ResetClockBankClean ring C root)
    (hg : resetColdPrivateGlobalGrantFree C)
    (hsp : (compileAdvice q).useSmall = false)
    (hno : ¬ ResetClockBankDefectEntry ring C root root) :
    ResetColdPrivateCStartSeed ring root
      ((protocol q).step ring C root) := by
  have hone := hc.2.2 1
    (by omega)
    (by have hb := resetTrialCompiledWidth q; omega)
  have hrow := resetColdLatchedPhysicalArmedFirstSet
    ring C root hc.1 (hg root) hsp hc.2.1
    hone.2 hone.1
  have hhead := (resetColdLatchedPhysicalFirstHead
    ring root C hc hg hsp).2
  have hstable := resetClockBankStableOfNoDefect
    ring C root root hno
  have hcnew :
      Complete ring ((protocol q).step ring C root) root := by
    intro j hj
    rw [hstable j hj]
    exact hc.1 j hj
  refine ⟨hcnew, hrow.1, hrow.2.1, ?_, ?_, hhead⟩
  · intro j hj hjb
    rw [resetColdOutgoingRootOtherDigitsFrame
      ring C root hc.1 j hj hjb]
    exact (hc.2.2 j (by omega) hjb).1
  · intro j hj hjb
    by_cases hfirst : j = 1
    · subst j
      exact hrow.2.2
    · rw [resetColdOutgoingRootOtherDigitsFrame
        ring C root hc.1 j (by omega) hjb]
      exact (hc.2.2 j hj hjb).2

/-- The actual latched observer remains LIVE through the first
Clean-to-CSTART outgoing service, if that service is not a defect.
It cannot mistake this first bit update for a private success. -/
theorem resetColdPrivateFirstOutgoingLive {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : ResetClockBankClean ring C root)
    (hg : resetColdPrivateGlobalGrantFree C)
    (hsp : (compileAdvice q).useSmall = false)
    (hno : ¬ ResetClockBankDefectEntry ring C root root) :
    resetColdLatchedPrivateNext ring root (.live C false) root =
      .live ((protocol q).step ring C root) true := by
  have hrow := resetColdLatchedPhysicalFirstHead
    ring root C hc hg hsp
  have hprivate :
      ¬ resetColdPrivateSuccessAt ring root C root :=
    resetColdPrivateCleanNotSuccess ring root root C hc
  have hbegin : resetColdLatchedBegun ring root root false :=
    Or.inr (Or.inl rfl)
  have hnotclean :
      ¬ ResetClockBankClean ring
        ((protocol q).step ring C root) root := by
    intro hclean
    have hmode := hclean.2.1
    rw [hrow.1] at hmode
    cases hmode
  have hnotabort :
      ¬ resetColdLatchedAbort ring root C root := by
    intro habort
    rcases habort with hincoming | hreset
    · exact hincoming.2.1 rfl
    · rw [hrow.1] at hreset
      cases hreset
  simp only [resetColdLatchedPrivateNext, if_neg hno,
    if_neg hprivate, if_pos hbegin, if_neg hnotclean,
    if_neg hnotabort]

/-- A comparator is launched only from a free CSTART root and an
empty first worker. The bit is preserved, and the new token
records the literal first comparison against theta(0). -/
theorem resetColdPrivateCStartComparatorBank
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hr : x.role = 0) (hg : x.grant = false)
    (hy : y.role = 1) (hm : x.mode = .CSTART)
    (ht : y.tok = .E) (hb : 0 < b) :
    (bankPair x y 1 b theta).1.mode = .CWAIT ∧
      (bankPair x y 1 b theta).2.bit = y.bit ∧
      (bankPair x y 1 b theta).2.tok =
        (if y.bit == theta 0 then .CR1 else .CR0) := by
  simp [bankPair, hr, hg, hy, hm, ht, hb,
    isRetTok, isWaitMode]

/-- The full protocol copies the exact CSTART comparator-launch
mode, unchanged first bit, and comparator token. No surrogate BANK
scheduler and no extra private field are introduced. -/
theorem resetColdPrivateCStartComparatorPhysical {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hm : (C root).mode = .CSTART)
    (ht : (C (site ring root 1)).tok = .E) :
    (((protocol q).step ring C root) root).mode = .CWAIT ∧
      (((protocol q).step ring C root)
        (site ring root 1)).bit =
        (C (site ring root 1)).bit ∧
      (((protocol q).step ring C root)
        (site ring root 1)).tok =
        (if (C (site ring root 1)).bit ==
          (compileAdvice q).theta 0 then .CR1 else .CR0) := by
  have hroot : (C root).pack.val = 0 := by
    simpa only [site] using hc 0 (by omega)
  have hone : (C (site ring root 1)).pack.val = 1 :=
    hc 1 (by have hb := resetTrialCompiledWidth q; omega)
  have hb : 0 < (compileAdvice q).b := by
    have hw := resetTrialCompiledWidth q
    omega
  have hpost :
      packNext (C root).pack.val
        (C (site ring root 1)).pack.val
        (compileAdvice q).b = 1 := by
    rw [hroot, hone]
    simp [packNext, hb]
  have hbank :
      (resetBankOld (C root)
        (C (site ring root 1))).1.mode = .CWAIT ∧
      (resetBankOld (C root)
        (C (site ring root 1))).2.bit =
        (C (site ring root 1)).bit ∧
      (resetBankOld (C root)
        (C (site ring root 1))).2.tok =
        (if (C (site ring root 1)).bit ==
          (compileAdvice q).theta 0 then .CR1 else .CR0) := by
    have h0 := resetColdPrivateCStartComparatorBank
        (bankCell (C root) (C root).pack.val)
        (bankCell (C (site ring root 1))
          (C (site ring root 1)).pack.val)
        (compileAdvice q).b (compileAdvice q).theta
        (by change (C root).pack.val = 0; exact hroot)
        (by change (C root).grant = false; exact hg)
        (by change (C (site ring root 1)).pack.val = 1; exact hone)
        hm ht hb
    unfold resetBankOld
    rw [hpost]
    exact h0
  have htrip := resetPhysicalEdgeBankTrip ring C root
    (resetColdRootPortDistinct ring C root hc) hsp
  have hbit :
      (((protocol q).step ring C root)
        (site ring root 1)).bit =
      (resetBankOld (C root)
        (C (site ring root 1))).2.bit := by
    exact congrArg (fun z : Mode × Bool × BTok => z.2.1)
      htrip.2
  have htok :
      (((protocol q).step ring C root)
        (site ring root 1)).tok =
      (resetBankOld (C root)
        (C (site ring root 1))).2.tok := by
    exact congrArg (fun z : Mode × Bool × BTok => z.2.2)
      htrip.2
  exact ⟨(resetColdOutgoingRootModeLease ring C root hc hsp).1.trans
      hbank.1,
    hbit.trans hbank.2.1,
    htok.trans hbank.2.2⟩

/-- The initial comparison phase carries exactly one CR worker
at digit one; all higher worker slots remain empty and all bits
still represent numerical head one. -/
structure ResetColdPrivateCWaitSeed {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) : Prop where
  complete : Complete ring C root
  cwait : (C root).mode = .CWAIT
  firstBit : (C (site ring root 1)).bit = true
  firstToken : (C (site ring root 1)).tok =
    (if true == (compileAdvice q).theta 0 then .CR1 else .CR0)
  higherBitsZero : ∀ i : Nat, 2 ≤ i → i ≤ (compileAdvice q).b →
    (C (site ring root i)).bit = false
  higherTokensEmpty : ∀ i : Nat, 2 ≤ i →
    i ≤ (compileAdvice q).b →
    (C (site ring root i)).tok = .E
  headOne : resetColdPrivateHeadValue ring root C = 1

/-- An exact CSTART->CWAIT phase seed. The comparator does not
change the represented numerical value, because it writes no IR
carry and preserves every digit bit. -/
theorem resetColdPrivateCWaitSeedOfCStart {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hseed : ResetColdPrivateCStartSeed ring root C)
    (hg : GrantFree C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hno : ¬ ResetClockBankDefectEntry ring C root root) :
    ResetColdPrivateCWaitSeed ring root
      ((protocol q).step ring C root) := by
  have hrow := resetColdPrivateCStartComparatorPhysical
    ring root C hseed.complete hg hsp hseed.cstart
    (hseed.noWorkers 1 (by omega)
      (by have hb := resetTrialCompiledWidth q; omega))
  have hstable :=
    resetClockBankStableOfNoDefect ring C root root hno
  have hcnew :
      Complete ring ((protocol q).step ring C root) root := by
    intro j hj
    rw [hstable j hj]
    exact hseed.complete j hj
  have hfirst :
      (((protocol q).step ring C root)
        (site ring root 1)).bit = true := by
    rw [hrow.2.1]
    exact hseed.firstBit
  have htoken :
      (((protocol q).step ring C root)
        (site ring root 1)).tok =
      (if true == (compileAdvice q).theta 0
        then .CR1 else .CR0) := by
    rw [hrow.2.2, hseed.firstBit]
  have hrest : ∀ j : Nat, 2 ≤ j →
      j ≤ (compileAdvice q).b →
      (((protocol q).step ring C root)
        (site ring root j)).bit = false := by
    intro j hj hjb
    rw [resetColdOutgoingRootOtherDigitsFrame
      ring C root hseed.complete j hj hjb]
    exact hseed.higherBitsZero j hj hjb
  have hresttok : ∀ j : Nat, 2 ≤ j →
      j ≤ (compileAdvice q).b →
      (((protocol q).step ring C root)
        (site ring root j)).tok = .E := by
    intro j hj hjb
    rw [resetColdOutgoingRootOtherDigitsFrame
      ring C root hseed.complete j hj hjb]
    exact hseed.noWorkers j (by omega) hjb
  have hnoir (j : Nat) (hj : 1 ≤ j)
      (hjb : j ≤ (compileAdvice q).b) :
      (((protocol q).step ring C root)
        (site ring root j)).tok ≠ .IR := by
    by_cases hone : j = 1
    · subst j
      rw [htoken]
      split <;> simp
    · rw [hresttok j (by omega) hjb]
      intro hh
      cases hh
  have hcarry :
      resetColdPrivateCarryValue ring root
        ((protocol q).step ring C root) = 0 := by
    unfold resetColdPrivateCarryValue
    apply resetColdPrivateZeroSum
    intro j
    have hh := hnoir (j.val + 1) (by omega)
      (by have hb := j.isLt; omega)
    simp [hh]
  have hhead :
      resetColdPrivateHeadValue ring root
        ((protocol q).step ring C root) = 1 := by
    unfold resetColdPrivateHeadValue
    rw [resetColdLatchedPrivateBitSingle
      ring root ((protocol q).step ring C root)
      hfirst hrest, hcarry]
  exact ⟨hcnew, hrow.1, hfirst, htoken,
    hrest, hresttok, hhead⟩

/-- At the first physical CWAIT seed only the first worker is
occupied. This is the exact base case needed for later comparator
transport, not a claim of wordwise single-worker preservation. -/
theorem resetColdPrivateCWaitSeedOneWorker {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (h : ResetColdPrivateCWaitSeed ring root C) :
    resetColdPrivateOnlyWorker ring root C 1
      (if true == (compileAdvice q).theta 0
        then .CR1 else .CR0) := by
  refine ⟨by omega, ?_, h.firstToken, ?_⟩
  · have hb := resetTrialCompiledWidth q
    omega
  · intro i hi hib hine
    exact h.higherTokensEmpty i (by omega) hib

/-- The binary-weight carry identity at the shifted physical
digit index: a continuing IR doubles its weight while a completed
carry becomes AL and changes no other bit contribution. -/
theorem resetColdPrivateCarryShiftValue (j : Nat) (bit : Bool) :
    (if bit then 2 ^ (j + 1) else 0) + 2 ^ (j + 1) =
      (if !bit then 2 ^ (j + 1) else 0) +
        (if bit then 2 ^ (j + 2) else 0) := by
  simpa only [Nat.add_assoc] using
    (resetColdLatchedPrivateIRWeight (j + 1) bit)

/-- The literal one-token IR advance (no destination collision)
already has a physical BANK symbolic certificate in Counter.lean. -/
theorem resetColdPrivateIRAdvanceRow
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : 1 ≤ x.role) (hlt : x.role < b)
    (hy : y.role = x.role + 1)
    (htx : x.tok = .IR) (hty : y.tok = .E) :
    (bankPair x y y.role b theta).1.tok = .E ∧
      (bankPair x y y.role b theta).2.bit = !y.bit ∧
      (bankPair x y y.role b theta).2.tok =
        (if y.bit then .IR else .AL) := by
  exact resetBankIncrementToggleSymbolic
    x y b theta hx hlt hy htx hty

end Counter
end L3

/-!
A word-invariant phase vocabulary and its certified base and
exterior cases.

The CSTART phase is explicitly worker-free. A CR worker is first
created in CWAIT. The comparator prefix witness distinguishes CR1
from CL1 and does not promote a local CL1 to a completed comparison
without a full-prefix certificate.

This section does NOT assert that the phase predicate is preserved
on every selected BANK edge, does NOT assert HeadRows, and does NOT
assert an unconditional private probability upper bound.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open K2ArbitraryElimination.FiniteAccounting

/-- A live comparator token, in either transport direction. -/
def resetColdPrivateComparatorToken (t : BTok) : Prop :=
  t = .CR0 ∨ t = .CR1 ∨ t = .CL0 ∨ t = .CL1

/-- A live increment token, in either transport direction. -/
def resetColdPrivateCarryToken (t : BTok) : Prop :=
  t = .IR ∨ t = .AL

/-- A CR1 at j certifies comparisons up through j. A CL1
return is required to certify the full b-digit prefix. -/
def resetColdPrivateMatchedPrefix {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (j : Nat) : Prop :=
  ∀ i : Nat, 1 ≤ i → i ≤ j →
    i ≤ (compileAdvice q).b →
      (C (site ring root i)).bit =
        (compileAdvice q).theta (i - 1)

/-- Proposed LIVE phase shape. The witness h is the last completed
head before an outstanding increment/comparison; in ARMED it is the
current head. The numerical value of every busy phase is h+1.

The CR1/CL1 clauses record the authentication information needed to
exclude a false positive return. The latter does not yet include
the converse or the binary-expansion identity for K. -/
def ResetColdPrivateLiveShape {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) : Prop :=
  (∃ h : Nat,
    h < (compileAdvice q).K ∧
    (C root).mode = .ARMED ∧
    resetColdPrivateNoWorkers ring root C ∧
    resetColdPrivateHeadValue ring root C = h) ∨
  (∃ h : Nat,
    h + 1 ≤ (compileAdvice q).K ∧
    (C root).mode = .CSTART ∧
    resetColdPrivateNoWorkers ring root C ∧
    resetColdPrivateHeadValue ring root C = h + 1) ∨
  (∃ h j : Nat, ∃ t : BTok,
    h + 1 ≤ (compileAdvice q).K ∧
    (C root).mode = .CWAIT ∧
    resetColdPrivateOnlyWorker ring root C j t ∧
    resetColdPrivateComparatorToken t ∧
    resetColdPrivateHeadValue ring root C = h + 1 ∧
    (t = .CR1 →
      resetColdPrivateMatchedPrefix ring root C j) ∧
    (t = .CL1 →
      resetColdPrivateMatchedPrefix ring root C
        (compileAdvice q).b)) ∨
  (∃ h j : Nat, ∃ t : BTok,
    h + 1 ≤ (compileAdvice q).K ∧
    (C root).mode = .IWAIT ∧
    resetColdPrivateOnlyWorker ring root C j t ∧
    resetColdPrivateCarryToken t ∧
    resetColdPrivateHeadValue ring root C = h + 1)

/-- The spatial selection hsp=false forces q above the SMALL band,
and in particular K is positive. -/
theorem resetColdPrivateKPositive (q : Nat)
    (hsp : (compileAdvice q).useSmall = false) :
    0 < (compileAdvice q).K := by
  have hq : ¬ q ≤ qStar := by
    intro hle
    have htrue : (compileAdvice q).useSmall = true := by
      simp [Compiled.useSmall, compileAdvice, hle]
    rw [htrue] at hsp
    cases hsp
  have hpositive : 0 < q := by
    unfold qStar at hq
    omega
  change 0 < 2 * q + productionKappa q
  omega

/-- Clean supplies the entire ARMED/empty/numeric-zero phase,
not merely its root mode. -/
theorem resetColdPrivateLiveShapeClean {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : ResetClockBankClean ring C root)
    (hsp : (compileAdvice q).useSmall = false) :
    ResetColdPrivateLiveShape ring root C := by
  have hseed := resetColdPrivateArmedSeedClean ring root C hc
  have hpositive := resetColdPrivateKPositive q hsp
  exact Or.inl
    ⟨0, hpositive, hseed.armed, hseed.noWorkers, hseed.headZero⟩

/-- First actual head increment: CSTART is an empty-worker
phase, with represented head 0+1, not a CR-bearing phase. -/
theorem resetColdPrivateLiveShapeCStartSeed {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hseed : ResetColdPrivateCStartSeed ring root C)
    (hsp : (compileAdvice q).useSmall = false) :
    ResetColdPrivateLiveShape ring root C := by
  have hpositive := resetColdPrivateKPositive q hsp
  exact Or.inr (Or.inl
    ⟨0, by omega, hseed.cstart, hseed.noWorkers, hseed.headOne⟩)

/-- The first CWAIT worker is CR1 precisely when its low digit
matches theta(0); the full-prefix CL1 implication is vacuous
at this first launch, because this token cannot yet be CL1. -/
theorem resetColdPrivateLiveShapeCWaitSeed {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hseed : ResetColdPrivateCWaitSeed ring root C)
    (hsp : (compileAdvice q).useSmall = false) :
    ResetColdPrivateLiveShape ring root C := by
  have hpositive := resetColdPrivateKPositive q hsp
  have hcomparator :
      resetColdPrivateComparatorToken
        (if true == (compileAdvice q).theta 0
          then BTok.CR1 else BTok.CR0) := by
    unfold resetColdPrivateComparatorToken
    split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
  have hprefix :
      (if true == (compileAdvice q).theta 0
        then BTok.CR1 else BTok.CR0) = .CR1 →
      resetColdPrivateMatchedPrefix ring root C 1 := by
    intro htok
    have htheta : (compileAdvice q).theta 0 = true := by
      cases htheta : (compileAdvice q).theta 0 with
      | false =>
          simp [htheta] at htok
      | true =>
          rfl
    intro i hi hione hib
    have hie : i = 1 := by omega
    subst i
    change (C (site ring root 1)).bit =
      (compileAdvice q).theta 0
    rw [htheta]
    exact hseed.firstBit
  have hnotreturn :
      (if true == (compileAdvice q).theta 0
        then BTok.CR1 else BTok.CR0) = .CL1 →
      resetColdPrivateMatchedPrefix ring root C
        (compileAdvice q).b := by
    intro htok
    split at htok <;> cases htok
  refine Or.inr (Or.inr (Or.inl
    ⟨0, 1,
      (if true == (compileAdvice q).theta 0
        then BTok.CR1 else BTok.CR0),
      ?_, hseed.cwait,
      resetColdPrivateCWaitSeedOneWorker ring root C hseed,
      hcomparator, hseed.headOne, hprefix, hnotreturn⟩))
  omega

/-- The numerical part of the proposed invariant already implies
a bounded head on every one of its four phases. -/
theorem resetColdPrivateLiveShapeHeadLe {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hshape : ResetColdPrivateLiveShape ring root C) :
    resetColdPrivateHeadValue ring root C ≤
      (compileAdvice q).K := by
  rcases hshape with harm | hrest
  · obtain ⟨h, hbound, hm, hn, hval⟩ := harm
    rw [hval]
    omega
  · rcases hrest with hstart | hrest
    · obtain ⟨h, hbound, hm, hn, hval⟩ := hstart
      rw [hval]
      exact hbound
    · rcases hrest with hcompare | hcarry
      · obtain ⟨h, j, t, hbound, hm, hw, ht, hval, hp, hall⟩ := hcompare
        rw [hval]
        exact hbound
      · obtain ⟨h, j, t, hbound, hm, hw, ht, hval⟩ := hcarry
        rw [hval]
        exact hbound

/-- The phase shape is literally invariant under a root-mode frame
and a full digit-site frame. In particular, all provenance predicates
are transported rather than recomputed from the new configuration. -/
theorem resetColdPrivateLiveShapeFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n)
    (hroot : (D root).mode = (C root).mode)
    (hframe : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      D (site ring root j) = C (site ring root j))
    (hshape : ResetColdPrivateLiveShape ring root C) :
    ResetColdPrivateLiveShape ring root D := by
  have hhead := resetColdLatchedPrivateHeadOfDigitFrame
    ring root C D hframe
  have hno
      (he : resetColdPrivateNoWorkers ring root C) :
      resetColdPrivateNoWorkers ring root D := by
    intro j hj hjb
    rw [hframe j hj hjb]
    exact he j hj hjb
  have hone (j : Nat) (t : BTok)
      (he : resetColdPrivateOnlyWorker ring root C j t) :
      resetColdPrivateOnlyWorker ring root D j t := by
    obtain ⟨hj, hjb, ht, hrest⟩ := he
    refine ⟨hj, hjb, ?_, ?_⟩
    · rw [hframe j hj hjb]
      exact ht
    · intro i hi hib hine
      rw [hframe i hi hib]
      exact hrest i hi hib hine
  have hp (j : Nat)
      (he : resetColdPrivateMatchedPrefix ring root C j) :
      resetColdPrivateMatchedPrefix ring root D j := by
    intro i hi hij hib
    rw [hframe i hi hib]
    exact he i hi hij hib
  rcases hshape with harm | hrest
  · obtain ⟨h, hbound, hm, hn, hval⟩ := harm
    exact Or.inl
      ⟨h, hbound, hroot.trans hm, hno hn, hhead.trans hval⟩
  · rcases hrest with hstart | hrest
    · obtain ⟨h, hbound, hm, hn, hval⟩ := hstart
      exact Or.inr (Or.inl
        ⟨h, hbound, hroot.trans hm, hno hn, hhead.trans hval⟩)
    · rcases hrest with hcompare | hcarry
      · obtain ⟨h, j, t, hbound, hm, hw, ht, hval,
            hprefix, hall⟩ := hcompare
        refine Or.inr (Or.inr (Or.inl
          ⟨h, j, t, hbound, hroot.trans hm,
            hone j t hw, ht, hhead.trans hval, ?_, ?_⟩))
        · intro hcr
          exact hp j (hprefix hcr)
        · intro hcl
          exact hp (compileAdvice q).b (hall hcl)
      · obtain ⟨h, j, t, hbound, hm, hw, ht, hval⟩ := hcarry
        exact Or.inr (Or.inr (Or.inr
          ⟨h, j, t, hbound, hroot.trans hm,
            hone j t hw, ht, hhead.trans hval⟩))

/-- An actual physical service touching neither root nor any
protected digit preserves the entire four-way phase invariant. -/
theorem resetColdPrivateLiveShapeOutside {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Config q n)
    (hrootSource : e ≠ root)
    (hrootTarget : ring.rightNeighbor e ≠ root)
    (hsource : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
        e ≠ site ring root j)
    (htarget : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
        ring.rightNeighbor e ≠ site ring root j)
    (hshape : ResetColdPrivateLiveShape ring root C) :
    ResetColdPrivateLiveShape ring root
      ((protocol q).step ring C e) := by
  have hmode :
      (((protocol q).step ring C e) root).mode =
        (C root).mode := by
    exact congrArg
      (fun a : Agent (compileAdvice q) => a.mode)
      (step_frame ring C e root
        (Ne.symm hrootSource) (Ne.symm hrootTarget))
  have hframe : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      ((protocol q).step ring C e) (site ring root j) =
        C (site ring root j) := by
    intro j hj hjb
    exact step_frame ring C e (site ring root j)
      (Ne.symm (hsource j hj hjb))
      (Ne.symm (htarget j hj hjb))
  exact resetColdPrivateLiveShapeFrame ring root C
    ((protocol q).step ring C e) hmode hframe hshape

/-- This same exterior case is a LIVE-observer statement. It uses
the actual observer successor equality, not a surrogate BANK
configuration; the numerical head is unchanged. -/
theorem resetColdPrivateLiveShapeOutsideObserver {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hrootSource : e ≠ root)
    (hrootTarget : ring.rightNeighbor e ≠ root)
    (hsource : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
        e ≠ site ring root j)
    (htarget : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
        ring.rightNeighbor e ≠ site ring root j)
    (hshape : ResetColdPrivateLiveShape ring root C)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) e = .live D started') :
    ResetColdPrivateLiveShape ring root D ∧
      resetColdPrivateHeadValue ring root D =
        resetColdPrivateHeadValue ring root C := by
  have hterm :
      ¬ resetColdLatchedPrivateTerminal
        (ResetColdLatchedPrivateState.live C started) := by
    intro h
    exact h
  have hphysical : D = (protocol q).step ring C e := by
    have hp := resetColdLatchedPrivatePhysicalNext
      ring root (.live C started) hterm e
    rw [hnext] at hp
    exact hp
  constructor
  · rw [hphysical]
    exact resetColdPrivateLiveShapeOutside ring root e C
      hrootSource hrootTarget hsource htarget hshape
  · rw [hphysical]
    exact resetColdLatchedPrivateHeadOutside
      ring root e C hsource htarget

/-- Any CL1 in an authenticated one-worker phase certifies a
full theta match. This is a state-local consequence of the strong
comparator provenance clause, independently of scheduling. -/
theorem resetColdPrivateLiveShapeCL1Matches {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (j : Nat)
    (hshape : ResetColdPrivateLiveShape ring root C)
    (hj : 1 ≤ j) (hjb : j ≤ (compileAdvice q).b)
    (htok : (C (site ring root j)).tok = .CL1) :
    resetColdPrivateMatchedPrefix ring root C
      (compileAdvice q).b := by
  have hslot (k : Nat) (t : BTok)
      (hw : resetColdPrivateOnlyWorker ring root C k t) :
      t = .CL1 := by
    by_cases hkj : k = j
    · have hk := hw.2.2.1
      rw [hkj] at hk
      exact hk.symm.trans htok
    · have he := hw.2.2.2 j hj hjb (Ne.symm hkj)
      rw [htok] at he
      cases he
  rcases hshape with harm | hrest
  · obtain ⟨h, hbound, hm, hn, hval⟩ := harm
    have he := hn j hj hjb
    rw [htok] at he
    cases he
  · rcases hrest with hstart | hrest
    · obtain ⟨h, hbound, hm, hn, hval⟩ := hstart
      have he := hn j hj hjb
      rw [htok] at he
      cases he
    · rcases hrest with hcompare | hcarry
      · obtain ⟨h, k, t, hbound, hm, hw, htype,
            hval, hprefix, hall⟩ := hcompare
        exact hall (hslot k t hw)
      · obtain ⟨h, k, t, hbound, hm, hw, htype, hval⟩ := hcarry
        have ht := hslot k t hw
        rcases htype with hir | hal
        · rw [hir] at ht
          cases ht
        · rw [hal] at ht
          cases ht

/-- The top carry is numerically incompatible with a bounded
live head if K is representable in b digits. This lemma is only
the arithmetic obstruction: it does not assert the missing
physical invariant or a machine-level overflow abort. -/
theorem resetColdPrivateTopCarryBound {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (hhead : resetColdPrivateHeadValue ring root C ≤
      (compileAdvice q).K)
    (htop : 2 ^ (compileAdvice q).b ≤
      resetColdPrivateCarryValue ring root C) :
    False := by
  unfold resetColdPrivateHeadValue at hhead
  omega

end Counter
end L3

/-!
Physical root-row phase induction.

This round handles the first root service in each non-return class:
ARMED low-bit set, ARMED low-bit carry launch, CSTART comparator
launch, and a CWAIT/IWAIT watchdog tick with a nonreturn digit-one
token. The root-return and interior-edge classes are not claimed.

A LIVE successor has neither the latched abort nor the root RESET
mode; this statement is proved directly from the observer definition.
Every phase result below uses the actual protocol step.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- A LIVE-to-LIVE observer transition cannot be a latched abort.
This is a selector fact and does not assume any BANK reachability. -/
theorem resetColdPrivateLiveNoAbort {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) e = .live D started') :
    ¬ resetColdLatchedAbort ring root C e := by
  intro habort
  by_cases hd : ResetClockBankDefectEntry ring C root e
  · simp only [resetColdLatchedPrivateNext, if_pos hd] at hnext
    cases hnext
  · by_cases hs : resetColdPrivateSuccessAt ring root C e
    · simp only [resetColdLatchedPrivateNext,
        if_neg hd, if_pos hs] at hnext
      cases hnext
    · by_cases hb : resetColdLatchedBegun ring root e started
      · by_cases hc : ResetClockBankClean ring
            ((protocol q).step ring C e) root
        · simp only [resetColdLatchedPrivateNext,
            if_neg hd, if_neg hs, if_pos hb, if_pos hc] at hnext
          cases hnext
        · simp only [resetColdLatchedPrivateNext,
            if_neg hd, if_neg hs, if_pos hb, if_neg hc,
            if_pos habort] at hnext
          cases hnext
      · simp only [resetColdLatchedPrivateNext,
          if_neg hd, if_neg hs, if_neg hb,
          if_pos habort] at hnext
        cases hnext

/-- Physical meaning of LIVE-to-LIVE, with the same scheduler edge. -/
theorem resetColdPrivateLivePhysical {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) e = .live D started') :
    D = (protocol q).step ring C e := by
  have hterm :
      ¬ resetColdLatchedPrivateTerminal
        (ResetColdLatchedPrivateState.live C started) := by
    intro h
    exact h
  have hp := resetColdLatchedPrivatePhysicalNext
    ring root (.live C started) hterm e
  rw [hnext] at hp
  exact hp

/-- A LIVE-to-LIVE transition does not leave RESET at the root. -/
theorem resetColdPrivateLiveRootNotReset {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) e = .live D started') :
    (((protocol q).step ring C e) root).mode ≠ .RESET := by
  intro hreset
  exact (resetColdPrivateLiveNoAbort ring root e
    C D started started' hnext) (Or.inr hreset)

/-- On a LIVE outgoing root service, a grant-free old root is
forced: a granted root is physically reset and then latched out. -/
theorem resetColdPrivateLiveOutgoingGrantFree {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) root = .live D started') :
    GrantFree C root := by
  cases hg : (C root).grant with
  | false =>
      exact hg
  | true =>
      have hreset := resetColdRecoveryPhysicalOutgoingGranted
        ring C root hc hsp hg
      have hnot := resetColdPrivateLiveRootNotReset
        ring root root C D started started' hnext
      exact False.elim (hnot hreset)

/-- Equality of all digit BANK bits and tokens suffices for
equality of the full numerical head; no lease or other fields
need be framed. -/
theorem resetColdPrivateHeadBankFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n)
    (hbit : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      (D (site ring root j)).bit = (C (site ring root j)).bit)
    (htok : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      (D (site ring root j)).tok = (C (site ring root j)).tok) :
    resetColdPrivateHeadValue ring root D =
      resetColdPrivateHeadValue ring root C := by
  have hbits :
      resetColdPrivateBitValue ring root D =
        resetColdPrivateBitValue ring root C := by
    unfold resetColdPrivateBitValue
    apply ofFn_sum_eq
    intro j
    rw [hbit (j.val + 1) (by omega)
      (by have hj := j.isLt; omega)]
  have hcarries :
      resetColdPrivateCarryValue ring root D =
        resetColdPrivateCarryValue ring root C := by
    unfold resetColdPrivateCarryValue
    apply ofFn_sum_eq
    intro j
    rw [htok (j.val + 1) (by omega)
      (by have hj := j.isLt; omega)]
  unfold resetColdPrivateHeadValue
  rw [hbits, hcarries]

/-- The same BANK-field frame transports all four live shapes,
including both comparator-prefix implications. -/
theorem resetColdPrivateLiveShapeBankFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n)
    (hroot : (D root).mode = (C root).mode)
    (hbit : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      (D (site ring root j)).bit = (C (site ring root j)).bit)
    (htok : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      (D (site ring root j)).tok = (C (site ring root j)).tok)
    (hshape : ResetColdPrivateLiveShape ring root C) :
    ResetColdPrivateLiveShape ring root D := by
  have hhead := resetColdPrivateHeadBankFrame
    ring root C D hbit htok
  have hno
      (he : resetColdPrivateNoWorkers ring root C) :
      resetColdPrivateNoWorkers ring root D := by
    intro j hj hjb
    rw [htok j hj hjb]
    exact he j hj hjb
  have hone (j : Nat) (t : BTok)
      (he : resetColdPrivateOnlyWorker ring root C j t) :
      resetColdPrivateOnlyWorker ring root D j t := by
    obtain ⟨hj, hjb, ht, hrest⟩ := he
    refine ⟨hj, hjb, ?_, ?_⟩
    · rw [htok j hj hjb]
      exact ht
    · intro i hi hib hine
      rw [htok i hi hib]
      exact hrest i hi hib hine
  have hp (j : Nat)
      (he : resetColdPrivateMatchedPrefix ring root C j) :
      resetColdPrivateMatchedPrefix ring root D j := by
    intro i hi hij hib
    rw [hbit i hi hib]
    exact he i hi hij hib
  rcases hshape with harm | hrest
  · obtain ⟨h, hbound, hm, hn, hval⟩ := harm
    exact Or.inl
      ⟨h, hbound, hroot.trans hm, hno hn, hhead.trans hval⟩
  · rcases hrest with hstart | hrest
    · obtain ⟨h, hbound, hm, hn, hval⟩ := hstart
      exact Or.inr (Or.inl
        ⟨h, hbound, hroot.trans hm, hno hn, hhead.trans hval⟩)
    · rcases hrest with hcompare | hcarry
      · obtain ⟨h, j, t, hbound, hm, hw, ht, hval,
            hprefix, hall⟩ := hcompare
        refine Or.inr (Or.inr (Or.inl
          ⟨h, j, t, hbound, hroot.trans hm,
            hone j t hw, ht, hhead.trans hval, ?_, ?_⟩))
        · intro hcr
          exact hp j (hprefix hcr)
        · intro hcl
          exact hp (compileAdvice q).b (hall hcl)
      · obtain ⟨h, j, t, hbound, hm, hw, ht, hval⟩ := hcarry
        exact Or.inr (Or.inr (Or.inr
          ⟨h, j, t, hbound, hroot.trans hm,
            hone j t hw, ht, hhead.trans hval⟩))

/-- One low bit changes from zero to one, all higher digit bits
are framed. Its binary sum gains exactly one unit. -/
theorem resetColdPrivateBitLowUp {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n)
    (hzero : (C (site ring root 1)).bit = false)
    (hone : (D (site ring root 1)).bit = true)
    (hrest : ∀ j : Nat, 2 ≤ j →
      j ≤ (compileAdvice q).b →
      (D (site ring root j)).bit = (C (site ring root j)).bit) :
    resetColdPrivateBitValue ring root D =
      resetColdPrivateBitValue ring root C + 1 := by
  have hb : 0 < (compileAdvice q).b := by
    have hw := resetTrialCompiledWidth q
    omega
  have hwidth : (compileAdvice q).b =
      ((compileAdvice q).b - 1) + 1 := by omega
  have hspike :
      (List.ofFn (fun j : Fin (compileAdvice q).b =>
        if j.val = 0 then 1 else 0)).sum = 1 := by
    rw [hwidth]
    exact resetColdLatchedSingleLowBit ((compileAdvice q).b - 1)
  have hpoint (j : Fin (compileAdvice q).b) :
      (if (D (site ring root (j.val + 1))).bit = true
        then 2 ^ j.val else 0) =
        (if (C (site ring root (j.val + 1))).bit = true
        then 2 ^ j.val else 0) +
          (if j.val = 0 then 1 else 0) := by
    by_cases hj : j.val = 0
    · have he : j.val + 1 = 1 := by omega
      rw [he, hone, hzero]
      simp [hj]
    · have hi : 2 ≤ j.val + 1 := by omega
      have hib : j.val + 1 ≤ (compileAdvice q).b := by
        have hh := j.isLt
        omega
      rw [hrest (j.val + 1) hi hib]
      simp [hj]
  unfold resetColdPrivateBitValue
  calc
    (List.ofFn (fun j : Fin (compileAdvice q).b =>
      if (D (site ring root (j.val + 1))).bit = true
        then 2 ^ j.val else 0)).sum =
      (List.ofFn (fun j : Fin (compileAdvice q).b =>
        (if (C (site ring root (j.val + 1))).bit = true
          then 2 ^ j.val else 0) +
        (if j.val = 0 then 1 else 0))).sum := by
          apply ofFn_sum_eq
          exact hpoint
    _ = (List.ofFn (fun j : Fin (compileAdvice q).b =>
        if (C (site ring root (j.val + 1))).bit = true
          then 2 ^ j.val else 0)).sum +
        (List.ofFn (fun j : Fin (compileAdvice q).b =>
          if j.val = 0 then 1 else 0)).sum := by
          rw [ofFn_sum_add]
    _ = (List.ofFn (fun j : Fin (compileAdvice q).b =>
        if (C (site ring root (j.val + 1))).bit = true
          then 2 ^ j.val else 0)).sum + 1 := by
          rw [hspike]

/-- The only IR is the low-digit token: it carries weight two,
not weight one. This distinguishes a pending increment from the
ordinary low bit's unit weight. -/
theorem resetColdPrivateCarryFirstWeight {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hfirst : (C (site ring root 1)).tok = .IR)
    (hrest : ∀ j : Nat, 2 ≤ j →
      j ≤ (compileAdvice q).b →
      (C (site ring root j)).tok ≠ .IR) :
    resetColdPrivateCarryValue ring root C = 2 := by
  have hb : 0 < (compileAdvice q).b := by
    have hw := resetTrialCompiledWidth q
    omega
  have hpoint (j : Fin (compileAdvice q).b) :
      (if (C (site ring root (j.val + 1))).tok = .IR
        then 2 ^ (j.val + 1) else 0) =
      (if j.val = 0 then 2 else 0) := by
    by_cases hj : j.val = 0
    · have he : j.val + 1 = 1 := by omega
      rw [he, hfirst]
      simp [hj]
    · have hi : 2 ≤ j.val + 1 := by omega
      have hib : j.val + 1 ≤ (compileAdvice q).b := by
        have hh := j.isLt
        omega
      have hn := hrest (j.val + 1) hi hib
      simp [hn, hj]
  have hspike :
      (List.ofFn (fun j : Fin (compileAdvice q).b =>
        if j.val = 0 then 2 else 0)).sum = 2 := by
    have heq :
        (List.ofFn (fun j : Fin (compileAdvice q).b =>
          if j.val = 0 then 2 else 0)).sum =
        (List.ofFn (fun j : Fin (compileAdvice q).b =>
          if j = (⟨0, hb⟩ : Fin (compileAdvice q).b)
            then 2 else 0)).sum := by
      apply ofFn_sum_eq
      intro j
      by_cases hj : j.val = 0
      · have he : j = (⟨0, hb⟩ : Fin (compileAdvice q).b) :=
          Fin.ext hj
        simp [hj, he]
      · have he : j ≠ (⟨0, hb⟩ : Fin (compileAdvice q).b) := by
          intro he
          have hv := congrArg Fin.val he
          have hz : j.val = 0 := by simpa using hv
          exact hj hz
        simp [hj, he]
    rw [heq]
    exact resetClockOfFnSpike (compileAdvice q).b
      ⟨0, hb⟩ 2
  unfold resetColdPrivateCarryValue
  calc
    (List.ofFn (fun j : Fin (compileAdvice q).b =>
      if (C (site ring root (j.val + 1))).tok = .IR
        then 2 ^ (j.val + 1) else 0)).sum =
      (List.ofFn (fun j : Fin (compileAdvice q).b =>
        if j.val = 0 then 2 else 0)).sum := by
          apply ofFn_sum_eq
          exact hpoint
    _ = 2 := hspike

/-- No IR token on any digit gives zero carry weight, regardless
of the other, non-IR token alphabet. -/
theorem resetColdPrivateCarryZeroOfNoIR {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hno : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      (C (site ring root j)).tok ≠ .IR) :
    resetColdPrivateCarryValue ring root C = 0 := by
  unfold resetColdPrivateCarryValue
  apply resetColdPrivateZeroSum
  intro j
  have hib : j.val + 1 ≤ (compileAdvice q).b := by
    have hh := j.isLt
    omega
  have hn := hno (j.val + 1) (by omega) hib
  simp [hn]

/-- Equal digit bits and absence of IR on either snapshot
imply unchanged head, even if CR or CL tokens are launched. -/
theorem resetColdPrivateHeadNoIRBitFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n)
    (hbit : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      (D (site ring root j)).bit = (C (site ring root j)).bit)
    (hnoC : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      (C (site ring root j)).tok ≠ .IR)
    (hnoD : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      (D (site ring root j)).tok ≠ .IR) :
    resetColdPrivateHeadValue ring root D =
      resetColdPrivateHeadValue ring root C := by
  have hbits :
      resetColdPrivateBitValue ring root D =
        resetColdPrivateBitValue ring root C := by
    unfold resetColdPrivateBitValue
    apply ofFn_sum_eq
    intro j
    rw [hbit (j.val + 1) (by omega)
      (by have hh := j.isLt; omega)]
  have hleft := resetColdPrivateCarryZeroOfNoIR
    ring root C hnoC
  have hright := resetColdPrivateCarryZeroOfNoIR
    ring root D hnoD
  unfold resetColdPrivateHeadValue
  rw [hbits, hleft, hright]

/-- OLD ARMED with a set low bit creates a real IR carry and IWAIT.
This is the BANK row already present in the source, now projected
to the actual spatial protocol edge. -/
theorem resetColdPrivateArmedCarryPhysical {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hm : (C root).mode = .ARMED)
    (ht : (C (site ring root 1)).tok = .E)
    (hbit : (C (site ring root 1)).bit = true) :
    (((protocol q).step ring C root) root).mode = .IWAIT ∧
      (((protocol q).step ring C root)
        (site ring root 1)).bit = false ∧
      (((protocol q).step ring C root)
        (site ring root 1)).tok = .IR := by
  have hroot : (C root).pack.val = 0 := by
    simpa only [site] using hc 0 (by omega)
  have hone : (C (site ring root 1)).pack.val = 1 :=
    hc 1 (by have hb := resetTrialCompiledWidth q; omega)
  have hb : 0 < (compileAdvice q).b := by
    have hw := resetTrialCompiledWidth q
    omega
  have hpost :
      packNext (C root).pack.val
        (C (site ring root 1)).pack.val
        (compileAdvice q).b = 1 := by
    rw [hroot, hone]
    simp [packNext, hb]
  have hbank :
      (resetBankOld (C root)
        (C (site ring root 1))).1.mode = .IWAIT ∧
      (resetBankOld (C root)
        (C (site ring root 1))).2.bit = false ∧
      (resetBankOld (C root)
        (C (site ring root 1))).2.tok = .IR := by
    have h0 := resetColdLatchedPrivateArmedCarryRow
      (bankCell (C root) (C root).pack.val)
      (bankCell (C (site ring root 1))
        (C (site ring root 1)).pack.val)
      (compileAdvice q).b (compileAdvice q).theta
      (by change (C root).pack.val = 0; exact hroot)
      (by change (C root).grant = false; exact hg)
      (by change (C (site ring root 1)).pack.val = 1; exact hone)
      hm ht hbit (by omega)
    unfold resetBankOld
    rw [hpost]
    exact h0
  have htrip := resetPhysicalEdgeBankTrip ring C root
    (resetColdRootPortDistinct ring C root hc) hsp
  have hbitPhysical :
      (((protocol q).step ring C root)
        (site ring root 1)).bit =
      (resetBankOld (C root)
        (C (site ring root 1))).2.bit := by
    exact congrArg (fun z : Mode × Bool × BTok => z.2.1)
      htrip.2
  have htokPhysical :
      (((protocol q).step ring C root)
        (site ring root 1)).tok =
      (resetBankOld (C root)
        (C (site ring root 1))).2.tok := by
    exact congrArg (fun z : Mode × Bool × BTok => z.2.2)
      htrip.2
  exact ⟨(resetColdOutgoingRootModeLease
      ring C root hc hsp).1.trans hbank.1,
    hbitPhysical.trans hbank.2.1,
    htokPhysical.trans hbank.2.2⟩

/-- ARMED/E/zero-bit launch preserves the four-way shape and adds
one head, for an arbitrary already authenticated h below K.
No assumption of zero higher bits is used. -/
theorem resetColdPrivateArmedSetShape {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hsp : (compileAdvice q).useSmall = false)
    (h : Nat)
    (hbound : h < (compileAdvice q).K)
    (hm : (C root).mode = .ARMED)
    (hn : resetColdPrivateNoWorkers ring root C)
    (hvalue : resetColdPrivateHeadValue ring root C = h)
    (hbit : (C (site ring root 1)).bit = false) :
    ResetColdPrivateLiveShape ring root
        ((protocol q).step ring C root) ∧
      resetColdPrivateHeadValue ring root
        ((protocol q).step ring C root) =
      resetColdPrivateHeadValue ring root C + 1 := by
  have hb : 1 ≤ (compileAdvice q).b := by
    have hw := resetTrialCompiledWidth q
    omega
  have hrow := resetColdLatchedPhysicalArmedFirstSet
    ring C root hc hg hsp hm (hn 1 (by omega) hb) hbit
  have hrestBit : ∀ j : Nat, 2 ≤ j →
      j ≤ (compileAdvice q).b →
      (((protocol q).step ring C root)
        (site ring root j)).bit =
        (C (site ring root j)).bit := by
    intro j hj hjb
    rw [resetColdOutgoingRootOtherDigitsFrame
      ring C root hc j hj hjb]
  have hrestTok : ∀ j : Nat, 2 ≤ j →
      j ≤ (compileAdvice q).b →
      (((protocol q).step ring C root)
        (site ring root j)).tok = .E := by
    intro j hj hjb
    rw [resetColdOutgoingRootOtherDigitsFrame
      ring C root hc j hj hjb]
    exact hn j (by omega) hjb
  have hnewempty :
      resetColdPrivateNoWorkers ring root
        ((protocol q).step ring C root) := by
    intro j hj hjb
    by_cases hone : j = 1
    · subst j
      exact hrow.2.2
    · exact hrestTok j (by omega) hjb
  have hbitUp := resetColdPrivateBitLowUp
    ring root C ((protocol q).step ring C root)
    hbit hrow.2.1 hrestBit
  have hcarryOld := resetColdLatchedPrivateCarryEmpty
    ring root C hn
  have hcarryNew := resetColdLatchedPrivateCarryEmpty
    ring root ((protocol q).step ring C root) hnewempty
  have hheadUp :
      resetColdPrivateHeadValue ring root
        ((protocol q).step ring C root) =
          resetColdPrivateHeadValue ring root C + 1 := by
    unfold resetColdPrivateHeadValue
    rw [hbitUp, hcarryNew, hcarryOld]
  have hnewvalue :
      resetColdPrivateHeadValue ring root
        ((protocol q).step ring C root) = h + 1 := by
    rw [hheadUp, hvalue]
  constructor
  · exact Or.inr (Or.inl
      ⟨h, by omega, hrow.1, hnewempty, hnewvalue⟩)
  · exact hheadUp

/-- ARMED/E/one-bit carry launch is the other genuine +1 root
case. IR at digit one contributes weight two, precisely replacing
the cleared unit low bit and the additional head increment. -/
theorem resetColdPrivateArmedCarryShape {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hsp : (compileAdvice q).useSmall = false)
    (h : Nat)
    (hbound : h < (compileAdvice q).K)
    (hm : (C root).mode = .ARMED)
    (hn : resetColdPrivateNoWorkers ring root C)
    (hvalue : resetColdPrivateHeadValue ring root C = h)
    (hbit : (C (site ring root 1)).bit = true) :
    ResetColdPrivateLiveShape ring root
        ((protocol q).step ring C root) ∧
      resetColdPrivateHeadValue ring root
        ((protocol q).step ring C root) =
      resetColdPrivateHeadValue ring root C + 1 := by
  have hb : 1 ≤ (compileAdvice q).b := by
    have hw := resetTrialCompiledWidth q
    omega
  have hrow := resetColdPrivateArmedCarryPhysical
    ring root C hc hg hsp hm (hn 1 (by omega) hb) hbit
  have hrestBit : ∀ j : Nat, 2 ≤ j →
      j ≤ (compileAdvice q).b →
      (((protocol q).step ring C root)
        (site ring root j)).bit =
        (C (site ring root j)).bit := by
    intro j hj hjb
    rw [resetColdOutgoingRootOtherDigitsFrame
      ring C root hc j hj hjb]
  have hrestTok : ∀ j : Nat, 2 ≤ j →
      j ≤ (compileAdvice q).b →
      (((protocol q).step ring C root)
        (site ring root j)).tok = .E := by
    intro j hj hjb
    rw [resetColdOutgoingRootOtherDigitsFrame
      ring C root hc j hj hjb]
    exact hn j (by omega) hjb
  have hnewone :
      resetColdPrivateOnlyWorker ring root
        ((protocol q).step ring C root) 1 .IR := by
    refine ⟨by omega, hb, hrow.2.2, ?_⟩
    intro j hj hjb hne
    exact hrestTok j (by omega) hjb
  have hbitDown := resetColdPrivateBitLowUp
    ring root ((protocol q).step ring C root) C
    hrow.2.1 hbit
    (by
      intro j hj hjb
      exact (hrestBit j hj hjb).symm)
  have hcarryOld := resetColdLatchedPrivateCarryEmpty
    ring root C hn
  have hcarryNew := resetColdPrivateCarryFirstWeight
    ring root ((protocol q).step ring C root)
    hrow.2.2 (by
      intro j hj hjb
      rw [hrestTok j hj hjb]
      intro he
      cases he)
  have hheadUp :
      resetColdPrivateHeadValue ring root
        ((protocol q).step ring C root) =
          resetColdPrivateHeadValue ring root C + 1 := by
    unfold resetColdPrivateHeadValue
    rw [hcarryOld, hcarryNew]
    omega
  have hnewvalue :
      resetColdPrivateHeadValue ring root
        ((protocol q).step ring C root) = h + 1 := by
    rw [hheadUp, hvalue]
  constructor
  · exact Or.inr (Or.inr (Or.inr
      ⟨h, 1, .IR, by omega, hrow.1, hnewone,
        Or.inl rfl, hnewvalue⟩))
  · exact hheadUp

/-- An actual ARMED LIVE root service, whether its old low bit
is zero or one, is authenticated and increases the numerical head
by exactly one. The root-grant guard is forced by LIVE. -/
theorem resetColdPrivateArmedRootLive {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (h : Nat)
    (hbound : h < (compileAdvice q).K)
    (hm : (C root).mode = .ARMED)
    (hn : resetColdPrivateNoWorkers ring root C)
    (hvalue : resetColdPrivateHeadValue ring root C = h)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) root = .live D started') :
    ResetColdPrivateLiveShape ring root D ∧
      resetColdPrivateHeadValue ring root D =
        resetColdPrivateHeadValue ring root C + 1 := by
  have hg := resetColdPrivateLiveOutgoingGrantFree
    ring root C D started started' hc hsp hnext
  have hp := resetColdPrivateLivePhysical
    ring root root C D started started' hnext
  cases hbit : (C (site ring root 1)).bit with
  | false =>
      rw [hp]
      exact resetColdPrivateArmedSetShape ring root C
        hc hg hsp h hbound hm hn hvalue hbit
  | true =>
      rw [hp]
      exact resetColdPrivateArmedCarryShape ring root C
        hc hg hsp h hbound hm hn hvalue hbit

/-- The generic CSTART-to-CWAIT comparator launch preserves the
head value, even after many earlier increments and arbitrary higher
bits. The CR1 prefix property is established at digit one. -/
theorem resetColdPrivateCStartLaunchShape {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hsp : (compileAdvice q).useSmall = false)
    (h : Nat)
    (hbound : h + 1 ≤ (compileAdvice q).K)
    (hm : (C root).mode = .CSTART)
    (hn : resetColdPrivateNoWorkers ring root C)
    (hvalue : resetColdPrivateHeadValue ring root C = h + 1) :
    ResetColdPrivateLiveShape ring root
        ((protocol q).step ring C root) ∧
      resetColdPrivateHeadValue ring root
        ((protocol q).step ring C root) =
        resetColdPrivateHeadValue ring root C := by
  have hb : 1 ≤ (compileAdvice q).b := by
    have hw := resetTrialCompiledWidth q
    omega
  have hrow := resetColdPrivateCStartComparatorPhysical
    ring root C hc hg hsp hm (hn 1 (by omega) hb)
  have hrestBit : ∀ j : Nat, 2 ≤ j →
      j ≤ (compileAdvice q).b →
      (((protocol q).step ring C root)
        (site ring root j)).bit =
        (C (site ring root j)).bit := by
    intro j hj hjb
    rw [resetColdOutgoingRootOtherDigitsFrame
      ring C root hc j hj hjb]
  have hrestTok : ∀ j : Nat, 2 ≤ j →
      j ≤ (compileAdvice q).b →
      (((protocol q).step ring C root)
        (site ring root j)).tok = .E := by
    intro j hj hjb
    rw [resetColdOutgoingRootOtherDigitsFrame
      ring C root hc j hj hjb]
    exact hn j (by omega) hjb
  have hbits : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      (((protocol q).step ring C root)
        (site ring root j)).bit =
        (C (site ring root j)).bit := by
    intro j hj hjb
    by_cases hjone : j = 1
    · subst j
      exact hrow.2.1
    · exact hrestBit j (by omega) hjb
  have hnoC : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      (C (site ring root j)).tok ≠ .IR := by
    intro j hj hjb
    rw [hn j hj hjb]
    intro he
    cases he
  have hnoD : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      (((protocol q).step ring C root)
        (site ring root j)).tok ≠ .IR := by
    intro j hj hjb
    by_cases hjone : j = 1
    · subst j
      rw [hrow.2.2]
      split <;> (intro he; cases he)
    · rw [hrestTok j (by omega) hjb]
      intro he
      cases he
  have hhead := resetColdPrivateHeadNoIRBitFrame
    ring root C ((protocol q).step ring C root) hbits hnoC hnoD
  have hchoice :
      resetColdPrivateComparatorToken
        (if (C (site ring root 1)).bit ==
          (compileAdvice q).theta 0 then .CR1 else .CR0) := by
    unfold resetColdPrivateComparatorToken
    split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
  have hnewone :
      resetColdPrivateOnlyWorker ring root
        ((protocol q).step ring C root) 1
          (if (C (site ring root 1)).bit ==
            (compileAdvice q).theta 0 then .CR1 else .CR0) := by
    refine ⟨by omega, hb, hrow.2.2, ?_⟩
    intro j hj hjb hne
    exact hrestTok j (by omega) hjb
  have hprefix :
      (if (C (site ring root 1)).bit ==
        (compileAdvice q).theta 0 then BTok.CR1 else BTok.CR0) =
          .CR1 →
      resetColdPrivateMatchedPrefix ring root
        ((protocol q).step ring C root) 1 := by
    intro htok
    have hmatch :
        (C (site ring root 1)).bit =
          (compileAdvice q).theta 0 := by
      by_cases heq : (C (site ring root 1)).bit =
          (compileAdvice q).theta 0
      · exact heq
      · have hfalse :
            (if (C (site ring root 1)).bit ==
              (compileAdvice q).theta 0
            then BTok.CR1 else BTok.CR0) = .CR0 := by
          simp [heq]
        rw [hfalse] at htok
        cases htok
    intro i hi hij hib
    have hie : i = 1 := by omega
    subst i
    change (((protocol q).step ring C root)
      (site ring root 1)).bit = (compileAdvice q).theta 0
    rw [hrow.2.1]
    exact hmatch
  have hnotreturn :
      (if (C (site ring root 1)).bit ==
        (compileAdvice q).theta 0 then BTok.CR1 else BTok.CR0) =
          .CL1 →
      resetColdPrivateMatchedPrefix ring root
        ((protocol q).step ring C root)
          (compileAdvice q).b := by
    intro htok
    split at htok <;> cases htok
  have hnewvalue :
      resetColdPrivateHeadValue ring root
        ((protocol q).step ring C root) = h + 1 := by
    rw [hhead, hvalue]
  constructor
  · exact Or.inr (Or.inr (Or.inl
      ⟨h, 1,
        (if (C (site ring root 1)).bit ==
          (compileAdvice q).theta 0 then .CR1 else .CR0),
        hbound, hrow.1, hnewone, hchoice,
        hnewvalue, hprefix, hnotreturn⟩))
  · exact hhead

/-- A CSTART LIVE root service launches the comparator for an
arbitrary completed head; no first-head seed hypothesis is used. -/
theorem resetColdPrivateCStartRootLive {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (h : Nat)
    (hbound : h + 1 ≤ (compileAdvice q).K)
    (hm : (C root).mode = .CSTART)
    (hn : resetColdPrivateNoWorkers ring root C)
    (hvalue : resetColdPrivateHeadValue ring root C = h + 1)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) root = .live D started') :
    ResetColdPrivateLiveShape ring root D ∧
      resetColdPrivateHeadValue ring root D =
        resetColdPrivateHeadValue ring root C := by
  have hg := resetColdPrivateLiveOutgoingGrantFree
    ring root C D started started' hc hsp hnext
  have hp := resetColdPrivateLivePhysical
    ring root root C D started started' hnext
  rw [hp]
  exact resetColdPrivateCStartLaunchShape ring root C
    hc hg hsp h hbound hm hn hvalue

/-- Literal waiting-mode root service with a nonreturn first-digit
token does not change the first digit BIT. The existing
root WAIT theorem already gives the root mode, lease and token. -/
theorem resetColdPrivateWaitNonreturnBitBank
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : x.role = 0) (hy : y.role = 1)
    (hg : x.grant = false) (hb : 1 < b)
    (hm : isWaitMode x.mode = true)
    (ht : isRetTok y.tok = false) :
    (bankPair x y 1 b theta).2.bit = y.bit := by
  have hbge : 1 ≤ b := by omega
  have hbne : b ≠ 1 := by omega
  cases hmode : x.mode <;> cases htok : y.tok <;>
    simp [isWaitMode, hmode] at hm <;>
    simp [isRetTok, htok] at ht <;>
    by_cases hlease : 1 < x.lease <;>
    simp [bankPair, hx, hy, hg, hbge, hbne,
      hmode, htok, hlease, isWaitMode, isRetTok,
      Id.run_pure, Id.run_bind] <;>
    repeat (first | rfl | omega |
      (split <;> simp [Id.run_pure, Id.run_bind]))

/-- The preceding bit row is the actual first protected digit of
the physical root-outgoing protocol step. -/
theorem resetColdPrivatePhysicalWaitNonreturnBit {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hm : isWaitMode (C root).mode = true)
    (ht : isRetTok (C (site ring root 1)).tok = false) :
    (((protocol q).step ring C root)
      (site ring root 1)).bit =
        (C (site ring root 1)).bit := by
  have hroot : (C root).pack.val = 0 := by
    simpa only [site] using hc 0 (by omega)
  have hone : (C (site ring root 1)).pack.val = 1 :=
    hc 1 (by have hw := resetTrialCompiledWidth q; omega)
  have hb : 1 < (compileAdvice q).b :=
    resetTrialCompiledWidth q
  have hpost :
      packNext (C root).pack.val
        (C (site ring root 1)).pack.val
        (compileAdvice q).b = 1 := by
    rw [hroot, hone]
    have hpos : 0 < (compileAdvice q).b := by omega
    simp [packNext, hpos]
  have hbank :
      (resetBankOld (C root)
        (C (site ring root 1))).2.bit =
          (C (site ring root 1)).bit := by
    have h0 := resetColdPrivateWaitNonreturnBitBank
      (bankCell (C root) (C root).pack.val)
      (bankCell (C (site ring root 1))
        (C (site ring root 1)).pack.val)
      (compileAdvice q).b (compileAdvice q).theta
      (by change (C root).pack.val = 0; exact hroot)
      (by change (C (site ring root 1)).pack.val = 1; exact hone)
      (by change (C root).grant = false; exact hg)
      hb hm ht
    unfold resetBankOld
    rw [hpost]
    exact h0
  have htrip := resetPhysicalEdgeBankTrip ring C root
    (resetColdRootPortDistinct ring C root hc) hsp
  have hp :=
    congrArg (fun z : Mode × Bool × BTok => z.2.1) htrip.2
  exact hp.trans hbank

/-- A CWAIT/IWAIT root wait with nonreturn first-digit token
cannot erase or duplicate any worker. If the observer remains LIVE,
the watchdog has not expired, so the mode and full BANK phase shape
are preserved, and the numerical head is fixed. -/
theorem resetColdPrivateWaitRootLive {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hm : isWaitMode (C root).mode = true)
    (ht : isRetTok (C (site ring root 1)).tok = false)
    (hshape : ResetColdPrivateLiveShape ring root C)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) root = .live D started') :
    ResetColdPrivateLiveShape ring root D ∧
      resetColdPrivateHeadValue ring root D =
        resetColdPrivateHeadValue ring root C := by
  have hg := resetColdPrivateLiveOutgoingGrantFree
    ring root C D started started' hc hsp hnext
  have hfields := resetColdPhysicalWaitNonreturn
    ring C root hc hg hsp hm ht
  have hfirstBit := resetColdPrivatePhysicalWaitNonreturnBit
    ring root C hc hg hsp hm ht
  have hnot := resetColdPrivateLiveRootNotReset
    ring root root C D started started' hnext
  have hlease : 1 < (C root).lease.val := by
    by_cases hl : 1 < (C root).lease.val
    · exact hl
    · have hreset :
          (((protocol q).step ring C root) root).mode = .RESET := by
        rw [hfields.1]
        simp [resetColdWaitTickMode, hl]
      exact False.elim (hnot hreset)
  have hmode :
      (((protocol q).step ring C root) root).mode =
        (C root).mode := by
    rw [hfields.1]
    simp [resetColdWaitTickMode, hlease]
  have hbits : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      (((protocol q).step ring C root)
        (site ring root j)).bit =
        (C (site ring root j)).bit := by
    intro j hj hjb
    by_cases hone : j = 1
    · subst j
      exact hfirstBit
    · rw [resetColdOutgoingRootOtherDigitsFrame
        ring C root hc j (by omega) hjb]
  have htoks : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      (((protocol q).step ring C root)
        (site ring root j)).tok =
        (C (site ring root j)).tok := by
    intro j hj hjb
    by_cases hone : j = 1
    · subst j
      exact hfields.2.2
    · rw [resetColdOutgoingRootOtherDigitsFrame
        ring C root hc j (by omega) hjb]
  have hp := resetColdPrivateLivePhysical
    ring root root C D started started' hnext
  rw [hp]
  exact ⟨resetColdPrivateLiveShapeBankFrame ring root
    C ((protocol q).step ring C root)
    hmode hbits htoks hshape,
    resetColdPrivateHeadBankFrame ring root
      C ((protocol q).step ring C root) hbits htoks⟩

/-- An incoming CSTART service on an exterior predecessor preserves
all digit BANK fields and the CSTART mode, hence the four-way shape.
The role classification is supplied explicitly; no ring-size
assumption is hidden. -/
theorem resetColdPrivateIncomingCStartLive {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hpred : ring.rightNeighbor e = root)
    (hrole : (C e).pack.val = (compileAdvice q).b ∨
      (C e).pack.val = (compileAdvice q).b + 1)
    (hex : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b → e ≠ site ring root j)
    (hm : (C root).mode = .CSTART)
    (hshape : ResetColdPrivateLiveShape ring root C)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) e = .live D started') :
    ResetColdPrivateLiveShape ring root D ∧
      resetColdPrivateHeadValue ring root D =
        resetColdPrivateHeadValue ring root C := by
  have hmode := (resetColdPhysicalIncomingCStart
    ring C root e hc hg hsp hpred hrole hm).1
  have hroot : (((protocol q).step ring C e) root).mode =
      (C root).mode := hmode.trans hm.symm
  have hframe : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      ((protocol q).step ring C e) (site ring root j) =
        C (site ring root j) := by
    intro j hj hjb
    exact resetColdIncomingRootDigitFrame
      ring C root e hc hpred hex j hj hjb
  have hbits : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      (((protocol q).step ring C e) (site ring root j)).bit =
        (C (site ring root j)).bit := by
    intro j hj hjb
    rw [hframe j hj hjb]
  have htoks : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      (((protocol q).step ring C e) (site ring root j)).tok =
        (C (site ring root j)).tok := by
    intro j hj hjb
    rw [hframe j hj hjb]
  have hp := resetColdPrivateLivePhysical
    ring root e C D started started' hnext
  rw [hp]
  exact ⟨resetColdPrivateLiveShapeBankFrame ring root
    C ((protocol q).step ring C e)
    hroot hbits htoks hshape,
    resetColdPrivateHeadBankFrame ring root
      C ((protocol q).step ring C e) hbits htoks⟩

/-- On an exterior incoming waiting-mode root edge, continued LIVE
forces a nonexpired lease and hence a mode frame. The entire shape
and head are preserved. This is distinct from the incoming ARMED
edge, which is preempted to recovery. -/
theorem resetColdPrivateIncomingWaitLive {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hpred : ring.rightNeighbor e = root)
    (hrole : (C e).pack.val = (compileAdvice q).b ∨
      (C e).pack.val = (compileAdvice q).b + 1)
    (hex : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b → e ≠ site ring root j)
    (hm : isWaitMode (C root).mode = true)
    (hshape : ResetColdPrivateLiveShape ring root C)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) e = .live D started') :
    ResetColdPrivateLiveShape ring root D ∧
      resetColdPrivateHeadValue ring root D =
        resetColdPrivateHeadValue ring root C := by
  have hfields := resetColdPhysicalIncomingWait
    ring C root e hc hg hsp hpred hrole hm
  have hnot := resetColdPrivateLiveRootNotReset
    ring root e C D started started' hnext
  have hlease : 1 < (C root).lease.val := by
    by_cases hl : 1 < (C root).lease.val
    · exact hl
    · have hreset :
          (((protocol q).step ring C e) root).mode = .RESET := by
        rw [hfields.1]
        simp [resetColdWaitTickMode, hl]
      exact False.elim (hnot hreset)
  have hroot :
      (((protocol q).step ring C e) root).mode =
        (C root).mode := by
    rw [hfields.1]
    simp [resetColdWaitTickMode, hlease]
  have hframe : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      ((protocol q).step ring C e) (site ring root j) =
        C (site ring root j) := by
    intro j hj hjb
    exact resetColdIncomingRootDigitFrame
      ring C root e hc hpred hex j hj hjb
  have hbits : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      (((protocol q).step ring C e) (site ring root j)).bit =
        (C (site ring root j)).bit := by
    intro j hj hjb
    rw [hframe j hj hjb]
  have htoks : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      (((protocol q).step ring C e) (site ring root j)).tok =
        (C (site ring root j)).tok := by
    intro j hj hjb
    rw [hframe j hj hjb]
  have hp := resetColdPrivateLivePhysical
    ring root e C D started started' hnext
  rw [hp]
  exact ⟨resetColdPrivateLiveShapeBankFrame ring root
    C ((protocol q).step ring C e)
    hroot hbits htoks hshape,
    resetColdPrivateHeadBankFrame ring root
      C ((protocol q).step ring C e) hbits htoks⟩

end Counter
end L3

/-!
Binary theta uniqueness and the literal CL1 root return.

The BANK comparison is an equality scan in least-significant-bit
order, not a magnitude comparator. A first mismatching low digit
being smaller than theta does NOT by itself imply the full word is
below K. The sound strict inequality below uses the reachable head
upper bound and binary uniqueness; it holds for a mismatch of
either orientation. CL0 mismatch provenance is still an additional
inductive obligation, not part of the earlier four-way shape.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- The sum of the weights of an arbitrary finite Boolean digit
word, indexed from the least significant digit. -/
def resetColdPrivateBinarySum (bits : Nat → Bool) (width : Nat) : Nat :=
  (List.ofFn (fun j : Fin width =>
    if bits j.val then 2 ^ j.val else 0)).sum

/-- Adding one most-significant slot doubles the weights of the
shifted remainder. This recursion uses only core List.ofFn. -/
theorem resetColdPrivateBinarySumSucc
    (bits : Nat → Bool) (width : Nat) :
    resetColdPrivateBinarySum bits (width + 1) =
      (if bits 0 then 1 else 0) +
        2 * resetColdPrivateBinarySum (fun j => bits (j + 1)) width := by
  have htail :
      (List.ofFn (fun j : Fin width =>
        if bits (j.val + 1) then 2 ^ (j.val + 1) else 0)).sum =
      2 * (List.ofFn (fun j : Fin width =>
        if bits (j.val + 1) then 2 ^ j.val else 0)).sum := by
    calc
      (List.ofFn (fun j : Fin width =>
        if bits (j.val + 1) then 2 ^ (j.val + 1) else 0)).sum =
        (List.ofFn (fun j : Fin width =>
          2 * (if bits (j.val + 1) then 2 ^ j.val else 0))).sum := by
            apply ofFn_sum_eq
            intro j
            cases hb : bits (j.val + 1) with
            | false => simp [hb]
            | true => simp [hb, Nat.pow_succ, Nat.mul_comm]
      _ = 2 * (List.ofFn (fun j : Fin width =>
        if bits (j.val + 1) then 2 ^ j.val else 0)).sum := by
          rw [ofFn_sum_mul_left]
  unfold resetColdPrivateBinarySum
  rw [List.ofFn_succ, List.sum_cons]
  change (if bits 0 then 1 else 0) +
    (List.ofFn (fun j : Fin width =>
      if bits (j.val + 1) then 2 ^ (j.val + 1) else 0)).sum =
    (if bits 0 then 1 else 0) +
      2 * (List.ofFn (fun j : Fin width =>
        if bits (j.val + 1) then 2 ^ j.val else 0)).sum
  exact congrArg (fun v : Nat => (if bits 0 then 1 else 0) + v) htail

/-- Every residue modulo two is one of its two Boolean digits. -/
private theorem resetColdPrivateBinaryLow (a : Nat) :
    (if a % 2 == 1 then 1 else 0) = a % 2 := by
  have hbound : a % 2 < 2 := Nat.mod_lt a (by decide)
  by_cases hone : a % 2 = 1
  · simp [hone]
  · have hzero : a % 2 = 0 := by omega
    simp [hzero]

/-- Binary reconstruction, including the unrecovered high quotient.
The proof uses the quotient-and-remainder equation at base two,
rather than postulating an expansion of the compiled threshold. -/
theorem resetColdPrivateBinaryReconstruct :
    ∀ width a : Nat,
      resetColdPrivateBinarySum
        (fun j => a / 2 ^ j % 2 == 1) width +
        2 ^ width * (a / 2 ^ width) = a := by
  intro width
  induction width with
  | zero =>
      intro a
      simp [resetColdPrivateBinarySum]
  | succ width ih =>
      intro a
      have hdiv (j : Nat) :
          a / 2 ^ (j + 1) = (a / 2) / 2 ^ j := by
        rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
        ac_rfl
      have htail :
          resetColdPrivateBinarySum
            (fun j => a / 2 ^ (j + 1) % 2 == 1) width =
          resetColdPrivateBinarySum
            (fun j => (a / 2) / 2 ^ j % 2 == 1) width := by
        unfold resetColdPrivateBinarySum
        apply ofFn_sum_eq
        intro j
        simp only [hdiv]
      have hpower :
          2 ^ (width + 1) * (a / 2 ^ (width + 1)) =
            2 * (2 ^ width * ((a / 2) / 2 ^ width)) := by
        rw [hdiv width, Nat.pow_succ]
        ac_rfl
      have hlow :
          (if a / 2 ^ 0 % 2 == 1 then 1 else 0) = a % 2 := by
        simpa only [Nat.pow_zero, Nat.div_one] using
          (resetColdPrivateBinaryLow a)
      have hhalf := ih (a / 2)
      have htwice := congrArg (fun v : Nat => 2 * v) hhalf
      rw [Nat.mul_add] at htwice
      have hquot := Nat.div_add_mod a 2
      rw [resetColdPrivateBinarySumSucc, htail, hpower, hlow]
      omega

/-- When the high quotient vanishes, theta's complete binary sum
is exactly the integer represented, with no asymptotic assumptions. -/
theorem resetColdPrivateBinaryFull (a width : Nat)
    (hwidth : a < 2 ^ width) :
    resetColdPrivateBinarySum
      (fun j => a / 2 ^ j % 2 == 1) width = a := by
  have h := resetColdPrivateBinaryReconstruct width a
  have hzero : a / 2 ^ width = 0 := Nat.div_eq_of_lt hwidth
  rw [hzero] at h
  simpa only [Nat.mul_zero, Nat.add_zero] using h

/-- Every Boolean representation of a fixed width is unique.
In the successor case parity identifies the low digit, and the
remaining quotient identifies the shifted word. -/
theorem resetColdPrivateBinaryUnique :
    ∀ width : Nat, ∀ bits other : Nat → Bool,
      resetColdPrivateBinarySum bits width =
        resetColdPrivateBinarySum other width →
      ∀ j : Nat, j < width → bits j = other j := by
  intro width
  induction width with
  | zero =>
      intro bits other he j hj
      omega
  | succ width ih =>
      intro bits other he j hj
      rw [resetColdPrivateBinarySumSucc bits width,
        resetColdPrivateBinarySumSucc other width] at he
      have hlow : bits 0 = other 0 := by
        cases hb : bits 0 <;> cases ho : other 0 <;>
          simp [hb, ho] at he ⊢ <;> omega
      have htail :
          resetColdPrivateBinarySum (fun k => bits (k + 1)) width =
          resetColdPrivateBinarySum (fun k => other (k + 1)) width := by
        rw [hlow] at he
        omega
      cases j with
      | zero =>
          exact hlow
      | succ k =>
          exact ih (fun i => bits (i + 1))
            (fun i => other (i + 1)) htail k (by omega)

/-- Physical BANK bit-value is literally the finite Boolean-weight
sum, independent of the active worker and of other protocol fields. -/
theorem resetColdPrivateBitValueAsBinary {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) :
    resetColdPrivateBitValue ring root C =
      resetColdPrivateBinarySum
        (fun j => (C (site ring root (j + 1))).bit)
        (compileAdvice q).b := by
  unfold resetColdPrivateBitValue resetColdPrivateBinarySum
  apply ofFn_sum_eq
  intro j
  cases hb : (C (site ring root (j.val + 1))).bit <;> simp [hb]

/-- Any full theta match of the b actual protected digits has
precisely the compiled target bit-value K, provided K < 2^b. -/
theorem resetColdPrivateFullThetaBitValue {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hmatch : resetColdPrivateMatchedPrefix ring root C
      (compileAdvice q).b) :
    resetColdPrivateBitValue ring root C =
      (compileAdvice q).K := by
  have hbits :
      resetColdPrivateBinarySum
        (fun j => (C (site ring root (j + 1))).bit)
        (compileAdvice q).b =
      resetColdPrivateBinarySum (compileAdvice q).theta
        (compileAdvice q).b := by
    unfold resetColdPrivateBinarySum
    apply ofFn_sum_eq
    intro j
    have hj := hmatch (j.val + 1) (by omega)
      (by have hh := j.isLt; omega)
      (by have hh := j.isLt; omega)
    have hsub : j.val + 1 - 1 = j.val := by omega
    rw [hsub] at hj
    change (if (C (site ring root (j.val + 1))).bit
      then 2 ^ j.val else 0) =
      (if (compileAdvice q).theta j.val then 2 ^ j.val else 0)
    exact congrArg (fun z : Bool => if z then 2 ^ j.val else 0) hj
  calc
    resetColdPrivateBitValue ring root C =
        resetColdPrivateBinarySum
          (fun j => (C (site ring root (j + 1))).bit)
          (compileAdvice q).b :=
      resetColdPrivateBitValueAsBinary ring root C
    _ = resetColdPrivateBinarySum (compileAdvice q).theta
          (compileAdvice q).b := hbits
    _ = (compileAdvice q).K := by
      change resetColdPrivateBinarySum
        (fun j => (compileAdvice q).K / 2 ^ j % 2 == 1)
        (compileAdvice q).b = (compileAdvice q).K
      exact resetColdPrivateBinaryFull
        (compileAdvice q).K (compileAdvice q).b hwidth

/-- Conversely, equality of the physical bit-value with K
forces every protected digit to agree with theta. -/
theorem resetColdPrivateThetaOfBitValue {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hvalue : resetColdPrivateBitValue ring root C =
      (compileAdvice q).K)
    (i : Nat) (hi : 1 ≤ i) (hib : i ≤ (compileAdvice q).b) :
    (C (site ring root i)).bit =
      (compileAdvice q).theta (i - 1) := by
  have hfull :
      resetColdPrivateBinarySum (compileAdvice q).theta
        (compileAdvice q).b = (compileAdvice q).K := by
    change resetColdPrivateBinarySum
      (fun j => (compileAdvice q).K / 2 ^ j % 2 == 1)
      (compileAdvice q).b = (compileAdvice q).K
    exact resetColdPrivateBinaryFull
      (compileAdvice q).K (compileAdvice q).b hwidth
  have hsums :
      resetColdPrivateBinarySum
        (fun j => (C (site ring root (j + 1))).bit)
          (compileAdvice q).b =
      resetColdPrivateBinarySum (compileAdvice q).theta
          (compileAdvice q).b := by
    calc
      resetColdPrivateBinarySum
          (fun j => (C (site ring root (j + 1))).bit)
          (compileAdvice q).b =
        resetColdPrivateBitValue ring root C :=
          (resetColdPrivateBitValueAsBinary ring root C).symm
      _ = (compileAdvice q).K := hvalue
      _ = resetColdPrivateBinarySum (compileAdvice q).theta
          (compileAdvice q).b := hfull.symm
  have hu := resetColdPrivateBinaryUnique
    (compileAdvice q).b
    (fun j => (C (site ring root (j + 1))).bit)
    (compileAdvice q).theta hsums (i - 1) (by omega)
  have hindex : i - 1 + 1 = i := by omega
  change (C (site ring root (i - 1 + 1))).bit =
    (compileAdvice q).theta (i - 1) at hu
  rw [hindex] at hu
  exact hu

/-- Under the actual bounded-head invariant, one mismatching
digit forces the head STRICTLY below K. The orientation of that
mismatch is irrelevant; this avoids the invalid low-to-high
lexicographic comparison argument. -/
theorem resetColdPrivateMismatchBelowK {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hnoIR : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      (C (site ring root j)).tok ≠ .IR)
    (hbound : resetColdPrivateHeadValue ring root C ≤
      (compileAdvice q).K)
    (i : Nat) (hi : 1 ≤ i) (hib : i ≤ (compileAdvice q).b)
    (hmismatch : (C (site ring root i)).bit ≠
      (compileAdvice q).theta (i - 1)) :
    resetColdPrivateHeadValue ring root C <
      (compileAdvice q).K := by
  have hcarry := resetColdPrivateCarryZeroOfNoIR
    ring root C hnoIR
  have hneq :
      resetColdPrivateHeadValue ring root C ≠
        (compileAdvice q).K := by
    intro he
    have hbit :
        resetColdPrivateBitValue ring root C =
          (compileAdvice q).K := by
      unfold resetColdPrivateHeadValue at he
      rw [hcarry] at he
      omega
    exact hmismatch (resetColdPrivateThetaOfBitValue
      ring root C hwidth hbit i hi hib)
  omega

/-- Exactly one comparator worker (of any CR/CL flavor) carries
no pending IR. -/
theorem resetColdPrivateComparatorNoIR {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (j : Nat) (t : BTok)
    (hworker : resetColdPrivateOnlyWorker ring root C j t)
    (htype : resetColdPrivateComparatorToken t) :
    ∀ i : Nat, 1 ≤ i → i ≤ (compileAdvice q).b →
      (C (site ring root i)).tok ≠ .IR := by
  have hnot : t ≠ .IR := by
    intro he
    rcases htype with hcr | hcr | hcl | hcl
    · rw [hcr] at he
      cases he
    · rw [hcr] at he
      cases he
    · rw [hcl] at he
      cases he
    · rw [hcl] at he
      cases he
  intro i hi hib
  by_cases hij : i = j
  · subst i
    rw [hworker.2.2.1]
    exact hnot
  · rw [hworker.2.2.2 i hi hib hij]
    intro he
    cases he

/-- Full theta comparison in a one-worker CWAIT phase has
actual head K, not merely matching individual Boolean digits. -/
theorem resetColdPrivateComparatorMatchedHead {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (j : Nat) (t : BTok)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hworker : resetColdPrivateOnlyWorker ring root C j t)
    (htype : resetColdPrivateComparatorToken t)
    (hmatch : resetColdPrivateMatchedPrefix ring root C
      (compileAdvice q).b) :
    resetColdPrivateHeadValue ring root C =
      (compileAdvice q).K := by
  have hbits := resetColdPrivateFullThetaBitValue
    ring root C hwidth hmatch
  have hnoIR := resetColdPrivateComparatorNoIR
    ring root C j t hworker htype
  have hcarry := resetColdPrivateCarryZeroOfNoIR
    ring root C hnoIR
  unfold resetColdPrivateHeadValue
  rw [hbits, hcarry, Nat.add_zero]

/-- The literal OLD BANK success predicate requires CL1 at the
first protected digit; a delivered grant is not this success. -/
theorem resetColdPrivateSuccessFirstCL1 {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Config q n)
    (hs : resetColdPrivateSuccessAt ring root C e) :
    (C (site ring root 1)).tok = .CL1 := by
  obtain ⟨he, hs⟩ := hs
  subst e
  change bankSuccess
    (bankCell (C root) (C root).pack.val)
    (bankCell (C (site ring root 1))
      (C (site ring root 1)).pack.val)
    (packNext (C root).pack.val
      (C (site ring root 1)).pack.val (compileAdvice q).b)
    (compileAdvice q).b = true at hs
  by_cases ht : (C (site ring root 1)).tok = .CL1
  · exact ht
  · have hf : bankSuccess
        (bankCell (C root) (C root).pack.val)
        (bankCell (C (site ring root 1))
          (C (site ring root 1)).pack.val)
        (packNext (C root).pack.val
          (C (site ring root 1)).pack.val (compileAdvice q).b)
        (compileAdvice q).b = false := by
      simp [bankSuccess, bankCell, ht]
    rw [hf] at hs
    cases hs

/-- The CL1 success clause of HeadRows follows immediately from
the existing four-phase shape and binary theta reconstruction.
This theorem makes no assumption on comparator histories beyond
what the shape itself records. -/
theorem resetColdPrivateSuccessHeadOfShape {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Config q n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hshape : ResetColdPrivateLiveShape ring root C)
    (hs : resetColdPrivateSuccessAt ring root C e) :
    resetColdPrivateHeadValue ring root C =
      (compileAdvice q).K := by
  have hmode := resetColdPrivateSuccessRequiresCWait
    ring root e C hs
  have htok := resetColdPrivateSuccessFirstCL1
    ring root e C hs
  have hb : 1 ≤ (compileAdvice q).b := by
    have hw := resetTrialCompiledWidth q
    omega
  have hmatch := resetColdPrivateLiveShapeCL1Matches
    ring root C 1 hshape (by omega) hb htok
  rcases hshape with harm | hrest
  · obtain ⟨h, hh, hm, hw, hvalue⟩ := harm
    rw [hm] at hmode
    cases hmode
  · rcases hrest with hstart | hrest
    · obtain ⟨h, hh, hm, hw, hvalue⟩ := hstart
      rw [hm] at hmode
      cases hmode
    · rcases hrest with hcompare | hcarry
      · obtain ⟨h, j, t, hbound, hm, hworker,
          htype, hvalue, hprefix, hfull⟩ := hcompare
        exact resetColdPrivateComparatorMatchedHead
          ring root C j t hwidth hworker htype hmatch
      · obtain ⟨h, j, t, hbound, hm, hworker,
          htype, hvalue⟩ := hcarry
        rw [hm] at hmode
        cases hmode

/-- The third HeadRows clause, including the observer's actual
success transition; only the phase induction is still missing. -/
theorem resetColdPrivateSuccessObserverHeadOfShape {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C D : Config q n) (started : Bool)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hshape : ResetColdPrivateLiveShape ring root C)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) e = .success D) :
    resetColdPrivateHeadValue ring root C =
      (compileAdvice q).K := by
  exact resetColdPrivateSuccessHeadOfShape ring root e C
    hwidth hshape
    (resetColdLatchedSuccessRequiresOldGuard
      ring root e C D started hnext)

end Counter
end L3

/-!
Strengthened comparator provenance and literal BANK row lemmas.

The CR token at physical digit j has checked precisely digits 1..j,
equivalently theta indices strictly below j. CL records the entire
comparison. The negative provenance is additional to the
four-phase shape; no reachability or word induction is assumed here.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- A mismatch somewhere in an explicitly bounded, low-first
comparison prefix. The physical digit index starts at one. -/
def resetColdPrivateMismatchPrefix {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (j : Nat) : Prop :=
  ∃ i : Nat, 1 ≤ i ∧ i ≤ j ∧
    i ≤ (compileAdvice q).b ∧
    (C (site ring root i)).bit ≠
      (compileAdvice q).theta (i - 1)

/-- The existing four-phase shape certifies positive comparator
provenance. The only missing information is negative provenance:
CR0 means a mismatch within the checked prefix; CL0 means a
mismatch in the whole word. -/
def ResetColdPrivateLiveShapeAuth {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) : Prop :=
  ResetColdPrivateLiveShape ring root C ∧
    (∀ j : Nat, 1 ≤ j → j ≤ (compileAdvice q).b →
      (C (site ring root j)).tok = .CR0 →
        resetColdPrivateMismatchPrefix ring root C j) ∧
    (∀ j : Nat, 1 ≤ j → j ≤ (compileAdvice q).b →
      (C (site ring root j)).tok = .CL0 →
        resetColdPrivateMismatchPrefix ring root C
          (compileAdvice q).b)

/-- Extending a prefix never loses a witnessed mismatch. -/
theorem resetColdPrivateMismatchPrefixMono {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (j k : Nat)
    (hjk : j ≤ k)
    (h : resetColdPrivateMismatchPrefix ring root C j) :
    resetColdPrivateMismatchPrefix ring root C k := by
  obtain ⟨i, hi, hij, hib, hm⟩ := h
  exact ⟨i, hi, by omega, hib, hm⟩

/-- A complete matched prefix followed by one matching digit
remains matched. The next digit uses theta j, not theta (j+1). -/
theorem resetColdPrivateMatchedPrefixExtend {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (j : Nat)
    (hj : j < (compileAdvice q).b)
    (hmatch : resetColdPrivateMatchedPrefix ring root C j)
    (hbit : (C (site ring root (j + 1))).bit =
      (compileAdvice q).theta j) :
    resetColdPrivateMatchedPrefix ring root C (j + 1) := by
  intro i hi hij hib
  by_cases hbefore : i ≤ j
  · exact hmatch i hi hbefore hib
  · have heq : i = j + 1 := by omega
    subst i
    have hs : j + 1 - 1 = j := by omega
    rw [hs]
    exact hbit

/-- One mismatched new digit witnesses a mismatch in the
extended comparison prefix. -/
theorem resetColdPrivateMismatchPrefixLast {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (j : Nat)
    (hj : j < (compileAdvice q).b)
    (hbit : (C (site ring root (j + 1))).bit ≠
      (compileAdvice q).theta j) :
    resetColdPrivateMismatchPrefix ring root C (j + 1) := by
  have hs : j + 1 - 1 = j := by omega
  exact ⟨j + 1, by omega, by omega, by omega,
    by simpa only [hs] using hbit⟩

/-- Full digit-bit frames preserve a witnessed mismatch. -/
theorem resetColdPrivateMismatchPrefixBitFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n) (j : Nat)
    (hbit : ∀ i : Nat, 1 ≤ i →
      i ≤ (compileAdvice q).b →
      (D (site ring root i)).bit =
        (C (site ring root i)).bit)
    (hm : resetColdPrivateMismatchPrefix ring root C j) :
    resetColdPrivateMismatchPrefix ring root D j := by
  obtain ⟨i, hi, hij, hib, he⟩ := hm
  refine ⟨i, hi, hij, hib, ?_⟩
  rw [hbit i hi hib]
  exact he

/-- Full digit-bit frames also preserve positive comparisons. -/
theorem resetColdPrivateMatchedPrefixBitFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n) (j : Nat)
    (hbit : ∀ i : Nat, 1 ≤ i →
      i ≤ (compileAdvice q).b →
      (D (site ring root i)).bit =
        (C (site ring root i)).bit)
    (hm : resetColdPrivateMatchedPrefix ring root C j) :
    resetColdPrivateMatchedPrefix ring root D j := by
  intro i hi hij hib
  rw [hbit i hi hib]
  exact hm i hi hij hib

/-- The stronger shape is preserved by any BANK-bit/token frame
and root-mode frame. This is the companion to the weak
four-phase frame. -/
theorem resetColdPrivateLiveShapeAuthBankFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n)
    (hroot : (D root).mode = (C root).mode)
    (hbit : ∀ i : Nat, 1 ≤ i →
      i ≤ (compileAdvice q).b →
      (D (site ring root i)).bit =
        (C (site ring root i)).bit)
    (htok : ∀ i : Nat, 1 ≤ i →
      i ≤ (compileAdvice q).b →
      (D (site ring root i)).tok =
        (C (site ring root i)).tok)
    (hshape : ResetColdPrivateLiveShapeAuth ring root C) :
    ResetColdPrivateLiveShapeAuth ring root D := by
  refine ⟨resetColdPrivateLiveShapeBankFrame
    ring root C D hroot hbit htok hshape.1, ?_, ?_⟩
  · intro j hj hjb hcr
    have hsource : (C (site ring root j)).tok = .CR0 := by
      rw [htok j hj hjb] at hcr
      exact hcr
    exact resetColdPrivateMismatchPrefixBitFrame
      ring root C D j hbit (hshape.2.1 j hj hjb hsource)
  · intro j hj hjb hcl
    have hsource : (C (site ring root j)).tok = .CL0 := by
      rw [htok j hj hjb] at hcl
      exact hcl
    exact resetColdPrivateMismatchPrefixBitFrame
      ring root C D (compileAdvice q).b hbit
      (hshape.2.2 j hj hjb hsource)

/-- The ARMED Clean seed is strong: neither CR0 nor CL0 can
occur in any protected slot. -/
theorem resetColdPrivateLiveShapeAuthClean {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : ResetClockBankClean ring C root)
    (hsp : (compileAdvice q).useSmall = false) :
    ResetColdPrivateLiveShapeAuth ring root C := by
  have hseed := resetColdPrivateLiveShapeClean ring root C hc hsp
  have hn := resetColdPrivateNoWorkersClean ring root C hc
  refine ⟨hseed, ?_, ?_⟩
  · intro j hj hjb hcr
    rw [hn j hj hjb] at hcr
    cases hcr
  · intro j hj hjb hcl
    rw [hn j hj hjb] at hcl
    cases hcl

/-- The CSTART phase has no comparator workers and therefore
already satisfies both negative-provenance clauses. -/
theorem resetColdPrivateLiveShapeAuthCStart {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hsp : (compileAdvice q).useSmall = false)
    (hseed : ResetColdPrivateCStartSeed ring root C) :
    ResetColdPrivateLiveShapeAuth ring root C := by
  have hs := resetColdPrivateLiveShapeCStartSeed
    ring root C hseed hsp
  refine ⟨hs, ?_, ?_⟩
  · intro j hj hjb ht
    rw [hseed.noWorkers j hj hjb] at ht
    cases ht
  · intro j hj hjb ht
    rw [hseed.noWorkers j hj hjb] at ht
    cases ht

/-- A first comparator launch produces either a genuine CR1
match or a genuine CR0 mismatch at the first digit. -/
theorem resetColdPrivateCStartLaunchAuth {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hsp : (compileAdvice q).useSmall = false)
    (h : Nat)
    (hbound : h + 1 ≤ (compileAdvice q).K)
    (hm : (C root).mode = .CSTART)
    (hn : resetColdPrivateNoWorkers ring root C)
    (hvalue : resetColdPrivateHeadValue ring root C = h + 1) :
    ResetColdPrivateLiveShapeAuth ring root
      ((protocol q).step ring C root) := by
  have hweak := (resetColdPrivateCStartLaunchShape
    ring root C hc hg hsp h hbound hm hn hvalue).1
  have hb : 1 ≤ (compileAdvice q).b := by
    have hw := resetTrialCompiledWidth q
    omega
  have hrow := resetColdPrivateCStartComparatorPhysical
    ring root C hc hg hsp hm (hn 1 (by omega) hb)
  have hother : ∀ j : Nat, 2 ≤ j →
      j ≤ (compileAdvice q).b →
      (((protocol q).step ring C root)
        (site ring root j)).tok = .E := by
    intro j hj hjb
    rw [resetColdOutgoingRootOtherDigitsFrame
      ring C root hc j hj hjb]
    exact hn j (by omega) hjb
  have hcr : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      (((protocol q).step ring C root)
        (site ring root j)).tok = .CR0 →
      resetColdPrivateMismatchPrefix ring root
        ((protocol q).step ring C root) j := by
    intro j hj hjb ht
    by_cases hfirst : j = 1
    · subst j
      have hneq :
          (C (site ring root 1)).bit ≠
            (compileAdvice q).theta 0 := by
        intro he
        have hnew :
            (((protocol q).step ring C root)
              (site ring root 1)).tok = .CR1 := by
          rw [hrow.2.2]
          simp [he]
        rw [hnew] at ht
        cases ht
      have hneqNew :
          (((protocol q).step ring C root)
            (site ring root 1)).bit ≠
              (compileAdvice q).theta 0 := by
        rw [hrow.2.1]
        exact hneq
      exact ⟨1, by omega, by omega, hb,
        by simpa only [Nat.reduceSubDiff] using hneqNew⟩
    · rw [hother j (by omega) hjb] at ht
      cases ht
  have hcl : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      (((protocol q).step ring C root)
        (site ring root j)).tok = .CL0 →
      resetColdPrivateMismatchPrefix ring root
        ((protocol q).step ring C root)
          (compileAdvice q).b := by
    intro j hj hjb ht
    by_cases hfirst : j = 1
    · subst j
      rw [hrow.2.2] at ht
      split at ht <;> cases ht
    · rw [hother j (by omega) hjb] at ht
      cases ht
  exact ⟨hweak, hcr, hcl⟩

/-- Actual CSTART LIVE root service gives an authenticated
comparison worker, even for later nonzero completed heads. -/
theorem resetColdPrivateCStartRootAuthLive {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (h : Nat)
    (hbound : h + 1 ≤ (compileAdvice q).K)
    (hm : (C root).mode = .CSTART)
    (hn : resetColdPrivateNoWorkers ring root C)
    (hvalue : resetColdPrivateHeadValue ring root C = h + 1)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) root = .live D started') :
    ResetColdPrivateLiveShapeAuth ring root D := by
  have hg := resetColdPrivateLiveOutgoingGrantFree
    ring root C D started started' hc hsp hnext
  have hp := resetColdPrivateLivePhysical
    ring root root C D started started' hnext
  rw [hp]
  exact resetColdPrivateCStartLaunchAuth ring root C
    hc hg hsp h hbound hm hn hvalue

/-- CR1 forward: a fresh destination yields CR1 exactly when its
bit matches the next theta digit; both bits are left unchanged. -/
theorem resetColdPrivateCRForwardBank
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : 1 ≤ x.role) (hxb : x.role < b)
    (hy : y.role = x.role + 1)
    (ht : x.tok = .CR0 ∨ x.tok = .CR1)
    (he : y.tok = .E) :
    (bankPair x y y.role b theta).1.tok = .E ∧
      (bankPair x y y.role b theta).1.bit = x.bit ∧
      (bankPair x y y.role b theta).2.bit = y.bit ∧
      (bankPair x y y.role b theta).2.tok =
        (if x.tok == .CR1 && y.bit == theta (y.role - 1)
          then .CR1 else .CR0) := by
  have hxne : x.role ≠ 0 := by omega
  have hyne : y.role ≠ 0 := by omega
  have hxle : x.role ≤ b := by omega
  have hyle : y.role ≤ b := by omega
  have hxneq : x.role ≠ b := by omega
  have hnlt : ¬ b < x.role + 1 := by omega
  rcases ht with ht | ht
  · simp [bankPair, hx, hxb, hy, he, ht, hxne, hyne,
      hxle, hyle, hxneq, hnlt] <;>
      repeat (first | rfl | split | omega)
  · simp [bankPair, hx, hxb, hy, he, ht, hxne, hyne,
      hxle, hyle, hxneq, hnlt] <;>
      repeat (first | rfl | split | omega)

/-- The all-match or some-mismatch provenance survives one
CR forward comparison at the next protected digit. -/
theorem resetColdPrivateCRForwardProvenance {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (j : Nat) (t : BTok)
    (hj : 1 ≤ j) (hjb : j < (compileAdvice q).b)
    (ht : t = .CR0 ∨ t = .CR1)
    (hgood : t = .CR1 →
      resetColdPrivateMatchedPrefix ring root C j)
    (hbad : t = .CR0 →
      resetColdPrivateMismatchPrefix ring root C j) :
    ((if t == .CR1 &&
        (C (site ring root (j + 1))).bit ==
          (compileAdvice q).theta j
      then BTok.CR1 else BTok.CR0) = .CR1 →
        resetColdPrivateMatchedPrefix ring root C (j + 1)) ∧
      ((if t == .CR1 &&
        (C (site ring root (j + 1))).bit ==
          (compileAdvice q).theta j
      then BTok.CR1 else BTok.CR0) = .CR0 →
        resetColdPrivateMismatchPrefix ring root C (j + 1)) := by
  rcases ht with hzero | hone
  · rw [hzero]
    constructor
    · intro hfalse
      simp at hfalse
    · intro hnew
      exact resetColdPrivateMismatchPrefixMono
        ring root C j (j + 1) (by omega) (hbad hzero)
  · rw [hone]
    by_cases hbit : (C (site ring root (j + 1))).bit =
        (compileAdvice q).theta j
    · constructor
      · intro hnew
        exact resetColdPrivateMatchedPrefixExtend
          ring root C j hjb (hgood hone) hbit
      · intro hnew
        simp [hbit] at hnew
    · constructor
      · intro hnew
        simp [hbit] at hnew
      · intro hnew
        exact resetColdPrivateMismatchPrefixLast
          ring root C j hjb hbit

/-- On the top turn, a CR1 becomes CL1 and a CR0 becomes CL0.
The source and responder bits remain exactly unchanged. -/
theorem resetColdPrivateCRTopTurnBank
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : 1 ≤ x.role) (hxb : x.role < b)
    (hy : y.role = x.role + 1)
    (htop : y.role = b)
    (he : x.tok = .E)
    (ht : y.tok = .CR0 ∨ y.tok = .CR1) :
    (bankPair x y y.role b theta).1.tok =
        (if y.tok = .CR1 then .CL1 else .CL0) ∧
      (bankPair x y y.role b theta).2.tok = .E ∧
      (bankPair x y y.role b theta).1.bit = x.bit ∧
      (bankPair x y y.role b theta).2.bit = y.bit := by
  have hxne : x.role ≠ 0 := by omega
  have hyne : y.role ≠ 0 := by omega
  have hxle : x.role ≤ b := by omega
  have hyle : y.role ≤ b := by omega
  have hxneq : x.role ≠ b := by omega
  have hnlt : ¬ b < x.role + 1 := by omega
  rcases ht with hzero | hone
  · simp [bankPair, hx, hxb, hy, htop, he, hzero,
      hxne, hyne, hxle, hyle, hxneq, hnlt] <;>
      repeat (first | rfl | (refine ⟨?_, ?_⟩) | split | omega)
  · simp [bankPair, hx, hxb, hy, htop, he, hone,
      hxne, hyne, hxle, hyle, hxneq, hnlt] <;>
      repeat (first | rfl | (refine ⟨?_, ?_⟩) | split | omega)

/-- A CL0/CL1 return travels backward unchanged to the
predecessor, erasing its former slot and preserving both bits. -/
theorem resetColdPrivateCLReturnBank
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : 1 ≤ x.role) (hxb : x.role < b)
    (hy : y.role = x.role + 1)
    (he : x.tok = .E)
    (ht : y.tok = .CL0 ∨ y.tok = .CL1) :
    (bankPair x y y.role b theta).1.tok = y.tok ∧
      (bankPair x y y.role b theta).2.tok = .E ∧
      (bankPair x y y.role b theta).1.bit = x.bit ∧
      (bankPair x y y.role b theta).2.bit = y.bit := by
  have hxne : x.role ≠ 0 := by omega
  have hyne : y.role ≠ 0 := by omega
  have hxle : x.role ≤ b := by omega
  have hyle : y.role ≤ b := by omega
  have hxneq : x.role ≠ b := by omega
  have hnlt : ¬ b < x.role + 1 := by omega
  rcases ht with hzero | hone
  · simp [bankPair, hx, hxb, hy, he, hzero,
      hxne, hyne, hxle, hyle, hxneq, hnlt] <;>
      repeat (first | rfl | split | omega)
  · simp [bankPair, hx, hxb, hy, he, hone,
      hxne, hyne, hxle, hyle, hxneq, hnlt] <;>
      repeat (first | rfl | split | omega)

/-- The strengthened shape rules out a CL0 worker with all
theta digits matched. In particular it supplies the missing
strict head bound for a possible CL0 rearm. -/
theorem resetColdPrivateCL0BelowKOfAuth {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hshape : ResetColdPrivateLiveShapeAuth ring root C)
    (hm : (C root).mode = .CWAIT)
    (ht : (C (site ring root 1)).tok = .CL0) :
    resetColdPrivateHeadValue ring root C <
      (compileAdvice q).K := by
  have hb : 1 ≤ (compileAdvice q).b := by
    have hw := resetTrialCompiledWidth q
    omega
  have hbad := hshape.2.2 1 (by omega) hb ht
  obtain ⟨i, hi, hib, hwidthi, hbit⟩ := hbad
  have hhead := resetColdPrivateLiveShapeHeadLe
    ring root C hshape.1
  have hnoIR : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      (C (site ring root j)).tok ≠ .IR := by
    rcases hshape.1 with harm | hrest
    · obtain ⟨h, hbound, hmode, hn, hvalue⟩ := harm
      rw [hmode] at hm
      cases hm
    · rcases hrest with hstart | hrest
      · obtain ⟨h, hbound, hmode, hn, hvalue⟩ := hstart
        rw [hmode] at hm
        cases hm
      · rcases hrest with hcompare | hcarry
        · obtain ⟨h, k, t, hbound, hmode, hworker,
              htype, hvalue, hprefix, hfull⟩ := hcompare
          exact resetColdPrivateComparatorNoIR
            ring root C k t hworker htype
        · obtain ⟨h, k, t, hbound, hmode, hworker,
              htype, hvalue⟩ := hcarry
          rw [hmode] at hm
          cases hm
  exact resetColdPrivateMismatchBelowK
    ring root C hwidth hnoIR hhead i hi hwidthi hbit

/-- An IR at the highest protected digit already contributes
2^b to the head. It is incompatible with h <= K < 2^b. -/
theorem resetColdPrivateTopIRImpossible {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hshape : ResetColdPrivateLiveShape ring root C)
    (htop : (C (site ring root (compileAdvice q).b)).tok = .IR) :
    False := by
  have hb : 0 < (compileAdvice q).b := by
    have hw := resetTrialCompiledWidth q
    omega
  have hindex : (compileAdvice q).b - 1 <
      (compileAdvice q).b := by omega
  have hterm := resetColdOneTermLeOfFn
    (compileAdvice q).b
    (fun j : Fin (compileAdvice q).b =>
      if (C (site ring root (j.val + 1))).tok = .IR
      then 2 ^ (j.val + 1) else 0)
    ⟨(compileAdvice q).b - 1, hindex⟩
  have heq : (compileAdvice q).b - 1 + 1 =
      (compileAdvice q).b := by omega
  change
    (if (C (site ring root
        ((compileAdvice q).b - 1 + 1))).tok = .IR
      then 2 ^ ((compileAdvice q).b - 1 + 1) else 0) ≤
      resetColdPrivateCarryValue ring root C at hterm
  rw [heq, htop] at hterm
  have hhead := resetColdPrivateLiveShapeHeadLe
    ring root C hshape
  exact resetColdPrivateTopCarryBound
    ring root C hwidth hhead hterm

/-- Stronger top-predecessor obstruction. If an IR at digit b-1
sees a set top bit, the OLD head is already >= 2^b. Thus a
bounded LIVE predecessor cannot take the top IR-to-IR row.
This checks the input of the transition, not a post-state invariant. -/
theorem resetColdPrivateTopPredecessorImpossible {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hwidth : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (hshape : ResetColdPrivateLiveShape ring root C)
    (hsrc : (C (site ring root
      ((compileAdvice q).b - 1))).tok = .IR)
    (hbit : (C (site ring root
      (compileAdvice q).b)).bit = true) :
    False := by
  have hb : 2 ≤ (compileAdvice q).b := by
    have hw := resetTrialCompiledWidth q
    omega
  have htopIndex : (compileAdvice q).b - 1 <
      (compileAdvice q).b := by omega
  have hsrcIndex : (compileAdvice q).b - 2 <
      (compileAdvice q).b := by omega
  have htopTerm := resetColdOneTermLeOfFn
    (compileAdvice q).b
    (fun j : Fin (compileAdvice q).b =>
      if (C (site ring root (j.val + 1))).bit
      then 2 ^ j.val else 0)
    ⟨(compileAdvice q).b - 1, htopIndex⟩
  have htopEq : (compileAdvice q).b - 1 + 1 =
      (compileAdvice q).b := by omega
  change (if (C (site ring root
      ((compileAdvice q).b - 1 + 1))).bit
      then 2 ^ ((compileAdvice q).b - 1) else 0) ≤
      resetColdPrivateBitValue ring root C at htopTerm
  rw [htopEq, hbit] at htopTerm
  have hsrcTerm := resetColdOneTermLeOfFn
    (compileAdvice q).b
    (fun j : Fin (compileAdvice q).b =>
      if (C (site ring root (j.val + 1))).tok = .IR
      then 2 ^ (j.val + 1) else 0)
    ⟨(compileAdvice q).b - 2, hsrcIndex⟩
  have hsrcEq : (compileAdvice q).b - 2 + 1 =
      (compileAdvice q).b - 1 := by omega
  change (if (C (site ring root
      ((compileAdvice q).b - 2 + 1))).tok = .IR
      then 2 ^ ((compileAdvice q).b - 2 + 1) else 0) ≤
      resetColdPrivateCarryValue ring root C at hsrcTerm
  rw [hsrcEq, hsrc] at hsrcTerm
  have hpower : 2 ^ (compileAdvice q).b =
      2 ^ ((compileAdvice q).b - 1) +
        2 ^ ((compileAdvice q).b - 1) := by
    have heq : (compileAdvice q).b =
        ((compileAdvice q).b - 1) + 1 := by omega
    calc
      2 ^ (compileAdvice q).b =
          2 ^ (((compileAdvice q).b - 1) + 1) := by rw [← heq]
      _ = _ := by rw [Nat.pow_succ]; omega
  rw [if_pos rfl] at htopTerm
  rw [if_pos rfl] at hsrcTerm
  have hhead := resetColdPrivateLiveShapeHeadLe
    ring root C hshape
  unfold resetColdPrivateHeadValue at hhead
  omega

end Counter
end L3

/-!
Authenticated LIVE spatial frame and root-row assembly.

Only actual (protocol q).step and resetColdLatchedPrivateNext
successors are used.
The full word induction is not claimed before every interior and
root-return row is proved in the physical model.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- The negative comparator provenance can be transported if the
new weak phase is already proved and all physical BANK bits/tokens
are framed. This avoids reproving the old mode/lease calculation. -/
theorem resetColdPrivateAuthOfWeakBitTok {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n)
    (hbit : ∀ i : Nat, 1 ≤ i →
      i ≤ (compileAdvice q).b →
        (D (site ring root i)).bit =
          (C (site ring root i)).bit)
    (htok : ∀ i : Nat, 1 ≤ i →
      i ≤ (compileAdvice q).b →
        (D (site ring root i)).tok =
          (C (site ring root i)).tok)
    (ha : ResetColdPrivateLiveShapeAuth ring root C)
    (hw : ResetColdPrivateLiveShape ring root D) :
    ResetColdPrivateLiveShapeAuth ring root D := by
  refine ⟨hw, ?_, ?_⟩
  · intro j hj hjb ht
    have hsource : (C (site ring root j)).tok = .CR0 := by
      rw [htok j hj hjb] at ht
      exact ht
    exact resetColdPrivateMismatchPrefixBitFrame
      ring root C D j hbit (ha.2.1 j hj hjb hsource)
  · intro j hj hjb ht
    have hsource : (C (site ring root j)).tok = .CL0 := by
      rw [htok j hj hjb] at ht
      exact ht
    exact resetColdPrivateMismatchPrefixBitFrame
      ring root C D (compileAdvice q).b hbit
      (ha.2.2 j hj hjb hsource)

/-- In a weak ARMED, CSTART or IWAIT phase no comparator
token can be hidden in another digit. The CWAIT exclusion is
essential: that phase really does contain a CR or CL worker. -/
private theorem resetColdPrivateWeakNonCWaitToken {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hm : (C root).mode ≠ .CWAIT)
    (hw : ResetColdPrivateLiveShape ring root C)
    (j : Nat) (hj : 1 ≤ j)
    (hjb : j ≤ (compileAdvice q).b)
    (u : BTok) (hE : u ≠ .E)
    (hIR : u ≠ .IR) (hAL : u ≠ .AL)
    (ht : (C (site ring root j)).tok = u) : False := by
  rcases hw with harm | hrest
  · obtain ⟨h, hk, hmode, hno, hvalue⟩ := harm
    have he := hno j hj hjb
    rw [ht] at he
    exact hE he
  · rcases hrest with hstart | hrest
    · obtain ⟨h, hk, hmode, hno, hvalue⟩ := hstart
      have he := hno j hj hjb
      rw [ht] at he
      exact hE he
    · rcases hrest with hcompare | hcarry
      · obtain ⟨h, k, t, hk, hmode, hone, htype,
            hvalue, hgood, hfull⟩ := hcompare
        exact hm hmode
      · obtain ⟨h, k, t, hk, hmode, hone, htype,
            hvalue⟩ := hcarry
        by_cases hjk : j = k
        · have htu : t = u := by
            rw [hjk] at ht
            exact hone.2.2.1.symm.trans ht
          rcases htype with hir | hal
          · rw [hir] at htu
            exact hIR htu.symm
          · rw [hal] at htu
            exact hAL htu.symm
        · have he := hone.2.2.2 j hj hjb hjk
          rw [ht] at he
          exact hE he

/-- A weak non-CWAIT phase automatically satisfies the stronger
negative-provenance clauses, even without a preexisting Auth phase. -/
theorem resetColdPrivateAuthOfWeakNonCWait {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hm : (C root).mode ≠ .CWAIT)
    (hw : ResetColdPrivateLiveShape ring root C) :
    ResetColdPrivateLiveShapeAuth ring root C := by
  refine ⟨hw, ?_, ?_⟩
  · intro j hj hjb ht
    exact False.elim
      (resetColdPrivateWeakNonCWaitToken
        ring root C hm hw j hj hjb .CR0
        (by intro he; cases he)
        (by intro he; cases he)
        (by intro he; cases he) ht)
  · intro j hj hjb ht
    exact False.elim
      (resetColdPrivateWeakNonCWaitToken
        ring root C hm hw j hj hjb .CL0
        (by intro he; cases he)
        (by intro he; cases he)
        (by intro he; cases he) ht)

/-- Exterior real scheduler edges preserve the full Auth shape.
The observer equality is used only as a hypothesis to identify
the exact physical successor; the source state is unchanged. -/
theorem resetColdPrivateAuthOutsideObserver {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hrsource : e ≠ root)
    (hrtarget : ring.rightNeighbor e ≠ root)
    (hsource : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b → e ≠ site ring root j)
    (htarget : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
        ring.rightNeighbor e ≠ site ring root j)
    (ha : ResetColdPrivateLiveShapeAuth ring root C)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) e = .live D started') :
    ResetColdPrivateLiveShapeAuth ring root D ∧
      resetColdPrivateHeadValue ring root D =
        resetColdPrivateHeadValue ring root C := by
  have hweak := resetColdPrivateLiveShapeOutsideObserver
    ring root e C D started started'
    hrsource hrtarget hsource htarget ha.1 hnext
  have hmode :
      (((protocol q).step ring C e) root).mode =
        (C root).mode := by
    exact congrArg
      (fun z : Agent (compileAdvice q) => z.mode)
      (step_frame ring C e root
        (Ne.symm hrsource) (Ne.symm hrtarget))
  have hframe : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      ((protocol q).step ring C e) (site ring root j) =
        C (site ring root j) := by
    intro j hj hjb
    exact step_frame ring C e (site ring root j)
      (Ne.symm (hsource j hj hjb))
      (Ne.symm (htarget j hj hjb))
  have hbits : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      (((protocol q).step ring C e)
        (site ring root j)).bit =
          (C (site ring root j)).bit := by
    intro j hj hjb
    rw [hframe j hj hjb]
  have htoks : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      (((protocol q).step ring C e)
        (site ring root j)).tok =
          (C (site ring root j)).tok := by
    intro j hj hjb
    rw [hframe j hj hjb]
  have hp := resetColdPrivateLivePhysical
    ring root e C D started started' hnext
  constructor
  · rw [hp]
    exact resetColdPrivateLiveShapeAuthBankFrame
      ring root C ((protocol q).step ring C e)
      hmode hbits htoks ha
  · exact hweak.2

/-- The incoming ARMED root edge never remains LIVE; the
observer's abort guard records it before the next classification. -/
theorem resetColdPrivateAuthIncomingArmedImpossible {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C D : Config q n) (started started' : Bool)
    (he : e ≠ root)
    (hpred : ring.rightNeighbor e = root)
    (hm : (C root).mode = .ARMED)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) e = .live D started') : False := by
  have hno := resetColdPrivateLiveNoAbort
    ring root e C D started started' hnext
  exact hno (Or.inl ⟨hm, he, hpred⟩)

/-- A LIVE outgoing ARMED root service is one of the two
head increments. Both resulting physical modes are non-CWAIT,
so their negative comparator provenance is automatic. -/
theorem resetColdPrivateAuthArmedRootLive {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (h : Nat)
    (hbound : h < (compileAdvice q).K)
    (hm : (C root).mode = .ARMED)
    (hn : resetColdPrivateNoWorkers ring root C)
    (hvalue : resetColdPrivateHeadValue ring root C = h)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) root = .live D started') :
    ResetColdPrivateLiveShapeAuth ring root D ∧
      resetColdPrivateHeadValue ring root D =
        resetColdPrivateHeadValue ring root C + 1 := by
  have hweak := resetColdPrivateArmedRootLive
    ring root C D started started' hc hsp
    h hbound hm hn hvalue hnext
  have hg := resetColdPrivateLiveOutgoingGrantFree
    ring root C D started started' hc hsp hnext
  have hp := resetColdPrivateLivePhysical
    ring root root C D started started' hnext
  have hb : 1 ≤ (compileAdvice q).b := by
    have hw := resetTrialCompiledWidth q
    omega
  cases hbit : (C (site ring root 1)).bit with
  | false =>
      have hrow := resetColdLatchedPhysicalArmedFirstSet
        ring C root hc hg hsp hm
        (hn 1 (by omega) hb) hbit
      have hmode : (D root).mode ≠ .CWAIT := by
        rw [hp, hrow.1]
        intro he
        cases he
      exact ⟨resetColdPrivateAuthOfWeakNonCWait
        ring root D hmode hweak.1, hweak.2⟩
  | true =>
      have hrow := resetColdPrivateArmedCarryPhysical
        ring root C hc hg hsp hm
        (hn 1 (by omega) hb) hbit
      have hmode : (D root).mode ≠ .CWAIT := by
        rw [hp, hrow.1]
        intro he
        cases he
      exact ⟨resetColdPrivateAuthOfWeakNonCWait
        ring root D hmode hweak.1, hweak.2⟩

/-- The general CSTART root launch already has authenticated
comparator provenance (proved earlier); this packages it as a LIVE case
along with its unchanged numerical head. -/
theorem resetColdPrivateAuthCStartRootLive {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (h : Nat)
    (hbound : h + 1 ≤ (compileAdvice q).K)
    (hm : (C root).mode = .CSTART)
    (hn : resetColdPrivateNoWorkers ring root C)
    (hvalue : resetColdPrivateHeadValue ring root C = h + 1)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) root = .live D started') :
    ResetColdPrivateLiveShapeAuth ring root D ∧
      resetColdPrivateHeadValue ring root D =
        resetColdPrivateHeadValue ring root C := by
  constructor
  · exact resetColdPrivateCStartRootAuthLive
      ring root C D started started' hc hsp
      h hbound hm hn hvalue hnext
  · exact (resetColdPrivateCStartRootLive
      ring root C D started started' hc hsp
      h hbound hm hn hvalue hnext).2

/-- A root CWAIT/IWAIT nonreturn watchdog service preserves the
extra comparator mismatch witnesses: its physical BANK bit/token
fields are unchanged, and supplies the weak phase. -/
theorem resetColdPrivateAuthWaitRootLive {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hm : isWaitMode (C root).mode = true)
    (ht : isRetTok (C (site ring root 1)).tok = false)
    (ha : ResetColdPrivateLiveShapeAuth ring root C)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) root = .live D started') :
    ResetColdPrivateLiveShapeAuth ring root D ∧
      resetColdPrivateHeadValue ring root D =
        resetColdPrivateHeadValue ring root C := by
  have hweak := resetColdPrivateWaitRootLive
    ring root C D started started' hc hsp hm ht ha.1 hnext
  have hg := resetColdPrivateLiveOutgoingGrantFree
    ring root C D started started' hc hsp hnext
  have hfields := resetColdPhysicalWaitNonreturn
    ring C root hc hg hsp hm ht
  have hfirstBit := resetColdPrivatePhysicalWaitNonreturnBit
    ring root C hc hg hsp hm ht
  have hbits : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      (((protocol q).step ring C root)
        (site ring root j)).bit =
          (C (site ring root j)).bit := by
    intro j hj hjb
    by_cases hone : j = 1
    · subst j
      exact hfirstBit
    · rw [resetColdOutgoingRootOtherDigitsFrame
        ring C root hc j (by omega) hjb]
  have htoks : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      (((protocol q).step ring C root)
        (site ring root j)).tok =
          (C (site ring root j)).tok := by
    intro j hj hjb
    by_cases hone : j = 1
    · subst j
      exact hfields.2.2
    · rw [resetColdOutgoingRootOtherDigitsFrame
        ring C root hc j (by omega) hjb]
  have hp := resetColdPrivateLivePhysical
    ring root root C D started started' hnext
  constructor
  · have hnew : ResetColdPrivateLiveShape ring root
        ((protocol q).step ring C root) := by
      rw [← hp]
      exact hweak.1
    rw [hp]
    exact resetColdPrivateAuthOfWeakBitTok
      ring root C ((protocol q).step ring C root)
      hbits htoks ha hnew
  · exact hweak.2

/-- Auth CSTART incoming-root service: use the weak root
mode proof and the true all-digit frame, not an invented BANK
transition. The source-role and exteriority hypotheses stay explicit. -/
theorem resetColdPrivateAuthIncomingCStartLive {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hpred : ring.rightNeighbor e = root)
    (hrole : (C e).pack.val = (compileAdvice q).b ∨
      (C e).pack.val = (compileAdvice q).b + 1)
    (hex : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b → e ≠ site ring root j)
    (hm : (C root).mode = .CSTART)
    (ha : ResetColdPrivateLiveShapeAuth ring root C)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) e = .live D started') :
    ResetColdPrivateLiveShapeAuth ring root D ∧
      resetColdPrivateHeadValue ring root D =
        resetColdPrivateHeadValue ring root C := by
  have hweak := resetColdPrivateIncomingCStartLive
    ring root e C D started started' hc hg hsp
    hpred hrole hex hm ha.1 hnext
  have hframe : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      ((protocol q).step ring C e) (site ring root j) =
        C (site ring root j) := by
    intro j hj hjb
    exact resetColdIncomingRootDigitFrame
      ring C root e hc hpred hex j hj hjb
  have hbits : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      (((protocol q).step ring C e)
        (site ring root j)).bit =
          (C (site ring root j)).bit := by
    intro j hj hjb
    rw [hframe j hj hjb]
  have htoks : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      (((protocol q).step ring C e)
        (site ring root j)).tok =
          (C (site ring root j)).tok := by
    intro j hj hjb
    rw [hframe j hj hjb]
  have hp := resetColdPrivateLivePhysical
    ring root e C D started started' hnext
  constructor
  · have hnew : ResetColdPrivateLiveShape ring root
        ((protocol q).step ring C e) := by
      rw [← hp]
      exact hweak.1
    rw [hp]
    exact resetColdPrivateAuthOfWeakBitTok
      ring root C ((protocol q).step ring C e)
      hbits htoks ha hnew
  · exact hweak.2

/-- Auth root incoming watchdog tick. Again, the source may
hold arbitrary non-BANK fields; only grant freedom, role support,
and the exterior digit frame are used. -/
theorem resetColdPrivateAuthIncomingWaitLive {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hpred : ring.rightNeighbor e = root)
    (hrole : (C e).pack.val = (compileAdvice q).b ∨
      (C e).pack.val = (compileAdvice q).b + 1)
    (hex : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b → e ≠ site ring root j)
    (hm : isWaitMode (C root).mode = true)
    (ha : ResetColdPrivateLiveShapeAuth ring root C)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) e = .live D started') :
    ResetColdPrivateLiveShapeAuth ring root D ∧
      resetColdPrivateHeadValue ring root D =
        resetColdPrivateHeadValue ring root C := by
  have hweak := resetColdPrivateIncomingWaitLive
    ring root e C D started started' hc hg hsp
    hpred hrole hex hm ha.1 hnext
  have hframe : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      ((protocol q).step ring C e) (site ring root j) =
        C (site ring root j) := by
    intro j hj hjb
    exact resetColdIncomingRootDigitFrame
      ring C root e hc hpred hex j hj hjb
  have hbits : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      (((protocol q).step ring C e)
        (site ring root j)).bit =
          (C (site ring root j)).bit := by
    intro j hj hjb
    rw [hframe j hj hjb]
  have htoks : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
      (((protocol q).step ring C e)
        (site ring root j)).tok =
          (C (site ring root j)).tok := by
    intro j hj hjb
    rw [hframe j hj hjb]
  have hp := resetColdPrivateLivePhysical
    ring root e C D started started' hnext
  constructor
  · have hnew : ResetColdPrivateLiveShape ring root
        ((protocol q).step ring C e) := by
      rw [← hp]
      exact hweak.1
    rw [hp]
    exact resetColdPrivateAuthOfWeakBitTok
      ring root C ((protocol q).step ring C e)
      hbits htoks ha hnew
  · exact hweak.2

/-- Any physically selected interior source j and responder j+1
with authenticated PACK roles use the exact BANK pair, independent
of the other Cartesian fields of either endpoint. -/
theorem resetColdPrivateInteriorPairTrip {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (j : Nat) (hj : 1 ≤ j)
    (hjb : j < (compileAdvice q).b) :
    resetAgentBankTrip
        (((protocol q).step ring C (site ring root j))
          (site ring root j)) =
      resetCellBankTrip
        (bankPair
          (bankCell (C (site ring root j)) j)
          (bankCell (C (site ring root (j + 1))) (j + 1))
          (j + 1) (compileAdvice q).b
          (compileAdvice q).theta).1 ∧
    resetAgentBankTrip
        (((protocol q).step ring C (site ring root j))
          (site ring root (j + 1))) =
      resetCellBankTrip
        (bankPair
          (bankCell (C (site ring root j)) j)
          (bankCell (C (site ring root (j + 1))) (j + 1))
          (j + 1) (compileAdvice q).b
          (compileAdvice q).theta).2 := by
  have hne : ring.rightNeighbor (site ring root j) ≠
      site ring root j := by
    change site ring root (j + 1) ≠ site ring root j
    exact resetCompleteSitesDifferent
      ring C root hc (j + 1) j (by omega) (by omega) (by omega)
  have hp := resetPhysicalEdgeBankTrip
    ring C (site ring root j) hne hsp
  change
    resetAgentBankTrip
        (((protocol q).step ring C (site ring root j))
          (site ring root j)) =
      resetCellBankTrip
        (resetBankOld (C (site ring root j))
          (C (site ring root (j + 1)))).1 ∧
    resetAgentBankTrip
        (((protocol q).step ring C (site ring root j))
          (site ring root (j + 1))) =
      resetCellBankTrip
        (resetBankOld (C (site ring root j))
          (C (site ring root (j + 1)))).2 at hp
  have hsource : (C (site ring root j)).pack.val = j :=
    hc j (by omega)
  have htarget : (C (site ring root (j + 1))).pack.val =
      j + 1 := hc (j + 1) (by omega)
  have hpost :
      packNext (C (site ring root j)).pack.val
        (C (site ring root (j + 1))).pack.val
        (compileAdvice q).b = j + 1 := by
    rw [hsource, htarget]
    simp [packNext, hjb]
  have hpostNat : packNext j (j + 1) (compileAdvice q).b = j + 1 := by
    simp [packNext, hjb]
  simpa only [resetBankOld, hsource, htarget, hpost, hpostNat] using hp

/-- Every protected digit except the two selected adjacent ones
is a genuine full-Agent frame at the physical interior edge. -/
theorem resetColdPrivateInteriorOtherFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : Complete ring C root)
    (j : Nat) (hj : 1 ≤ j)
    (hjb : j < (compileAdvice q).b)
    (i : Nat) (hi : 1 ≤ i)
    (hib : i ≤ (compileAdvice q).b)
    (hine : i ≠ j) (hnext : i ≠ j + 1) :
    ((protocol q).step ring C (site ring root j))
      (site ring root i) = C (site ring root i) := by
  have hs : site ring root i ≠ site ring root j :=
    resetCompleteSitesDifferent ring C root hc
      i j hib (by omega) hine
  have ht : site ring root i ≠
      ring.rightNeighbor (site ring root j) := by
    change site ring root i ≠ site ring root (j + 1)
    exact resetCompleteSitesDifferent ring C root hc
      i (j + 1) hib (by omega) hnext
  exact step_frame ring C (site ring root j)
    (site ring root i) hs ht

/-- An interior selected edge cannot alter the root BANK mode.
This includes the CR forward, CR turn, CL return and IR advance
rows for which a subsequent digit-shape proof is required. -/
theorem resetColdPrivateInteriorRootModeFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : Complete ring C root)
    (j : Nat) (hj : 1 ≤ j)
    (hjb : j < (compileAdvice q).b) :
    (((protocol q).step ring C (site ring root j)) root).mode =
      (C root).mode := by
  have hs : root ≠ site ring root j := by
    change site ring root 0 ≠ site ring root j
    exact resetCompleteSitesDifferent ring C root hc
      0 j (by omega) (by omega) (by omega)
  have ht : root ≠ ring.rightNeighbor (site ring root j) := by
    change site ring root 0 ≠ site ring root (j + 1)
    exact resetCompleteSitesDifferent ring C root hc
      0 (j + 1) (by omega) (by omega) (by omega)
  exact congrArg (fun z : Agent (compileAdvice q) => z.mode)
    (step_frame ring C (site ring root j) root hs ht)

end Counter
end L3

/-!
Interior physical comparator propagation.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- The literal BANK row at the consecutive physical digit pair.
This is an abbreviation for its old-state BANK inputs, not a
replacement transition system. -/
def resetColdPrivateInteriorBankAt {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (j : Nat) : BankCell × BankCell :=
  bankPair
    (bankCell (C (site ring root j)) j)
    (bankCell (C (site ring root (j + 1))) (j + 1))
    (j + 1) (compileAdvice q).b (compileAdvice q).theta

/-- Convert a selected BANK four-field certificate to a
full-protocol physical pair of consecutive protected digits. -/
theorem resetColdPrivateInteriorRowFields {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (j : Nat) (hj : 1 ≤ j) (hjb : j < (compileAdvice q).b)
    (tx ty : BTok) (vx vy : Bool)
    (hr : (resetColdPrivateInteriorBankAt ring root C j).1.tok = tx ∧
      (resetColdPrivateInteriorBankAt ring root C j).1.bit = vx ∧
      (resetColdPrivateInteriorBankAt ring root C j).2.tok = ty ∧
      (resetColdPrivateInteriorBankAt ring root C j).2.bit = vy) :
    (((protocol q).step ring C (site ring root j))
      (site ring root j)).tok = tx ∧
    (((protocol q).step ring C (site ring root j))
      (site ring root j)).bit = vx ∧
    (((protocol q).step ring C (site ring root j))
      (site ring root (j + 1))).tok = ty ∧
    (((protocol q).step ring C (site ring root j))
      (site ring root (j + 1))).bit = vy := by
  have hp := resetColdPrivateInteriorPairTrip
    ring root C hc hsp j hj hjb
  have hs := resetTrialTripBitTok
    (((protocol q).step ring C (site ring root j))
      (site ring root j))
    (resetColdPrivateInteriorBankAt ring root C j).1 hp.1
  have ht := resetTrialTripBitTok
    (((protocol q).step ring C (site ring root j))
      (site ring root (j + 1)))
    (resetColdPrivateInteriorBankAt ring root C j).2 hp.2
  exact ⟨hs.2.trans hr.1, hs.1.trans hr.2.1,
    ht.2.trans hr.2.2.1, ht.1.trans hr.2.2.2⟩

/-- Physical endpoint BIT identities imply the full protected
digit frame, including the two endpoints and all other sites. -/
theorem resetColdPrivateInteriorBitFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (hc : Complete ring C root)
    (j : Nat) (hj : 1 ≤ j) (hjb : j < (compileAdvice q).b)
    (hs : (((protocol q).step ring C (site ring root j))
      (site ring root j)).bit = (C (site ring root j)).bit)
    (ht : (((protocol q).step ring C (site ring root j))
      (site ring root (j + 1))).bit =
        (C (site ring root (j + 1))).bit) :
    ∀ i : Nat, 1 ≤ i → i ≤ (compileAdvice q).b →
      (((protocol q).step ring C (site ring root j))
        (site ring root i)).bit = (C (site ring root i)).bit := by
  intro i hi hib
  by_cases he : i = j
  · subst i
    exact hs
  · by_cases hf : i = j + 1
    · subst i
      exact ht
    · rw [resetColdPrivateInteriorOtherFrame
        ring root C hc j hj hjb i hi hib he hf]

/-- A unique comparator worker actually advances from j to j+1.
No hidden second worker can be created on a framed site. -/
theorem resetColdPrivateInteriorWorkerForward {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (hc : Complete ring C root)
    (j : Nat) (hj : 1 ≤ j) (hjb : j < (compileAdvice q).b)
    (t u : BTok)
    (hw : resetColdPrivateOnlyWorker ring root C j t)
    (hs : (((protocol q).step ring C (site ring root j))
      (site ring root j)).tok = .E)
    (ht : (((protocol q).step ring C (site ring root j))
      (site ring root (j + 1))).tok = u) :
    resetColdPrivateOnlyWorker ring root
      ((protocol q).step ring C (site ring root j)) (j + 1) u := by
  refine ⟨by omega, by omega, ht, ?_⟩
  intro i hi hib hneq
  by_cases he : i = j
  · subst i
    exact hs
  · rw [resetColdPrivateInteriorOtherFrame
      ring root C hc j hj hjb i hi hib he hneq]
    exact hw.2.2.2 i hi hib he

/-- A returning unique worker moves from j+1 back to j,
erasing the old position. -/
theorem resetColdPrivateInteriorWorkerBackward {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (hc : Complete ring C root)
    (j : Nat) (hj : 1 ≤ j) (hjb : j < (compileAdvice q).b)
    (t u : BTok)
    (hw : resetColdPrivateOnlyWorker ring root C (j + 1) t)
    (hs : (((protocol q).step ring C (site ring root j))
      (site ring root j)).tok = u)
    (ht : (((protocol q).step ring C (site ring root j))
      (site ring root (j + 1))).tok = .E) :
    resetColdPrivateOnlyWorker ring root
      ((protocol q).step ring C (site ring root j)) j u := by
  refine ⟨hj, by omega, hs, ?_⟩
  intro i hi hib hneq
  by_cases he : i = j + 1
  · subst i
    exact ht
  · rw [resetColdPrivateInteriorOtherFrame
      ring root C hc j hj hjb i hi hib hneq he]
    exact hw.2.2.2 i hi hib he

/-- Build an Auth CWAIT state from its unique comparator worker,
numerical head, and positive/negative prefix witnesses. -/
theorem resetColdPrivateAuthCWaitOfWorker {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (h j : Nat) (t : BTok)
    (hb : h + 1 ≤ (compileAdvice q).K)
    (hm : (C root).mode = .CWAIT)
    (hw : resetColdPrivateOnlyWorker ring root C j t)
    (ht : resetColdPrivateComparatorToken t)
    (hv : resetColdPrivateHeadValue ring root C = h + 1)
    (hcr : t = .CR1 → resetColdPrivateMatchedPrefix ring root C j)
    (hcl : t = .CL1 → resetColdPrivateMatchedPrefix
      ring root C (compileAdvice q).b)
    (hbadCR : t = .CR0 → resetColdPrivateMismatchPrefix ring root C j)
    (hbadCL : t = .CL0 → resetColdPrivateMismatchPrefix
      ring root C (compileAdvice q).b) :
    ResetColdPrivateLiveShapeAuth ring root C := by
  refine ⟨Or.inr (Or.inr (Or.inl
    ⟨h, j, t, hb, hm, hw, ht, hv, hcr, hcl⟩)), ?_, ?_⟩
  · intro i hi hib htok
    by_cases he : i = j
    · subst i
      exact hbadCR (hw.2.2.1.symm.trans htok)
    · have hz := hw.2.2.2 i hi hib he
      rw [htok] at hz
      cases hz
  · intro i hi hib htok
    by_cases he : i = j
    · subst i
      exact hbadCL (hw.2.2.1.symm.trans htok)
    · have hz := hw.2.2.2 i hi hib he
      rw [htok] at hz
      cases hz

/-- CR0/CR1 forward under the actual physical protocol:
one worker moves one digit, the head remains fixed, and the
extended authenticated comparison prefix is preserved. -/
theorem resetColdPrivateCRForwardPhysical {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (j h : Nat) (hj : 1 ≤ j) (hjb : j < (compileAdvice q).b)
    (t : BTok)
    (hb : h + 1 ≤ (compileAdvice q).K)
    (hm : (C root).mode = .CWAIT)
    (hw : resetColdPrivateOnlyWorker ring root C j t)
    (ht : t = .CR0 ∨ t = .CR1)
    (hv : resetColdPrivateHeadValue ring root C = h + 1)
    (hgood : t = .CR1 →
      resetColdPrivateMatchedPrefix ring root C j)
    (hbad : t = .CR0 →
      resetColdPrivateMismatchPrefix ring root C j) :
    ResetColdPrivateLiveShapeAuth ring root
      ((protocol q).step ring C (site ring root j)) ∧
    resetColdPrivateHeadValue ring root
      ((protocol q).step ring C (site ring root j)) =
        resetColdPrivateHeadValue ring root C := by
  have hdest : (C (site ring root (j + 1))).tok = .E :=
    hw.2.2.2 (j + 1) (by omega) (by omega) (by omega)
  have hidx : j + 1 - 1 = j := by omega
  have hbankRaw := resetColdPrivateCRForwardBank
    (bankCell (C (site ring root j)) j)
    (bankCell (C (site ring root (j + 1))) (j + 1))
    (compileAdvice q).b (compileAdvice q).theta
    (by change 1 ≤ j; exact hj)
    (by change j < (compileAdvice q).b; exact hjb)
    rfl
    (by
      change (C (site ring root j)).tok = .CR0 ∨
        (C (site ring root j)).tok = .CR1
      rw [hw.2.2.1]
      exact ht)
    (by change (C (site ring root (j + 1))).tok = .E; exact hdest)
  have hbank :
      (resetColdPrivateInteriorBankAt ring root C j).1.tok = .E ∧
      (resetColdPrivateInteriorBankAt ring root C j).1.bit =
        (C (site ring root j)).bit ∧
      (resetColdPrivateInteriorBankAt ring root C j).2.tok =
        (if t == .CR1 &&
          (C (site ring root (j + 1))).bit ==
            (compileAdvice q).theta j
          then BTok.CR1 else BTok.CR0) ∧
      (resetColdPrivateInteriorBankAt ring root C j).2.bit =
        (C (site ring root (j + 1))).bit := by
    unfold resetColdPrivateInteriorBankAt
    have hr := hbankRaw
    simp only [bankCell, hw.2.2.1, hidx] at hr ⊢
    exact ⟨hr.1, hr.2.1, hr.2.2.2, hr.2.2.1⟩
  have hf := resetColdPrivateInteriorRowFields
    ring root C hc hsp j hj hjb
    .E
    (if t == .CR1 &&
      (C (site ring root (j + 1))).bit ==
        (compileAdvice q).theta j
      then BTok.CR1 else BTok.CR0)
    (C (site ring root j)).bit
    (C (site ring root (j + 1))).bit hbank
  have hbits := resetColdPrivateInteriorBitFrame
    ring root C hc j hj hjb hf.2.1 hf.2.2.2
  have hnewWorker := resetColdPrivateInteriorWorkerForward
    ring root C hc j hj hjb t
    (if t == .CR1 &&
      (C (site ring root (j + 1))).bit ==
        (compileAdvice q).theta j
      then BTok.CR1 else BTok.CR0)
    hw hf.1 hf.2.2.1
  have htOld : resetColdPrivateComparatorToken t := by
    rcases ht with hzero | hone
    · exact Or.inl hzero
    · exact Or.inr (Or.inl hone)
  have htNew : resetColdPrivateComparatorToken
      (if t == .CR1 &&
        (C (site ring root (j + 1))).bit ==
          (compileAdvice q).theta j
        then BTok.CR1 else BTok.CR0) := by
    unfold resetColdPrivateComparatorToken
    split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
  have hhead := resetColdPrivateHeadNoIRBitFrame
    ring root C ((protocol q).step ring C (site ring root j))
    hbits
    (resetColdPrivateComparatorNoIR ring root C j t hw htOld)
    (resetColdPrivateComparatorNoIR ring root
      ((protocol q).step ring C (site ring root j))
      (j + 1)
      (if t == .CR1 &&
        (C (site ring root (j + 1))).bit ==
          (compileAdvice q).theta j
        then BTok.CR1 else BTok.CR0)
      hnewWorker htNew)
  have hmode :
      (((protocol q).step ring C (site ring root j)) root).mode =
        .CWAIT :=
    (resetColdPrivateInteriorRootModeFrame
      ring root C hc j hj hjb).trans hm
  have hp := resetColdPrivateCRForwardProvenance
    ring root C j t hj hjb ht hgood hbad
  have hgoodNew :
      (if t == .CR1 &&
        (C (site ring root (j + 1))).bit ==
          (compileAdvice q).theta j
        then BTok.CR1 else BTok.CR0) = .CR1 →
      resetColdPrivateMatchedPrefix ring root
        ((protocol q).step ring C (site ring root j)) (j + 1) := by
    intro he
    exact resetColdPrivateMatchedPrefixBitFrame
      ring root C ((protocol q).step ring C (site ring root j))
      (j + 1) hbits (hp.1 he)
  have hbadNew :
      (if t == .CR1 &&
        (C (site ring root (j + 1))).bit ==
          (compileAdvice q).theta j
        then BTok.CR1 else BTok.CR0) = .CR0 →
      resetColdPrivateMismatchPrefix ring root
        ((protocol q).step ring C (site ring root j)) (j + 1) := by
    intro he
    exact resetColdPrivateMismatchPrefixBitFrame
      ring root C ((protocol q).step ring C (site ring root j))
      (j + 1) hbits (hp.2 he)
  have hclNew :
      (if t == .CR1 &&
        (C (site ring root (j + 1))).bit ==
          (compileAdvice q).theta j
        then BTok.CR1 else BTok.CR0) = .CL1 →
      resetColdPrivateMatchedPrefix ring root
        ((protocol q).step ring C (site ring root j))
        (compileAdvice q).b := by
    intro he
    split at he <;> cases he
  have hbclNew :
      (if t == .CR1 &&
        (C (site ring root (j + 1))).bit ==
          (compileAdvice q).theta j
        then BTok.CR1 else BTok.CR0) = .CL0 →
      resetColdPrivateMismatchPrefix ring root
        ((protocol q).step ring C (site ring root j))
        (compileAdvice q).b := by
    intro he
    split at he <;> cases he
  have hvalueNew :
      resetColdPrivateHeadValue ring root
        ((protocol q).step ring C (site ring root j)) = h + 1 := by
    rw [hhead, hv]
  exact ⟨resetColdPrivateAuthCWaitOfWorker ring root
    ((protocol q).step ring C (site ring root j))
    h (j + 1)
    (if t == .CR1 &&
      (C (site ring root (j + 1))).bit ==
        (compileAdvice q).theta j
      then BTok.CR1 else BTok.CR0)
    hb hmode hnewWorker htNew hvalueNew
    hgoodNew hclNew hbadNew hbclNew, hhead⟩

end Counter
end L3

/-!
Physical top comparison turn, backward CL transport,
and forward IR conservation.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- The highest CR worker turns into a CL return on its
predecessor. Both physical bits and the represented head are
unchanged; the full-prefix positive and negative certificates
move with the returning token. -/
theorem resetColdPrivateCRTopTurnPhysical {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (j h : Nat) (hj : 1 ≤ j)
    (hjb : j < (compileAdvice q).b)
    (htop : j + 1 = (compileAdvice q).b)
    (t : BTok)
    (hb : h + 1 ≤ (compileAdvice q).K)
    (hm : (C root).mode = .CWAIT)
    (hw : resetColdPrivateOnlyWorker ring root C (j + 1) t)
    (ht : t = .CR0 ∨ t = .CR1)
    (hv : resetColdPrivateHeadValue ring root C = h + 1)
    (hgood : t = .CR1 →
      resetColdPrivateMatchedPrefix ring root C
        (compileAdvice q).b)
    (hbad : t = .CR0 →
      resetColdPrivateMismatchPrefix ring root C
        (compileAdvice q).b) :
    ResetColdPrivateLiveShapeAuth ring root
      ((protocol q).step ring C (site ring root j)) ∧
    resetColdPrivateHeadValue ring root
      ((protocol q).step ring C (site ring root j)) =
        resetColdPrivateHeadValue ring root C := by
  have hempty : (C (site ring root j)).tok = .E :=
    hw.2.2.2 j hj (by omega) (by omega)
  have hbankRaw := resetColdPrivateCRTopTurnBank
    (bankCell (C (site ring root j)) j)
    (bankCell (C (site ring root (j + 1))) (j + 1))
    (compileAdvice q).b (compileAdvice q).theta
    (by change 1 ≤ j; exact hj)
    (by change j < (compileAdvice q).b; exact hjb)
    rfl
    (by change j + 1 = (compileAdvice q).b; exact htop)
    (by change (C (site ring root j)).tok = .E; exact hempty)
    (by
      change (C (site ring root (j + 1))).tok = .CR0 ∨
        (C (site ring root (j + 1))).tok = .CR1
      rw [hw.2.2.1]
      exact ht)
  have hbank :
      (resetColdPrivateInteriorBankAt ring root C j).1.tok =
        (if t = .CR1 then BTok.CL1 else BTok.CL0) ∧
      (resetColdPrivateInteriorBankAt ring root C j).1.bit =
        (C (site ring root j)).bit ∧
      (resetColdPrivateInteriorBankAt ring root C j).2.tok = .E ∧
      (resetColdPrivateInteriorBankAt ring root C j).2.bit =
        (C (site ring root (j + 1))).bit := by
    unfold resetColdPrivateInteriorBankAt
    have hr := hbankRaw
    simp only [bankCell, hw.2.2.1] at hr ⊢
    exact ⟨hr.1, hr.2.2.1, hr.2.1, hr.2.2.2⟩
  have hf := resetColdPrivateInteriorRowFields
    ring root C hc hsp j hj hjb
    (if t = .CR1 then BTok.CL1 else BTok.CL0)
    .E
    (C (site ring root j)).bit
    (C (site ring root (j + 1))).bit hbank
  have hbits := resetColdPrivateInteriorBitFrame
    ring root C hc j hj hjb hf.2.1 hf.2.2.2
  have hnewWorker := resetColdPrivateInteriorWorkerBackward
    ring root C hc j hj hjb t
    (if t = .CR1 then BTok.CL1 else BTok.CL0)
    hw hf.1 hf.2.2.1
  have htOld : resetColdPrivateComparatorToken t := by
    rcases ht with hzero | hone
    · exact Or.inl hzero
    · exact Or.inr (Or.inl hone)
  have htNew : resetColdPrivateComparatorToken
      (if t = .CR1 then BTok.CL1 else BTok.CL0) := by
    unfold resetColdPrivateComparatorToken
    split
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl rfl))
  have hhead := resetColdPrivateHeadNoIRBitFrame
    ring root C ((protocol q).step ring C (site ring root j))
    hbits
    (resetColdPrivateComparatorNoIR ring root C (j + 1) t
      hw htOld)
    (resetColdPrivateComparatorNoIR ring root
      ((protocol q).step ring C (site ring root j))
      j (if t = .CR1 then BTok.CL1 else BTok.CL0)
      hnewWorker htNew)
  have hmode :
      (((protocol q).step ring C (site ring root j)) root).mode =
        .CWAIT :=
    (resetColdPrivateInteriorRootModeFrame
      ring root C hc j hj hjb).trans hm
  have hgoodCR :
      (if t = .CR1 then BTok.CL1 else BTok.CL0) = .CR1 →
      resetColdPrivateMatchedPrefix ring root
        ((protocol q).step ring C (site ring root j)) j := by
    intro he
    split at he <;> cases he
  have hbadCR :
      (if t = .CR1 then BTok.CL1 else BTok.CL0) = .CR0 →
      resetColdPrivateMismatchPrefix ring root
        ((protocol q).step ring C (site ring root j)) j := by
    intro he
    split at he <;> cases he
  have hgoodCL :
      (if t = .CR1 then BTok.CL1 else BTok.CL0) = .CL1 →
      resetColdPrivateMatchedPrefix ring root
        ((protocol q).step ring C (site ring root j))
        (compileAdvice q).b := by
    intro he
    have hone : t = .CR1 := by
      rcases ht with hzero | hone
      · simp [hzero] at he
      · exact hone
    exact resetColdPrivateMatchedPrefixBitFrame
      ring root C ((protocol q).step ring C (site ring root j))
      (compileAdvice q).b hbits (hgood hone)
  have hbadCL :
      (if t = .CR1 then BTok.CL1 else BTok.CL0) = .CL0 →
      resetColdPrivateMismatchPrefix ring root
        ((protocol q).step ring C (site ring root j))
        (compileAdvice q).b := by
    intro he
    have hzero : t = .CR0 := by
      rcases ht with hzero | hone
      · exact hzero
      · simp [hone] at he
    exact resetColdPrivateMismatchPrefixBitFrame
      ring root C ((protocol q).step ring C (site ring root j))
      (compileAdvice q).b hbits (hbad hzero)
  have hvalueNew :
      resetColdPrivateHeadValue ring root
        ((protocol q).step ring C (site ring root j)) = h + 1 := by
    rw [hhead, hv]
  exact ⟨resetColdPrivateAuthCWaitOfWorker
    ring root ((protocol q).step ring C (site ring root j))
    h j (if t = .CR1 then BTok.CL1 else BTok.CL0)
    hb hmode hnewWorker htNew hvalueNew
    hgoodCR hgoodCL hbadCR hbadCL, hhead⟩

/-- Each physical CL return moves left by one protected digit,
erases its former slot and keeps the full-word comparison result.
It does not change any digit bit or any IR carry. -/
theorem resetColdPrivateCLBackwardPhysical {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (j h : Nat) (hj : 1 ≤ j)
    (hjb : j < (compileAdvice q).b)
    (t : BTok)
    (hb : h + 1 ≤ (compileAdvice q).K)
    (hm : (C root).mode = .CWAIT)
    (hw : resetColdPrivateOnlyWorker ring root C (j + 1) t)
    (ht : t = .CL0 ∨ t = .CL1)
    (hv : resetColdPrivateHeadValue ring root C = h + 1)
    (hgood : t = .CL1 →
      resetColdPrivateMatchedPrefix ring root C
        (compileAdvice q).b)
    (hbad : t = .CL0 →
      resetColdPrivateMismatchPrefix ring root C
        (compileAdvice q).b) :
    ResetColdPrivateLiveShapeAuth ring root
      ((protocol q).step ring C (site ring root j)) ∧
    resetColdPrivateHeadValue ring root
      ((protocol q).step ring C (site ring root j)) =
        resetColdPrivateHeadValue ring root C := by
  have hempty : (C (site ring root j)).tok = .E :=
    hw.2.2.2 j hj (by omega) (by omega)
  have hbankRaw := resetColdPrivateCLReturnBank
    (bankCell (C (site ring root j)) j)
    (bankCell (C (site ring root (j + 1))) (j + 1))
    (compileAdvice q).b (compileAdvice q).theta
    (by change 1 ≤ j; exact hj)
    (by change j < (compileAdvice q).b; exact hjb)
    rfl
    (by change (C (site ring root j)).tok = .E; exact hempty)
    (by
      change (C (site ring root (j + 1))).tok = .CL0 ∨
        (C (site ring root (j + 1))).tok = .CL1
      rw [hw.2.2.1]
      exact ht)
  have hbank :
      (resetColdPrivateInteriorBankAt ring root C j).1.tok = t ∧
      (resetColdPrivateInteriorBankAt ring root C j).1.bit =
        (C (site ring root j)).bit ∧
      (resetColdPrivateInteriorBankAt ring root C j).2.tok = .E ∧
      (resetColdPrivateInteriorBankAt ring root C j).2.bit =
        (C (site ring root (j + 1))).bit := by
    unfold resetColdPrivateInteriorBankAt
    have hr := hbankRaw
    simp only [bankCell, hw.2.2.1] at hr ⊢
    exact ⟨hr.1, hr.2.2.1, hr.2.1, hr.2.2.2⟩
  have hf := resetColdPrivateInteriorRowFields
    ring root C hc hsp j hj hjb t .E
    (C (site ring root j)).bit
    (C (site ring root (j + 1))).bit hbank
  have hbits := resetColdPrivateInteriorBitFrame
    ring root C hc j hj hjb hf.2.1 hf.2.2.2
  have hnewWorker := resetColdPrivateInteriorWorkerBackward
    ring root C hc j hj hjb t t hw hf.1 hf.2.2.1
  have htNew : resetColdPrivateComparatorToken t := by
    rcases ht with hzero | hone
    · exact Or.inr (Or.inr (Or.inl hzero))
    · exact Or.inr (Or.inr (Or.inr hone))
  have hhead := resetColdPrivateHeadNoIRBitFrame
    ring root C ((protocol q).step ring C (site ring root j))
    hbits
    (resetColdPrivateComparatorNoIR ring root C (j + 1) t
      hw htNew)
    (resetColdPrivateComparatorNoIR ring root
      ((protocol q).step ring C (site ring root j))
      j t hnewWorker htNew)
  have hmode :
      (((protocol q).step ring C (site ring root j)) root).mode =
        .CWAIT :=
    (resetColdPrivateInteriorRootModeFrame
      ring root C hc j hj hjb).trans hm
  have hgoodCR : t = .CR1 →
      resetColdPrivateMatchedPrefix ring root
        ((protocol q).step ring C (site ring root j)) j := by
    intro he
    rcases ht with hz | ho
    · rw [hz] at he
      cases he
    · rw [ho] at he
      cases he
  have hbadCR : t = .CR0 →
      resetColdPrivateMismatchPrefix ring root
        ((protocol q).step ring C (site ring root j)) j := by
    intro he
    rcases ht with hz | ho
    · rw [hz] at he
      cases he
    · rw [ho] at he
      cases he
  have hgoodCL : t = .CL1 →
      resetColdPrivateMatchedPrefix ring root
        ((protocol q).step ring C (site ring root j))
        (compileAdvice q).b := by
    intro he
    exact resetColdPrivateMatchedPrefixBitFrame
      ring root C ((protocol q).step ring C (site ring root j))
      (compileAdvice q).b hbits (hgood he)
  have hbadCL : t = .CL0 →
      resetColdPrivateMismatchPrefix ring root
        ((protocol q).step ring C (site ring root j))
        (compileAdvice q).b := by
    intro he
    exact resetColdPrivateMismatchPrefixBitFrame
      ring root C ((protocol q).step ring C (site ring root j))
      (compileAdvice q).b hbits (hbad he)
  have hvalueNew :
      resetColdPrivateHeadValue ring root
        ((protocol q).step ring C (site ring root j)) = h + 1 := by
    rw [hhead, hv]
  exact ⟨resetColdPrivateAuthCWaitOfWorker
    ring root ((protocol q).step ring C (site ring root j))
    h j t hb hmode hnewWorker htNew hvalueNew
    hgoodCR hgoodCL hbadCR hbadCL, hhead⟩

/-- Finite indexed spike, used for an arbitrary one-worker
position rather than only the least-significant digit. -/
theorem resetColdPrivateIndexedSpike (width index value : Nat)
    (hindex : index < width) :
    (List.ofFn (fun i : Fin width =>
      if i.val = index then value else 0)).sum = value := by
  have heq :
      (List.ofFn (fun i : Fin width =>
        if i.val = index then value else 0)).sum =
      (List.ofFn (fun i : Fin width =>
        if i = (⟨index, hindex⟩ : Fin width)
        then value else 0)).sum := by
    apply ofFn_sum_eq
    intro i
    by_cases hi : i.val = index
    · have he : i = (⟨index, hindex⟩ : Fin width) :=
        Fin.ext hi
      simp [hi, he]
    · have he : i ≠ (⟨index, hindex⟩ : Fin width) := by
        intro he
        have hv := congrArg Fin.val he
        exact hi hv
      simp [hi, he]
  rw [heq]
  exact resetClockOfFnSpike width ⟨index, hindex⟩ value

/-- A unique IR worker at digit j has carry weight 2^j;
a unique other worker has zero carry weight. -/
theorem resetColdPrivateCarryOnlyWorker {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (j : Nat) (t : BTok)
    (hw : resetColdPrivateOnlyWorker ring root C j t) :
    resetColdPrivateCarryValue ring root C =
      (if t = .IR then 2 ^ j else 0) := by
  have hindex : j - 1 < (compileAdvice q).b := by
    have hj := hw.1
    have hjb := hw.2.1
    omega
  have hpoint (i : Fin (compileAdvice q).b) :
      (if (C (site ring root (i.val + 1))).tok = .IR
        then 2 ^ (i.val + 1) else 0) =
      (if i.val = j - 1
        then (if t = .IR then 2 ^ j else 0)
        else 0) := by
    by_cases he : i.val = j - 1
    · have hs : i.val + 1 = j := by
        have hj := hw.1
        omega
      rw [hs, hw.2.2.1]
      simp [he]
    · have hs : i.val + 1 ≠ j := by
        have hj := hw.1
        omega
      have hib : i.val + 1 ≤ (compileAdvice q).b := by
        have hh := i.isLt
        omega
      have hzero := hw.2.2.2 (i.val + 1)
        (by omega) hib hs
      rw [hzero]
      simp [he]
  unfold resetColdPrivateCarryValue
  calc
    (List.ofFn (fun i : Fin (compileAdvice q).b =>
      if (C (site ring root (i.val + 1))).tok = .IR
      then 2 ^ (i.val + 1) else 0)).sum =
      (List.ofFn (fun i : Fin (compileAdvice q).b =>
        if i.val = j - 1
        then (if t = .IR then 2 ^ j else 0)
        else 0)).sum := by
          apply ofFn_sum_eq
          exact hpoint
    _ = (if t = .IR then 2 ^ j else 0) :=
      resetColdPrivateIndexedSpike
        (compileAdvice q).b (j - 1)
        (if t = .IR then 2 ^ j else 0) hindex

/-- Toggle one arbitrary protected bit. The balance uses
one indexed spike on each side; no subtraction of natural
numbers or informal binary arithmetic is needed. -/
theorem resetColdPrivateBitToggleBalance {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n) (k : Nat)
    (hk : 1 ≤ k) (hkb : k ≤ (compileAdvice q).b)
    (htoggle : (D (site ring root k)).bit =
      !(C (site ring root k)).bit)
    (hother : ∀ i : Nat, 1 ≤ i →
      i ≤ (compileAdvice q).b → i ≠ k →
      (D (site ring root i)).bit =
        (C (site ring root i)).bit) :
    resetColdPrivateBitValue ring root D +
      (if (C (site ring root k)).bit
        then 2 ^ (k - 1) else 0) =
    resetColdPrivateBitValue ring root C +
      (if !(C (site ring root k)).bit
        then 2 ^ (k - 1) else 0) := by
  have hindex : k - 1 < (compileAdvice q).b := by omega
  have hpoint (i : Fin (compileAdvice q).b) :
      (if (D (site ring root (i.val + 1))).bit = true
        then 2 ^ i.val else 0) +
        (if i.val = k - 1
          then (if (C (site ring root k)).bit
            then 2 ^ (k - 1) else 0) else 0) =
      (if (C (site ring root (i.val + 1))).bit = true
        then 2 ^ i.val else 0) +
        (if i.val = k - 1
          then (if !(C (site ring root k)).bit
            then 2 ^ (k - 1) else 0) else 0) := by
    by_cases he : i.val = k - 1
    · have hs : i.val + 1 = k := by omega
      rw [hs, htoggle, he]
      cases hbit : (C (site ring root k)).bit <;>
        simp [he, hbit]
    · have hs : i.val + 1 ≠ k := by omega
      have hib : i.val + 1 ≤ (compileAdvice q).b := by
        have hi := i.isLt
        omega
      rw [hother (i.val + 1) (by omega) hib hs]
      simp [he]
  have hsum :
      (List.ofFn (fun i : Fin (compileAdvice q).b =>
        (if (D (site ring root (i.val + 1))).bit = true
          then 2 ^ i.val else 0) +
        (if i.val = k - 1
          then (if (C (site ring root k)).bit
            then 2 ^ (k - 1) else 0) else 0))).sum =
      (List.ofFn (fun i : Fin (compileAdvice q).b =>
        (if (C (site ring root (i.val + 1))).bit = true
          then 2 ^ i.val else 0) +
        (if i.val = k - 1
          then (if !(C (site ring root k)).bit
            then 2 ^ (k - 1) else 0) else 0))).sum := by
    apply ofFn_sum_eq
    exact hpoint
  rw [ofFn_sum_add, ofFn_sum_add] at hsum
  rw [resetColdPrivateIndexedSpike (compileAdvice q).b
      (k - 1)
      (if (C (site ring root k)).bit
        then 2 ^ (k - 1) else 0) hindex,
    resetColdPrivateIndexedSpike (compileAdvice q).b
      (k - 1)
      (if !(C (site ring root k)).bit
        then 2 ^ (k - 1) else 0) hindex] at hsum
  change resetColdPrivateBitValue ring root D +
    (if (C (site ring root k)).bit
      then 2 ^ (k - 1) else 0) =
    resetColdPrivateBitValue ring root C +
    (if !(C (site ring root k)).bit
      then 2 ^ (k - 1) else 0) at hsum
  exact hsum

/-- Full IR BANK row, adding the source-bit frame missing from
the earlier three-field symbolic increment certificate. -/
theorem resetColdPrivateIRForwardBank
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : 1 ≤ x.role) (hxb : x.role < b)
    (hy : y.role = x.role + 1)
    (htx : x.tok = .IR) (hty : y.tok = .E) :
    (bankPair x y y.role b theta).1.tok = .E ∧
      (bankPair x y y.role b theta).1.bit = x.bit ∧
      (bankPair x y y.role b theta).2.tok =
        (if y.bit then .IR else .AL) ∧
      (bankPair x y y.role b theta).2.bit = !y.bit := by
  have hr := resetColdPrivateIRAdvanceRow
    x y b theta hx hxb hy htx hty
  have hxne : x.role ≠ 0 := by omega
  have hyne : y.role ≠ 0 := by omega
  have hxle : x.role ≤ b := by omega
  have hyle : y.role ≤ b := by omega
  have hxneq : x.role ≠ b := by omega
  have hsource : (bankPair x y y.role b theta).1.bit =
      x.bit := by
    simp [bankPair, hx, hxb, hy, htx, hty,
      hxne, hyne, hxle, hyle, hxneq]
  exact ⟨hr.1, hsource, hr.2.2, hr.2.1⟩

/-- A physical forward IR service toggles precisely its next
digit. If that digit was one, IR shifts to the next weight;
otherwise it becomes a returning AL. The total numerical
head is invariant under the actual protocol step. -/
theorem resetColdPrivateIRForwardPhysical {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (j h : Nat) (hj : 1 ≤ j)
    (hjb : j < (compileAdvice q).b)
    (hb : h + 1 ≤ (compileAdvice q).K)
    (hm : (C root).mode = .IWAIT)
    (hw : resetColdPrivateOnlyWorker ring root C j .IR)
    (hv : resetColdPrivateHeadValue ring root C = h + 1) :
    ResetColdPrivateLiveShapeAuth ring root
      ((protocol q).step ring C (site ring root j)) ∧
    resetColdPrivateHeadValue ring root
      ((protocol q).step ring C (site ring root j)) =
        resetColdPrivateHeadValue ring root C := by
  have hempty : (C (site ring root (j + 1))).tok = .E :=
    hw.2.2.2 (j + 1) (by omega) (by omega) (by omega)
  have hbankRaw := resetColdPrivateIRForwardBank
    (bankCell (C (site ring root j)) j)
    (bankCell (C (site ring root (j + 1))) (j + 1))
    (compileAdvice q).b (compileAdvice q).theta
    (by change 1 ≤ j; exact hj)
    (by change j < (compileAdvice q).b; exact hjb)
    rfl
    (by change (C (site ring root j)).tok = .IR; exact hw.2.2.1)
    (by change (C (site ring root (j + 1))).tok = .E; exact hempty)
  have hbank :
      (resetColdPrivateInteriorBankAt ring root C j).1.tok = .E ∧
      (resetColdPrivateInteriorBankAt ring root C j).1.bit =
        (C (site ring root j)).bit ∧
      (resetColdPrivateInteriorBankAt ring root C j).2.tok =
        (if (C (site ring root (j + 1))).bit
          then BTok.IR else BTok.AL) ∧
      (resetColdPrivateInteriorBankAt ring root C j).2.bit =
        !(C (site ring root (j + 1))).bit := by
    unfold resetColdPrivateInteriorBankAt
    have hr := hbankRaw
    simp only [bankCell] at hr ⊢
    exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2⟩
  have hf := resetColdPrivateInteriorRowFields
    ring root C hc hsp j hj hjb
    .E
    (if (C (site ring root (j + 1))).bit
      then BTok.IR else BTok.AL)
    (C (site ring root j)).bit
    (!(C (site ring root (j + 1))).bit) hbank
  have hnewWorker := resetColdPrivateInteriorWorkerForward
    ring root C hc j hj hjb .IR
    (if (C (site ring root (j + 1))).bit
      then BTok.IR else BTok.AL)
    hw hf.1 hf.2.2.1
  have htNew : resetColdPrivateCarryToken
      (if (C (site ring root (j + 1))).bit
        then BTok.IR else BTok.AL) := by
    unfold resetColdPrivateCarryToken
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hother : ∀ i : Nat, 1 ≤ i →
      i ≤ (compileAdvice q).b → i ≠ j + 1 →
      (((protocol q).step ring C (site ring root j))
        (site ring root i)).bit =
          (C (site ring root i)).bit := by
    intro i hi hib hine
    by_cases he : i = j
    · subst i
      exact hf.2.1
    · rw [resetColdPrivateInteriorOtherFrame
        ring root C hc j hj hjb i hi hib he hine]
  have hbalance := resetColdPrivateBitToggleBalance
    ring root C
      ((protocol q).step ring C (site ring root j))
    (j + 1) (by omega) (by omega) hf.2.2.2 hother
  have hindex : j + 1 - 1 = j := by omega
  rw [hindex] at hbalance
  have hcarryOld :
      resetColdPrivateCarryValue ring root C = 2 ^ j := by
    rw [resetColdPrivateCarryOnlyWorker ring root C j .IR hw]
    simp
  have hcarryNew :
      resetColdPrivateCarryValue ring root
        ((protocol q).step ring C (site ring root j)) =
      (if (C (site ring root (j + 1))).bit
        then 2 ^ (j + 1) else 0) := by
    rw [resetColdPrivateCarryOnlyWorker
      ring root ((protocol q).step ring C (site ring root j))
      (j + 1)
      (if (C (site ring root (j + 1))).bit
        then BTok.IR else BTok.AL) hnewWorker]
    cases hbit : (C (site ring root (j + 1))).bit <;>
      simp [hbit]
  have hweight := resetColdLatchedPrivateIRWeight j
    (C (site ring root (j + 1))).bit
  have hhead :
      resetColdPrivateHeadValue ring root
        ((protocol q).step ring C (site ring root j)) =
          resetColdPrivateHeadValue ring root C := by
    unfold resetColdPrivateHeadValue
    rw [hcarryOld, hcarryNew]
    omega
  have hmode :
      (((protocol q).step ring C (site ring root j)) root).mode =
        .IWAIT :=
    (resetColdPrivateInteriorRootModeFrame
      ring root C hc j hj hjb).trans hm
  have hvalueNew :
      resetColdPrivateHeadValue ring root
        ((protocol q).step ring C (site ring root j)) = h + 1 := by
    rw [hhead, hv]
  have hweak : ResetColdPrivateLiveShape ring root
      ((protocol q).step ring C (site ring root j)) :=
    Or.inr (Or.inr (Or.inr
      ⟨h, j + 1,
        (if (C (site ring root (j + 1))).bit
          then BTok.IR else BTok.AL),
        hb, hmode, hnewWorker, htNew, hvalueNew⟩))
  have hnotC :
      (((protocol q).step ring C (site ring root j)) root).mode ≠
        .CWAIT := by
    rw [hmode]
    intro he
    cases he
  exact ⟨resetColdPrivateAuthOfWeakNonCWait ring root
    ((protocol q).step ring C (site ring root j))
    hnotC hweak, hhead⟩

/-- The sole apparently overflowing top forward IR row has
an impossible OLD predecessor whenever the next top bit is set.
The contradiction is at the input, before any state update. -/
theorem resetColdPrivateIRTopBlocked {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (hshape : ResetColdPrivateLiveShape ring root C)
    (j : Nat) (htop : j + 1 = (compileAdvice q).b)
    (hw : resetColdPrivateOnlyWorker ring root C j .IR)
    (hbit : (C (site ring root (compileAdvice q).b)).bit =
      true) : False := by
  have heq : j = (compileAdvice q).b - 1 := by omega
  have hsrc :
      (C (site ring root ((compileAdvice q).b - 1))).tok =
        .IR := by
    rw [← heq]
    exact hw.2.2.1
  exact resetColdPrivateTopPredecessorImpossible
    ring root C hwidth hshape hsrc hbit

end Counter
end L3

/-!
Root return rows, AL retreat, interior idle holds,
and incoming-root LIVE assembly.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Literal CWAIT/CL0 root return: the result is ARMED,
the returning byte is consumed, and its digit bit is framed. -/
theorem resetColdPrivateRootCL0Bank
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : x.role = 0) (hg : x.grant = false)
    (hy : y.role = 1) (hb : 1 ≤ b)
    (hm : x.mode = .CWAIT) (ht : y.tok = .CL0) :
    (bankPair x y 1 b theta).1.mode = .ARMED ∧
      (bankPair x y 1 b theta).2.tok = .E ∧
      (bankPair x y 1 b theta).2.bit = y.bit := by
  simp [bankPair, hx, hg, hy, hb, hm, ht, isRetTok]

/-- Literal IWAIT/AL root return: the result is CSTART,
the returning byte is consumed, and its digit bit is framed. -/
theorem resetColdPrivateRootALBank
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : x.role = 0) (hg : x.grant = false)
    (hy : y.role = 1) (hb : 1 ≤ b)
    (hm : x.mode = .IWAIT) (ht : y.tok = .AL) :
    (bankPair x y 1 b theta).1.mode = .CSTART ∧
      (bankPair x y 1 b theta).2.tok = .E ∧
      (bankPair x y 1 b theta).2.bit = y.bit := by
  simp [bankPair, hx, hg, hy, hb, hm, ht, isRetTok]

/-- True full-protocol projection of the CL0 root-return row. -/
theorem resetColdPrivateRootCL0PhysicalFields {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hm : (C root).mode = .CWAIT)
    (ht : (C (site ring root 1)).tok = .CL0) :
    (((protocol q).step ring C root) root).mode = .ARMED ∧
      (((protocol q).step ring C root)
        (site ring root 1)).tok = .E ∧
      (((protocol q).step ring C root)
        (site ring root 1)).bit =
          (C (site ring root 1)).bit := by
  have hb : 1 ≤ (compileAdvice q).b := by
    have hh := resetTrialCompiledWidth q
    omega
  have hroot : (C root).pack.val = 0 := by
    simpa only [site] using hc 0 (by omega)
  have hone : (C (site ring root 1)).pack.val = 1 :=
    hc 1 hb
  have hpost :
      packNext 0 1 (compileAdvice q).b = 1 := by
    unfold packNext
    rw [if_pos (by omega : 0 < (compileAdvice q).b)]
  have hrowRaw := resetColdPrivateRootCL0Bank
    (bankCell (C root) 0)
    (bankCell (C (site ring root 1)) 1)
    (compileAdvice q).b (compileAdvice q).theta
    rfl
    (by change (C root).grant = false; exact hg)
    rfl hb
    (by change (C root).mode = .CWAIT; exact hm)
    (by change (C (site ring root 1)).tok = .CL0; exact ht)
  have hrow :
      (resetBankOld (C root)
        (C (site ring root 1))).1.mode = .ARMED ∧
      (resetBankOld (C root)
        (C (site ring root 1))).2.tok = .E ∧
      (resetBankOld (C root)
        (C (site ring root 1))).2.bit =
          (C (site ring root 1)).bit := by
    simpa only [resetBankOld, hroot, hone, hpost, bankCell]
      using hrowRaw
  have hp := resetPhysicalEdgeBankTrip ring C root
    (resetColdRootPortDistinct ring C root hc) hsp
  have hmode :=
    congrArg (fun z : Mode × Bool × BTok => z.1) hp.1
  have htok :=
    congrArg (fun z : Mode × Bool × BTok => z.2.2) hp.2
  have hbit :=
    congrArg (fun z : Mode × Bool × BTok => z.2.1) hp.2
  exact ⟨hmode.trans hrow.1,
    htok.trans hrow.2.1, hbit.trans hrow.2.2⟩

/-- True full-protocol projection of the AL root-return row. -/
theorem resetColdPrivateRootALPhysicalFields {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hm : (C root).mode = .IWAIT)
    (ht : (C (site ring root 1)).tok = .AL) :
    (((protocol q).step ring C root) root).mode = .CSTART ∧
      (((protocol q).step ring C root)
        (site ring root 1)).tok = .E ∧
      (((protocol q).step ring C root)
        (site ring root 1)).bit =
          (C (site ring root 1)).bit := by
  have hb : 1 ≤ (compileAdvice q).b := by
    have hh := resetTrialCompiledWidth q
    omega
  have hroot : (C root).pack.val = 0 := by
    simpa only [site] using hc 0 (by omega)
  have hone : (C (site ring root 1)).pack.val = 1 :=
    hc 1 hb
  have hpost :
      packNext 0 1 (compileAdvice q).b = 1 := by
    unfold packNext
    rw [if_pos (by omega : 0 < (compileAdvice q).b)]
  have hrowRaw := resetColdPrivateRootALBank
    (bankCell (C root) 0)
    (bankCell (C (site ring root 1)) 1)
    (compileAdvice q).b (compileAdvice q).theta
    rfl
    (by change (C root).grant = false; exact hg)
    rfl hb
    (by change (C root).mode = .IWAIT; exact hm)
    (by change (C (site ring root 1)).tok = .AL; exact ht)
  have hrow :
      (resetBankOld (C root)
        (C (site ring root 1))).1.mode = .CSTART ∧
      (resetBankOld (C root)
        (C (site ring root 1))).2.tok = .E ∧
      (resetBankOld (C root)
        (C (site ring root 1))).2.bit =
          (C (site ring root 1)).bit := by
    simpa only [resetBankOld, hroot, hone, hpost, bankCell]
      using hrowRaw
  have hp := resetPhysicalEdgeBankTrip ring C root
    (resetColdRootPortDistinct ring C root hc) hsp
  have hmode :=
    congrArg (fun z : Mode × Bool × BTok => z.1) hp.1
  have htok :=
    congrArg (fun z : Mode × Bool × BTok => z.2.2) hp.2
  have hbit :=
    congrArg (fun z : Mode × Bool × BTok => z.2.1) hp.2
  exact ⟨hmode.trans hrow.1,
    htok.trans hrow.2.1, hbit.trans hrow.2.2⟩

/-- Consuming the only worker at digit one leaves no worker
on the entire protected physical word. -/
theorem resetColdPrivateRootConsumeNoWorkers {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : Complete ring C root)
    (t : BTok)
    (hw : resetColdPrivateOnlyWorker ring root C 1 t)
    (hfirst : (((protocol q).step ring C root)
      (site ring root 1)).tok = .E) :
    resetColdPrivateNoWorkers ring root
      ((protocol q).step ring C root) := by
  intro i hi hib
  by_cases hone : i = 1
  · subst i
    exact hfirst
  · rw [resetColdOutgoingRootOtherDigitsFrame
      ring C root hc i (by omega) hib]
    exact hw.2.2.2 i hi hib hone

/-- The root return consumes a token but does not toggle a
digit bit; all higher digits are genuine physical frames. -/
theorem resetColdPrivateRootConsumeBitFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : Complete ring C root)
    (hfirst : (((protocol q).step ring C root)
      (site ring root 1)).bit =
        (C (site ring root 1)).bit) :
    ∀ i : Nat, 1 ≤ i → i ≤ (compileAdvice q).b →
      (((protocol q).step ring C root)
        (site ring root i)).bit =
          (C (site ring root i)).bit := by
  intro i hi hib
  by_cases hone : i = 1
  · subst i
    exact hfirst
  · rw [resetColdOutgoingRootOtherDigitsFrame
      ring C root hc i (by omega) hib]

/-- A unique non-IR worker cannot hide a second IR token. -/
theorem resetColdPrivateOnlyWorkerNotIR {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (j : Nat) (t : BTok)
    (hw : resetColdPrivateOnlyWorker ring root C j t)
    (ht : t ≠ .IR) :
    ∀ i : Nat, 1 ≤ i → i ≤ (compileAdvice q).b →
      (C (site ring root i)).tok ≠ .IR := by
  intro i hi hib
  by_cases he : i = j
  · subst i
    rw [hw.2.2.1]
    exact ht
  · rw [hw.2.2.2 i hi hib he]
    intro h
    cases h

/-- An entirely empty worker word has no pending carry. -/
theorem resetColdPrivateNoWorkersNotIR {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hn : resetColdPrivateNoWorkers ring root C) :
    ∀ i : Nat, 1 ≤ i → i ≤ (compileAdvice q).b →
      (C (site ring root i)).tok ≠ .IR := by
  intro i hi hib
  rw [hn i hi hib]
  intro h
  cases h

/-- Physical CL0 return rearms the root below K. The
strict bound is authenticated by a full-word mismatch. -/
theorem resetColdPrivateCL0RootPhysical {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (h : Nat) (hb : h + 1 ≤ (compileAdvice q).K)
    (hm : (C root).mode = .CWAIT)
    (hw : resetColdPrivateOnlyWorker ring root C 1 .CL0)
    (hv : resetColdPrivateHeadValue ring root C = h + 1)
    (ha : ResetColdPrivateLiveShapeAuth ring root C) :
    ResetColdPrivateLiveShapeAuth ring root
      ((protocol q).step ring C root) ∧
    resetColdPrivateHeadValue ring root
      ((protocol q).step ring C root) =
        resetColdPrivateHeadValue ring root C := by
  have hf := resetColdPrivateRootCL0PhysicalFields
    ring root C hc hg hsp hm hw.2.2.1
  have hn := resetColdPrivateRootConsumeNoWorkers
    ring root C hc .CL0 hw hf.2.1
  have hbits := resetColdPrivateRootConsumeBitFrame
    ring root C hc hf.2.2
  have hhead := resetColdPrivateHeadNoIRBitFrame
    ring root C ((protocol q).step ring C root)
    hbits
    (resetColdPrivateOnlyWorkerNotIR ring root C 1 .CL0
      hw (by intro he; cases he))
    (resetColdPrivateNoWorkersNotIR ring root
      ((protocol q).step ring C root) hn)
  have hstrict : h + 1 < (compileAdvice q).K := by
    have hh := resetColdPrivateCL0BelowKOfAuth
      ring root C hwidth ha hm hw.2.2.1
    rw [hv] at hh
    exact hh
  have hval :
      resetColdPrivateHeadValue ring root
        ((protocol q).step ring C root) = h + 1 :=
    hhead.trans hv
  have hweak : ResetColdPrivateLiveShape ring root
      ((protocol q).step ring C root) :=
    Or.inl ⟨h + 1, hstrict, hf.1, hn, hval⟩
  have hnot :
      (((protocol q).step ring C root) root).mode ≠ .CWAIT := by
    rw [hf.1]
    intro he
    cases he
  exact ⟨resetColdPrivateAuthOfWeakNonCWait
    ring root ((protocol q).step ring C root) hnot hweak,
    hhead⟩

/-- Physical AL return finishes the carry, leaves h+1 fixed,
and launches an empty-worker CSTART comparator phase. -/
theorem resetColdPrivateALRootPhysical {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hsp : (compileAdvice q).useSmall = false)
    (h : Nat) (hb : h + 1 ≤ (compileAdvice q).K)
    (hm : (C root).mode = .IWAIT)
    (hw : resetColdPrivateOnlyWorker ring root C 1 .AL)
    (hv : resetColdPrivateHeadValue ring root C = h + 1) :
    ResetColdPrivateLiveShapeAuth ring root
      ((protocol q).step ring C root) ∧
    resetColdPrivateHeadValue ring root
      ((protocol q).step ring C root) =
        resetColdPrivateHeadValue ring root C := by
  have hf := resetColdPrivateRootALPhysicalFields
    ring root C hc hg hsp hm hw.2.2.1
  have hn := resetColdPrivateRootConsumeNoWorkers
    ring root C hc .AL hw hf.2.1
  have hbits := resetColdPrivateRootConsumeBitFrame
    ring root C hc hf.2.2
  have hhead := resetColdPrivateHeadNoIRBitFrame
    ring root C ((protocol q).step ring C root)
    hbits
    (resetColdPrivateOnlyWorkerNotIR ring root C 1 .AL
      hw (by intro he; cases he))
    (resetColdPrivateNoWorkersNotIR ring root
      ((protocol q).step ring C root) hn)
  have hval :
      resetColdPrivateHeadValue ring root
        ((protocol q).step ring C root) = h + 1 :=
    hhead.trans hv
  have hweak : ResetColdPrivateLiveShape ring root
      ((protocol q).step ring C root) :=
    Or.inr (Or.inl ⟨h, hb, hf.1, hn, hval⟩)
  have hnot :
      (((protocol q).step ring C root) root).mode ≠ .CWAIT := by
    rw [hf.1]
    intro he
    cases he
  exact ⟨resetColdPrivateAuthOfWeakNonCWait
    ring root ((protocol q).step ring C root) hnot hweak,
    hhead⟩

/-- A LIVE root CL0 return is the same physical successor;
it is not a fabricated ghost rearm transition. -/
theorem resetColdPrivateCL0RootLive {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (h : Nat) (hb : h + 1 ≤ (compileAdvice q).K)
    (hm : (C root).mode = .CWAIT)
    (hw : resetColdPrivateOnlyWorker ring root C 1 .CL0)
    (hv : resetColdPrivateHeadValue ring root C = h + 1)
    (ha : ResetColdPrivateLiveShapeAuth ring root C)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) root = .live D started') :
    ResetColdPrivateLiveShapeAuth ring root D ∧
      resetColdPrivateHeadValue ring root D =
        resetColdPrivateHeadValue ring root C := by
  have hg := resetColdPrivateLiveOutgoingGrantFree
    ring root C D started started' hc hsp hnext
  have hp := resetColdPrivateLivePhysical
    ring root root C D started started' hnext
  rw [hp]
  exact resetColdPrivateCL0RootPhysical ring root C
    hc hg hsp hwidth h hb hm hw hv ha

/-- A LIVE root AL return is the true physical CSTART step. -/
theorem resetColdPrivateALRootLive {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (h : Nat) (hb : h + 1 ≤ (compileAdvice q).K)
    (hm : (C root).mode = .IWAIT)
    (hw : resetColdPrivateOnlyWorker ring root C 1 .AL)
    (hv : resetColdPrivateHeadValue ring root C = h + 1)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) root = .live D started') :
    ResetColdPrivateLiveShapeAuth ring root D ∧
      resetColdPrivateHeadValue ring root D =
        resetColdPrivateHeadValue ring root C := by
  have hg := resetColdPrivateLiveOutgoingGrantFree
    ring root C D started started' hc hsp hnext
  have hp := resetColdPrivateLivePhysical
    ring root root C D started started' hnext
  rw [hp]
  exact resetColdPrivateALRootPhysical ring root C
    hc hg hsp h hb hm hw hv

/-- An AL responder retreats to the predecessor without
changing either physical digit bit. -/
theorem resetColdPrivateALRetreatBank
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : 1 ≤ x.role) (hxb : x.role < b)
    (hy : y.role = x.role + 1)
    (he : x.tok = .E) (ht : y.tok = .AL) :
    (bankPair x y y.role b theta).1.tok = .AL ∧
      (bankPair x y y.role b theta).2.tok = .E ∧
      (bankPair x y y.role b theta).1.bit = x.bit ∧
      (bankPair x y y.role b theta).2.bit = y.bit := by
  have hxne : x.role ≠ 0 := by omega
  have hyne : y.role ≠ 0 := by omega
  have hxle : x.role ≤ b := by omega
  have hyle : y.role ≤ b := by omega
  have hxneq : x.role ≠ b := by omega
  have hnlt : ¬ b < x.role + 1 := by omega
  simp [bankPair, hx, hxb, hy, he, ht,
    hxne, hyne, hxle, hyle, hxneq, hnlt] <;>
    repeat (first | rfl | split | omega)

/-- The AL backward step is physical, unique-worker, and
head-preserving; it continues IWAIT without spurious comparator
provenance. -/
theorem resetColdPrivateALRetreatPhysical {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (j h : Nat) (hj : 1 ≤ j)
    (hjb : j < (compileAdvice q).b)
    (hb : h + 1 ≤ (compileAdvice q).K)
    (hm : (C root).mode = .IWAIT)
    (hw : resetColdPrivateOnlyWorker ring root C (j + 1) .AL)
    (hv : resetColdPrivateHeadValue ring root C = h + 1) :
    ResetColdPrivateLiveShapeAuth ring root
      ((protocol q).step ring C (site ring root j)) ∧
    resetColdPrivateHeadValue ring root
      ((protocol q).step ring C (site ring root j)) =
        resetColdPrivateHeadValue ring root C := by
  have hempty : (C (site ring root j)).tok = .E :=
    hw.2.2.2 j hj (by omega) (by omega)
  have hraw := resetColdPrivateALRetreatBank
    (bankCell (C (site ring root j)) j)
    (bankCell (C (site ring root (j + 1))) (j + 1))
    (compileAdvice q).b (compileAdvice q).theta
    (by change 1 ≤ j; exact hj)
    (by change j < (compileAdvice q).b; exact hjb)
    rfl
    (by change (C (site ring root j)).tok = .E; exact hempty)
    (by change (C (site ring root (j + 1))).tok = .AL; exact hw.2.2.1)
  have hbank :
      (resetColdPrivateInteriorBankAt ring root C j).1.tok = .AL ∧
      (resetColdPrivateInteriorBankAt ring root C j).1.bit =
        (C (site ring root j)).bit ∧
      (resetColdPrivateInteriorBankAt ring root C j).2.tok = .E ∧
      (resetColdPrivateInteriorBankAt ring root C j).2.bit =
        (C (site ring root (j + 1))).bit := by
    unfold resetColdPrivateInteriorBankAt
    have hr := hraw
    simp only [bankCell] at hr ⊢
    exact ⟨hr.1, hr.2.2.1, hr.2.1, hr.2.2.2⟩
  have hf := resetColdPrivateInteriorRowFields
    ring root C hc hsp j hj hjb .AL .E
    (C (site ring root j)).bit
    (C (site ring root (j + 1))).bit hbank
  have hbits := resetColdPrivateInteriorBitFrame
    ring root C hc j hj hjb hf.2.1 hf.2.2.2
  have hnewWorker := resetColdPrivateInteriorWorkerBackward
    ring root C hc j hj hjb .AL .AL hw hf.1 hf.2.2.1
  have hhead := resetColdPrivateHeadNoIRBitFrame
    ring root C ((protocol q).step ring C (site ring root j))
    hbits
    (resetColdPrivateOnlyWorkerNotIR ring root C (j + 1) .AL
      hw (by intro he; cases he))
    (resetColdPrivateOnlyWorkerNotIR ring root
      ((protocol q).step ring C (site ring root j)) j .AL
      hnewWorker (by intro he; cases he))
  have hmode :
      (((protocol q).step ring C (site ring root j)) root).mode =
        .IWAIT :=
    (resetColdPrivateInteriorRootModeFrame
      ring root C hc j hj hjb).trans hm
  have hval :
      resetColdPrivateHeadValue ring root
        ((protocol q).step ring C (site ring root j)) = h + 1 :=
    hhead.trans hv
  have hweak : ResetColdPrivateLiveShape ring root
      ((protocol q).step ring C (site ring root j)) :=
    Or.inr (Or.inr (Or.inr
      ⟨h, j, BTok.AL, hb, hmode, hnewWorker,
        Or.inr rfl, hval⟩))
  have hnot :
      (((protocol q).step ring C (site ring root j)) root).mode ≠
        .CWAIT := by
    rw [hmode]
    intro he
    cases he
  exact ⟨resetColdPrivateAuthOfWeakNonCWait ring root
    ((protocol q).step ring C (site ring root j)) hnot hweak,
    hhead⟩

/-- An empty internal edge, or a return token serving as
initiator with an empty successor, is a literal BANK hold. -/
theorem resetColdPrivateInteriorHoldBank
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : 1 ≤ x.role) (hxb : x.role < b)
    (hy : y.role = x.role + 1)
    (ht : x.tok = .E ∨ x.tok = .AL ∨
      x.tok = .CL0 ∨ x.tok = .CL1)
    (he : y.tok = .E) :
    (bankPair x y y.role b theta).1.tok = x.tok ∧
      (bankPair x y y.role b theta).1.bit = x.bit ∧
      (bankPair x y y.role b theta).2.tok = y.tok ∧
      (bankPair x y y.role b theta).2.bit = y.bit := by
  have hxne : x.role ≠ 0 := by omega
  have hyne : y.role ≠ 0 := by omega
  have hxle : x.role ≤ b := by omega
  have hyle : y.role ≤ b := by omega
  have hxneq : x.role ≠ b := by omega
  have hnlt : ¬ b < x.role + 1 := by omega
  rcases ht with ht | ht | ht | ht
  all_goals
    simp [bankPair, hx, hxb, hy, ht, he,
      hxne, hyne, hxle, hyle, hxneq, hnlt] <;>
      repeat (first | rfl | split | omega)

/-- Exact physical frame at every inactive interior BANK pair,
including the source-side AL/CL holds. -/
theorem resetColdPrivateInteriorHoldPhysical {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (j : Nat) (hj : 1 ≤ j)
    (hjb : j < (compileAdvice q).b)
    (ht : (C (site ring root j)).tok = .E ∨
      (C (site ring root j)).tok = .AL ∨
      (C (site ring root j)).tok = .CL0 ∨
      (C (site ring root j)).tok = .CL1)
    (he : (C (site ring root (j + 1))).tok = .E)
    (ha : ResetColdPrivateLiveShapeAuth ring root C) :
    ResetColdPrivateLiveShapeAuth ring root
      ((protocol q).step ring C (site ring root j)) ∧
    resetColdPrivateHeadValue ring root
      ((protocol q).step ring C (site ring root j)) =
        resetColdPrivateHeadValue ring root C := by
  have hraw := resetColdPrivateInteriorHoldBank
    (bankCell (C (site ring root j)) j)
    (bankCell (C (site ring root (j + 1))) (j + 1))
    (compileAdvice q).b (compileAdvice q).theta
    (by change 1 ≤ j; exact hj)
    (by change j < (compileAdvice q).b; exact hjb)
    rfl
    (by
      change (C (site ring root j)).tok = .E ∨
        (C (site ring root j)).tok = .AL ∨
        (C (site ring root j)).tok = .CL0 ∨
        (C (site ring root j)).tok = .CL1
      exact ht)
    (by change (C (site ring root (j + 1))).tok = .E; exact he)
  have hbank :
      (resetColdPrivateInteriorBankAt ring root C j).1.tok =
        (C (site ring root j)).tok ∧
      (resetColdPrivateInteriorBankAt ring root C j).1.bit =
        (C (site ring root j)).bit ∧
      (resetColdPrivateInteriorBankAt ring root C j).2.tok =
        (C (site ring root (j + 1))).tok ∧
      (resetColdPrivateInteriorBankAt ring root C j).2.bit =
        (C (site ring root (j + 1))).bit := by
    unfold resetColdPrivateInteriorBankAt
    have hr := hraw
    simp only [bankCell] at hr ⊢
    exact hr
  have hf := resetColdPrivateInteriorRowFields
    ring root C hc hsp j hj hjb
    (C (site ring root j)).tok
    (C (site ring root (j + 1))).tok
    (C (site ring root j)).bit
    (C (site ring root (j + 1))).bit hbank
  have hbits := resetColdPrivateInteriorBitFrame
    ring root C hc j hj hjb hf.2.1 hf.2.2.2
  have htoks : ∀ i : Nat, 1 ≤ i →
      i ≤ (compileAdvice q).b →
      (((protocol q).step ring C (site ring root j))
        (site ring root i)).tok =
          (C (site ring root i)).tok := by
    intro i hi hib
    by_cases hs : i = j
    · subst i
      exact hf.1
    · by_cases hd : i = j + 1
      · subst i
        exact hf.2.2.1
      · rw [resetColdPrivateInteriorOtherFrame
          ring root C hc j hj hjb i hi hib hs hd]
  have hroot := resetColdPrivateInteriorRootModeFrame
    ring root C hc j hj hjb
  exact ⟨resetColdPrivateLiveShapeAuthBankFrame
    ring root C ((protocol q).step ring C (site ring root j))
    hroot hbits htoks ha,
    resetColdPrivateHeadBankFrame
      ring root C ((protocol q).step ring C (site ring root j))
      hbits htoks⟩

/-- For a non-defective incoming-root edge, the legal source
PACK role and active-digit exteriority reduce all LIVE phases to
the earlier root incoming cases. The root grant condition
is explicit; it is not inferred from the phase predicate. -/
theorem resetColdPrivateIncomingAuthLive {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hpred : ring.rightNeighbor e = root)
    (ha : ResetColdPrivateLiveShapeAuth ring root C)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) e = .live D started') :
    ResetColdPrivateLiveShapeAuth ring root D ∧
      resetColdPrivateHeadValue ring root D =
        resetColdPrivateHeadValue ring root C := by
  have hno : ¬ ResetClockBankDefectEntry ring C root e := by
    intro hd
    simp only [resetColdLatchedPrivateNext, if_pos hd] at hnext
    cases hnext
  have hrole := resetColdIncomingRoleOfNoDefect
    ring C root e hc hpred hno
  have hex := resetColdIncomingExteriorOfLarge
    ring C root e hc hlarge hpred
  have he : e ≠ root := by
    intro hh
    subst e
    exact (resetColdRootPortDistinct ring C root hc) hpred
  rcases ha.1 with harm | hrest
  · obtain ⟨h, hb, hm, hn, hv⟩ := harm
    exact False.elim
      (resetColdPrivateAuthIncomingArmedImpossible
        ring root e C D started started' he hpred hm hnext)
  · rcases hrest with hstart | hrest
    · obtain ⟨h, hb, hm, hn, hv⟩ := hstart
      exact resetColdPrivateAuthIncomingCStartLive
        ring root e C D started started'
        hc hg hsp hpred hrole hex hm ha hnext
    · rcases hrest with hcompare | hcarry
      · obtain ⟨h, j, t, hb, hm, hw, ht, hv,
          hgood, hfull⟩ := hcompare
        have hwait : isWaitMode (C root).mode = true := by
          rw [hm]
          rfl
        exact resetColdPrivateAuthIncomingWaitLive
          ring root e C D started started'
          hc hg hsp hpred hrole hex hwait ha hnext
      · obtain ⟨h, j, t, hb, hm, hw, ht, hv⟩ := hcarry
        have hwait : isWaitMode (C root).mode = true := by
          rw [hm]
          rfl
        exact resetColdPrivateAuthIncomingWaitLive
          ring root e C D started started'
          hc hg hsp hpred hrole hex hwait ha hnext

end Counter
end L3

/-!
Nondefective LIVE environment and top-source
physical frame, with grant transport audited separately.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- The defect classifier is consulted before all other
observer outcomes. Thus a LIVE successor has a stable
protected PACK interval even when other Cartesian fields
are arbitrary. -/
theorem resetColdPrivateLiveNoDefect {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) e = .live D started') :
    ¬ ResetClockBankDefectEntry ring C root e := by
  intro hd
  simp only [resetColdLatchedPrivateNext, if_pos hd] at hnext
  cases hnext

/-- Complete is preserved on every LIVE observer letter,
not only those that leave every PACK field untouched
as an Agent. -/
theorem resetColdPrivateLiveCompleteStep {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) e = .live D started') :
    Complete ring D root := by
  have hs := resetClockBankStableOfNoDefect ring C root e
    (resetColdPrivateLiveNoDefect
      ring root e C D started started' hnext)
  have hp := resetColdPrivateLivePhysical
    ring root e C D started started' hnext
  intro j hj
  have hpack := congrArg Fin.val (hs j hj)
  change (((protocol q).step ring C e)
      (site ring root j)).pack.val =
    (C (site ring root j)).pack.val at hpack
  rw [hp]
  exact hpack.trans (hc j hj)

/-- The geometric part of the LIVE environment. The
ring-size and compiled binary-width inequalities do not
change with scheduler letters; no assertion of root
grant-freeness is made here. -/
def ResetColdPrivateLiveEnvironment {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) : Prop :=
  Complete ring C root ∧
    2 * (compileAdvice q).bankLeaseCap ≤ n ∧
    (compileAdvice q).K < 2 ^ (compileAdvice q).b

theorem resetColdPrivateLiveEnvironmentClean {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : ResetClockBankClean ring C root)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b) :
    ResetColdPrivateLiveEnvironment ring root C := by
  exact ⟨hc.1, hlarge, hwidth⟩

theorem resetColdPrivateLiveEnvironmentStep {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C D : Config q n) (started started' : Bool)
    (henv : ResetColdPrivateLiveEnvironment ring root C)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) e = .live D started') :
    ResetColdPrivateLiveEnvironment ring root D := by
  exact ⟨resetColdPrivateLiveCompleteStep ring root e C D
    started started' henv.1 hnext, henv.2.1, henv.2.2⟩

/-- Any actual LIVE root-incident edge already has a grant-free
OLD root. This is deliberately an *edge precondition*, not an
invariant of arbitrary intermediate LIVE states. -/
theorem resetColdPrivateLiveIncidentGrantFree {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hincident : e = root ∨ ring.rightNeighbor e = root)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) e = .live D started') :
    GrantFree C root := by
  rcases hincident with he | hpred
  · subst e
    exact resetColdPrivateLiveOutgoingGrantFree
      ring root C D started started' hc hsp hnext
  · have hrole := resetColdIncomingRoleOfNoDefect
      ring C root e hc hpred
      (resetColdPrivateLiveNoDefect
        ring root e C D started started' hnext)
    cases hg : (C root).grant with
    | false =>
        exact hg
    | true =>
        have hreset := resetColdRecoveryPhysicalIncomingGranted
          ring C root e hc hsp hpred hrole hg
        exact False.elim
          ((resetColdPrivateLiveRootNotReset
            ring root e C D started started' hnext) hreset)

/-- On an actual LIVE incoming-root edge, a granted OLD root is
impossible: the granted physical row resets that root, so the
observer cannot return LIVE. Thus no grant hypothesis is needed
in the final incoming classification. -/
theorem resetColdPrivateIncomingAuthLiveUnconditionalGrant {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hpred : ring.rightNeighbor e = root)
    (ha : ResetColdPrivateLiveShapeAuth ring root C)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) e = .live D started') :
    ResetColdPrivateLiveShapeAuth ring root D ∧
      resetColdPrivateHeadValue ring root D =
        resetColdPrivateHeadValue ring root C := by
  have hno : ¬ ResetClockBankDefectEntry ring C root e := by
    intro hd
    simp only [resetColdLatchedPrivateNext, if_pos hd] at hnext
    cases hnext
  have hrole := resetColdIncomingRoleOfNoDefect
    ring C root e hc hpred hno
  have hg : GrantFree C root := by
    cases hgrant : (C root).grant with
    | false =>
        exact hgrant
    | true =>
        have hreset := resetColdRecoveryPhysicalIncomingGranted
          ring C root e hc hsp hpred hrole hgrant
        exact False.elim
          ((resetColdPrivateLiveRootNotReset
            ring root e C D started started' hnext) hreset)
  exact resetColdPrivateIncomingAuthLive
    ring root e C D started started'
    hc hg hsp hlarge hpred ha hnext

/-- The top source never changes its bit; the first-match
branch that may erase an IR worker is irrelevant to bit value. -/
theorem resetColdPrivateTopSourceBitBank
    (x y : BankCell) (postRole b : Nat) (theta : Nat → Bool)
    (hx : x.role = b) (hb : 0 < b) :
    (bankPair x y postRole b theta).1.bit = x.bit := by
  obtain ⟨xr, xm, xb, xt, xl, xg⟩ := x
  obtain ⟨yr, ym, yb, yt, yl, yg⟩ := y
  change xr = b at hx
  subst xr
  have hb0 : b ≠ 0 := by omega
  have hbge : 1 ≤ b := by omega
  have hnlt : ¬ b < b := by omega
  rw [bankPair_nonroot ⟨b, xm, xb, xt, xl, xg⟩ ⟨yr, ym, yb, yt, yl, yg⟩ postRole b theta hb0]
  by_cases hsame : postRole = yr
  · subst postRole
    cases xt <;>
      simp [bankPairNR, hb0, hbge, hnlt, isWaitMode, apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd, apply_ite BankCell.tok, apply_ite BankCell.role, apply_ite BankCell.bit, ite_self] <;>
      (repeat' split) <;> first | rfl | (simp [Id.run]) | omega
  · cases xt <;>
      simp [bankPairNR, hb0, hbge, hnlt, hsame, isWaitMode, apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd, apply_ite BankCell.tok, apply_ite BankCell.role, apply_ite BankCell.bit, ite_self] <;>
      (repeat' split) <;> first | rfl | (simp [Id.run]) | omega

/-- A top-source service cannot affect a lower protected digit.
The responder is site (b+1), and injectivity of the successor
map excludes it from all lower-digit targets. -/
theorem resetColdPrivateTopSourceLowerFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : Complete ring C root)
    (i : Nat) (hi : 1 ≤ i)
    (hib : i < (compileAdvice q).b) :
    ((protocol q).step ring C
      (site ring root (compileAdvice q).b))
      (site ring root i) = C (site ring root i) := by
  have hs : site ring root i ≠
      site ring root (compileAdvice q).b :=
    resetCompleteSitesDifferent ring C root hc
      i (compileAdvice q).b (by omega) (by omega) (by omega)
  have ht : site ring root i ≠
      ring.rightNeighbor
        (site ring root (compileAdvice q).b) := by
    intro he
    have hprev : i - 1 + 1 = i := by omega
    have hneighbors :
        ring.rightNeighbor (site ring root (i - 1)) =
          ring.rightNeighbor
            (site ring root (compileAdvice q).b) := by
      change site ring root (i - 1 + 1) =
        site ring root ((compileAdvice q).b + 1)
      rw [hprev]
      exact he
    have hsame : site ring root (i - 1) =
        site ring root (compileAdvice q).b :=
      resetTrialNeighborInjective ring hneighbors
    have hdiff : site ring root (i - 1) ≠
        site ring root (compileAdvice q).b :=
      resetCompleteSitesDifferent ring C root hc
        (i - 1) (compileAdvice q).b
        (by omega) (by omega) (by omega)
    exact hdiff hsame
  exact step_frame ring C
    (site ring root (compileAdvice q).b)
    (site ring root i) hs ht

/-- An inner `if` whose condition fails, under an outer `if`
with equal fallbacks; stated on a plain type so that no motive
mentions a configuration. -/
private theorem resetColdIteKeep {α : Type} (P Q : Prop)
    [Decidable P] [Decidable Q] (e t : α) (hq : ¬ Q) :
    (if P then (if Q then e else t) else t) = t := by
  rw [if_neg hq, ite_self]

/-- Top-source physical hold. A bounded authenticated LIVE
state cannot have IR on digit b. The exact BANK row therefore
frames that source token and bit, and every lower digit is a
physical full-Agent frame. -/
theorem resetColdPrivateTopSourceAuthPhysical {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (ha : ResetColdPrivateLiveShapeAuth ring root C) :
    ResetColdPrivateLiveShapeAuth ring root
      ((protocol q).step ring C
        (site ring root (compileAdvice q).b)) ∧
      resetColdPrivateHeadValue ring root
        ((protocol q).step ring C
          (site ring root (compileAdvice q).b)) =
          resetColdPrivateHeadValue ring root C := by
  have hb : 0 < (compileAdvice q).b := by
    have hh := resetTrialCompiledWidth q
    omega
  have hn : 2 ≤ n := by
    have hh : 2 * (13 * ((compileAdvice q).b + 2)) ≤ n := by
      simpa only [Compiled.bankLeaseCap] using hlarge
    omega
  have hne :
      ring.rightNeighbor
        (site ring root (compileAdvice q).b) ≠
          site ring root (compileAdvice q).b :=
    resetRootPortDistinct ring
      (site ring root (compileAdvice q).b) hn
  have hrole :
      (C (site ring root (compileAdvice q).b)).pack.val =
        (compileAdvice q).b :=
    hc (compileAdvice q).b (by omega)
  have hnotIR :
      (C (site ring root (compileAdvice q).b)).tok ≠ .IR := by
    intro he
    exact resetColdPrivateTopIRImpossible
      ring root C hwidth ha.1 he
  have hrawTok := resetColdBankTopSourceToken
    (bankCell (C (site ring root (compileAdvice q).b))
      (C (site ring root (compileAdvice q).b)).pack.val)
    (bankCell (C (site ring root ((compileAdvice q).b + 1)))
      (C (site ring root ((compileAdvice q).b + 1))).pack.val)
    (packNext
      (C (site ring root (compileAdvice q).b)).pack.val
      (C (site ring root ((compileAdvice q).b + 1))).pack.val
      (compileAdvice q).b)
    (compileAdvice q).b (compileAdvice q).theta
    (by exact hrole)
    hb
  have hrawBit := resetColdPrivateTopSourceBitBank
    (bankCell (C (site ring root (compileAdvice q).b))
      (C (site ring root (compileAdvice q).b)).pack.val)
    (bankCell (C (site ring root ((compileAdvice q).b + 1)))
      (C (site ring root ((compileAdvice q).b + 1))).pack.val)
    (packNext
      (C (site ring root (compileAdvice q).b)).pack.val
      (C (site ring root ((compileAdvice q).b + 1))).pack.val
      (compileAdvice q).b)
    (compileAdvice q).b (compileAdvice q).theta
    (by exact hrole)
    hb
  have hbankTok :
      (resetBankOld
        (C (site ring root (compileAdvice q).b))
        (C (site ring root ((compileAdvice q).b + 1)))).1.tok =
          (C (site ring root (compileAdvice q).b)).tok := by
    exact hrawTok.trans (resetColdIteKeep _ _ _ _ hnotIR)
  have hbankBit :
      (resetBankOld
        (C (site ring root (compileAdvice q).b))
        (C (site ring root ((compileAdvice q).b + 1)))).1.bit =
          (C (site ring root (compileAdvice q).b)).bit := by
    simpa only [resetBankOld, bankCell] using hrawBit
  have htrip := resetPhysicalEdgeBankTrip ring C
    (site ring root (compileAdvice q).b) hne hsp
  have htopTok :
      (((protocol q).step ring C
        (site ring root (compileAdvice q).b))
        (site ring root (compileAdvice q).b)).tok =
          (C (site ring root (compileAdvice q).b)).tok :=
    (congrArg (fun z : Mode × Bool × BTok => z.2.2)
      htrip.1).trans hbankTok
  have htopBit :
      (((protocol q).step ring C
        (site ring root (compileAdvice q).b))
        (site ring root (compileAdvice q).b)).bit =
          (C (site ring root (compileAdvice q).b)).bit :=
    (congrArg (fun z : Mode × Bool × BTok => z.2.1)
      htrip.1).trans hbankBit
  have hbits : ∀ i : Nat, 1 ≤ i →
      i ≤ (compileAdvice q).b →
      (((protocol q).step ring C
        (site ring root (compileAdvice q).b))
        (site ring root i)).bit =
          (C (site ring root i)).bit := by
    intro i hi hib
    by_cases he : i = (compileAdvice q).b
    · subst i
      exact htopBit
    · rw [resetColdPrivateTopSourceLowerFrame
        ring root C hc i hi (by omega)]
  have htoks : ∀ i : Nat, 1 ≤ i →
      i ≤ (compileAdvice q).b →
      (((protocol q).step ring C
        (site ring root (compileAdvice q).b))
        (site ring root i)).tok =
          (C (site ring root i)).tok := by
    intro i hi hib
    by_cases he : i = (compileAdvice q).b
    · subst i
      exact htopTok
    · rw [resetColdPrivateTopSourceLowerFrame
        ring root C hc i hi (by omega)]
  have hroot := resetColdTopRootPhysicalFrame
    ring C root hc hlarge
  have hmode :=
    congrArg (fun z : Agent (compileAdvice q) => z.mode) hroot
  exact ⟨resetColdPrivateLiveShapeAuthBankFrame
    ring root C ((protocol q).step ring C
      (site ring root (compileAdvice q).b))
    hmode hbits htoks ha,
    resetColdPrivateHeadBankFrame
      ring root C ((protocol q).step ring C
        (site ring root (compileAdvice q).b))
      hbits htoks⟩



/-- A comparator or IR worker occupying the *responder* of
a non-top interior pair is not moving along its orientation.
The source must be E. At the top, CR has a separate turn,
and IR is ruled out by the bounded head. -/
theorem resetColdPrivateInteriorResponderHoldBank
    (x y : BankCell) (b : Nat) (theta : Nat → Bool)
    (hx : 1 ≤ x.role) (hxb : x.role < b)
    (hy : y.role = x.role + 1)
    (hntop : y.role ≠ b)
    (he : x.tok = .E)
    (ht : y.tok = .IR ∨ y.tok = .CR0 ∨ y.tok = .CR1) :
    (bankPair x y y.role b theta).1.tok = x.tok ∧
      (bankPair x y y.role b theta).1.bit = x.bit ∧
      (bankPair x y y.role b theta).2.tok = y.tok ∧
      (bankPair x y y.role b theta).2.bit = y.bit := by
  have hxne : x.role ≠ 0 := by omega
  have hyne : y.role ≠ 0 := by omega
  have hxle : x.role ≤ b := by omega
  have hyle : y.role ≤ b := by omega
  have hxneq : x.role ≠ b := by omega
  have hnlt : ¬ b < x.role + 1 := by omega
  rcases ht with ht | ht | ht
  all_goals
    simp [bankPair, hx, hxb, hy, hntop, he, ht,
      hxne, hyne, hxle, hyle, hxneq, hnlt, Id.run_pure, Id.run_bind] <;>
      (repeat' split) <;>
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩ | (simp_all [Id.run]) | omega

/-- The non-top responder hold is an actual full-protocol frame
on all protected digit bits/tokens, not an assumed BANK-only
scheduler. It preserves Auth provenance and the numerical head. -/
theorem resetColdPrivateInteriorResponderHoldPhysical {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (j : Nat) (hj : 1 ≤ j)
    (hjb : j < (compileAdvice q).b)
    (hntop : j + 1 ≠ (compileAdvice q).b)
    (he : (C (site ring root j)).tok = .E)
    (ht : (C (site ring root (j + 1))).tok = .IR ∨
      (C (site ring root (j + 1))).tok = .CR0 ∨
      (C (site ring root (j + 1))).tok = .CR1)
    (ha : ResetColdPrivateLiveShapeAuth ring root C) :
    ResetColdPrivateLiveShapeAuth ring root
      ((protocol q).step ring C (site ring root j)) ∧
    resetColdPrivateHeadValue ring root
      ((protocol q).step ring C (site ring root j)) =
        resetColdPrivateHeadValue ring root C := by
  have hraw := resetColdPrivateInteriorResponderHoldBank
    (bankCell (C (site ring root j)) j)
    (bankCell (C (site ring root (j + 1))) (j + 1))
    (compileAdvice q).b (compileAdvice q).theta
    (by change 1 ≤ j; exact hj)
    (by change j < (compileAdvice q).b; exact hjb)
    rfl
    (by change j + 1 ≠ (compileAdvice q).b; exact hntop)
    (by change (C (site ring root j)).tok = .E; exact he)
    (by exact ht)
  have hbank :
      (resetColdPrivateInteriorBankAt ring root C j).1.tok =
        (C (site ring root j)).tok ∧
      (resetColdPrivateInteriorBankAt ring root C j).1.bit =
        (C (site ring root j)).bit ∧
      (resetColdPrivateInteriorBankAt ring root C j).2.tok =
        (C (site ring root (j + 1))).tok ∧
      (resetColdPrivateInteriorBankAt ring root C j).2.bit =
        (C (site ring root (j + 1))).bit := by
    unfold resetColdPrivateInteriorBankAt
    have hr := hraw
    simp only [bankCell] at hr ⊢
    exact hr
  have hf := resetColdPrivateInteriorRowFields
    ring root C hc hsp j hj hjb
    (C (site ring root j)).tok
    (C (site ring root (j + 1))).tok
    (C (site ring root j)).bit
    (C (site ring root (j + 1))).bit hbank
  have hbits := resetColdPrivateInteriorBitFrame
    ring root C hc j hj hjb hf.2.1 hf.2.2.2
  have htoks : ∀ i : Nat, 1 ≤ i →
      i ≤ (compileAdvice q).b →
      (((protocol q).step ring C (site ring root j))
        (site ring root i)).tok =
          (C (site ring root i)).tok := by
    intro i hi hib
    by_cases hs : i = j
    · subst i
      exact hf.1
    · by_cases hd : i = j + 1
      · subst i
        exact hf.2.2.1
      · rw [resetColdPrivateInteriorOtherFrame
          ring root C hc j hj hjb i hi hib hs hd]
  have hroot := resetColdPrivateInteriorRootModeFrame
    ring root C hc j hj hjb
  exact ⟨resetColdPrivateLiveShapeAuthBankFrame
    ring root C ((protocol q).step ring C (site ring root j))
    hroot hbits htoks ha,
    resetColdPrivateHeadBankFrame
      ring root C ((protocol q).step ring C (site ring root j))
      hbits htoks⟩


/-- Exhaustive interior case for an authenticated comparator phase.
The selected source is j and the responder is j+1; the unique
worker is either the source, responder, or neither. -/
theorem resetColdPrivateCWaitInteriorPhysical {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (j : Nat) (hj : 1 ≤ j)
    (hjb : j < (compileAdvice q).b)
    (h k : Nat) (t : BTok)
    (hb : h + 1 ≤ (compileAdvice q).K)
    (hm : (C root).mode = .CWAIT)
    (hw : resetColdPrivateOnlyWorker ring root C k t)
    (ht : resetColdPrivateComparatorToken t)
    (hv : resetColdPrivateHeadValue ring root C = h + 1)
    (hgood : t = .CR1 →
      resetColdPrivateMatchedPrefix ring root C k)
    (hfull : t = .CL1 →
      resetColdPrivateMatchedPrefix ring root C
        (compileAdvice q).b)
    (ha : ResetColdPrivateLiveShapeAuth ring root C) :
    ResetColdPrivateLiveShapeAuth ring root
      ((protocol q).step ring C (site ring root j)) ∧
    resetColdPrivateHeadValue ring root
      ((protocol q).step ring C (site ring root j)) =
        resetColdPrivateHeadValue ring root C := by
  have hbadCR : t = .CR0 →
      resetColdPrivateMismatchPrefix ring root C k := by
    intro he
    exact ha.2.1 k hw.1 hw.2.1
      (hw.2.2.1.trans he)
  have hbadCL : t = .CL0 →
      resetColdPrivateMismatchPrefix ring root C
        (compileAdvice q).b := by
    intro he
    exact ha.2.2 k hw.1 hw.2.1
      (hw.2.2.1.trans he)
  by_cases hleft : k = j
  · subst k
    have heY : (C (site ring root (j + 1))).tok = .E :=
      hw.2.2.2 (j + 1) (by omega) (by omega) (by omega)
    rcases ht with hcr | hcr | hcl | hcl
    · exact resetColdPrivateCRForwardPhysical
        ring root C hc hsp j h hj hjb t hb hm hw
        (Or.inl hcr) hv hgood hbadCR
    · exact resetColdPrivateCRForwardPhysical
        ring root C hc hsp j h hj hjb t hb hm hw
        (Or.inr hcr) hv hgood hbadCR
    · have hs : (C (site ring root j)).tok = .CL0 :=
        hw.2.2.1.trans hcl
      exact resetColdPrivateInteriorHoldPhysical
        ring root C hc hsp j hj hjb
        (Or.inr (Or.inr (Or.inl hs))) heY ha
    · have hs : (C (site ring root j)).tok = .CL1 :=
        hw.2.2.1.trans hcl
      exact resetColdPrivateInteriorHoldPhysical
        ring root C hc hsp j hj hjb
        (Or.inr (Or.inr (Or.inr hs))) heY ha
  · by_cases hright : k = j + 1
    · subst k
      have heX : (C (site ring root j)).tok = .E :=
        hw.2.2.2 j hj (by omega) (by omega)
      rcases ht with hcr | hcr | hcl | hcl
      · by_cases htop : j + 1 = (compileAdvice q).b
        · have hgoodTop : t = .CR1 →
              resetColdPrivateMatchedPrefix ring root C
                (compileAdvice q).b := by
            intro he
            rw [← htop]
            exact hgood he
          have hbadTop : t = .CR0 →
              resetColdPrivateMismatchPrefix ring root C
                (compileAdvice q).b := by
            intro he
            rw [← htop]
            exact hbadCR he
          exact resetColdPrivateCRTopTurnPhysical
            ring root C hc hsp j h hj hjb htop t
            hb hm hw (Or.inl hcr) hv hgoodTop hbadTop
        · have htY : (C (site ring root (j + 1))).tok =
              .CR0 := hw.2.2.1.trans hcr
          exact resetColdPrivateInteriorResponderHoldPhysical
            ring root C hc hsp j hj hjb htop heX
            (Or.inr (Or.inl htY)) ha
      · by_cases htop : j + 1 = (compileAdvice q).b
        · have hgoodTop : t = .CR1 →
              resetColdPrivateMatchedPrefix ring root C
                (compileAdvice q).b := by
            intro he
            rw [← htop]
            exact hgood he
          have hbadTop : t = .CR0 →
              resetColdPrivateMismatchPrefix ring root C
                (compileAdvice q).b := by
            intro he
            rw [← htop]
            exact hbadCR he
          exact resetColdPrivateCRTopTurnPhysical
            ring root C hc hsp j h hj hjb htop t
            hb hm hw (Or.inr hcr) hv hgoodTop hbadTop
        · have htY : (C (site ring root (j + 1))).tok =
              .CR1 := hw.2.2.1.trans hcr
          exact resetColdPrivateInteriorResponderHoldPhysical
            ring root C hc hsp j hj hjb htop heX
            (Or.inr (Or.inr htY)) ha
      · exact resetColdPrivateCLBackwardPhysical
          ring root C hc hsp j h hj hjb t hb hm hw
          (Or.inl hcl) hv hfull hbadCL
      · exact resetColdPrivateCLBackwardPhysical
          ring root C hc hsp j h hj hjb t hb hm hw
          (Or.inr hcl) hv hfull hbadCL
    · have heX : (C (site ring root j)).tok = .E :=
        hw.2.2.2 j hj (by omega) (Ne.symm hleft)
      have heY : (C (site ring root (j + 1))).tok = .E :=
        hw.2.2.2 (j + 1) (by omega) (by omega)
          (Ne.symm hright)
      exact resetColdPrivateInteriorHoldPhysical
        ring root C hc hsp j hj hjb (Or.inl heX) heY ha

/-- Exhaustive interior case for an authenticated increment phase.
IR advances clockwise, AL retreats counterclockwise, and an
occupied IR responder is a hold except at the impossible top. -/
theorem resetColdPrivateIWaitInteriorPhysical {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (j : Nat) (hj : 1 ≤ j)
    (hjb : j < (compileAdvice q).b)
    (h k : Nat) (t : BTok)
    (hb : h + 1 ≤ (compileAdvice q).K)
    (hm : (C root).mode = .IWAIT)
    (hw : resetColdPrivateOnlyWorker ring root C k t)
    (ht : resetColdPrivateCarryToken t)
    (hv : resetColdPrivateHeadValue ring root C = h + 1)
    (ha : ResetColdPrivateLiveShapeAuth ring root C) :
    ResetColdPrivateLiveShapeAuth ring root
      ((protocol q).step ring C (site ring root j)) ∧
    resetColdPrivateHeadValue ring root
      ((protocol q).step ring C (site ring root j)) =
        resetColdPrivateHeadValue ring root C := by
  by_cases hleft : k = j
  · subst k
    have heY : (C (site ring root (j + 1))).tok = .E :=
      hw.2.2.2 (j + 1) (by omega) (by omega) (by omega)
    rcases ht with hir | hal
    · rw [hir] at hw
      exact resetColdPrivateIRForwardPhysical
        ring root C hc hsp j h hj hjb hb hm hw hv
    · have hs : (C (site ring root j)).tok = .AL :=
        hw.2.2.1.trans hal
      exact resetColdPrivateInteriorHoldPhysical
        ring root C hc hsp j hj hjb
        (Or.inr (Or.inl hs)) heY ha
  · by_cases hright : k = j + 1
    · subst k
      have heX : (C (site ring root j)).tok = .E :=
        hw.2.2.2 j hj (by omega) (by omega)
      rcases ht with hir | hal
      · have htY : (C (site ring root (j + 1))).tok =
            .IR := hw.2.2.1.trans hir
        have hnotTop : j + 1 ≠ (compileAdvice q).b := by
          intro htop
          have htopTok :
              (C (site ring root (compileAdvice q).b)).tok =
                .IR := by
            rw [← htop]
            exact htY
          exact resetColdPrivateTopIRImpossible
            ring root C hwidth ha.1 htopTok
        exact resetColdPrivateInteriorResponderHoldPhysical
          ring root C hc hsp j hj hjb hnotTop heX
          (Or.inl htY) ha
      · rw [hal] at hw
        exact resetColdPrivateALRetreatPhysical
          ring root C hc hsp j h hj hjb hb hm hw hv
    · have heX : (C (site ring root j)).tok = .E :=
        hw.2.2.2 j hj (by omega) (Ne.symm hleft)
      have heY : (C (site ring root (j + 1))).tok = .E :=
        hw.2.2.2 (j + 1) (by omega) (by omega)
          (Ne.symm hright)
      exact resetColdPrivateInteriorHoldPhysical
        ring root C hc hsp j hj hjb (Or.inl heX) heY ha

/-- The full four-phase Auth shape is preserved on any physical
interior edge with source j in [1,b), using the CR/CL/IR/AL
rows and the two true idle families. -/
theorem resetColdPrivateAuthInteriorPhysical {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (j : Nat) (hj : 1 ≤ j)
    (hjb : j < (compileAdvice q).b)
    (ha : ResetColdPrivateLiveShapeAuth ring root C) :
    ResetColdPrivateLiveShapeAuth ring root
      ((protocol q).step ring C (site ring root j)) ∧
    resetColdPrivateHeadValue ring root
      ((protocol q).step ring C (site ring root j)) =
        resetColdPrivateHeadValue ring root C := by
  rcases ha.1 with harm | hrest
  · obtain ⟨h, hb, hm, hn, hv⟩ := harm
    have heX := hn j hj (by omega)
    have heY := hn (j + 1) (by omega) (by omega)
    exact resetColdPrivateInteriorHoldPhysical
      ring root C hc hsp j hj hjb (Or.inl heX) heY ha
  · rcases hrest with hstart | hrest
    · obtain ⟨h, hb, hm, hn, hv⟩ := hstart
      have heX := hn j hj (by omega)
      have heY := hn (j + 1) (by omega) (by omega)
      exact resetColdPrivateInteriorHoldPhysical
        ring root C hc hsp j hj hjb (Or.inl heX) heY ha
    · rcases hrest with hcompare | hcarry
      · obtain ⟨h, k, t, hb, hm, hw, ht, hv,
          hgood, hfull⟩ := hcompare
        exact resetColdPrivateCWaitInteriorPhysical
          ring root C hc hsp j hj hjb h k t
          hb hm hw ht hv hgood hfull ha
      · obtain ⟨h, k, t, hb, hm, hw, ht, hv⟩ := hcarry
        exact resetColdPrivateIWaitInteriorPhysical
          ring root C hc hsp hwidth j hj hjb h k t
          hb hm hw ht hv ha


/-- A genuine first-digit CL1 in a CWAIT phase is a terminal
private success if the observer tries to service the root.
It cannot be a LIVE-to-LIVE root service. -/
theorem resetColdPrivateLiveCL1RootImpossible {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hm : (C root).mode = .CWAIT)
    (ht : (C (site ring root 1)).tok = .CL1)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) root = .live D started') : False := by
  have hg := resetColdPrivateLiveOutgoingGrantFree
    ring root C D started started' hc hsp hnext
  have hno := resetColdPrivateLiveNoDefect
    ring root root C D started started' hnext
  have hb : 0 < (compileAdvice q).b := by
    have hh := resetTrialCompiledWidth q
    omega
  have hroot : (C root).pack.val = 0 := by
    simpa only [site] using hc 0 (by omega)
  have hone : (C (site ring root 1)).pack.val = 1 :=
    hc 1 (by omega)
  have hpostNat :
      packNext 0 1 (compileAdvice q).b = 1 := by
    unfold packNext
    rw [if_pos (by omega : 0 < (compileAdvice q).b)]
  have hsuc : resetColdPrivateSuccessAt ring root C root := by
    refine ⟨rfl, ?_⟩
    change bankSuccess
      (bankCell (C root) (C root).pack.val)
      (bankCell (C (site ring root 1))
        (C (site ring root 1)).pack.val)
      (packNext (C root).pack.val
        (C (site ring root 1)).pack.val
        (compileAdvice q).b)
      (compileAdvice q).b = true
    have hg' : (C root).grant = false := hg
    simp [bankSuccess, bankCell, hroot, hone,
      hpostNat, hg', hm, ht]
  simp only [resetColdLatchedPrivateNext, if_neg hno,
    if_pos hsuc] at hnext
  cases hnext

/-- All physical root outgoing LIVE cases. The ARMED case
increments the represented completed head exactly once;
every other surviving case preserves it. -/
theorem resetColdPrivateAuthRootLive {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (ha : ResetColdPrivateLiveShapeAuth ring root C)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) root = .live D started') :
    ResetColdPrivateLiveShapeAuth ring root D ∧
    (((C root).mode = .ARMED ∧
      resetColdPrivateHeadValue ring root D =
        resetColdPrivateHeadValue ring root C + 1) ∨
     ((C root).mode ≠ .ARMED ∧
      resetColdPrivateHeadValue ring root D =
        resetColdPrivateHeadValue ring root C)) := by
  rcases ha.1 with harm | hrest
  · obtain ⟨h, hb, hm, hn, hv⟩ := harm
    have hh := resetColdPrivateAuthArmedRootLive
      ring root C D started started' hc hsp
      h hb hm hn hv hnext
    exact ⟨hh.1, Or.inl ⟨hm, hh.2⟩⟩
  · rcases hrest with hstart | hrest
    · obtain ⟨h, hb, hm, hn, hv⟩ := hstart
      have hh := resetColdPrivateAuthCStartRootLive
        ring root C D started started' hc hsp
        h hb hm hn hv hnext
      have hnot : (C root).mode ≠ .ARMED := by
        rw [hm]
        intro he
        cases he
      exact ⟨hh.1, Or.inr ⟨hnot, hh.2⟩⟩
    · rcases hrest with hcompare | hcarry
      · obtain ⟨h, k, t, hb, hm, hw, htype, hv,
          hgood, hfull⟩ := hcompare
        have hnot : (C root).mode ≠ .ARMED := by
          rw [hm]
          intro he
          cases he
        have hwait : isWaitMode (C root).mode = true := by
          rw [hm]
          rfl
        by_cases hone : k = 1
        · subst k
          rcases htype with hcr | hcr | hcl | hcl
          · have hret : isRetTok
                (C (site ring root 1)).tok = false := by
              rw [hw.2.2.1, hcr]
              rfl
            have hh := resetColdPrivateAuthWaitRootLive
              ring root C D started started' hc hsp
              hwait hret ha hnext
            exact ⟨hh.1, Or.inr ⟨hnot, hh.2⟩⟩
          · have hret : isRetTok
                (C (site ring root 1)).tok = false := by
              rw [hw.2.2.1, hcr]
              rfl
            have hh := resetColdPrivateAuthWaitRootLive
              ring root C D started started' hc hsp
              hwait hret ha hnext
            exact ⟨hh.1, Or.inr ⟨hnot, hh.2⟩⟩
          · have hh := resetColdPrivateCL0RootLive
              ring root C D started started'
              hc hsp hwidth h hb hm
              (by rw [hcl] at hw; exact hw)
              hv ha hnext
            exact ⟨hh.1, Or.inr ⟨hnot, hh.2⟩⟩
          · have ht : (C (site ring root 1)).tok = .CL1 :=
              hw.2.2.1.trans hcl
            exact False.elim
              (resetColdPrivateLiveCL1RootImpossible
                ring root C D started started' hc hsp hm ht hnext)
        · have hbwidth : 1 ≤ (compileAdvice q).b := by
            have hh := resetTrialCompiledWidth q
            omega
          have hfirst : (C (site ring root 1)).tok = .E :=
            hw.2.2.2 1 (by omega) hbwidth (Ne.symm hone)
          have hret : isRetTok
              (C (site ring root 1)).tok = false := by
            rw [hfirst]
            rfl
          have hh := resetColdPrivateAuthWaitRootLive
            ring root C D started started' hc hsp
            hwait hret ha hnext
          exact ⟨hh.1, Or.inr ⟨hnot, hh.2⟩⟩
      · obtain ⟨h, k, t, hb, hm, hw, htype, hv⟩ := hcarry
        have hnot : (C root).mode ≠ .ARMED := by
          rw [hm]
          intro he
          cases he
        have hwait : isWaitMode (C root).mode = true := by
          rw [hm]
          rfl
        by_cases hone : k = 1
        · subst k
          rcases htype with hir | hal
          · have hret : isRetTok
                (C (site ring root 1)).tok = false := by
              rw [hw.2.2.1, hir]
              rfl
            have hh := resetColdPrivateAuthWaitRootLive
              ring root C D started started' hc hsp
              hwait hret ha hnext
            exact ⟨hh.1, Or.inr ⟨hnot, hh.2⟩⟩
          · have hh := resetColdPrivateALRootLive
              ring root C D started started' hc hsp
              h hb hm (by rw [hal] at hw; exact hw) hv hnext
            exact ⟨hh.1, Or.inr ⟨hnot, hh.2⟩⟩
        · have hbwidth : 1 ≤ (compileAdvice q).b := by
            have hh := resetTrialCompiledWidth q
            omega
          have hfirst : (C (site ring root 1)).tok = .E :=
            hw.2.2.2 1 (by omega) hbwidth (Ne.symm hone)
          have hret : isRetTok
              (C (site ring root 1)).tok = false := by
            rw [hfirst]
            rfl
          have hh := resetColdPrivateAuthWaitRootLive
            ring root C D started started' hc hsp
            hwait hret ha hnext
          exact ⟨hh.1, Or.inr ⟨hnot, hh.2⟩⟩


/-- The complete geometric classification of every LIVE physical
edge. The strong Auth phase is preserved, and its numerical head
either increases once on an ARMED root service or stays equal.
The two alternatives are exclusive at the OLD snapshot. -/
theorem resetColdPrivateLiveAuthStep {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (ha : ResetColdPrivateLiveShapeAuth ring root C)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) e = .live D started') :
    ResetColdPrivateLiveShapeAuth ring root D ∧
    ((e = root ∧ (C root).mode = .ARMED ∧
      resetColdPrivateHeadValue ring root D =
        resetColdPrivateHeadValue ring root C + 1) ∨
     ((e ≠ root ∨ (C root).mode ≠ .ARMED) ∧
      resetColdPrivateHeadValue ring root D =
        resetColdPrivateHeadValue ring root C)) := by
  rcases resetTrialEdgeGeometry (q := q) ring root e with
      hsite | hincoming | houtside
  · obtain ⟨j, hjb, he⟩ := hsite
    subst e
    by_cases hzero : j = 0
    · subst j
      have hr := resetColdPrivateAuthRootLive
        ring root C D started started' hc hsp hwidth ha hnext
      constructor
      · exact hr.1
      · rcases hr.2 with hinc | hstay
        · exact Or.inl ⟨rfl, hinc.1, hinc.2⟩
        · exact Or.inr ⟨Or.inr hstay.1, hstay.2⟩
    · have hj : 1 ≤ j := by omega
      have hne : site ring root j ≠ root := by
        change site ring root j ≠ site ring root 0
        exact resetCompleteSitesDifferent ring C root hc
          j 0 hjb (by omega) (by omega)
      have hp := resetColdPrivateLivePhysical
        ring root (site ring root j) C D started started' hnext
      by_cases htop : j = (compileAdvice q).b
      · have hh := resetColdPrivateTopSourceAuthPhysical
          ring root C hc hsp hlarge hwidth ha
        have hnew : ResetColdPrivateLiveShapeAuth ring root D ∧
            resetColdPrivateHeadValue ring root D =
              resetColdPrivateHeadValue ring root C := by
          rw [hp, htop]
          exact hh
        exact ⟨hnew.1, Or.inr ⟨Or.inl hne, hnew.2⟩⟩
      · have hlt : j < (compileAdvice q).b := by omega
        have hh := resetColdPrivateAuthInteriorPhysical
          ring root C hc hsp hwidth j hj hlt ha
        have hnew : ResetColdPrivateLiveShapeAuth ring root D ∧
            resetColdPrivateHeadValue ring root D =
              resetColdPrivateHeadValue ring root C := by
          rw [hp]
          exact hh
        exact ⟨hnew.1, Or.inr ⟨Or.inl hne, hnew.2⟩⟩
  · have hh := resetColdPrivateIncomingAuthLiveUnconditionalGrant
      ring root e C D started started'
      hc hsp hlarge hincoming ha hnext
    have hne : e ≠ root := by
      intro he
      subst e
      exact (resetColdRootPortDistinct ring C root hc) hincoming
    exact ⟨hh.1, Or.inr ⟨Or.inl hne, hh.2⟩⟩
  · have hrs : e ≠ root := by
      change e ≠ site ring root 0
      exact (houtside 0 (by omega)).1
    have hrt : ring.rightNeighbor e ≠ root := by
      change ring.rightNeighbor e ≠ site ring root 0
      exact (houtside 0 (by omega)).2
    have hs : ∀ j : Nat, 1 ≤ j →
        j ≤ (compileAdvice q).b →
        e ≠ site ring root j := by
      intro j hj hjb
      exact (houtside j hjb).1
    have ht : ∀ j : Nat, 1 ≤ j →
        j ≤ (compileAdvice q).b →
        ring.rightNeighbor e ≠ site ring root j := by
      intro j hj hjb
      exact (houtside j hjb).2
    have hh := resetColdPrivateAuthOutsideObserver
      ring root e C D started started'
      hrs hrt hs ht ha hnext
    exact ⟨hh.1, Or.inr ⟨Or.inl hrs, hh.2⟩⟩

/-- The actual observer word can have LIVE successors only
from LIVE predecessors. The one-step closure therefore carries
Auth and Complete through arbitrary scheduler words; terminal
and recovery states never re-enter LIVE. -/
private theorem resetColdPrivateLiveAuthCompleteRun {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b) :
    ∀ (z : ResetColdLatchedPrivateState q n)
      (w : List (Fin n)),
    (∀ (A : Config q n) (s : Bool), z = .live A s →
      ResetColdPrivateLiveShapeAuth ring root A ∧
      Complete ring A root) →
    ∀ (D : Config q n) (started' : Bool),
      resetColdLatchedPrivateRun ring root z w =
        .live D started' →
      ResetColdPrivateLiveShapeAuth ring root D ∧
      Complete ring D root := by
  intro z w
  induction w generalizing z with
  | nil =>
      intro hz D started' hresult
      exact hz D started' hresult
  | cons e w ih =>
      intro hz D started' hresult
      have hnext :
          ∀ (A : Config q n) (s : Bool),
            resetColdLatchedPrivateNext ring root z e =
              .live A s →
            ResetColdPrivateLiveShapeAuth ring root A ∧
            Complete ring A root := by
        intro A s hn
        cases z with
        | live B old =>
            have hbase := hz B old rfl
            have ha := resetColdPrivateLiveAuthStep
              ring root e B A old s hbase.2 hsp hlarge hwidth
              hbase.1 hn
            exact ⟨ha.1,
              resetColdPrivateLiveCompleteStep
                ring root e B A old s hbase.2 hn⟩
        | recovery B =>
            simp only [resetColdLatchedPrivateNext] at hn
            by_cases h1 : ResetClockBankDefectEntry ring B root e
            · rw [if_pos h1] at hn
              cases hn
            · rw [if_neg h1] at hn
              by_cases h2 : ResetClockBankClean ring
                  ((protocol q).step ring B e) root
              · rw [if_pos h2] at hn
                cases hn
              · rw [if_neg h2] at hn
                cases hn
        | success B =>
            cases hn
        | failure B =>
            cases hn
      exact ih (resetColdLatchedPrivateNext ring root z e)
        hnext D started' hresult

/-- The authenticated LIVE word theorem for the large spatial
domain: any word starting at Clean has Auth and Complete at
every surviving LIVE endpoint. No root grant-freedom premise
is inserted at intermediate cuts. -/
theorem resetColdPrivateLiveShapeAuthWord {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (Czero : Config q n)
    (hc : ResetClockBankClean ring Czero root)
    (w : List (Fin n)) (C : Config q n) (started : Bool)
    (hrun : resetColdLatchedPrivateRun ring root
      (.live Czero false) w = .live C started) :
    ResetColdPrivateLiveShapeAuth ring root C ∧
      Complete ring C root := by
  have hseed :
      ∀ (A : Config q n) (s : Bool),
        (ResetColdLatchedPrivateState.live Czero false) =
          .live A s →
        ResetColdPrivateLiveShapeAuth ring root A ∧
          Complete ring A root := by
    intro A s he
    cases he
    exact ⟨resetColdPrivateLiveShapeAuthClean
      ring root Czero hc hsp, hc.1⟩
  exact resetColdPrivateLiveAuthCompleteRun
    ring root hsp hlarge hwidth
    (.live Czero false) w hseed C started hrun

/-- The surviving LIVE endpoint also retains the static
environment needed by the physical row proofs. -/
theorem resetColdPrivateLiveEnvironmentWord {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (Czero : Config q n)
    (hc : ResetClockBankClean ring Czero root)
    (w : List (Fin n)) (C : Config q n) (started : Bool)
    (hrun : resetColdLatchedPrivateRun ring root
      (.live Czero false) w = .live C started) :
    ResetColdPrivateLiveEnvironment ring root C := by
  have hh := resetColdPrivateLiveShapeAuthWord
    ring root hsp hlarge hwidth Czero hc w C started hrun
  exact ⟨hh.2, hlarge, hwidth⟩

/-- HeadRows for the explicitly large spatial ring and the
compiled binary-width inequality. No circular probability
or ghost-step hypothesis is used. -/
theorem resetColdPrivateHeadRowsLargeWidth {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b) :
    ResetColdLatchedHeadRows (q := q) ring root := by
  intro Czero hc hg w C started hrun
  have hs := resetColdPrivateLiveShapeAuthWord
    ring root hsp hlarge hwidth Czero hc w C started hrun
  constructor
  · intro e D started' hnext
    have hh := resetColdPrivateLiveAuthStep
      ring root e C D started started' hs.2
      hsp hlarge hwidth hs.1 hnext
    rcases hh.2 with hinc | hstay
    · obtain ⟨he, hm, hv⟩ := hinc
      have hyes : e = root ∧ (C root).mode = .ARMED :=
        ⟨he, hm⟩
      rw [if_pos hyes, hv]
      exact Nat.le_refl _
    · have hno : ¬ (e = root ∧ (C root).mode = .ARMED) := by
        intro hyes
        rcases hstay.1 with hne | hnm
        · exact hne hyes.1
        · exact hnm hyes.2
      rw [if_neg hno, Nat.add_zero, hstay.2]
      exact Nat.le_refl _
  · constructor
    · intro e D started' hnext hnot
      have hh := resetColdPrivateLiveAuthStep
        ring root e C D started started' hs.2
        hsp hlarge hwidth hs.1 hnext
      rcases hh.2 with hinc | hstay
      · obtain ⟨he, hm, hv⟩ := hinc
        rcases hnot with hne | hnm
        · exact False.elim (hne he)
        · exact False.elim (hnm hm)
      · exact hstay.2
    · intro e D hnext
      exact resetColdPrivateSuccessObserverHeadOfShape
        ring root e C D started hwidth hs.1.1 hnext

/-- No HeadRows assumption remains in the probability bound on
the explicit large-ring/binary-width domain. -/
theorem resetColdLatchedPrivateUpperSpatial {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (Czero : Config q n)
    (hc : ResetClockBankClean ring Czero root)
    (hg : resetColdPrivateGlobalGrantFree Czero)
    (T : Nat) :
    2 ^ (compileAdvice q).K *
      resetColdLatchedPrivateSuccessMass ring root Czero T ≤
        n ^ T := by
  exact resetColdLatchedPrivateUpperOfHeadRows
    ring root hsp
    (resetColdPrivateHeadRowsLargeWidth
      ring root hsp hlarge hwidth)
    Czero hc hg T

end Counter
end L3

/-!
Compilation-width and headline-ring discharge.
ParamsFacts.lean already proves the general width capacity
at q >= 3, but is not in CounterCold.lean's existing import
closure.
The small core arithmetic argument is therefore given here
under fresh names.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- The exact production spatial selector switches after qStar=79. -/
theorem resetColdPrivateSpatialAdviceGe (q : Nat)
    (hsp : (compileAdvice q).useSmall = false) :
    80 ≤ q := by
  have hnot : ¬ q ≤ qStar := by
    intro hle
    have ht : (compileAdvice q).useSmall = true := by
      simp [Compiled.useSmall, compileAdvice, hle]
    rw [ht] at hsp
    cases hsp
  unfold qStar at hnot
  omega

/-- Core logarithm specification, copied in a local form. -/
private theorem resetColdHeadlineCeilEq (m : Nat)
    (hm : 2 ≤ m) :
    ceilLogTwo m = Nat.log2 (m - 1) + 1 := by
  unfold ceilLogTwo
  have h : ¬ m ≤ 1 := by omega
  rw [if_neg h]

private theorem resetColdHeadlineCeilSpec (m : Nat)
    (hm : 2 ≤ m) :
    2 ^ (ceilLogTwo m - 1) < m ∧
      m ≤ 2 ^ ceilLogTwo m := by
  rw [resetColdHeadlineCeilEq m hm]
  have hne : m - 1 ≠ 0 := by omega
  have hh := (Nat.log2_eq_iff hne).1 rfl
  simp only [Nat.add_sub_cancel]
  omega

private theorem resetColdHeadlineCeilLeSelf (m : Nat) :
    ceilLogTwo m ≤ m := by
  by_cases hm : 2 ≤ m
  · have h := (resetColdHeadlineCeilSpec m hm).1
    have hp : ceilLogTwo m - 1 <
        2 ^ (ceilLogTwo m - 1) :=
      Nat.lt_two_pow_self
    omega
  · unfold ceilLogTwo
    have h : m ≤ 1 := by omega
    rw [if_pos h]
    omega

/-- For spatial advice, the padded width is already >=6. -/
private theorem resetColdHeadlineLogGeSix (q : Nat)
    (hq : 33 ≤ q) :
    6 ≤ ceilLogTwo q := by
  have hupper :=
    (resetColdHeadlineCeilSpec q (by omega)).2
  rcases Nat.lt_or_ge (ceilLogTwo q) 6 with hsmall | hlarge
  · have hexp : ceilLogTwo q ≤ 5 := by omega
    have hp : 2 ^ ceilLogTwo q ≤ 2 ^ 5 :=
      Nat.pow_le_pow_right (by omega) hexp
    have h32 : (2 : Nat) ^ 5 = 32 := by decide
    omega
  · exact hlarge

/-- Elementary bound for the production kappa on s>=6. -/
private theorem resetColdHeadlineKappaBound (s : Nat)
    (hs : 6 ≤ s) :
    kappaDot s ≤ 557 * s + 119982 := by
  unfold kappaDot
  have hn2 : ¬ s = 2 := by omega
  have hn3 : ¬ s = 3 := by omega
  have hn4 : ¬ s = 4 := by omega
  have hn5 : ¬ s = 5 := by omega
  have hnsmall : ¬ s ≤ 5 := by omega
  rw [if_neg hn2, if_neg hn3, if_neg hn4,
    if_neg hn5, if_neg hnsmall]
  by_cases h6 : s = 6
  · rw [if_pos h6]
    omega
  · rw [if_neg h6]
    have hh := resetColdHeadlineCeilLeSelf
      (557 * s + 119981 + 1)
    omega

/-- The compile-time capacity inequality for an exponential
digit word; the base is just 2^6=64. -/
private theorem resetColdHeadlineGrowth (s : Nat)
    (hs : 6 ≤ s) :
    557 * s + 119983 < 2046 * 2 ^ s := by
  have hkey : ∀ k : Nat,
      557 * (k + 6) + 119983 <
        2046 * 2 ^ (k + 6) := by
    intro k
    induction k with
    | zero =>
        have hp : (2 : Nat) ^ 6 = 64 := by decide
        rw [hp]
        omega
    | succ k ih =>
        have hpositive : 0 < 2 ^ (k + 6) :=
          Nat.two_pow_pos (k + 6)
        have htwice :
            2 ^ (k + 1 + 6) =
              2 ^ (k + 6) * 2 := by
          have heq : k + 1 + 6 = (k + 6) + 1 := by omega
          rw [heq]
          exact Nat.pow_succ 2 (k + 6)
        omega
  have hh := hkey (s - 6)
  have heq : s - 6 + 6 = s := by omega
  rw [heq] at hh
  exact hh

/-- Stronger production property K+1 < 2^b on the spatial band.
In particular the bank's compiled target word cannot overflow. -/
theorem resetColdPrivateCompiledSpatialCapacity (q : Nat)
    (hsp : (compileAdvice q).useSmall = false) :
    (compileAdvice q).K + 1 <
      2 ^ (compileAdvice q).b := by
  have hq : 80 ≤ q :=
    resetColdPrivateSpatialAdviceGe q hsp
  have hlog := resetColdHeadlineLogGeSix q (by omega)
  have hupper :=
    (resetColdHeadlineCeilSpec q (by omega)).2
  have hmax :
      max 2 (ceilLogTwo q) = ceilLogTwo q := by omega
  have hnot32 : ¬ q ≤ 32 := by omega
  have hk :
      productionKappa q = kappaDot (ceilLogTwo q) := by
    unfold productionKappa
    rw [if_neg hnot32]
    change kappaDot (max 2 (ceilLogTwo q)) =
      kappaDot (ceilLogTwo q)
    rw [hmax]
  have hkd := resetColdHeadlineKappaBound
    (ceilLogTwo q) hlog
  have hg := resetColdHeadlineGrowth
    (ceilLogTwo q) hlog
  have h11 : (2 : Nat) ^ 11 = 2048 := by decide
  have hpow :
      2 ^ (ceilLogTwo q + 11) =
        2 ^ ceilLogTwo q * 2048 := by
    rw [Nat.pow_add, h11]
  change 2 * q + productionKappa q + 1 <
    2 ^ (max 2 (ceilLogTwo q) + 11)
  rw [hmax, hk, hpow]
  omega

/-- Exactly the width hypothesis consumed by the
word and probability theorems. -/
theorem resetColdPrivateCompiledSpatialWidth (q : Nat)
    (hsp : (compileAdvice q).useSmall = false) :
    (compileAdvice q).K < 2 ^ (compileAdvice q).b := by
  have hh := resetColdPrivateCompiledSpatialCapacity q hsp
  omega

/-- A general, small-base linear-versus-exponential inequality.
The base uses 2^10=1024, not a large closed computation. -/
private theorem resetColdHeadlineSizeGrowth :
    ∀ k : Nat,
      26 * (k + 24) ≤ 2 ^ (k + 10) := by
  intro k
  induction k with
  | zero =>
      have hp : (2 : Nat) ^ 10 = 1024 := by decide
      rw [hp]
      omega
  | succ k ih =>
      have htwice :
          2 ^ (k + 1 + 10) =
            2 ^ (k + 10) * 2 := by
        have heq : k + 1 + 10 = (k + 10) + 1 := by omega
        rw [heq]
        exact Nat.pow_succ 2 (k + 10)
      omega

private theorem resetColdHeadlineSizeBound (q : Nat)
    (hq : 11 ≤ q) :
    26 * (q + 13) ≤ 2 ^ (q - 1) := by
  have hh := resetColdHeadlineSizeGrowth (q - 11)
  have harg : q - 11 + 24 = q + 13 := by omega
  have hexp : q - 11 + 10 = q - 1 := by omega
  rw [harg, hexp] at hh
  exact hh

/-- Since s=ceilLogTwo q <= q on the spatial branch,
the doubled BANK lease never exceeds 26(q+13). -/
private theorem resetColdHeadlineLeaseBound (q : Nat)
    (hq : 80 ≤ q) :
    2 * (compileAdvice q).bankLeaseCap ≤
      26 * (q + 13) := by
  have hlog := resetColdHeadlineLogGeSix q (by omega)
  have hmax :
      max 2 (ceilLogTwo q) = ceilLogTwo q := by omega
  have hceil := resetColdHeadlineCeilLeSelf q
  change 2 * (13 * (max 2 (ceilLogTwo q) + 11 + 2)) ≤
    26 * (q + 13)
  rw [hmax]
  omega

/-- Actual headline ring size: q=ceilLogTwo n and spatial
q>=80 imply n>2^(q-1), already above twice the BANK cap. -/
theorem resetColdPrivateHeadlineLarge (n : Nat)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n := by
  have hq : 80 ≤ ceilLogTwo n :=
    resetColdPrivateSpatialAdviceGe (ceilLogTwo n) hsp
  have hlease :=
    resetColdHeadlineLeaseBound (ceilLogTwo n) hq
  have hpower :=
    resetColdHeadlineSizeBound (ceilLogTwo n) (by omega)
  have hlower :=
    (resetColdHeadlineCeilSpec n (by omega)).1
  omega

/-- For clarity, the compiled spatial switch in headline terms
already forces n>2^79; no assumption q>512 is needed. -/
theorem resetColdPrivateHeadlineSpatialLower (n : Nat)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    2 ^ 79 < n := by
  have hq : 80 ≤ ceilLogTwo n :=
    resetColdPrivateSpatialAdviceGe (ceilLogTwo n) hsp
  have hpow : 2 ^ 79 ≤ 2 ^ (ceilLogTwo n - 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hlower :=
    (resetColdHeadlineCeilSpec n (by omega)).1
  omega

/-- Headline specialization of the physical finite-horizon
probability bound. No independent width, size, or HeadRows
premise survives; only the spatial selection and the genuine
Clean/global-grant-free starting domain are required. -/
theorem resetColdLatchedPrivateUpperHeadline {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (Czero : Config (ceilLogTwo n) n)
    (hc : ResetClockBankClean ring Czero root)
    (hg : resetColdPrivateGlobalGrantFree Czero)
    (T : Nat) :
    2 ^ (compileAdvice (ceilLogTwo n)).K *
      resetColdLatchedPrivateSuccessMass ring root Czero T ≤
        n ^ T := by
  exact resetColdLatchedPrivateUpperSpatial
    ring root hsp
    (resetColdPrivateHeadlineLarge n hn hsp)
    (resetColdPrivateCompiledSpatialWidth (ceilLogTwo n) hsp)
    Czero hc hg T

end Counter
end L3

/-!
Deterministic head/tail decisions and the positive
private-success converse for the latched physical observer.

The private success guard reads the OLD root grant bit.
No globally grant-free cut is inferred from Auth alone.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- Decision made by the orientation of the next root-incident
service at an ARMED root. This is used only at ARMED cuts. -/
inductive ResetColdPrivateArmDecision where
  | head
  | tail
  deriving DecidableEq, Repr

def resetColdPrivateArmDecision {n : Nat}
    (root e : Fin n) : ResetColdPrivateArmDecision :=
  if e = root then .head else .tail

/-- Outgoing service of an ARMED root is the HEAD orientation. -/
theorem resetColdPrivateArmHeadChoice {n : Nat}
    (root e : Fin n) (he : e = root) :
    resetColdPrivateArmDecision root e = .head := by
  unfold resetColdPrivateArmDecision
  rw [if_pos he]

/-- At a root-incident edge other than the outgoing root edge,
the orientation is the incoming TAIL. -/
theorem resetColdPrivateArmTailChoice {n : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (hincident : resetColdLatchedIncident ring root e)
    (hne : e ≠ root) :
    resetColdPrivateArmDecision root e = .tail ∧
      ring.rightNeighbor e = root := by
  have hpred : ring.rightNeighbor e = root := by
    rcases hincident with he | hp
    · exact False.elim (hne he)
    · exact hp
  constructor
  · unfold resetColdPrivateArmDecision
    rw [if_neg hne]
  · exact hpred

/-- A HEAD which remains LIVE is one genuine increment of the
represented head, irrespective of the low digit/carry branch. -/
theorem resetColdPrivateArmHeadLive {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (ha : ResetColdPrivateLiveShapeAuth ring root C)
    (hm : (C root).mode = .ARMED)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) root = .live D started') :
    ResetColdPrivateLiveShapeAuth ring root D ∧
      resetColdPrivateHeadValue ring root D =
        resetColdPrivateHeadValue ring root C + 1 := by
  have hh := resetColdPrivateAuthRootLive
    ring root C D started started' hc hsp hwidth ha hnext
  refine ⟨hh.1, ?_⟩
  rcases hh.2 with hhead | hother
  · exact hhead.2
  · exact False.elim (hother.1 hm)

/-- The exact HEAD increment at any surviving LIVE cut of an
arbitrary genuine observer word issued from Clean. -/
theorem resetColdPrivateArmHeadFromClean {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (Czero : Config q n)
    (hclean : ResetClockBankClean ring Czero root)
    (w : List (Fin n)) (C : Config q n)
    (started : Bool)
    (hrun : resetColdLatchedPrivateRun ring root
      (.live Czero false) w = .live C started)
    (hm : (C root).mode = .ARMED)
    (D : Config q n) (started' : Bool)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) root = .live D started') :
    ResetColdPrivateLiveShapeAuth ring root D ∧
      resetColdPrivateHeadValue ring root D =
        resetColdPrivateHeadValue ring root C + 1 := by
  have ha := resetColdPrivateLiveShapeAuthWord
    ring root hsp hlarge hwidth
    Czero hclean w C started hrun
  exact resetColdPrivateArmHeadLive
    ring root C D started started'
    ha.2 hsp hwidth ha.1 hm hnext

/-- Every incoming ARMED tail exits LIVE immediately.
A detected defect or a newly Clean cut is failure; otherwise
the abort latch enters recovery. The observer does not
instantaneously restart a new trial. -/
theorem resetColdPrivateArmTailClassified {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Config q n) (started : Bool)
    (hm : (C root).mode = .ARMED)
    (hne : e ≠ root)
    (hpred : ring.rightNeighbor e = root) :
    resetColdLatchedPrivateNext ring root
        (.live C started) e =
      .failure ((protocol q).step ring C e) ∨
    resetColdLatchedPrivateNext ring root
        (.live C started) e =
      .recovery ((protocol q).step ring C e) := by
  have hprivate : ¬ resetColdPrivateSuccessAt ring root C e := by
    intro hs
    exact hne (resetColdPrivateSuccessOutgoing
      ring root e C hs)
  have hbegin : resetColdLatchedBegun ring root e started :=
    Or.inr (Or.inr hpred)
  have habort : resetColdLatchedAbort ring root C e :=
    Or.inl ⟨hm, hne, hpred⟩
  by_cases hd : ResetClockBankDefectEntry ring C root e
  · apply Or.inl
    simp only [resetColdLatchedPrivateNext, if_pos hd]
  · by_cases hclean : ResetClockBankClean ring
        ((protocol q).step ring C e) root
    · apply Or.inl
      simp only [resetColdLatchedPrivateNext,
        if_neg hd, if_neg hprivate, if_pos hbegin,
        if_pos hclean]
    · apply Or.inr
      simp only [resetColdLatchedPrivateNext,
        if_neg hd, if_neg hprivate, if_pos hbegin,
        if_neg hclean, if_pos habort]

/-- In particular a TAIL is never a LIVE-to-LIVE transition. -/
theorem resetColdPrivateArmTailNotLive {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hm : (C root).mode = .ARMED)
    (hne : e ≠ root)
    (hpred : ring.rightNeighbor e = root) :
    ¬ resetColdLatchedPrivateNext ring root
      (.live C started) e = .live D started' := by
  intro hn
  exact resetColdPrivateAuthIncomingArmedImpossible
    ring root e C D started started' hne hpred hm hn

/-- At a nondefective, grant-free, complete ARMED cut,
the physical incoming service really resets the root and
the observer enters recovery (not merely an abstract tail). -/
theorem resetColdPrivateArmTailRecovery {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Config q n) (started : Bool)
    (hsp : (compileAdvice q).useSmall = false)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hno : ¬ ResetClockBankDefectEntry ring C root e)
    (hm : (C root).mode = .ARMED)
    (hne : e ≠ root)
    (hpred : ring.rightNeighbor e = root) :
    resetColdLatchedPrivateNext ring root
      (.live C started) e =
        .recovery ((protocol q).step ring C e) := by
  exact resetColdLatchedPrivateIncomingTail
    ring root e C started hsp hc hg
    hno hpred hne hm

/-- Positive OLD-pair BANK success guard. GrantFree is
essential: Auth and a represented head of K do not inspect
the token owner's old root GRANT bit. -/
theorem resetColdPrivateCL1PositiveGuard {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hm : (C root).mode = .CWAIT)
    (ht : (C (site ring root 1)).tok = .CL1) :
    resetColdPrivateSuccessAt ring root C root := by
  have hb : 0 < (compileAdvice q).b := by
    have hh := resetTrialCompiledWidth q
    omega
  have hroot : (C root).pack.val = 0 := by
    simpa only [site] using hc 0 (by omega)
  have hone : (C (site ring root 1)).pack.val = 1 :=
    hc 1 (by omega)
  have hpost :
      packNext 0 1 (compileAdvice q).b = 1 := by
    unfold packNext
    rw [if_pos (by omega : 0 < (compileAdvice q).b)]
  refine ⟨rfl, ?_⟩
  change bankSuccess
    (bankCell (C root) (C root).pack.val)
    (bankCell (C (site ring root 1))
      (C (site ring root 1)).pack.val)
    (packNext (C root).pack.val
      (C (site ring root 1)).pack.val
      (compileAdvice q).b)
    (compileAdvice q).b = true
  have hg' : (C root).grant = false := hg
  simp [bankSuccess, bankCell, hroot, hone,
    hpost, hg', hm, ht]

/-- On a complete, OLD grant-free physical CWAIT/CL1 pair,
the observer actually enters its success constructor on
the next outgoing root service. -/
theorem resetColdPrivateCL1PositiveObserver {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (started : Bool)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hm : (C root).mode = .CWAIT)
    (ht : (C (site ring root 1)).tok = .CL1) :
    resetColdLatchedPrivateNext ring root
      (.live C started) root =
        .success ((protocol q).step ring C root) := by
  have hb : 0 < (compileAdvice q).b := by
    have hh := resetTrialCompiledWidth q
    omega
  have hgood := internal_good ring C root 0 hc hb
  change goodPair (compileAdvice q).b
    (C root).pack
    (C (ring.rightNeighbor root)).pack = true at hgood
  have hno : ¬ ResetClockBankDefectEntry
      ring C root root :=
    resetColdNoDefectOfGood ring root root C hgood
  have hs := resetColdPrivateCL1PositiveGuard
    ring root C hc hg hm ht
  simp only [resetColdLatchedPrivateNext,
    if_neg hno, if_pos hs]

/-- The authenticated returning CL1 branch is automatically
at head K (the full theta word), and the physical observer
takes private success at the next root service. This is
stronger than assuming the head equality separately. -/
theorem resetColdPrivateCL1AuthenticatedSuccess {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (started : Bool)
    (hc : Complete ring C root)
    (hg : GrantFree C root)
    (hsp : (compileAdvice q).useSmall = false)
    (ha : ResetColdPrivateLiveShapeAuth ring root C)
    (hm : (C root).mode = .CWAIT)
    (ht : (C (site ring root 1)).tok = .CL1) :
    resetColdPrivateHeadValue ring root C =
        (compileAdvice q).K ∧
      resetColdPrivateSuccessAt ring root C root ∧
      resetColdLatchedPrivateNext ring root
        (.live C started) root =
          .success ((protocol q).step ring C root) := by
  have hs := resetColdPrivateCL1PositiveGuard
    ring root C hc hg hm ht
  have hwidth :=
    resetColdPrivateCompiledSpatialWidth q hsp
  have hhead := resetColdPrivateSuccessHeadOfShape
    ring root root C hwidth ha.1 hs
  have hnext := resetColdPrivateCL1PositiveObserver
    ring root C started hc hg hm ht
  exact ⟨hhead, hs, hnext⟩

/-- Apply the positive result at any still-LIVE endpoint
of a real Clean-start word. The root's old grant-free bit
is an explicit condition at this endpoint. -/
theorem resetColdPrivateCL1SuccessFromClean {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (Czero : Config q n)
    (hclean : ResetClockBankClean ring Czero root)
    (w : List (Fin n)) (C : Config q n)
    (started : Bool)
    (hrun : resetColdLatchedPrivateRun ring root
      (.live Czero false) w = .live C started)
    (hg : GrantFree C root)
    (hm : (C root).mode = .CWAIT)
    (ht : (C (site ring root 1)).tok = .CL1) :
    resetColdPrivateHeadValue ring root C =
        (compileAdvice q).K ∧
      resetColdPrivateSuccessAt ring root C root ∧
      resetColdLatchedPrivateNext ring root
        (.live C started) root =
          .success ((protocol q).step ring C root) := by
  have ha := resetColdPrivateLiveShapeAuthWord
    ring root hsp hlarge hwidth
    Czero hclean w C started hrun
  exact resetColdPrivateCL1AuthenticatedSuccess
    ring root C started ha.2 hg hsp ha.1 hm ht

end Counter
end L3

/-!
Unique-worker launch origin at a LIVE Clean-start cut.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

/-- ARMED and Auth imply every protected worker slot is empty. -/
theorem resetColdPrivateArmedAuthNoWorkers {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (ha : ResetColdPrivateLiveShapeAuth ring root C)
    (hm : (C root).mode = .ARMED) :
    resetColdPrivateNoWorkers ring root C := by
  rcases ha.1 with harm | hrest
  · obtain ⟨h, hb, hmode, hn, hv⟩ := harm
    exact hn
  · rcases hrest with hs | hrest
    · obtain ⟨h, hb, hmode, hn, hv⟩ := hs
      rw [hm] at hmode
      cases hmode
    · rcases hrest with hc | hi
      · obtain ⟨h, j, t, hb, hmode, hw, ht, hv,
          hprefix, hfull⟩ := hc
        rw [hm] at hmode
        cases hmode
      · obtain ⟨h, j, t, hb, hmode, hw, ht, hv⟩ := hi
        rw [hm] at hmode
        cases hmode

/-- CSTART and Auth likewise imply an empty protected worker word. -/
theorem resetColdPrivateCStartAuthNoWorkers {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (ha : ResetColdPrivateLiveShapeAuth ring root C)
    (hm : (C root).mode = .CSTART) :
    resetColdPrivateNoWorkers ring root C := by
  rcases ha.1 with harm | hrest
  · obtain ⟨h, hb, hmode, hn, hv⟩ := harm
    rw [hm] at hmode
    cases hmode
  · rcases hrest with hs | hrest
    · obtain ⟨h, hb, hmode, hn, hv⟩ := hs
      exact hn
    · rcases hrest with hc | hi
      · obtain ⟨h, j, t, hb, hmode, hw, ht, hv,
          hprefix, hfull⟩ := hc
        rw [hm] at hmode
        cases hmode
      · obtain ⟨h, j, t, hb, hmode, hw, ht, hv⟩ := hi
        rw [hm] at hmode
        cases hmode

/-- A genuinely launched IWAIT worker is isolated at digit one.
The old snapshot is an arbitrary surviving LIVE prefix from Clean;
it cannot contain a leftover CR/IR at digit two. -/
theorem resetColdPrivateIncrementLaunchIsolated {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (Czero : Config q n)
    (hclean : ResetClockBankClean ring Czero root)
    (hgzero : resetColdPrivateGlobalGrantFree Czero)
    (w : List (Fin n)) (C D : Config q n)
    (started started' : Bool)
    (hrun : resetColdLatchedPrivateRun ring root
      (.live Czero false) w = .live C started)
    (hm : (C root).mode = .ARMED)
    (hnew : (D root).mode = .IWAIT)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) root = .live D started') :
    resetColdPrivateOnlyWorker ring root D 1 .IR := by
  have hold := resetColdPrivateLiveShapeAuthWord
    ring root hsp hlarge hwidth
    Czero hclean w C started hrun
  have hn := resetColdPrivateArmedAuthNoWorkers
    ring root C hold.1 hm
  have hg := resetColdPrivateLiveOutgoingGrantFree
    ring root C D started started' hold.2 hsp hnext
  have hp := resetColdPrivateLivePhysical
    ring root root C D started started' hnext
  have hb : 1 ≤ (compileAdvice q).b := by
    have hh := resetTrialCompiledWidth q
    omega
  have ht : (C (site ring root 1)).tok = .E :=
    hn 1 (by omega) hb
  cases hbit : (C (site ring root 1)).bit with
  | false =>
      have hrow := resetColdLatchedPhysicalArmedFirstSet
        ring C root hold.2 hg hsp hm ht hbit
      have hmnew : (D root).mode = .CSTART := by
        rw [hp]
        exact hrow.1
      rw [hmnew] at hnew
      cases hnew
  | true =>
      have hrow := resetColdPrivateArmedCarryPhysical
        ring root C hold.2 hg hsp hm ht hbit
      refine ⟨by omega, hb, ?_, ?_⟩
      · rw [hp]
        exact hrow.2.2
      · intro j hj hjb hne
        have htwo : 2 ≤ j := by omega
        rw [hp, resetColdOutgoingRootOtherDigitsFrame
          ring C root hold.2 j htwo hjb]
        exact hn j hj hjb

/-- A CSTART root service on a surviving Clean-start LIVE word
launches exactly one first-digit comparator, with no stale worker
on any higher digit, even after arbitrary earlier head decisions. -/
theorem resetColdPrivateComparatorLaunchIsolated {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (Czero : Config q n)
    (hclean : ResetClockBankClean ring Czero root)
    (hgzero : resetColdPrivateGlobalGrantFree Czero)
    (w : List (Fin n)) (C D : Config q n)
    (started started' : Bool)
    (hrun : resetColdLatchedPrivateRun ring root
      (.live Czero false) w = .live C started)
    (hm : (C root).mode = .CSTART)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) root = .live D started') :
    (D root).mode = .CWAIT ∧
      ∃ t : BTok, (t = .CR0 ∨ t = .CR1) ∧
        resetColdPrivateOnlyWorker ring root D 1 t := by
  have hold := resetColdPrivateLiveShapeAuthWord
    ring root hsp hlarge hwidth
    Czero hclean w C started hrun
  have hn := resetColdPrivateCStartAuthNoWorkers
    ring root C hold.1 hm
  have hg := resetColdPrivateLiveOutgoingGrantFree
    ring root C D started started' hold.2 hsp hnext
  have hp := resetColdPrivateLivePhysical
    ring root root C D started started' hnext
  have hb : 1 ≤ (compileAdvice q).b := by
    have hh := resetTrialCompiledWidth q
    omega
  have ht : (C (site ring root 1)).tok = .E :=
    hn 1 (by omega) hb
  have hrow := resetColdPrivateCStartComparatorPhysical
    ring root C hold.2 hg hsp hm ht
  have hmode : (D root).mode = .CWAIT := by
    rw [hp]
    exact hrow.1
  have htok :
      (D (site ring root 1)).tok =
        (if (C (site ring root 1)).bit ==
            (compileAdvice q).theta 0 then .CR1 else .CR0) := by
    rw [hp]
    exact hrow.2.2
  refine ⟨hmode,
    (if (C (site ring root 1)).bit ==
      (compileAdvice q).theta 0 then BTok.CR1 else BTok.CR0),
    ?_, ?_⟩
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl
  · refine ⟨by omega, hb, htok, ?_⟩
    intro j hj hjb hne
    have htwo : 2 ≤ j := by omega
    rw [hp, resetColdOutgoingRootOtherDigitsFrame
      ring C root hold.2 j htwo hjb]
    exact hn j hj hjb


/-- A waiting root with a nonreturn first digit cannot change
its mode on a LIVE outgoing service. Lease expiry would abort. -/
theorem resetColdPrivateLiveWaitNonreturnMode {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hm : isWaitMode (C root).mode = true)
    (ht : isRetTok (C (site ring root 1)).tok = false)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) root = .live D started') :
    (D root).mode = (C root).mode := by
  have hg := resetColdPrivateLiveOutgoingGrantFree
    ring root C D started started' hc hsp hnext
  have hrow := resetColdPhysicalWaitNonreturn
    ring C root hc hg hsp hm ht
  have hn := resetColdPrivateLiveRootNotReset
    ring root root C D started started' hnext
  have hlease : 1 < (C root).lease.val := by
    by_cases hl : 1 < (C root).lease.val
    · exact hl
    · have hf :
          (((protocol q).step ring C root) root).mode =
            .RESET := by
        rw [hrow.1]
        simp [resetColdWaitTickMode, hl]
      exact False.elim (hn hf)
  have hp := resetColdPrivateLivePhysical
    ring root root C D started started' hnext
  rw [hp, hrow.1]
  simp [resetColdWaitTickMode, hlease]

/-- A non-root service retaining LIVE cannot change the root
mode. Incoming services frame CSTART and tick a wait, and an
incoming ARMED service instead exits LIVE. -/
theorem resetColdPrivateLiveNonRootModeFrame {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (ha : ResetColdPrivateLiveShapeAuth ring root C)
    (he : e ≠ root)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) e = .live D started') :
    (D root).mode = (C root).mode := by
  have hp := resetColdPrivateLivePhysical
    ring root e C D started started' hnext
  by_cases hpred : ring.rightNeighbor e = root
  · have hrole := resetColdIncomingRoleOfNoDefect
      ring C root e hc hpred
      (resetColdPrivateLiveNoDefect
        ring root e C D started started' hnext)
    have hg := resetColdPrivateLiveIncidentGrantFree
      ring root e C D started started' hc hsp
      (Or.inr hpred) hnext
    rcases ha.1 with harm | hrest
    · obtain ⟨h, hb, hm, hn, hv⟩ := harm
      exact False.elim
        (resetColdPrivateAuthIncomingArmedImpossible
          ring root e C D started started'
          he hpred hm hnext)
    · rcases hrest with hs | hrest
      · obtain ⟨h, hb, hm, hn, hv⟩ := hs
        have hf := resetColdPhysicalIncomingCStart
          ring C root e hc hg hsp hpred hrole hm
        rw [hp, hf.1, hm]
      · rcases hrest with hcwait | hiwait
        · obtain ⟨h, j, t, hb, hm, hw, ht, hv,
              hprefix, hfull⟩ := hcwait
          have hwm : isWaitMode (C root).mode = true := by
            rw [hm]
            rfl
          have hf := resetColdPhysicalIncomingWait
            ring C root e hc hg hsp hpred hrole hwm
          have hn := resetColdPrivateLiveRootNotReset
            ring root e C D started started' hnext
          have hlease : 1 < (C root).lease.val := by
            by_cases hl : 1 < (C root).lease.val
            · exact hl
            · have hreset :
                  (((protocol q).step ring C e) root).mode =
                    .RESET := by
                rw [hf.1]
                simp [resetColdWaitTickMode, hl]
              exact False.elim (hn hreset)
          rw [hp, hf.1]
          simp [resetColdWaitTickMode, hlease]
        · obtain ⟨h, j, t, hb, hm, hw, ht, hv⟩ := hiwait
          have hwm : isWaitMode (C root).mode = true := by
            rw [hm]
            rfl
          have hf := resetColdPhysicalIncomingWait
            ring C root e hc hg hsp hpred hrole hwm
          have hn := resetColdPrivateLiveRootNotReset
            ring root e C D started started' hnext
          have hlease : 1 < (C root).lease.val := by
            by_cases hl : 1 < (C root).lease.val
            · exact hl
            · have hreset :
                  (((protocol q).step ring C e) root).mode =
                    .RESET := by
                rw [hf.1]
                simp [resetColdWaitTickMode, hl]
              exact False.elim (hn hreset)
          rw [hp, hf.1]
          simp [resetColdWaitTickMode, hlease]
  · have hf := step_frame ring C e root
      (Ne.symm he) (Ne.symm hpred)
    rw [hp, hf]

/-- ARMED root services that remain LIVE have only the ordinary
CSTART/low-set and IWAIT/carry physical successors. -/
theorem resetColdPrivateLiveArmedRootModes {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (ha : ResetColdPrivateLiveShapeAuth ring root C)
    (hm : (C root).mode = .ARMED)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) root = .live D started') :
    (D root).mode = .CSTART ∨ (D root).mode = .IWAIT := by
  have hn := resetColdPrivateArmedAuthNoWorkers ring root C ha hm
  have hg := resetColdPrivateLiveOutgoingGrantFree
    ring root C D started started' hc hsp hnext
  have hp := resetColdPrivateLivePhysical
    ring root root C D started started' hnext
  have hb : 1 ≤ (compileAdvice q).b := by
    have hh := resetTrialCompiledWidth q
    omega
  have ht := hn 1 (by omega) hb
  cases hbit : (C (site ring root 1)).bit with
  | false =>
      have hf := resetColdLatchedPhysicalArmedFirstSet
        ring C root hc hg hsp hm ht hbit
      left
      rw [hp]
      exact hf.1
  | true =>
      have hf := resetColdPrivateArmedCarryPhysical
        ring root C hc hg hsp hm ht hbit
      right
      rw [hp]
      exact hf.1

/-- A CSTART root service that remains LIVE starts CWAIT. -/
theorem resetColdPrivateLiveCStartRootMode {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (ha : ResetColdPrivateLiveShapeAuth ring root C)
    (hm : (C root).mode = .CSTART)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) root = .live D started') :
    (D root).mode = .CWAIT := by
  have hn := resetColdPrivateCStartAuthNoWorkers ring root C ha hm
  have hg := resetColdPrivateLiveOutgoingGrantFree
    ring root C D started started' hc hsp hnext
  have hp := resetColdPrivateLivePhysical
    ring root root C D started started' hnext
  have hb : 1 ≤ (compileAdvice q).b := by
    have hh := resetTrialCompiledWidth q
    omega
  have ht := hn 1 (by omega) hb
  have hf := resetColdPrivateCStartComparatorPhysical
    ring root C hc hg hsp hm ht
  rw [hp]
  exact hf.1

/-- IWAIT can stay waiting or accept its returning AL and enter
CSTART. No other LIVE root mode is produced. -/
theorem resetColdPrivateLiveIWaitRootModes {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (ha : ResetColdPrivateLiveShapeAuth ring root C)
    (hm : (C root).mode = .IWAIT)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) root = .live D started') :
    (D root).mode = .IWAIT ∨ (D root).mode = .CSTART := by
  rcases ha.1 with harm | hrest
  · obtain ⟨h, hb, hmode, hn, hv⟩ := harm
    rw [hm] at hmode
    cases hmode
  · rcases hrest with hs | hrest
    · obtain ⟨h, hb, hmode, hn, hv⟩ := hs
      rw [hm] at hmode
      cases hmode
    · rcases hrest with hcwait | hiwait
      · obtain ⟨h, j, t, hb, hmode, hw, ht, hv,
            hprefix, hfull⟩ := hcwait
        rw [hm] at hmode
        cases hmode
      · obtain ⟨h, j, t, hb, hmode, hw, ht, hv⟩ := hiwait
        have hwidth : 1 ≤ (compileAdvice q).b := by
          have hh := resetTrialCompiledWidth q
          omega
        by_cases hjone : j = 1
        · subst j
          rcases ht with hir | hal
          · have hfirst : isRetTok (C (site ring root 1)).tok =
                false := by
              rw [hw.2.2.1, hir]
              rfl
            left
            rw [resetColdPrivateLiveWaitNonreturnMode
              ring root C D started started'
              hc hsp (by rw [hm]; rfl) hfirst hnext]
            exact hm
          · have htok : (C (site ring root 1)).tok = .AL :=
              hw.2.2.1.trans hal
            have hg := resetColdPrivateLiveOutgoingGrantFree
              ring root C D started started' hc hsp hnext
            have hp := resetColdPrivateLivePhysical
              ring root root C D started started' hnext
            have hf := resetColdPrivateRootALPhysicalFields
              ring root C hc hg hsp hm htok
            right
            rw [hp]
            exact hf.1
        · have hfirst : (C (site ring root 1)).tok = .E :=
            hw.2.2.2 1 (by omega) hwidth (Ne.symm hjone)
          have hret : isRetTok (C (site ring root 1)).tok =
              false := by
            rw [hfirst]
            rfl
          left
          rw [resetColdPrivateLiveWaitNonreturnMode
            ring root C D started started'
            hc hsp (by rw [hm]; rfl) hret hnext]
          exact hm

/-- CWAIT can stay waiting or consume CL0 and rearm.
The CL1 return is terminal private success, not LIVE. -/
theorem resetColdPrivateLiveCWaitRootModes {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (ha : ResetColdPrivateLiveShapeAuth ring root C)
    (hm : (C root).mode = .CWAIT)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) root = .live D started') :
    (D root).mode = .CWAIT ∨ (D root).mode = .ARMED := by
  rcases ha.1 with harm | hrest
  · obtain ⟨h, hb, hmode, hn, hv⟩ := harm
    rw [hm] at hmode
    cases hmode
  · rcases hrest with hs | hrest
    · obtain ⟨h, hb, hmode, hn, hv⟩ := hs
      rw [hm] at hmode
      cases hmode
    · rcases hrest with hcwait | hiwait
      · obtain ⟨h, j, t, hb, hmode, hw, ht, hv,
            hprefix, hfull⟩ := hcwait
        have hwidth : 1 ≤ (compileAdvice q).b := by
          have hh := resetTrialCompiledWidth q
          omega
        by_cases hjone : j = 1
        · subst j
          rcases ht with hcr | hcr | hcl | hcl
          · have hfirst : isRetTok (C (site ring root 1)).tok =
                false := by
              rw [hw.2.2.1, hcr]
              rfl
            left
            rw [resetColdPrivateLiveWaitNonreturnMode
              ring root C D started started'
              hc hsp (by rw [hm]; rfl) hfirst hnext]
            exact hm
          · have hfirst : isRetTok (C (site ring root 1)).tok =
                false := by
              rw [hw.2.2.1, hcr]
              rfl
            left
            rw [resetColdPrivateLiveWaitNonreturnMode
              ring root C D started started'
              hc hsp (by rw [hm]; rfl) hfirst hnext]
            exact hm
          · have htok : (C (site ring root 1)).tok = .CL0 :=
              hw.2.2.1.trans hcl
            have hg := resetColdPrivateLiveOutgoingGrantFree
              ring root C D started started' hc hsp hnext
            have hp := resetColdPrivateLivePhysical
              ring root root C D started started' hnext
            have hf := resetColdPrivateRootCL0PhysicalFields
              ring root C hc hg hsp hm htok
            right
            rw [hp]
            exact hf.1
          · have htok : (C (site ring root 1)).tok = .CL1 :=
              hw.2.2.1.trans hcl
            exact False.elim
              (resetColdPrivateLiveCL1RootImpossible
                ring root C D started started' hc hsp hm htok hnext)
        · have hfirst : (C (site ring root 1)).tok = .E :=
            hw.2.2.2 1 (by omega) hwidth (Ne.symm hjone)
          have hret : isRetTok (C (site ring root 1)).tok =
              false := by
            rw [hfirst]
            rfl
          left
          rw [resetColdPrivateLiveWaitNonreturnMode
            ring root C D started started'
            hc hsp (by rw [hm]; rfl) hret hnext]
          exact hm
      · obtain ⟨h, j, t, hb, hmode, hw, ht, hv⟩ := hiwait
        rw [hm] at hmode
        cases hmode


/-- Three distinct genuine physical worker-launch categories.
Their origin is the service, not a guessed later return. -/
inductive ResetColdPrivateLaunchKind where
  | reset
  | increment
  | comparator
  deriving DecidableEq, Repr

/-- At most one actual root worker launch per physical service.
RESET requires an OLD RESET root and a new RWAIT root;
increment requires ARMED to IWAIT; comparator requires
CSTART to CWAIT. Recovery and terminal states emit nothing. -/
noncomputable def resetColdPrivateWorkerStarts {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ResetColdLatchedPrivateState q n → Fin n →
      List ResetColdPrivateLaunchKind
  | .live C _, e =>
      if e = root then
        match (C root).mode with
        | .RESET =>
            if (((protocol q).step ring C root) root).mode = .RWAIT
            then [.reset] else []
        | .ARMED =>
            if (((protocol q).step ring C root) root).mode = .IWAIT
            then [.increment] else []
        | .CSTART =>
            if (((protocol q).step ring C root) root).mode = .CWAIT
            then [.comparator] else []
        | _ => []
      else []
  | _, _ => []

/-- The one unit of comparator work pending during IWAIT/CSTART
is counted in addition to the two slots per remaining head. -/
def resetColdPrivatePendingCredit : Mode → Nat
  | .IWAIT => 1
  | .CSTART => 1
  | _ => 0

def resetColdPrivateWorkerBudget {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) : Nat :=
  2 * ((compileAdvice q).K -
    resetColdPrivateHeadValue ring root C) +
      resetColdPrivatePendingCredit (C root).mode

/-- The Auth step proves exact head conservation off the
only head-producing ARMED outgoing edge. -/
theorem resetColdPrivateLiveNonHeadConserves {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (ha : ResetColdPrivateLiveShapeAuth ring root C)
    (hnot : e ≠ root ∨ (C root).mode ≠ .ARMED)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) e = .live D started') :
    resetColdPrivateHeadValue ring root D =
      resetColdPrivateHeadValue ring root C := by
  have hh := resetColdPrivateLiveAuthStep
    ring root e C D started started'
    hc hsp hlarge hwidth ha hnext
  rcases hh.2 with hinc | hstay
  · rcases hnot with hne | hnm
    · exact False.elim (hne hinc.1)
    · exact False.elim (hnm hinc.2.1)
  · exact hstay.2

/-- Every surviving LIVE service spends at least as much
remaining worker budget as the number of origins it creates.
The inequality includes an outgoing ARMED service that only
sets a low bit and hence emits no increment worker. -/
theorem resetColdPrivateWorkerBudgetLiveStep {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (ha : ResetColdPrivateLiveShapeAuth ring root C)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) e = .live D started') :
    (resetColdPrivateWorkerStarts ring root (.live C started) e).length +
      resetColdPrivateWorkerBudget ring root D ≤
        resetColdPrivateWorkerBudget ring root C := by
  have hp := resetColdPrivateLivePhysical
    ring root e C D started started' hnext
  have hheadle := resetColdPrivateLiveShapeHeadLe ring root C ha.1
  by_cases he : e = root
  · subst e
    rcases ha.1 with harm | hrest
    · obtain ⟨h, hbound, hm, hn, hv⟩ := harm
      have hnewhead := (resetColdPrivateArmHeadLive
        ring root C D started started'
        hc hsp hwidth ha hm hnext).2
      rcases resetColdPrivateLiveArmedRootModes
          ring root C D started started' hc hsp ha hm hnext with
          hstart | hwait
      · have hnewphys :
            (((protocol q).step ring C root) root).mode =
              .CSTART := by
          rw [← hp]
          exact hstart
        have hcost :
            (resetColdPrivateWorkerStarts
              ring root (.live C started) root).length = 0 := by
          simp [resetColdPrivateWorkerStarts, hm, hnewphys]
        simp [resetColdPrivateWorkerBudget,
          resetColdPrivatePendingCredit,
          hcost, hm, hstart, hnewhead, hv] <;> omega
      · have hnewphys :
            (((protocol q).step ring C root) root).mode =
              .IWAIT := by
          rw [← hp]
          exact hwait
        have hcost :
            (resetColdPrivateWorkerStarts
              ring root (.live C started) root).length = 1 := by
          simp [resetColdPrivateWorkerStarts, hm, hnewphys]
        simp [resetColdPrivateWorkerBudget,
          resetColdPrivatePendingCredit,
          hcost, hm, hwait, hnewhead, hv] <;> omega
    · rcases hrest with hs | hrest
      · obtain ⟨h, hbound, hm, hn, hv⟩ := hs
        have hnew := resetColdPrivateLiveCStartRootMode
          ring root C D started started' hc hsp ha hm hnext
        have hnewphys :
            (((protocol q).step ring C root) root).mode =
              .CWAIT := by
          rw [← hp]
          exact hnew
        have hcost :
            (resetColdPrivateWorkerStarts
              ring root (.live C started) root).length = 1 := by
          simp [resetColdPrivateWorkerStarts, hm, hnewphys]
        have hsame := resetColdPrivateLiveNonHeadConserves
          ring root root C D started started'
          hc hsp hlarge hwidth ha
          (Or.inr (by rw [hm]; intro he; cases he)) hnext
        simp [resetColdPrivateWorkerBudget,
          resetColdPrivatePendingCredit,
          hcost, hm, hnew, hsame] <;> omega
      · rcases hrest with hcwait | hiwait
        · obtain ⟨h, j, t, hbound, hm, hw, ht, hv,
              hprefix, hfull⟩ := hcwait
          have hnew := resetColdPrivateLiveCWaitRootModes
            ring root C D started started' hc hsp ha hm hnext
          have hcost :
              (resetColdPrivateWorkerStarts
                ring root (.live C started) root).length = 0 := by
            simp [resetColdPrivateWorkerStarts, hm]
          have hsame := resetColdPrivateLiveNonHeadConserves
            ring root root C D started started'
            hc hsp hlarge hwidth ha
            (Or.inr (by rw [hm]; intro he; cases he)) hnext
          rcases hnew with hmode | hmode
          · simp [resetColdPrivateWorkerBudget,
              resetColdPrivatePendingCredit,
              hcost, hm, hmode, hsame]
          · simp [resetColdPrivateWorkerBudget,
              resetColdPrivatePendingCredit,
              hcost, hm, hmode, hsame]
        · obtain ⟨h, j, t, hbound, hm, hw, ht, hv⟩ := hiwait
          have hnew := resetColdPrivateLiveIWaitRootModes
            ring root C D started started' hc hsp ha hm hnext
          have hcost :
              (resetColdPrivateWorkerStarts
                ring root (.live C started) root).length = 0 := by
            simp [resetColdPrivateWorkerStarts, hm]
          have hsame := resetColdPrivateLiveNonHeadConserves
            ring root root C D started started'
            hc hsp hlarge hwidth ha
            (Or.inr (by rw [hm]; intro he; cases he)) hnext
          rcases hnew with hmode | hmode
          · simp [resetColdPrivateWorkerBudget,
              resetColdPrivatePendingCredit,
              hcost, hm, hmode, hsame]
          · simp [resetColdPrivateWorkerBudget,
              resetColdPrivatePendingCredit,
              hcost, hm, hmode, hsame]
  · have hmode := resetColdPrivateLiveNonRootModeFrame
      ring root e C D started started' hc hsp ha he hnext
    have hsame := resetColdPrivateLiveNonHeadConserves
      ring root e C D started started'
      hc hsp hlarge hwidth ha (Or.inl he) hnext
    have hcost :
        (resetColdPrivateWorkerStarts
          ring root (.live C started) e).length = 0 := by
      simp [resetColdPrivateWorkerStarts, he]
    simp [resetColdPrivateWorkerBudget, hcost, hmode, hsame]


/-- Even when the selected service exits LIVE, no more than
the current phase budget can be spent on its one final origin. -/
theorem resetColdPrivateWorkerStartsLengthLeBudget {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C : Config q n) (started : Bool)
    (ha : ResetColdPrivateLiveShapeAuth ring root C) :
    (resetColdPrivateWorkerStarts ring root
      (.live C started) e).length ≤
        resetColdPrivateWorkerBudget ring root C := by
  by_cases he : e = root
  · subst e
    rcases ha.1 with harm | hrest
    · obtain ⟨h, hb, hm, hn, hv⟩ := harm
      cases hpost : (((protocol q).step ring C root) root).mode <;>
        simp [resetColdPrivateWorkerStarts,
          resetColdPrivateWorkerBudget,
          resetColdPrivatePendingCredit,
          hm, hpost, hv] <;> omega
    · rcases hrest with hs | hrest
      · obtain ⟨h, hb, hm, hn, hv⟩ := hs
        cases hpost : (((protocol q).step ring C root) root).mode <;>
          simp [resetColdPrivateWorkerStarts,
            resetColdPrivateWorkerBudget,
            resetColdPrivatePendingCredit,
            hm, hpost, hv] <;> omega
      · rcases hrest with hc | hi
        · obtain ⟨h, j, t, hb, hm, hw, ht, hv,
              hprefix, hfull⟩ := hc
          simp [resetColdPrivateWorkerStarts,
            resetColdPrivateWorkerBudget,
            resetColdPrivatePendingCredit, hm]
        · obtain ⟨h, j, t, hb, hm, hw, ht, hv⟩ := hi
          simp [resetColdPrivateWorkerStarts,
            resetColdPrivateWorkerBudget,
            resetColdPrivatePendingCredit, hm]
  · simp only [resetColdPrivateWorkerStarts,
      if_neg he, List.length_nil]
    exact Nat.zero_le _

/-- Recovery, failure, and their full suffixes never create
another private worker origin. This is the latched observer,
not a physical restart after the first failed trial. -/
private theorem resetColdPrivateWorkerOriginsDead {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (z : ResetColdLatchedPrivateState q n)
      (w : List (Fin n)),
      resetColdLatchedPrivateDead z →
      L3.Prob.originsWord
        (resetColdLatchedPrivateNext ring root)
        resetColdLatchedPrivateTerminal
        (resetColdPrivateWorkerStarts ring root) z w = 0 := by
  intro z w
  induction w generalizing z with
  | nil =>
      intro hz
      rfl
  | cons e tail ih =>
      intro hz
      cases z with
      | live C started =>
          exact False.elim hz
      | recovery C =>
          have hd := resetColdLatchedPrivateDeadStep
            ring root (.recovery C) (by exact True.intro) e
          have hh := ih
            (resetColdLatchedPrivateNext ring root
              (.recovery C) e) hd
          rw [L3.Prob.originsWord, if_neg
            (show ¬ resetColdLatchedPrivateTerminal
              (.recovery C : ResetColdLatchedPrivateState q n) from id)]
          change 0 + L3.Prob.originsWord
              (resetColdLatchedPrivateNext ring root)
              resetColdLatchedPrivateTerminal
              (resetColdPrivateWorkerStarts ring root)
              (resetColdLatchedPrivateNext ring root
                (.recovery C) e) tail = 0
          simpa only [Nat.zero_add] using hh
      | success C =>
          simp [L3.Prob.originsWord, resetColdLatchedPrivateTerminal]
      | failure C =>
          simp [L3.Prob.originsWord, resetColdLatchedPrivateTerminal]

/-- Full word induction on the genuine observer tape.
The remaining capacity is 2(K-head) plus one pending
IWAIT/CSTART comparator slot. No future-selected success
word is used in the count. -/
private theorem resetColdPrivateWorkerOriginsBudget {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b) :
    ∀ (C : Config q n) (started : Bool)
      (w : List (Fin n)),
      ResetColdPrivateLiveShapeAuth ring root C →
      Complete ring C root →
      L3.Prob.originsWord
        (resetColdLatchedPrivateNext ring root)
        resetColdLatchedPrivateTerminal
        (resetColdPrivateWorkerStarts ring root)
        (.live C started) w ≤
          resetColdPrivateWorkerBudget ring root C := by
  intro C started w
  induction w generalizing C started with
  | nil =>
      intro ha hc
      change 0 ≤ resetColdPrivateWorkerBudget ring root C
      exact Nat.zero_le _
  | cons e tail ih =>
      intro ha hc
      rw [L3.Prob.originsWord, if_neg
        (show ¬ resetColdLatchedPrivateTerminal
          (.live C started : ResetColdLatchedPrivateState q n) from id)]
      change (resetColdPrivateWorkerStarts
          ring root (.live C started) e).length +
        L3.Prob.originsWord
          (resetColdLatchedPrivateNext ring root)
          resetColdLatchedPrivateTerminal
          (resetColdPrivateWorkerStarts ring root)
          (resetColdLatchedPrivateNext ring root
            (.live C started) e) tail ≤
        resetColdPrivateWorkerBudget ring root C
      cases hnext : resetColdLatchedPrivateNext
          ring root (.live C started) e with
      | live D started' =>
          have hh := resetColdPrivateLiveAuthStep
            ring root e C D started started'
            hc hsp hlarge hwidth ha hnext
          have hcD := resetColdPrivateLiveCompleteStep
            ring root e C D started started' hc hnext
          have hbudget := resetColdPrivateWorkerBudgetLiveStep
            ring root e C D started started'
            hc hsp hlarge hwidth ha hnext
          have hi := ih D started' hh.1 hcD
          exact Nat.le_trans
            (Nat.add_le_add_left hi
              (resetColdPrivateWorkerStarts
                ring root (.live C started) e).length)
            hbudget
      | recovery D =>
          have hh := resetColdPrivateWorkerStartsLengthLeBudget
            ring root e C started ha
          have hz := resetColdPrivateWorkerOriginsDead
            ring root (.recovery D) tail (by exact True.intro)
          rw [hz, Nat.add_zero]
          exact hh
      | success D =>
          have hh := resetColdPrivateWorkerStartsLengthLeBudget
            ring root e C started ha
          have hz : L3.Prob.originsWord
              (resetColdLatchedPrivateNext ring root)
              resetColdLatchedPrivateTerminal
              (resetColdPrivateWorkerStarts ring root)
              (.success D) tail = 0 := by
            cases tail <;>
              simp [L3.Prob.originsWord, resetColdLatchedPrivateTerminal]
          rw [hz, Nat.add_zero]
          exact hh
      | failure D =>
          have hh := resetColdPrivateWorkerStartsLengthLeBudget
            ring root e C started ha
          have hz : L3.Prob.originsWord
              (resetColdLatchedPrivateNext ring root)
              resetColdLatchedPrivateTerminal
              (resetColdPrivateWorkerStarts ring root)
              (.failure D) tail = 0 := by
            cases tail <;>
              simp [L3.Prob.originsWord, resetColdLatchedPrivateTerminal]
          rw [hz, Nat.add_zero]
          exact hh

/-- Stronger than C.4's 2K+1 multiplicity premise: from a
genuine Clean cut there are at most 2K physical worker origins
before the latched observer stops, for every finite edge word. -/
theorem resetColdPrivateWorkerStartCapTight {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (Czero : Config q n)
    (hclean : ResetClockBankClean ring Czero root)
    (hgzero : resetColdPrivateGlobalGrantFree Czero)
    (w : List (Fin n)) :
    L3.Prob.originsWord
      (resetColdLatchedPrivateNext ring root)
      resetColdLatchedPrivateTerminal
      (resetColdPrivateWorkerStarts ring root)
      (.live Czero false) w ≤ 2 * (compileAdvice q).K := by
  have hh := resetColdPrivateWorkerOriginsBudget
    ring root hsp hlarge hwidth Czero false w
    (resetColdPrivateLiveShapeAuthClean
      ring root Czero hclean hsp) hclean.1
  have hz := resetColdPrivateHeadValueClean
    ring root Czero hclean
  have hm := hclean.2.1
  have hbudget :
      resetColdPrivateWorkerBudget ring root Czero =
        2 * (compileAdvice q).K := by
    simp [resetColdPrivateWorkerBudget,
      resetColdPrivatePendingCredit, hz, hm]
  rw [hbudget] at hh
  exact hh

/-- The exact originsWord/starts-function shape of
CounterTrialLower.PrivateCleanWorkerStartCap, without a
circular import of CounterTrialLower into CounterCold.
It allows the stipulated extra RESET worker slot. -/
theorem resetColdPrivateWorkerStartCap {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (Czero : Config q n)
    (hclean : ResetClockBankClean ring Czero root)
    (hgzero : resetColdPrivateGlobalGrantFree Czero) :
    ∀ w : List (Fin n),
      L3.Prob.originsWord
        (resetColdLatchedPrivateNext ring root)
        resetColdLatchedPrivateTerminal
        (resetColdPrivateWorkerStarts ring root)
        (.live Czero false) w ≤
          2 * (compileAdvice q).K + 1 := by
  intro w
  have hh := resetColdPrivateWorkerStartCapTight
    ring root hsp hlarge hwidth
    Czero hclean hgzero w
  omega


/-- Pointwise domination of starts-list lengths lifts through
the exact finite-word originsWord recursion. A future bridge
may specialize it to the downstream CounterTrialLower starts. -/
theorem resetColdPrivateWorkerOriginsMonotone {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    {O : Type}
    (starts : ResetColdLatchedPrivateState q n →
      Fin n → List O)
    (hpoint : ∀ z e,
      (starts z e).length ≤
        (resetColdPrivateWorkerStarts ring root z e).length) :
    ∀ (z : ResetColdLatchedPrivateState q n)
      (w : List (Fin n)),
      L3.Prob.originsWord
        (resetColdLatchedPrivateNext ring root)
        resetColdLatchedPrivateTerminal
        starts z w ≤
      L3.Prob.originsWord
        (resetColdLatchedPrivateNext ring root)
        resetColdLatchedPrivateTerminal
        (resetColdPrivateWorkerStarts ring root) z w := by
  intro z w
  induction w generalizing z with
  | nil =>
      exact Nat.le_refl _
  | cons e tail ih =>
      by_cases ht : resetColdLatchedPrivateTerminal z
      · simp only [L3.Prob.originsWord, if_pos ht]
        exact Nat.le_refl _
      · simp only [L3.Prob.originsWord, if_neg ht]
        exact Nat.add_le_add (hpoint z e)
          (ih (resetColdLatchedPrivateNext ring root z e))

/-- Any postservice-certified subset of these literal physical
launch kinds inherits C.4's 2K+1 origin cap. This theorem
is stated in the same polymorphic starts-list format used by
CounterTrialLower, avoiding an illegal reverse import. -/
theorem resetColdPrivateWorkerStartCapOfDomination {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (Czero : Config q n)
    (hclean : ResetClockBankClean ring Czero root)
    (hgzero : resetColdPrivateGlobalGrantFree Czero)
    {O : Type}
    (starts : ResetColdLatchedPrivateState q n →
      Fin n → List O)
    (hpoint : ∀ z e,
      (starts z e).length ≤
        (resetColdPrivateWorkerStarts ring root z e).length) :
    ∀ w : List (Fin n),
      L3.Prob.originsWord
        (resetColdLatchedPrivateNext ring root)
        resetColdLatchedPrivateTerminal
        starts (.live Czero false) w ≤
          2 * (compileAdvice q).K + 1 := by
  intro w
  have hmono := resetColdPrivateWorkerOriginsMonotone
    ring root starts hpoint (.live Czero false) w
  have hcap := resetColdPrivateWorkerStartCap
    ring root hsp hlarge hwidth Czero hclean hgzero w
  exact Nat.le_trans hmono hcap

end Counter
end L3


/-!
Current-worker LIVE potential.

This counts the currently present worker, not future launches.
A fresh CSTART -> CWAIT launch raises the potential from zero.
-/

namespace L3
namespace Counter

set_option autoImplicit false
set_option Elab.async false

open Classical

/-- Remaining designated services for an authenticated worker.
CR/CL are included because LIVE Auth also permits comparison. -/
def resetColdPrivateWorkerDistance
    (b j : Nat) (t : BTok) : Nat :=
  match t with
  | .IR => 2 * b + 2 - j
  | .CR0 => 2 * b + 2 - j
  | .CR1 => 2 * b + 2 - j
  | .AL => j
  | .CL0 => j
  | .CL1 => j
  | _ => 0

/-- Classical choice is canonical on Auth, since Auth has
at most one nonempty protected digit. -/
noncomputable def resetColdPrivateLivePotential {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) : Nat :=
  if h : ∃ j : Nat, 1 ≤ j ∧
      j ≤ (compileAdvice q).b ∧
      (C (site ring root j)).tok ≠ .E then
    resetColdPrivateWorkerDistance
      (compileAdvice q).b (Classical.choose h)
      (C (site ring root (Classical.choose h))).tok
  else
    0

theorem resetColdPrivateLivePotentialOfWorker {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (j : Nat) (t : BTok)
    (hw : resetColdPrivateOnlyWorker ring root C j t)
    (ht : t ≠ .E) :
    resetColdPrivateLivePotential ring root C =
      resetColdPrivateWorkerDistance (compileAdvice q).b j t := by
  have hex : ∃ k : Nat, 1 ≤ k ∧
      k ≤ (compileAdvice q).b ∧
      (C (site ring root k)).tok ≠ .E :=
    ⟨j, hw.1, hw.2.1, by rw [hw.2.2.1]; exact ht⟩
  unfold resetColdPrivateLivePotential
  rw [dif_pos hex]
  have hs := Classical.choose_spec hex
  have hj : Classical.choose hex = j := by
    by_cases he : Classical.choose hex = j
    · exact he
    · have hz := hw.2.2.2 (Classical.choose hex)
        hs.1 hs.2.1 he
      exact False.elim (hs.2.2 hz)
  rw [hj, hw.2.2.1]

theorem resetColdPrivateLivePotentialIR {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (j : Nat)
    (hw : resetColdPrivateOnlyWorker ring root C j .IR) :
    resetColdPrivateLivePotential ring root C =
      2 * (compileAdvice q).b + 2 - j := by
  rw [resetColdPrivateLivePotentialOfWorker
    ring root C j .IR hw (by intro he; cases he)]
  rfl

theorem resetColdPrivateLivePotentialAL {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n) (j : Nat)
    (hw : resetColdPrivateOnlyWorker ring root C j .AL) :
    resetColdPrivateLivePotential ring root C = j := by
  rw [resetColdPrivateLivePotentialOfWorker
    ring root C j .AL hw (by intro he; cases he)]
  rfl

theorem resetColdPrivateLivePotentialNoWorkers {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (hn : resetColdPrivateNoWorkers ring root C) :
    resetColdPrivateLivePotential ring root C = 0 := by
  have he : ¬ ∃ j : Nat, 1 ≤ j ∧
      j ≤ (compileAdvice q).b ∧
      (C (site ring root j)).tok ≠ .E := by
    intro hx
    obtain ⟨j, hj, hjb, ht⟩ := hx
    exact ht (hn j hj hjb)
  unfold resetColdPrivateLivePotential
  rw [dif_neg he]

theorem resetColdPrivateOnlyWorkerTokFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n)
    (hf : ∀ i : Nat, 1 ≤ i →
      i ≤ (compileAdvice q).b →
      (D (site ring root i)).tok =
        (C (site ring root i)).tok)
    (j : Nat) (t : BTok)
    (hw : resetColdPrivateOnlyWorker ring root C j t) :
    resetColdPrivateOnlyWorker ring root D j t := by
  refine ⟨hw.1, hw.2.1, ?_, ?_⟩
  · exact (hf j hw.1 hw.2.1).trans hw.2.2.1
  · intro i hi hib hne
    exact (hf i hi hib).trans (hw.2.2.2 i hi hib hne)

theorem resetColdPrivateNoWorkersTokFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n)
    (hf : ∀ i : Nat, 1 ≤ i →
      i ≤ (compileAdvice q).b →
      (D (site ring root i)).tok =
        (C (site ring root i)).tok)
    (hn : resetColdPrivateNoWorkers ring root C) :
    resetColdPrivateNoWorkers ring root D := by
  intro i hi hib
  exact (hf i hi hib).trans (hn i hi hib)

/-- Auth is precisely a no-worker phase or a single nonempty
comparator/carry worker phase. -/
theorem resetColdPrivateAuthWorkerOrEmpty {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Config q n)
    (ha : ResetColdPrivateLiveShapeAuth ring root C) :
    (∃ j : Nat, ∃ t : BTok,
        resetColdPrivateOnlyWorker ring root C j t ∧
        t ≠ .E) ∨
      resetColdPrivateNoWorkers ring root C := by
  rcases ha.1 with harm | hrest
  · obtain ⟨h, hb, hm, hn, hv⟩ := harm
    exact Or.inr hn
  · rcases hrest with hstart | hrest
    · obtain ⟨h, hb, hm, hn, hv⟩ := hstart
      exact Or.inr hn
    · rcases hrest with hcompare | hcarry
      · obtain ⟨h, j, t, hb, hm, hw, ht, hv,
          hgood, hfull⟩ := hcompare
        refine Or.inl ⟨j, t, hw, ?_⟩
        rcases ht with hcr | hcr | hcl | hcl
        · rw [hcr]; intro he; cases he
        · rw [hcr]; intro he; cases he
        · rw [hcl]; intro he; cases he
        · rw [hcl]; intro he; cases he
      · obtain ⟨h, j, t, hb, hm, hw, ht, hv⟩ := hcarry
        refine Or.inl ⟨j, t, hw, ?_⟩
        rcases ht with hir | hal
        · rw [hir]; intro he; cases he
        · rw [hal]; intro he; cases he

/-- Every full protected-digit token frame preserves potential. -/
theorem resetColdPrivateLivePotentialTokFrame {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n)
    (ha : ResetColdPrivateLiveShapeAuth ring root C)
    (hf : ∀ i : Nat, 1 ≤ i →
      i ≤ (compileAdvice q).b →
      (D (site ring root i)).tok =
        (C (site ring root i)).tok) :
    resetColdPrivateLivePotential ring root D =
      resetColdPrivateLivePotential ring root C := by
  rcases resetColdPrivateAuthWorkerOrEmpty
      ring root C ha with hworker | hn
  · obtain ⟨j, t, hw, ht⟩ := hworker
    have hnew := resetColdPrivateOnlyWorkerTokFrame
      ring root C D hf j t hw
    rw [resetColdPrivateLivePotentialOfWorker
      ring root D j t hnew ht,
      resetColdPrivateLivePotentialOfWorker
        ring root C j t hw ht]
  · have hnew := resetColdPrivateNoWorkersTokFrame
      ring root C D hf hn
    rw [resetColdPrivateLivePotentialNoWorkers
      ring root D hnew,
      resetColdPrivateLivePotentialNoWorkers
        ring root C hn]

/-- (b) exterior scheduler edges that touch neither BANK nor root. -/
theorem resetColdPrivateLivePotentialOutside {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (C D : Config q n) (started started' : Bool)
    (ha : ResetColdPrivateLiveShapeAuth ring root C)
    (hrsource : e ≠ root)
    (hrtarget : ring.rightNeighbor e ≠ root)
    (hsource : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b → e ≠ site ring root j)
    (htarget : ∀ j : Nat, 1 ≤ j →
      j ≤ (compileAdvice q).b →
        ring.rightNeighbor e ≠ site ring root j)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) e = .live D started') :
    resetColdPrivateLivePotential ring root D =
      resetColdPrivateLivePotential ring root C := by
  have hp := resetColdPrivateLivePhysical
    ring root e C D started started' hnext
  apply resetColdPrivateLivePotentialTokFrame
    ring root C D ha
  intro i hi hib
  rw [hp]
  rw [step_frame ring C e (site ring root i)
    (Ne.symm (hsource i hi hib))
    (Ne.symm (htarget i hi hib))]

/-- (b) root WAIT lease ticks with no return token. -/
theorem resetColdPrivateLivePotentialWaitRoot {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (ha : ResetColdPrivateLiveShapeAuth ring root C)
    (hm : isWaitMode (C root).mode = true)
    (ht : isRetTok (C (site ring root 1)).tok = false)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) root = .live D started') :
    resetColdPrivateLivePotential ring root D =
      resetColdPrivateLivePotential ring root C := by
  have hg := resetColdPrivateLiveOutgoingGrantFree
    ring root C D started started' hc hsp hnext
  have hf := resetColdPhysicalWaitNonreturn
    ring C root hc hg hsp hm ht
  have hp := resetColdPrivateLivePhysical
    ring root root C D started started' hnext
  apply resetColdPrivateLivePotentialTokFrame
    ring root C D ha
  intro i hi hib
  rw [hp]
  by_cases hone : i = 1
  · subst i
    exact hf.2.2
  · rw [resetColdOutgoingRootOtherDigitsFrame
      ring C root hc i (by omega) hib]

/-- (b) empty internal BANK pair, including every nonincident
service whose source index is in the interval [1,b). -/
theorem resetColdPrivateLivePotentialInteriorEmpty {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (j : Nat) (hj : 1 ≤ j)
    (hjb : j < (compileAdvice q).b)
    (ha : ResetColdPrivateLiveShapeAuth ring root C)
    (hx : (C (site ring root j)).tok = .E)
    (hy : (C (site ring root (j + 1))).tok = .E)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) (site ring root j) =
        .live D started') :
    resetColdPrivateLivePotential ring root D =
      resetColdPrivateLivePotential ring root C := by
  have hraw := resetColdPrivateInteriorHoldBank
    (bankCell (C (site ring root j)) j)
    (bankCell (C (site ring root (j + 1))) (j + 1))
    (compileAdvice q).b (compileAdvice q).theta
    (by change 1 ≤ j; exact hj)
    (by change j < (compileAdvice q).b; exact hjb)
    rfl
    (by change (C (site ring root j)).tok = .E ∨
      (C (site ring root j)).tok = .AL ∨
      (C (site ring root j)).tok = .CL0 ∨
      (C (site ring root j)).tok = .CL1; exact Or.inl hx)
    (by change (C (site ring root (j + 1))).tok = .E; exact hy)
  have hbank :
      (resetColdPrivateInteriorBankAt ring root C j).1.tok =
        (C (site ring root j)).tok ∧
      (resetColdPrivateInteriorBankAt ring root C j).1.bit =
        (C (site ring root j)).bit ∧
      (resetColdPrivateInteriorBankAt ring root C j).2.tok =
        (C (site ring root (j + 1))).tok ∧
      (resetColdPrivateInteriorBankAt ring root C j).2.bit =
        (C (site ring root (j + 1))).bit := by
    unfold resetColdPrivateInteriorBankAt
    have hr := hraw
    simp only [bankCell] at hr ⊢
    exact hr
  have hf := resetColdPrivateInteriorRowFields
    ring root C hc hsp j hj hjb
    (C (site ring root j)).tok
    (C (site ring root (j + 1))).tok
    (C (site ring root j)).bit
    (C (site ring root (j + 1))).bit hbank
  have hp := resetColdPrivateLivePhysical
    ring root (site ring root j) C D started started' hnext
  apply resetColdPrivateLivePotentialTokFrame
    ring root C D ha
  intro i hi hib
  rw [hp]
  by_cases hs : i = j
  · subst i
    exact hf.1
  · by_cases hd : i = j + 1
    · subst i
      exact hf.2.2.1
    · rw [resetColdPrivateInteriorOtherFrame
        ring root C hc j hj hjb i hi hib hs hd]

/-- (b), an interior pair disjoint from the sole worker. -/
theorem resetColdPrivateLivePotentialInteriorAway {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (j k : Nat) (hj : 1 ≤ j)
    (hjb : j < (compileAdvice q).b)
    (t : BTok)
    (ha : ResetColdPrivateLiveShapeAuth ring root C)
    (hw : resetColdPrivateOnlyWorker ring root C k t)
    (hl : k ≠ j) (hr : k ≠ j + 1)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) (site ring root j) =
        .live D started') :
    resetColdPrivateLivePotential ring root D =
      resetColdPrivateLivePotential ring root C := by
  have hx : (C (site ring root j)).tok = .E :=
    hw.2.2.2 j hj (by omega) (Ne.symm hl)
  have hy : (C (site ring root (j + 1))).tok = .E :=
    hw.2.2.2 (j + 1) (by omega) (by omega) (Ne.symm hr)
  exact resetColdPrivateLivePotentialInteriorEmpty
    ring root C D started started' hc hsp
    j hj hjb ha hx hy hnext

/-- (a), IR(j) goes to IR(j+1) or AL(j+1), both cheaper. -/
theorem resetColdPrivateLivePotentialIRForward {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (j : Nat) (hj : 1 ≤ j)
    (hjb : j < (compileAdvice q).b)
    (hw : resetColdPrivateOnlyWorker ring root C j .IR)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) (site ring root j) =
        .live D started') :
    resetColdPrivateLivePotential ring root D + 1 ≤
      resetColdPrivateLivePotential ring root C := by
  have hempty : (C (site ring root (j + 1))).tok = .E :=
    hw.2.2.2 (j + 1) (by omega) (by omega) (by omega)
  have hraw := resetColdPrivateIRForwardBank
    (bankCell (C (site ring root j)) j)
    (bankCell (C (site ring root (j + 1))) (j + 1))
    (compileAdvice q).b (compileAdvice q).theta
    (by change 1 ≤ j; exact hj)
    (by change j < (compileAdvice q).b; exact hjb)
    rfl
    (by change (C (site ring root j)).tok = .IR; exact hw.2.2.1)
    (by change (C (site ring root (j + 1))).tok = .E; exact hempty)
  have hbank :
      (resetColdPrivateInteriorBankAt ring root C j).1.tok = .E ∧
      (resetColdPrivateInteriorBankAt ring root C j).1.bit =
        (C (site ring root j)).bit ∧
      (resetColdPrivateInteriorBankAt ring root C j).2.tok =
        (if (C (site ring root (j + 1))).bit
          then BTok.IR else BTok.AL) ∧
      (resetColdPrivateInteriorBankAt ring root C j).2.bit =
        !(C (site ring root (j + 1))).bit := by
    unfold resetColdPrivateInteriorBankAt
    have hr := hraw
    simp only [bankCell] at hr ⊢
    exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2⟩
  have hf := resetColdPrivateInteriorRowFields
    ring root C hc hsp j hj hjb
    .E
    (if (C (site ring root (j + 1))).bit
      then BTok.IR else BTok.AL)
    (C (site ring root j)).bit
    (!(C (site ring root (j + 1))).bit) hbank
  have hnew := resetColdPrivateInteriorWorkerForward
    ring root C hc j hj hjb .IR
    (if (C (site ring root (j + 1))).bit
      then BTok.IR else BTok.AL)
    hw hf.1 hf.2.2.1
  have hp := resetColdPrivateLivePhysical
    ring root (site ring root j) C D started started' hnext
  have hd : resetColdPrivateOnlyWorker ring root D (j + 1)
      (if (C (site ring root (j + 1))).bit
        then BTok.IR else BTok.AL) := by
    rw [hp]
    exact hnew
  cases hbit : (C (site ring root (j + 1))).bit with
  | false =>
      have hal : resetColdPrivateOnlyWorker
          ring root D (j + 1) .AL := by
        simpa only [hbit, Bool.false_eq_true, ↓reduceIte] using hd
      rw [resetColdPrivateLivePotentialAL
        ring root D (j + 1) hal,
        resetColdPrivateLivePotentialIR ring root C j hw]
      omega
  | true =>
      have hir : resetColdPrivateOnlyWorker
          ring root D (j + 1) .IR := by
        simpa only [hbit, Bool.false_eq_true, ↓reduceIte] using hd
      rw [resetColdPrivateLivePotentialIR
        ring root D (j + 1) hir,
        resetColdPrivateLivePotentialIR ring root C j hw]
      omega

/-- (a), AL(j+1) retreats to AL(j), a one-service drop. -/
theorem resetColdPrivateLivePotentialALRetreat {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (j : Nat) (hj : 1 ≤ j)
    (hjb : j < (compileAdvice q).b)
    (hw : resetColdPrivateOnlyWorker ring root C (j + 1) .AL)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) (site ring root j) =
        .live D started') :
    resetColdPrivateLivePotential ring root D + 1 =
      resetColdPrivateLivePotential ring root C := by
  have hempty : (C (site ring root j)).tok = .E :=
    hw.2.2.2 j hj (by omega) (by omega)
  have hraw := resetColdPrivateALRetreatBank
    (bankCell (C (site ring root j)) j)
    (bankCell (C (site ring root (j + 1))) (j + 1))
    (compileAdvice q).b (compileAdvice q).theta
    (by change 1 ≤ j; exact hj)
    (by change j < (compileAdvice q).b; exact hjb)
    rfl
    (by change (C (site ring root j)).tok = .E; exact hempty)
    (by change (C (site ring root (j + 1))).tok = .AL; exact hw.2.2.1)
  have hbank :
      (resetColdPrivateInteriorBankAt ring root C j).1.tok = .AL ∧
      (resetColdPrivateInteriorBankAt ring root C j).1.bit =
        (C (site ring root j)).bit ∧
      (resetColdPrivateInteriorBankAt ring root C j).2.tok = .E ∧
      (resetColdPrivateInteriorBankAt ring root C j).2.bit =
        (C (site ring root (j + 1))).bit := by
    unfold resetColdPrivateInteriorBankAt
    have hr := hraw
    simp only [bankCell] at hr ⊢
    exact ⟨hr.1, hr.2.2.1, hr.2.1, hr.2.2.2⟩
  have hf := resetColdPrivateInteriorRowFields
    ring root C hc hsp j hj hjb .AL .E
    (C (site ring root j)).bit
    (C (site ring root (j + 1))).bit hbank
  have hnew := resetColdPrivateInteriorWorkerBackward
    ring root C hc j hj hjb .AL .AL
    hw hf.1 hf.2.2.1
  have hp := resetColdPrivateLivePhysical
    ring root (site ring root j) C D started started' hnext
  have hd : resetColdPrivateOnlyWorker ring root D j .AL := by
    rw [hp]
    exact hnew
  rw [resetColdPrivateLivePotentialAL ring root D j hd,
    resetColdPrivateLivePotentialAL ring root C (j + 1) hw]

/-- (a), AL(1) is consumed by root, leaving empty CSTART. -/
theorem resetColdPrivateLivePotentialALRoot {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C D : Config q n) (started started' : Bool)
    (hc : Complete ring C root)
    (hsp : (compileAdvice q).useSmall = false)
    (hm : (C root).mode = .IWAIT)
    (hw : resetColdPrivateOnlyWorker ring root C 1 .AL)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) root = .live D started') :
    resetColdPrivateLivePotential ring root D + 1 =
      resetColdPrivateLivePotential ring root C := by
  have hg := resetColdPrivateLiveOutgoingGrantFree
    ring root C D started started' hc hsp hnext
  have hf := resetColdPrivateRootALPhysicalFields
    ring root C hc hg hsp hm hw.2.2.1
  have hn := resetColdPrivateRootConsumeNoWorkers
    ring root C hc .AL hw hf.2.1
  have hp := resetColdPrivateLivePhysical
    ring root root C D started started' hnext
  have hnone : resetColdPrivateNoWorkers ring root D := by
    rw [hp]
    exact hn
  rw [resetColdPrivateLivePotentialNoWorkers ring root D hnone,
    resetColdPrivateLivePotentialAL ring root C 1 hw]

/-- Obstruction to the UNRESTRICTED (b): no-worker CSTART
root service creates CR0/CR1 and raises current-worker potential.
This is a new launch, not backward motion of an old worker. -/
theorem resetColdPrivateComparatorLaunchRaisesPotential {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hwidth : (compileAdvice q).K <
      2 ^ (compileAdvice q).b)
    (Czero : Config q n)
    (hclean : ResetClockBankClean ring Czero root)
    (hgzero : resetColdPrivateGlobalGrantFree Czero)
    (w : List (Fin n)) (C D : Config q n)
    (started started' : Bool)
    (hrun : resetColdLatchedPrivateRun ring root
      (.live Czero false) w = .live C started)
    (hm : (C root).mode = .CSTART)
    (hnext : resetColdLatchedPrivateNext ring root
      (.live C started) root = .live D started') :
    resetColdPrivateLivePotential ring root C <
      resetColdPrivateLivePotential ring root D := by
  have ha := resetColdPrivateLiveShapeAuthWord
    ring root hsp hlarge hwidth
    Czero hclean w C started hrun
  have hn := resetColdPrivateCStartAuthNoWorkers
    ring root C ha.1 hm
  have hlaunch := resetColdPrivateComparatorLaunchIsolated
    ring root hsp hlarge hwidth Czero hclean hgzero
    w C D started started' hrun hm hnext
  obtain ⟨hmode, t, ht, hw⟩ := hlaunch
  have hb : 1 ≤ (compileAdvice q).b := by
    have hh := resetTrialCompiledWidth q
    omega
  have hz := resetColdPrivateLivePotentialNoWorkers
    ring root C hn
  have hd :
      resetColdPrivateLivePotential ring root D =
        2 * (compileAdvice q).b + 2 - 1 := by
    rcases ht with hcr | hcr
    · rw [hcr] at hw
      rw [resetColdPrivateLivePotentialOfWorker
        ring root D 1 .CR0 hw (by intro he; cases he)]
      rfl
    · rw [hcr] at hw
      rw [resetColdPrivateLivePotentialOfWorker
        ring root D 1 .CR1 hw (by intro he; cases he)]
      rfl
  rw [hz, hd]
  omega

end Counter
end L3
