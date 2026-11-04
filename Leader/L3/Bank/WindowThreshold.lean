import Leader.L3.Bank.WindowOverlapJoint

/-!
R11 consequence: the BANK window exactness invariant J holds at every
state of the rooted renewal run (bankWindowExactStart, bankWindowExactStep),
and the genuine-head threshold at a fresh BANK cut follows from J at the
cut state. This discharges the headline premise hthreshold of
HeadlineCleanAssembly.
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

/-- J is preserved along any continuation of a run word: if J holds after
pre, it holds after pre ++ tail (bankWindowExactStep once per edge;
rbRun of pre ++ [e] is renewalBankNext of rbRun of pre, rbRunAppend).
Consumer: bankWindowExactRun. -/
theorem bankWindowExactRunAppend {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) :
    ∀ (tail pre : List (Fin n)),
      BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre) →
      BankWindowExact ring
        (rbRun ring (renewalBankStart ring seed) (pre ++ tail))
  | [], pre, h => by
      rw [List.append_nil]
      exact h
  | e :: tail, pre, h => by
      have hrun : rbRun ring (renewalBankStart ring seed) (pre ++ [e]) =
          renewalBankNext ring (rbRun ring (renewalBankStart ring seed) pre) e := by
        rw [rbRunAppend]
        rfl
      have hstep : BankWindowExact ring
          (rbRun ring (renewalBankStart ring seed) (pre ++ [e])) := by
        rw [hrun]
        exact bankWindowExactStep ring hn hbank seed pre e h
      have hrest := bankWindowExactRunAppend ring hn hbank seed tail
        (pre ++ [e]) hstep
      rw [List.append_assoc] at hrest
      exact hrest

/-- J at every state of the rooted renewal run.
Consumer: bankCutGenuineHeadThresholdAll. -/
theorem bankWindowExactRun {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (pre : List (Fin n)) :
    BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre) :=
  bankWindowExactRunAppend ring hn hbank seed pre [] (bankWindowExactStart ring seed)

/-- A fresh CL1 cut has the empty waiting list at its source (copy of the
file-private BankWindowInv lemma bankWindowFreshWaitingEmpty).
Consumer: bankCutGenuineHeadThresholdOfWindowExact. -/
theorem bankWindowThresholdFreshWaitingEmpty {n : Nat}
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

/-- The genuine-head threshold from J at every run state: at a fresh cut
the e+ worker is a CL1 comparator of the CWAIT root e with waiting []
(bankComparatorCutPhysicalGuards, bankWindowThresholdFreshWaitingEmpty), so J
phaseFlags makes every digit bit theta (value K), J compareExact gives
heads equal to the value (uncapped), and ReceiptInv identifies heads with
rbHeadCount (bankComparatorFreshCutOwnRoot). Same route as
bankCutGenuineHeadThresholdOfWindowInv, with the exact clauses.
Consumer: bankCutGenuineHeadThresholdAll. -/
theorem bankCutGenuineHeadThresholdOfWindowExact {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hwords : ∀ (seed : RootedSeed ring) (pre : List (Fin n)),
      BankWindowExact ring (rbRun ring (renewalBankStart ring seed) pre)) :
    BankCutGenuineHeadThreshold ring hbank := by
  have hq : 3 ≤ ceilLogTwo n := by
    have hs :
        (compileAdvice (ceilLogTwo n)).useSmall =
          decide (ceilLogTwo n ≤ qStar) := rfl
    have hbank' := hbank
    rw [hs] at hbank'
    have hnot : ¬ ceilLogTwo n ≤ qStar := of_decide_eq_false hbank'
    change ¬ ceilLogTwo n ≤ 79 at hnot
    omega
  intro seed pre e p o hcut hw ho
  have hroot := bankComparatorFreshCutOwnRoot
    ring hn hbank seed pre e p o hcut hw ho
  have hguard := bankComparatorCutPhysicalGuards
    ring (rbRun ring (renewalBankStart ring seed) pre) e hcut
  have hmode :
      ((rbRun ring (renewalBankStart ring seed) pre).1 o.root).mode = .CWAIT := by
    rw [hroot.1]
    exact hguard.1
  have hwait :
      ((rbRun ring (renewalBankStart ring seed) pre).2.sites o.root).controller =
        .waiting [] := by
    rw [hroot.1]
    exact bankWindowThresholdFreshWaitingEmpty ring
      (rbRun ring (renewalBankStart ring seed) pre) e hcut
  have hcmp :
      BankComparatorOriginWorker ring
        (rbRun ring (renewalBankStart ring seed) pre)
        o (ring.rightNeighbor e) p := by
    refine ⟨hw, ho, ?_⟩
    rw [hguard.2]
    exact Or.inr (Or.inr (Or.inr rfl))
  have hmatch := ((hwords seed pre).phaseFlags
    o (ring.rightNeighbor e) p hcmp hmode).2.2.1 hguard.2
  have hbinary := bankComparatorFullMatchBinary ring
    (rbRun ring (renewalBankStart ring seed) pre) o hmatch
  have hexact := (hwords seed pre).compareExact
    o (ring.rightNeighbor e) p hw ho hmode hwait
  have hpaid : p.heads = (compileAdvice (ceilLogTwo n)).K := by
    rw [hexact.2.2.1, hbinary, bankComparatorThetaIsK (ceilLogTwo n) hq]
  exact Nat.le_of_eq (hpaid.symm.trans hroot.2)

/-- The headline premise hthreshold of HeadlineCleanAssembly, for every
ring with at least five agents: J at every run state
(bankWindowExactRun) gives the genuine-head threshold.
Consumer: L3.HeadlineCleanAssembly (replaces the premise hthreshold). -/
theorem bankCutGenuineHeadThresholdAll {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n) :
    ∀ hbank : (compileAdvice (ceilLogTwo n)).useSmall = false,
      BankCutGenuineHeadThreshold ring hbank :=
  fun hbank => bankCutGenuineHeadThresholdOfWindowExact ring hn hbank
    (fun seed pre => bankWindowExactRun ring hn hbank seed pre)

end L3.BankWindow

#print axioms L3.BankWindow.bankWindowExactRunAppend
#print axioms L3.BankWindow.bankWindowExactRun
#print axioms L3.BankWindow.bankWindowThresholdFreshWaitingEmpty
#print axioms L3.BankWindow.bankCutGenuineHeadThresholdOfWindowExact
#print axioms L3.BankWindow.bankCutGenuineHeadThresholdAll
