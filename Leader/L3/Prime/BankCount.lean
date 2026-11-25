import Leader.L3.Headline.RenewalCleanBank
import Leader.L3.Bank.WindowOverlapJoint
import Leader.L3.Prime.RenewalSharp

/-!
Q4656 replacement draft for Leader/L3/Prime/BankCount.lean.

Pinned source: c3a5ea6bbee840b32f228b8e1953453243365a90.
No compiler run or resulting axiom audit is claimed.

EligibleAt, bankCountNom, bankCountPsi and BankCountInv retain the
Q4650 definitions. BankCountStepBound now uses the requested
BankCountInv AND BankSlotInv antecedent. Its conditional consumers
take an explicit slot-preservation premise.

U2 has a proof body below. U1 has actual-launch and strict-age
lemmas, but its uninterrupted interval remains a commented goal.
bankSlotInvNext and bankCountPotentialStep remain commented goals.
The sharp averaging composition is proved conditionally using
L3.Prob.nominated_numerator_le.

The pinned RenewalSharp dependency is also an uncompiled draft.
Its two distributivity proof corrections are described with this
delivery; this file cannot repair an error inside its imported file.
No BANK row or observer row is changed.
-/

namespace L3.Prime

open L3.HeadlineRenewal
open L3.HeadlineRenewalCleanBank
open L3.RenewalReferenceClock
open L3.BankWindow
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false

abbrev bankCountWidth (n : Nat) : Nat :=
  (compileAdvice (ceilLogTwo n)).b

abbrev bankCountHalf (n : Nat) : Nat :=
  bankCountWidth n / 2

/-- A first-token snapshot certificate. This does not assert complete
returning-sweep cleanliness; its reached-state use is a separate obligation.
There is deliberately no grant-free hypothesis here. -/
structure EligibleAt {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n) (j : Nat) : Prop where
  rootRole : (r.1 root).pack.val = 0
  rootMode : (r.1 root).mode = .RWAIT
  currentWait : (r.2.sites root).controller = .waiting []
  positive : 1 ≤ j
  leWidth : j ≤ bankCountWidth n
  roles : ∀ k : Nat, k ≤ j →
    (r.1 (Counter.site ring root k)).pack.val = k
  emptyPrefix : ∀ k : Nat, 1 ≤ k → k < j →
    (r.1 (Counter.site ring root k)).tok = .E
  pending : ∃ rho : RenewalBankReceipt n,
    (r.2.sites (Counter.site ring root j)).worker = .pending rho ∧
    rho.root = root
  resetToken :
    (r.1 (Counter.site ring root j)).tok = .RR ∨
    (r.1 (Counter.site ring root j)).tok = .RL


/-- The proposed slot shape, with no grant hypothesis. -/
structure BankSlotAt {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n) (j : Nat) : Prop
    extends EligibleAt ring r root j where
  phase :
    ((r.1 (Counter.site ring root j)).tok = .RR ∧
      ∀ k : Nat, 1 ≤ k → k < j →
        ∀ rho : RenewalBankReceipt n,
          (r.2.sites (Counter.site ring root k)).worker ≠
            .pending rho) ∨
    (j < bankCountWidth n ∧
      (r.1 (Counter.site ring root j)).tok = .RL ∧
      (∀ k : Nat, k ≤ bankCountWidth n →
        (r.1 (Counter.site ring root k)).pack.val = k) ∧
      ∀ k : Nat, 1 ≤ k → k ≤ bankCountWidth n → k ≠ j →
        (r.1 (Counter.site ring root k)).tok = .E)

/-- Generated reset slots have their own first-token frontier.
An inherited waiting controller has no pending receipt of its root.
The second clause is restricted to role-zero reset-wait roots. -/
structure BankSlotInv {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) : Prop where
  generated :
    ∀ root : Fin n,
      (r.1 root).pack.val = 0 →
      (r.1 root).mode = .RWAIT →
      (r.2.sites root).controller = .waiting [] →
      ∃ j : Nat, BankSlotAt ring r root j
  inherited :
    ∀ (root inheritedAt : Fin n),
      (r.1 root).pack.val = 0 →
      (r.1 root).mode = .RWAIT →
      (r.2.sites root).controller =
        .waiting [(inheritedAt, true)] →
      ∀ (i : Fin n) (rho : RenewalBankReceipt n),
        rho.root = root →
        (r.2.sites i).worker ≠ .pending rho

/-- Nominate the actual source edge of a certified outward frontier.
Historical current-slot identification is not assumed here. -/
noncomputable def bankCountNom {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n) : Bool := by
  classical
  exact decide (∃ (root : Fin n) (j : Nat),
    EligibleAt ring r root j ∧ bankCountHalf n ≤ j ∧
    j < bankCountWidth n ∧
    (r.1 (Counter.site ring root j)).tok = .RR ∧
    e = Counter.site ring root j)

def bankCountCredit (n j : Nat) (tok : BTok) : Nat :=
  if tok = .RL then bankCountWidth n - bankCountHalf n
  else j - bankCountHalf n

noncomputable def bankCountRootCredit {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (root : Fin n) : Nat := by
  classical
  exact if hex : ∃ j : Nat, EligibleAt ring r root j then
    bankCountCredit n (Classical.choose hex)
      (r.1 (Counter.site ring root (Classical.choose hex))).tok
  else 0

noncomputable def bankCountPsi {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) : Nat :=
  (List.ofFn (fun root : Fin n =>
    bankCountRootCredit ring r root)).sum

/-- The closed source invariant J, the receipt ledger, and an actual
run witness. This definition contains no counting/drift assumption. -/
def BankCountInv {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) : Prop :=
  ∃ (seed : RootedSeed ring) (pre : List (Fin n)),
    r = rbRun ring (renewalBankStart ring seed) pre ∧
    ReceiptInv ring seed pre r ∧ BankWindowExact ring r

theorem bankCountInvStart {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) :
    BankCountInv ring (renewalBankStart ring seed) := by
  refine ⟨seed, [], rfl, ?_, ?_⟩
  · exact rbReceiptInvBankWordOfInv ring (by omega) seed hbank []
  · exact bankWindowExactStart ring seed

theorem bankCountInvNext {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hr : BankCountInv ring r) :
    BankCountInv ring (renewalBankNext ring r e) := by
  rcases hr with ⟨seed, pre, rfl, hreceipt, hwindow⟩
  refine ⟨seed, pre ++ [e], ?_, ?_, ?_⟩
  · simp only [rbRunAppend, rbRun]
  · simpa only [rbRunAppend, rbRun] using
      (rbReceiptInvBankWordOfInv ring (by omega) seed hbank
        (pre ++ [e]))
  · exact bankWindowExactStep ring hn hbank seed pre e hwindow

theorem bankCountInvOfCausal {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n)
    (hr : RenewalBankCausalReference ring r) :
    BankCountInv ring r := by
  induction hr with
  | initial seed =>
      exact bankCountInvStart ring hn hbank seed
  | step r e hprev ih =>
      exact bankCountInvNext ring hn hbank r e ih

theorem eligibleTokenNeEmpty {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n) (j : Nat)
    (hj : EligibleAt ring r root j) :
    (r.1 (Counter.site ring root j)).tok ≠ .E := by
  intro he
  rcases hj.resetToken with ht | ht
  · rw [ht] at he
    cases he
  · rw [ht] at he
    cases he

theorem eligibleDepthUnique {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n) (j k : Nat)
    (hj : EligibleAt ring r root j)
    (hk : EligibleAt ring r root k) : j = k := by
  have hnot : ¬ j < k := by
    intro hlt
    exact eligibleTokenNeEmpty ring r root j hj
      (hk.emptyPrefix j hj.positive hlt)
  have hnot' : ¬ k < j := by
    intro hlt
    exact eligibleTokenNeEmpty ring r root k hk
      (hj.emptyPrefix k hk.positive hlt)
  omega


theorem bankSlotInvEligible {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (hs : BankSlotInv ring r)
    (root : Fin n) (hrole : (r.1 root).pack.val = 0)
    (hmode : (r.1 root).mode = .RWAIT)
    (hwait : (r.2.sites root).controller = .waiting []) :
    ∃ j : Nat, EligibleAt ring r root j := by
  obtain ⟨j, hj⟩ := hs.generated root hrole hmode hwait
  exact ⟨j, hj.toEligibleAt⟩

theorem bankSlotDepthUnique {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n) (j k : Nat)
    (hj : BankSlotAt ring r root j)
    (hk : BankSlotAt ring r root k) : j = k := by
  exact eligibleDepthUnique ring r root j k
    hj.toEligibleAt hk.toEligibleAt

theorem bankCountRootCreditEq {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n) (j : Nat)
    (hj : EligibleAt ring r root j) :
    bankCountRootCredit ring r root =
      bankCountCredit n j (r.1 (Counter.site ring root j)).tok := by
  classical
  have hex : ∃ k : Nat, EligibleAt ring r root k := ⟨j, hj⟩
  unfold bankCountRootCredit
  rw [dif_pos hex]
  have hchoose : Classical.choose hex = j :=
    eligibleDepthUnique ring r root (Classical.choose hex) j
      (Classical.choose_spec hex) hj
  rw [hchoose]

theorem bankCountSlotOutCredit {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n) (j : Nat)
    (hj : BankSlotAt ring r root j)
    (ht : (r.1 (Counter.site ring root j)).tok = .RR) :
    bankCountRootCredit ring r root = j - bankCountHalf n := by
  rw [bankCountRootCreditEq ring r root j hj.toEligibleAt]
  simp [bankCountCredit, ht]

theorem bankCountSlotReturnCredit {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n) (j : Nat)
    (hj : BankSlotAt ring r root j)
    (ht : (r.1 (Counter.site ring root j)).tok = .RL) :
    bankCountRootCredit ring r root =
      bankCountWidth n - bankCountHalf n := by
  rw [bankCountRootCreditEq ring r root j hj.toEligibleAt]
  simp [bankCountCredit, ht]

theorem bankSlotFirstTokenDepth {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n) (j : Nat)
    (hj : BankSlotAt ring r root j)
    (ht : (r.1 (ring.rightNeighbor root)).tok ≠ .E) :
    j = 1 := by
  have hp := hj.toEligibleAt.positive
  by_cases heq : j = 1
  · exact heq
  · have hlt : 1 < j := by omega
    have hE := hj.toEligibleAt.emptyPrefix 1 (by omega) hlt
    change (r.1 (ring.rightNeighbor root)).tok = .E at hE
    exact False.elim (ht hE)

theorem bankCountNomIff {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (e : Fin n) :
    bankCountNom ring r e = true ↔
      ∃ (root : Fin n) (j : Nat),
        EligibleAt ring r root j ∧ bankCountHalf n ≤ j ∧
        j < bankCountWidth n ∧
        (r.1 (Counter.site ring root j)).tok = .RR ∧
        e = Counter.site ring root j := by
  classical
  simp [bankCountNom]

theorem bankCountCreditLe (n j : Nat) (tok : BTok)
    (hj : j ≤ bankCountWidth n) :
    bankCountCredit n j tok ≤ bankCountWidth n - bankCountHalf n := by
  unfold bankCountCredit
  split <;> omega


theorem bankCountHalfPositive (n : Nat) :
    1 ≤ bankCountHalf n := by
  change 1 ≤ ((compileAdvice (ceilLogTwo n)).s + 11) / 2
  omega

theorem bankCountLaunchCredit (n : Nat) :
    bankCountCredit n 1 .RR = 0 := by
  have hh := bankCountHalfPositive n
  have ht : BTok.RR ≠ BTok.RL := by decide
  simp only [bankCountCredit, if_neg ht]
  omega

/-- Pure credit arithmetic for an actual outward move. A selected
nomination whose row only repairs PACK need not make such a move. -/
theorem bankCountAdvanceCredit (n j : Nat) :
    bankCountCredit n (j + 1) .RR =
      bankCountCredit n j .RR +
        (if bankCountHalf n ≤ j then 1 else 0) := by
  have ht : BTok.RR ≠ BTok.RL := by decide
  simp only [bankCountCredit, if_neg ht]
  split <;> omega

theorem bankCountBounceCredit (n : Nat) :
    bankCountCredit n (bankCountWidth n) .RR =
      bankCountCredit n (bankCountWidth n - 1) .RL := by
  have ht : BTok.RR ≠ BTok.RL := by decide
  simp [bankCountCredit, ht]

theorem bankCountRootCreditLe {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root : Fin n) :
    bankCountRootCredit ring r root ≤
      bankCountWidth n - bankCountHalf n := by
  classical
  unfold bankCountRootCredit
  split
  · rename_i hex
    exact bankCountCreditLe n (Classical.choose hex) _
      (Classical.choose_spec hex).leWidth
  · exact Nat.zero_le _

theorem bankCountPsiLe {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) :
    bankCountPsi ring r ≤
      (bankCountWidth n - bankCountHalf n) * n := by
  have hs := ofFn_sum_le
    (fun root : Fin n => bankCountRootCredit ring r root)
    (fun _ : Fin n => bankCountWidth n - bankCountHalf n)
    (fun root => bankCountRootCreditLe ring r root)
  rw [ofFn_sum_const] at hs
  simpa only [bankCountPsi, Nat.mul_comm] using hs

theorem bankCountInitialWorkerNotPending {n : Nat}
    (C : HeadlineConfiguration n) (i : Fin n)
    (rho : RenewalBankReceipt n) :
    (renewalBankInitialSite C i).worker ≠ .pending rho := by
  by_cases ht : (C i).tok = .E <;>
    simp [renewalBankInitialSite, ht]


theorem bankSlotInvStart {n : Nat} (ring : DirectedRing n)
    (seed : RootedSeed ring) :
    BankSlotInv ring (renewalBankStart ring seed) := by
  constructor
  · intro root hrole hmode hwait
    have hwait' :
        (renewalBankInitialSite seed.val root).controller =
          .waiting [] := hwait
    change (seed.val root).pack.val = 0 at hrole
    change (seed.val root).mode = .RWAIT at hmode
    simp [renewalBankInitialSite, hrole, hmode] at hwait'
  · intro root inheritedAt _ _ _ i rho _
    exact bankCountInitialWorkerNotPending seed.val i rho

theorem bankCountNoInitialEligible {n : Nat} (ring : DirectedRing n)
    (seed : RootedSeed ring) (root : Fin n) (j : Nat) :
    ¬ EligibleAt ring (renewalBankStart ring seed) root j := by
  intro hj
  obtain ⟨rho, hw, hroot⟩ := hj.pending
  exact bankCountInitialWorkerNotPending seed.val
    (Counter.site ring root j) rho hw

theorem bankCountRootCreditStart {n : Nat} (ring : DirectedRing n)
    (seed : RootedSeed ring) (root : Fin n) :
    bankCountRootCredit ring (renewalBankStart ring seed) root = 0 := by
  classical
  have hnone : ¬ ∃ j : Nat,
      EligibleAt ring (renewalBankStart ring seed) root j := by
    rintro ⟨j, hj⟩
    exact bankCountNoInitialEligible ring seed root j hj
  simp [bankCountRootCredit, hnone]

theorem bankCountPsiStart {n : Nat} (ring : DirectedRing n)
    (seed : RootedSeed ring) :
    bankCountPsi ring (renewalBankStart ring seed) = 0 := by
  have hs := ofFn_sum_eq
    (fun root : Fin n =>
      bankCountRootCredit ring (renewalBankStart ring seed) root)
    (fun _ : Fin n => 0)
    (fun root => bankCountRootCreditStart ring seed root)
  rw [ofFn_sum_const] at hs
  simpa only [bankCountPsi, Nat.mul_zero] using hs

/-- Literal correction: the RL row can overwrite a nonempty source.
This checks a pair calculation, not a reached-reference counterexample. -/
theorem bankPairReturnOverwritesCarry :
    let x : BankCell :=
      { role := 1, mode := .RESET, bit := true,
        tok := .IR, lease := 0, grant := false }
    let y : BankCell :=
      { role := 2, mode := .RESET, bit := true,
        tok := .RL, lease := 0, grant := false }
    bankPair x y 2 18 (fun _ => false) =
      ({ x with bit := false, tok := .RL },
       { y with tok := .E }) := by
  decide

/-- Clockwise one-step translation is injective. -/
theorem bankCountRightInjective {n : Nat}
    (ring : DirectedRing n) :
    Function.Injective ring.rightNeighbor := by
  intro a b hab
  apply Fin.ext
  have hv := congrArg Fin.val hab
  change (a.val + 1) % n = (b.val + 1) % n at hv
  have hai := a.isLt
  have hbi := b.isLt
  by_cases ha : a.val + 1 < n
  · rw [Nat.mod_eq_of_lt ha] at hv
    by_cases hb : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb] at hv
      omega
    · have hbeq : b.val + 1 = n := by omega
      rw [hbeq, Nat.mod_self] at hv
      omega
  · have haeq : a.val + 1 = n := by omega
    rw [haeq, Nat.mod_self] at hv
    by_cases hb : b.val + 1 < n
    · rw [Nat.mod_eq_of_lt hb] at hv
      omega
    · have hbeq : b.val + 1 = n := by omega
      omega

theorem bankCountSiteRootInjective {n : Nat}
    (ring : DirectedRing n) (k : Nat) :
    Function.Injective (fun root : Fin n =>
      Counter.site ring root k) := by
  induction k with
  | zero =>
      intro a b hab
      exact hab
  | succ k ih =>
      intro a b hab
      apply ih
      have hs :
          ring.rightNeighbor (Counter.site ring a k) =
            ring.rightNeighbor (Counter.site ring b k) := hab
      exact bankCountRightInjective ring hs


/-- The receipt ledger identifies the owner at every labelled depth. -/
theorem bankCountPendingOwnRoot {n : Nat} (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n)
    (hi : ReceiptInv ring seed pre r)
    (root : Fin n) (j : Nat) (rho : RenewalBankReceipt n)
    (hrole : (r.1 (Counter.site ring root j)).pack.val = j)
    (hworker :
      (r.2.sites (Counter.site ring root j)).worker = .pending rho) :
    rho.root = root := by
  obtain ⟨_, _, k, _, _, hsite, hpack, _⟩ :=
    hi.pending (Counter.site ring root j) rho hworker
  have hkj : k = j := hpack.symm.trans hrole
  rw [hkj] at hsite
  exact (bankCountSiteRootInjective ring j hsite).symm

theorem bankCountEmptyNotPending {n : Nat} (ring : DirectedRing n)
    (seed : RootedSeed ring) (pre : List (Fin n))
    (r : RenewalBankReference n)
    (hi : ReceiptInv ring seed pre r)
    (i : Fin n) (ht : (r.1 i).tok = .E)
    (rho : RenewalBankReceipt n) :
    (r.2.sites i).worker ≠ .pending rho := by
  intro hw
  obtain ⟨_, _, _, _, _, _, _, hr | hr⟩ :=
    hi.pending i rho hw
  · rw [ht] at hr
    cases hr
  · rw [ht] at hr
    cases hr


/-- Whole-block returning cleanliness excludes every other pending
carrier owned by this root, including receipts from earlier slots. -/
theorem bankSlotReturnPendingSite {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (pre : List (Fin n)) (r : RenewalBankReference n)
    (hi : ReceiptInv ring seed pre r)
    (root : Fin n) (j : Nat) (hs : BankSlotAt ring r root j)
    (ht : (r.1 (Counter.site ring root j)).tok = .RL)
    (i : Fin n) (rho : RenewalBankReceipt n)
    (hown : rho.root = root)
    (hw : (r.2.sites i).worker = .pending rho) :
    i = Counter.site ring root j := by
  have hclean : ∀ k : Nat, 1 ≤ k → k ≤ bankCountWidth n → k ≠ j →
      (r.1 (Counter.site ring root k)).tok = .E := by
    rcases hs.phase with ⟨hrr, _⟩ | ⟨_, _, _, hE⟩
    · rw [ht] at hrr
      cases hrr
    · exact hE
  obtain ⟨_, _, k, hk, hkb, hsite, _, htok⟩ := hi.pending i rho hw
  have hsite' : i = Counter.site ring root k := by
    simpa only [hown] using hsite
  by_cases hkj : k = j
  · simpa only [hkj] using hsite'
  · have he : (r.1 i).tok = .E := by
      rw [hsite']
      exact hclean k hk hkb hkj
    rcases htok with hrr | hrl
    · rw [he] at hrr
      cases hrr
    · rw [he] at hrl
      cases hrl

/-- Include the root itself: each nominee is charged h+1 sites. -/
def bankCountPrefixSites {n : Nat}
    (ring : DirectedRing n) (h : Nat) (root : Fin n) :
    List (Fin n) :=
  (List.finRange (h + 1)).map
    (fun j => Counter.site ring root j.val)

theorem bankCountPrefixSitesLength {n : Nat}
    (ring : DirectedRing n) (h : Nat) (root : Fin n) :
    (bankCountPrefixSites ring h root).length = h + 1 := by
  simp [bankCountPrefixSites]

theorem bankCountPrefixSitesNodup {n : Nat}
    (ring : DirectedRing n) (h : Nat) (root : Fin n)
    (role : Fin n → Nat)
    (hroles : ∀ j : Fin (h + 1),
      role (Counter.site ring root j.val) = j.val) :
    (bankCountPrefixSites ring h root).Nodup := by
  change List.Pairwise (fun x y : Fin n => x ≠ y)
    ((List.finRange (h + 1)).map
      (fun j => Counter.site ring root j.val))
  apply List.pairwise_map.mpr
  refine List.Pairwise.imp ?_ (List.nodup_finRange (h + 1))
  intro a b hab heq
  apply hab
  apply Fin.ext
  have ha := hroles a
  have hb := hroles b
  rw [heq] at ha
  exact ha.symm.trans hb

/-- A generic finite packing lemma. Its hypotheses are role labels
and uniqueness per root, not the desired cardinality inequality. -/
theorem bankCountPackedPrefixesBound {n : Nat}
    (ring : DirectedRing n) (h : Nat)
    (nom : Fin n → Bool) (rootOf : Fin n → Fin n)
    (role : Fin n → Nat)
    (hroles : ∀ e : Fin n, nom e = true →
      ∀ j : Fin (h + 1),
        role (Counter.site ring (rootOf e) j.val) = j.val)
    (hroot : ∀ e f : Fin n,
      nom e = true → nom f = true →
      rootOf e = rootOf f → e = f) :
    (h + 1) * ((List.finRange n).filter nom).length ≤ n := by
  let block : Fin n → List (Fin n) :=
    fun e => bankCountPrefixSites ring h (rootOf e)
  have hblockLength : ∀ e : Fin n,
      (block e).length = h + 1 := by
    intro e
    exact bankCountPrefixSitesLength ring h (rootOf e)
  have hblockNodup : ∀ e : Fin n, nom e = true →
      (block e).Nodup := by
    intro e he
    exact bankCountPrefixSitesNodup ring h (rootOf e)
      role (hroles e he)
  have hoverlap : ∀ e f : Fin n,
      nom e = true → nom f = true →
      ∀ x : Fin n, x ∈ block e → x ∈ block f → e = f := by
    intro e f he hf x hxe hxf
    have hxe' :
        x ∈ (List.finRange (h + 1)).map
          (fun j => Counter.site ring (rootOf e) j.val) := hxe
    have hxf' :
        x ∈ (List.finRange (h + 1)).map
          (fun j => Counter.site ring (rootOf f) j.val) := hxf
    obtain ⟨i, _, hi⟩ := List.mem_map.mp hxe'
    obtain ⟨j, _, hj⟩ := List.mem_map.mp hxf'
    have hsite :
        Counter.site ring (rootOf e) i.val =
          Counter.site ring (rootOf f) j.val :=
      hi.trans hj.symm
    have hval : i.val = j.val :=
      (hroles e he i).symm.trans
        ((congrArg role hsite).trans (hroles f hf j))
    rw [← hval] at hsite
    exact hroot e f he hf
      (bankCountSiteRootInjective ring i.val hsite)
  have hflat : ∀ es : List (Fin n),
      es.Nodup →
      (∀ e, e ∈ es → nom e = true) →
      (es.flatMap block).Nodup := by
    intro es
    induction es with
    | nil =>
        intro _ _
        simp
    | cons e es ih =>
        intro hnd hmarked
        have hn := List.nodup_cons.mp hnd
        have he : nom e = true := hmarked e (by simp)
        have hrest : ∀ f, f ∈ es → nom f = true := by
          intro f hf
          exact hmarked f (List.mem_cons_of_mem e hf)
        simp only [List.flatMap_cons]
        apply List.nodup_append.mpr
        refine ⟨hblockNodup e he, ih hn.2 hrest, ?_⟩
        intro x hx y hy hxy
        obtain ⟨f, hf, hyf⟩ := List.mem_flatMap.mp hy
        have hef : e = f :=
          hoverlap e f he (hrest f hf) x hx
            (by simpa only [hxy] using hyf)
        apply hn.1
        rw [hef]
        exact hf
  have hflatLength : ∀ es : List (Fin n),
      (es.flatMap block).length = (h + 1) * es.length := by
    intro es
    induction es with
    | nil => simp
    | cons e es ih =>
        simp only [List.flatMap_cons, List.length_append,
          hblockLength, List.length_cons, ih]
        simp [Nat.mul_add, Nat.add_comm]
  let es := (List.finRange n).filter nom
  have hesNodup : es.Nodup := by
    exact List.Pairwise.filter nom (List.nodup_finRange n)
  have hesMarked : ∀ e, e ∈ es → nom e = true := by
    intro e he
    change e ∈ (List.finRange n).filter nom at he
    exact (List.mem_filter.mp he).2
  have hcharged : (es.flatMap block).Nodup :=
    hflat es hesNodup hesMarked
  have hlength : (es.flatMap block).length ≤
      (List.finRange n).length :=
    List.Nodup.length_le_of_subset hcharged (by
      intro x _
      exact List.mem_finRange x)
  have hbound : (h + 1) * es.length ≤ n := by
    simpa only [hflatLength, List.length_finRange] using hlength
  exact hbound

noncomputable def bankCountRootOfNom {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n) : Fin n := by
  classical
  exact
    if he : bankCountNom ring r e = true then
      Classical.choose ((bankCountNomIff ring r e).mp he)
    else e

theorem bankCountRootOfNomSpec {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n) (he : bankCountNom ring r e = true) :
    ∃ j : Nat,
      EligibleAt ring r (bankCountRootOfNom ring r e) j ∧
      bankCountHalf n ≤ j ∧
      j < bankCountWidth n ∧
      (r.1
        (Counter.site ring (bankCountRootOfNom ring r e) j)).tok =
          .RR ∧
      e = Counter.site ring (bankCountRootOfNom ring r e) j := by
  classical
  have hw :=
    Classical.choose_spec ((bankCountNomIff ring r e).mp he)
  simpa only [bankCountRootOfNom, dif_pos he] using hw

/-- BANK nomination packing, without any reachability premise.
Reachability is needed for charging, not for this injection. -/
theorem bankCountNomPacked {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n) :
    (bankCountHalf n + 1) *
        ((List.finRange n).filter (bankCountNom ring r)).length ≤
      n := by
  classical
  apply bankCountPackedPrefixesBound
    ring (bankCountHalf n) (bankCountNom ring r)
    (bankCountRootOfNom ring r)
    (fun i => (r.1 i).pack.val)
  · intro e he i
    obtain ⟨j, hj, hhalf, _, _, _⟩ :=
      bankCountRootOfNomSpec ring r e he
    exact hj.roles i.val (by
      have hi := i.isLt
      omega)
  · intro e f he hf hroot
    obtain ⟨j, hj, _, _, _, hsitee⟩ :=
      bankCountRootOfNomSpec ring r e he
    obtain ⟨k, hk, _, _, _, hsitef⟩ :=
      bankCountRootOfNomSpec ring r f hf
    have hk' :
        EligibleAt ring r (bankCountRootOfNom ring r e) k := by
      rw [hroot]
      exact hk
    have hjk : j = k :=
      eligibleDepthUnique ring r
        (bankCountRootOfNom ring r e) j k hj hk'
    calc
      e = Counter.site ring (bankCountRootOfNom ring r e) j :=
        hsitee
      _ = Counter.site ring (bankCountRootOfNom ring r f) k := by
        rw [hroot, hjk]
      _ = f := hsitef.symm

theorem bankCountBoolListSum {A : Type}
    (xs : List A) (p : A → Bool) :
    (xs.map (fun x => if p x then 1 else 0)).sum =
      (xs.filter p).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases hx : p x <;> simp [hx, ih] <;> omega

theorem bankCountNomSumEq {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n) :
    (List.ofFn (fun e : Fin n =>
      if bankCountNom ring r e then 1 else 0)).sum =
        ((List.finRange n).filter (bankCountNom ring r)).length := by
  have hs := bankCountBoolListSum
    (List.finRange n) (bankCountNom ring r)
  simpa only [List.finRange, List.map_ofFn, Function.comp_def]
    using hs

theorem bankCountNomPackedSum {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n) :
    (bankCountHalf n + 1) *
        (List.ofFn (fun e : Fin n =>
          if bankCountNom ring r e then 1 else 0)).sum ≤
      n := by
  rw [bankCountNomSumEq]
  exact bankCountNomPacked ring r

open Classical in
/-- Count nominated selections until Stop, including the edge
which enters Stop, exactly as originsWord counts its births. -/
noncomputable def bankCountNominatedWord {S : Type} {n : Nat}
    (next : S → Fin n → S) (Stop : S → Prop)
    (nom : S → Fin n → Bool) :
    S → List (Fin n) → Nat
  | _, [] => 0
  | x, e :: word =>
      if Stop x then 0
      else (if nom x e then 1 else 0) +
        bankCountNominatedWord next Stop nom (next x e) word

/-- A generic telescope, conditional on the displayed LOCAL drift
inequality. This theorem does not assert that BANK satisfies it. -/
theorem bankCountOriginChargeOfPotential
    {S O : Type} {n : Nat}
    (next : S → Fin n → S) (Stop : S → Prop)
    (spawn : S → Fin n → List O)
    (nom : S → Fin n → Bool)
    (Inv : S → Prop) (potential : S → Nat) (weight : Nat)
    (hnext : ∀ x e, Inv x → Inv (next x e))
    (hstep : ∀ x e, Inv x → ¬ Stop x →
      potential (next x e) + weight * (spawn x e).length ≤
        potential x + (if nom x e then 1 else 0)) :
    ∀ (word : List (Fin n)) (x : S), Inv x →
      weight * Prob.originsWord next Stop spawn x word ≤
        potential x +
          bankCountNominatedWord next Stop nom x word := by
  classical
  intro word
  induction word with
  | nil =>
      intro x hx
      simp [Prob.originsWord, bankCountNominatedWord]
  | cons e word ih =>
      intro x hx
      by_cases hs : Stop x
      · simp [Prob.originsWord, bankCountNominatedWord, hs]
      · have ht := ih (next x e) (hnext x e hx)
        have hp := hstep x e hx hs
        rw [Prob.originsWord, if_neg hs,
          bankCountNominatedWord, if_neg hs, Nat.mul_add]
        omega

theorem bankCountOriginChargeWithReserve
    {S O : Type} {n : Nat}
    (next : S → Fin n → S) (Stop : S → Prop)
    (spawn : S → Fin n → List O)
    (nom : S → Fin n → Bool)
    (Inv : S → Prop) (potential : S → Nat) (weight : Nat)
    (hnext : ∀ x e, Inv x → Inv (next x e))
    (hstep : ∀ x e, Inv x → ¬ Stop x →
      potential (next x e) + weight * (spawn x e).length ≤
        potential x + (if nom x e then 1 else 0))
    (hcap : ∀ x, Inv x → potential x ≤ weight * n)
    (word : List (Fin n)) (x : S) (hx : Inv x) :
    weight * Prob.originsWord next Stop spawn x word ≤
      weight * n + bankCountNominatedWord next Stop nom x word := by
  exact Nat.le_trans
    (bankCountOriginChargeOfPotential next Stop spawn nom
      Inv potential weight hnext hstep word x hx)
    (Nat.add_le_add_right (hcap x hx)
      (bankCountNominatedWord next Stop nom x word))


/-- Propagate the conjunction along an actual word, conditional on
the exact slot-preservation theorem that remains to be proved. -/
theorem bankCountInvRunOfSlotNext {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hslotnext : ∀ (r : RenewalBankReference n) (e : Fin n),
      BankCountInv ring r ∧ BankSlotInv ring r →
        BankSlotInv ring (renewalBankNext ring r e))
    (word : List (Fin n)) (r : RenewalBankReference n)
    (hr : BankCountInv ring r ∧ BankSlotInv ring r) :
    BankCountInv ring (rbRun ring r word) ∧
      BankSlotInv ring (rbRun ring r word) := by
  induction word generalizing r with
  | nil => exact hr
  | cons e word ih =>
      exact ih (renewalBankNext ring r e)
        ⟨bankCountInvNext ring hn hbank r e hr.1,
          hslotnext r e hr⟩

/-- The run witness in BankCountInv supplies the initial slot state;
only the displayed slot-preservation premise is still conditional. -/
theorem bankSlotInvOfCountInvOfNext {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hslotnext : ∀ (r : RenewalBankReference n) (e : Fin n),
      BankCountInv ring r ∧ BankSlotInv ring r →
        BankSlotInv ring (renewalBankNext ring r e))
    (r : RenewalBankReference n) (hr : BankCountInv ring r) :
    BankSlotInv ring r := by
  rcases hr with ⟨seed, word, heq, _, _⟩
  rw [heq]
  exact (bankCountInvRunOfSlotNext ring hn hbank hslotnext word
    (renewalBankStart ring seed)
    ⟨bankCountInvStart ring hn hbank seed,
      bankSlotInvStart ring seed⟩).2

/-- The requested local drift under BankCountInv AND BankSlotInv.
This definition installs no proof of the drift inequality. -/
def BankCountStepBound {n : Nat} (ring : DirectedRing n) : Prop :=
  ∀ (r : RenewalBankReference n) (e : Fin n),
    BankCountInv ring r ∧ BankSlotInv ring r →
      bankCountPsi ring (renewalBankNext ring r e) +
          (bankCountWidth n - bankCountHalf n) *
            (renewalBankSpawn ring r e).length ≤
        bankCountPsi ring r +
          (if bankCountNom ring r e then 1 else 0)

/-- Conditional pathwise reserve bound. The new slot-preservation
premise is explicit because BankCountStepBound now has the requested
conjunctive antecedent. Stop is arbitrary. -/
theorem bankCountWordChargeOfStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hslotnext : ∀ (r : RenewalBankReference n) (e : Fin n),
      BankCountInv ring r ∧ BankSlotInv ring r →
        BankSlotInv ring (renewalBankNext ring r e))
    (hstep : BankCountStepBound ring)
    (Stop : RenewalBankReference n → Prop)
    (r : RenewalBankReference n) (hr : BankCountInv ring r)
    (word : List (Fin n)) :
    (bankCountWidth n - bankCountHalf n) *
        Prob.originsWord (renewalBankNext ring) Stop
          (renewalBankSpawn ring) r word ≤
      (bankCountWidth n - bankCountHalf n) * n +
        bankCountNominatedWord (renewalBankNext ring) Stop
          (bankCountNom ring) r word := by
  exact bankCountOriginChargeWithReserve
    (renewalBankNext ring) Stop (renewalBankSpawn ring)
    (bankCountNom ring)
    (fun x => BankCountInv ring x ∧ BankSlotInv ring x)
    (bankCountPsi ring) (bankCountWidth n - bankCountHalf n)
    (fun x e hx =>
      ⟨bankCountInvNext ring hn hbank x e hx.1,
        hslotnext x e hx⟩)
    (fun x e hx _ => hstep x e hx)
    (fun x _ => bankCountPsiLe ring x)
    word r
    ⟨hr, bankSlotInvOfCountInvOfNext
      ring hn hbank hslotnext r hr⟩

/-- At a fresh observer start the reserve is zero, still conditional
on the same slot-preservation and local-drift premises. -/
theorem bankCountStartWordChargeOfStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hslotnext : ∀ (r : RenewalBankReference n) (e : Fin n),
      BankCountInv ring r ∧ BankSlotInv ring r →
        BankSlotInv ring (renewalBankNext ring r e))
    (hstep : BankCountStepBound ring)
    (Stop : RenewalBankReference n → Prop)
    (seed : RootedSeed ring) (word : List (Fin n)) :
    (bankCountWidth n - bankCountHalf n) *
        Prob.originsWord (renewalBankNext ring) Stop
          (renewalBankSpawn ring) (renewalBankStart ring seed) word ≤
      bankCountNominatedWord (renewalBankNext ring) Stop
        (bankCountNom ring) (renewalBankStart ring seed) word := by
  have ht := bankCountOriginChargeOfPotential
    (renewalBankNext ring) Stop (renewalBankSpawn ring)
    (bankCountNom ring)
    (fun x => BankCountInv ring x ∧ BankSlotInv ring x)
    (bankCountPsi ring) (bankCountWidth n - bankCountHalf n)
    (fun x e hx =>
      ⟨bankCountInvNext ring hn hbank x e hx.1,
        hslotnext x e hx⟩)
    (fun x e hx _ => hstep x e hx)
    word (renewalBankStart ring seed)
    ⟨bankCountInvStart ring hn hbank seed,
      bankSlotInvStart ring seed⟩
  simpa only [bankCountPsiStart, Nat.zero_add] using ht

/-- Conditional charge on the exact valid-subtype reference and its
clean-target stop. No substitution of the stop is made. -/
theorem bankCountCleanReferenceWordChargeOfStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hslotnext : ∀ (r : RenewalBankReference n) (e : Fin n),
      BankCountInv ring r ∧ BankSlotInv ring r →
        BankSlotInv ring (renewalBankNext ring r e))
    (hstep : BankCountStepBound ring)
    (r : (bankCleanRootedReferenceData ring hbank).Reference)
    (hr : BankCountInv ring r.val) (word : List (Fin n)) :
    (bankCountWidth n - bankCountHalf n) *
        Prob.originsWord
          (bankCleanRootedReferenceData ring hbank).referenceNext
          (bankCleanRootedReferenceData ring hbank).referenceStop
          (bankCleanRootedReferenceData ring hbank).spawn r word ≤
      (bankCountWidth n - bankCountHalf n) * n +
        bankCountNominatedWord
          (bankCleanRootedReferenceData ring hbank).referenceNext
          (bankCleanRootedReferenceData ring hbank).referenceStop
          (fun x e => bankCountNom ring x.val e) r word := by
  exact bankCountOriginChargeWithReserve
    (bankCleanRootedReferenceData ring hbank).referenceNext
    (bankCleanRootedReferenceData ring hbank).referenceStop
    (bankCleanRootedReferenceData ring hbank).spawn
    (fun x e => bankCountNom ring x.val e)
    (fun x => BankCountInv ring x.val ∧ BankSlotInv ring x.val)
    (fun x => bankCountPsi ring x.val)
    (bankCountWidth n - bankCountHalf n)
    (fun x e hx =>
      ⟨bankCountInvNext ring hn hbank x.val e hx.1,
        hslotnext x.val e hx⟩)
    (fun x e hx _ => hstep x.val e hx)
    (fun x _ => bankCountPsiLe ring x.val)
    word r
    ⟨hr, bankSlotInvOfCountInvOfNext
      ring hn hbank hslotnext r.val hr⟩


/-- The closed window invariant already gives a generated-slot
EligibleAt witness whenever the root is grant-free. Both complete
and incomplete PACK prefixes are covered. This is not BankSlotInv:
it does not prove the strict returning depth or grant-true cases. -/
theorem bankCountGrantFreeGeneratedEligible {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (hr : BankCountInv ring r)
    (root : Fin n) (hx : (r.1 root).pack.val = 0)
    (hg : (r.1 root).grant = false)
    (hm : (r.1 root).mode = .RWAIT)
    (hctl : (r.2.sites root).controller = .waiting []) :
    ∃ j : Nat, EligibleAt ring r root j := by
  rcases hr with ⟨seed, pre, _, hi, hJ⟩
  have assemble (j : Fin (bankCountWidth n))
      (rho : RenewalBankReceipt n)
      (hw : (r.2.sites (Counter.site ring root (j.val + 1))).worker =
        .pending rho)
      (ht : (r.1 (Counter.site ring root (j.val + 1))).tok = .RR ∨
        (r.1 (Counter.site ring root (j.val + 1))).tok = .RL)
      (hroles : ∀ k : Nat, k ≤ j.val + 1 →
        (r.1 (Counter.site ring root k)).pack.val = k)
      (hE : ∀ k : Fin (bankCountWidth n), k.val < j.val →
        (r.1 (Counter.site ring root (k.val + 1))).tok = .E) :
      EligibleAt ring r root (j.val + 1) := by
    refine {
      rootRole := hx
      rootMode := hm
      currentWait := hctl
      positive := by omega
      leWidth := by have hj := j.isLt; omega
      roles := hroles
      emptyPrefix := ?_
      pending := ⟨rho, hw, ?_⟩
      resetToken := ht }
    · intro k hk hkj
      have hkb : k - 1 < bankCountWidth n := by
        have hj := j.isLt
        omega
      have hkfront : k - 1 < j.val := by omega
      have hh := hE ⟨k - 1, hkb⟩ hkfront
      change (r.1 (Counter.site ring root (k - 1 + 1))).tok = .E at hh
      have hidx : k - 1 + 1 = k := by omega
      simpa only [hidx] using hh
    · exact bankCountPendingOwnRoot ring seed pre r hi root
        (j.val + 1) rho (hroles _ (Nat.le_refl _)) hw
  by_cases hc : Counter.Complete ring r.1 root
  · obtain ⟨j, rho, hw, ht, _, hE, _⟩ :=
      hJ.resetWait root ⟨hc, hg⟩ hm hctl
    refine ⟨j.val + 1, assemble j rho hw ht ?_ hE⟩
    intro k hk
    apply hc k
    have hj := j.isLt
    omega
  · obtain ⟨limit, hproto⟩ :=
      bankWindowOverlapSourceActiveIncompleteProto ring r root hx hc
    obtain ⟨j, hjle, rho, hw, ht, _, hE⟩ :=
      (hJ.proto root limit hproto).2.2.1 ⟨hm, hctl⟩
    refine ⟨j.val + 1, assemble j rho hw (Or.inl ht) ?_ hE⟩
    intro k hk
    exact hproto.2.1 k (by omega)

private theorem bankCountReturnRowFields
    (x y : BankCell) (postRole b : Nat)
    (hrow : Counter.resetRootRow x y postRole b =
      .resetReturn) :
    x.role = 0 ∧ x.grant = false ∧
    postRole = y.role ∧ postRole = 1 ∧
    x.mode = .RWAIT ∧ y.tok = .RL := by
  have hroot : x.role = 0 := by
    by_cases hx : x.role = 0
    · exact hx
    · have hh : Counter.resetRootRow x y postRole b =
          .notRoot := by
        simp [Counter.resetRootRow, hx]
      rw [hh] at hrow
      cases hrow
  have hgrant : x.grant = false := by
    cases hg : x.grant with
    | false => rfl
    | true =>
        have hh : Counter.resetRootRow x y postRole b =
            .grantExit := by
          simp [Counter.resetRootRow, hroot, hg]
        rw [hh] at hrow
        cases hrow
  have hsame : postRole = y.role := by
    by_cases hs : postRole = y.role
    · exact hs
    · have hh : Counter.resetRootRow x y postRole b =
          .changedRole := by
        simp [Counter.resetRootRow, hroot, hgrant, hs]
      rw [hh] at hrow
      cases hrow
  have hone : postRole = 1 := by
    by_cases hs : postRole = 1
    · exact hs
    · have hnotY : y.role ≠ 1 := by
        intro hy
        exact hs (hsame.trans hy)
      have hh : Counter.resetRootRow x y postRole b =
          .wrongNeighbor := by
        simp [Counter.resetRootRow, hroot, hgrant,
          hsame, hnotY]
      rw [hh] at hrow
      cases hrow
  have hdestRole : y.role = 1 := hsame.symm.trans hone
  have hother : y.tok = .RL ∧ x.mode = .RWAIT := by
    cases ht : y.tok <;> cases hm : x.mode <;>
      simp [Counter.resetRootRow, hroot, hgrant,
        hsame, hdestRole, ht, hm, isRetTok] at hrow ⊢
    all_goals (split at hrow <;> cases hrow)
  exact ⟨hroot, hgrant, hsame, hone,
    hother.2, hother.1⟩


/-- U2: accepted pending RL is the depth-one eligible frontier.
The proof uses the already-closed BANK window invariant, not slot
preservation or the missing drift theorem. -/
theorem bankCountBirthEligible {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (o : RenewalBankOrigin n) (hr : BankCountInv ring r)
    (hb : renewalBankBirth ring r.1 r.2 e = some o) :
    EligibleAt ring r e 1 ∧
      (r.1 (Counter.site ring e 1)).tok = .RL ∧
      (r.2.sites (Counter.site ring e 1)).worker =
        .pending o.receipt ∧
      o.receipt.root = e ∧
      bankCountRootCredit ring r e =
        bankCountWidth n - bankCountHalf n := by
  rcases hr with ⟨seed, pre, _, hi, hJ⟩
  have hrow : rbTrackedRootRow ring r e = .resetReturn := by
    by_cases h : rbTrackedRootRow ring r e = .resetReturn
    · exact h
    · have hz := rbTrackedRootNonreturnNoBirth ring r e h
      rw [hz] at hb
      cases hb
  unfold rbTrackedRootRow at hrow
  obtain ⟨hx, hg, hsame, hone, hm, ht⟩ :=
    bankCountReturnRowFields
      (bankCell (r.1 e) (r.1 e).pack.val)
      (bankCell (r.1 (ring.rightNeighbor e))
        (r.1 (ring.rightNeighbor e)).pack.val)
      (packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (bankCountWidth n))
      (bankCountWidth n) hrow
  change (r.1 e).pack.val = 0 at hx
  change (r.1 e).grant = false at hg
  change (r.1 e).mode = .RWAIT at hm
  change (r.1 (ring.rightNeighbor e)).tok = .RL at ht
  have hy : (r.1 (ring.rightNeighbor e)).pack.val = 1 :=
    hsame.symm.trans hone
  have hw := rbTrackedAcceptedPending ring r e o hb
  have hroot := rbBankPendingReceiptOwnRoot
    ring seed pre r e hi o.receipt hy hw
  have hctl : (r.2.sites e).controller = .waiting [] :=
    (bankWindowJointTaintedResponderScope ring r e hJ
      hx hy hg (Or.inl hm) (Or.inl ⟨o.receipt, hw⟩)).1
  have helig : EligibleAt ring r e 1 := by
    refine {
      rootRole := hx
      rootMode := hm
      currentWait := hctl
      positive := by omega
      leWidth := ?_
      roles := ?_
      emptyPrefix := ?_
      pending := ⟨o.receipt, hw, hroot⟩
      resetToken := Or.inr ht }
    · change 1 ≤ (compileAdvice (ceilLogTwo n)).s + 11
      omega
    · intro k hk
      have hkcases : k = 0 ∨ k = 1 := by omega
      rcases hkcases with hzero | hone
      · subst k
        exact hx
      · subst k
        exact hy
    · intro k hk hlt
      omega
  refine ⟨helig, ht, hw, hroot, ?_⟩
  rw [bankCountRootCreditEq ring r e 1 helig]
  have ht' : (r.1 (Counter.site ring e 1)).tok = .RL := ht
  simp only [bankCountCredit, ht']
  exact if_pos trivial


theorem bankCountFilterLengthCount {A : Type}
    (xs : List A) (p : A → Bool) :
    (xs.filter p).length = xs.countP p := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases hx : p x <;>
        simp [List.countP_cons, hx, ih, Nat.add_comm]

theorem bankCountNominatedWordEq {S : Type} {n : Nat}
    (next : S → Fin n → S) (Stop : S → Prop)
    (nom : S → Fin n → Bool)
    (word : List (Fin n)) (x : S) :
    bankCountNominatedWord next Stop nom x word =
      Prob.nominatedWord next Stop nom x word := by
  classical
  induction word generalizing x with
  | nil => rfl
  | cons e word ih =>
      by_cases hs : Stop x
      · simp only [bankCountNominatedWord, Prob.nominatedWord,
          if_pos hs]
      · simp only [bankCountNominatedWord, Prob.nominatedWord,
          if_neg hs, Prob.indicator, ih]

private theorem bankCountScheduleSumMono {n : Nat} (T : Nat)
    (f g : List (Fin n) → Nat)
    (h : ∀ word, f word ≤ g word) :
    Prob.scheduleSum n T f ≤ Prob.scheduleSum n T g := by
  change FixedSpanRenewalPayload.wordSum n T f ≤
    FixedSpanRenewalPayload.wordSum n T g
  rw [← FixedSpanRenewalPayload.rawWord_sum n T f,
    ← FixedSpanRenewalPayload.rawWord_sum n T g]
  exact ofFn_sum_le _ _ (fun i => h _)

private theorem bankCountScheduleSumConst {n : Nat}
    (T c : Nat) :
    Prob.scheduleSum n T (fun _ => c) = n ^ T * c := by
  change FixedSpanRenewalPayload.wordSum n T (fun _ => c) = _
  rw [← FixedSpanRenewalPayload.rawWord_sum n T (fun _ => c)]
  exact ofFn_sum_const (n ^ T) c

private theorem bankCountScheduleSumAdd {n : Nat} (T : Nat)
    (f g : List (Fin n) → Nat) :
    Prob.scheduleSum n T (fun word => f word + g word) =
      Prob.scheduleSum n T f + Prob.scheduleSum n T g := by
  change FixedSpanRenewalPayload.wordSum n T
      (fun word => f word + g word) =
    FixedSpanRenewalPayload.wordSum n T f +
      FixedSpanRenewalPayload.wordSum n T g
  rw [← FixedSpanRenewalPayload.rawWord_sum n T
        (fun word => f word + g word),
    ← FixedSpanRenewalPayload.rawWord_sum n T f,
    ← FixedSpanRenewalPayload.rawWord_sum n T g]
  exact ofFn_sum_add _ _

private theorem bankCountScheduleSumMul {n : Nat}
    (T c : Nat) (f : List (Fin n) → Nat) :
    Prob.scheduleSum n T (fun word => c * f word) =
      c * Prob.scheduleSum n T f := by
  change FixedSpanRenewalPayload.wordSum n T
      (fun word => c * f word) =
    c * FixedSpanRenewalPayload.wordSum n T f
  rw [← FixedSpanRenewalPayload.rawWord_sum n T
        (fun word => c * f word),
    ← FixedSpanRenewalPayload.rawWord_sum n T f,
    ofFn_sum_mul_left]

/-- Generic finite-horizon composition. The wordwise charge is an
explicit premise. Packing alone discharges the nomination average. -/
theorem bankCountOriginNumeratorChargeOfWordCharge
    {S O : Type} {n : Nat}
    (next : S → Fin n → S) (Stop : S → Prop)
    (spawn : S → Fin n → List O)
    (nom : S → Fin n → Bool)
    (weight m reserve : Nat)
    (hcard : ∀ x : S,
      m * ((List.finRange n).countP (fun e => nom x e)) ≤ n)
    (x : S)
    (hword : ∀ word : List (Fin n),
      weight * Prob.originsWord next Stop spawn x word ≤
        weight * reserve +
          bankCountNominatedWord next Stop nom x word)
    (T : Nat) :
    (weight * m) *
        Prob.originsNumerator next Stop spawn x T ≤
      (weight * m) * (n ^ T * reserve) +
        costNumerator next Stop x T := by
  classical
  have hnom :=
    Prob.nominated_numerator_le next Stop nom
      (fun _ : S => True) m
      (fun _ _ _ _ => True.intro)
      (fun y _ _ => hcard y)
      x True.intro T
  have heq :
      bankCountNominatedWord next Stop nom x =
        Prob.nominatedWord next Stop nom x := by
    funext word
    exact bankCountNominatedWordEq next Stop nom word x
  rw [← heq] at hnom
  have hsum := bankCountScheduleSumMono T
    (fun word => weight * Prob.originsWord next Stop spawn x word)
    (fun word => weight * reserve +
      bankCountNominatedWord next Stop nom x word)
    hword
  rw [bankCountScheduleSumMul, bankCountScheduleSumAdd,
    bankCountScheduleSumConst] at hsum
  change
    weight * Prob.originsNumerator next Stop spawn x T ≤
      n ^ T * (weight * reserve) +
        Prob.scheduleSum n T
          (bankCountNominatedWord next Stop nom x)
    at hsum
  calc
    (weight * m) *
        Prob.originsNumerator next Stop spawn x T =
      m * (weight * Prob.originsNumerator next Stop spawn x T) := by
        ac_rfl
    _ ≤ m * (n ^ T * (weight * reserve) +
          Prob.scheduleSum n T
            (bankCountNominatedWord next Stop nom x)) :=
      Nat.mul_le_mul_left m hsum
    _ = (weight * m) * (n ^ T * reserve) +
          m * Prob.scheduleSum n T
            (bankCountNominatedWord next Stop nom x) := by
      rw [Nat.mul_add]
      ac_rfl
    _ ≤ (weight * m) * (n ^ T * reserve) +
          costNumerator next Stop x T :=
      Nat.add_le_add_left hnom _

/-- Exact clean-reference sharp charge, conditional only on the
displayed clean-reference wordwise charge. -/
theorem bankCleanReferenceOriginChargeSharpOfWordCharge {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hword :
      ∀ (seed : RootedSeed ring) (word : List (Fin n)),
        (bankCountWidth n - bankCountHalf n) *
            Prob.originsWord
              (bankCleanRootedReferenceData ring hbank).referenceNext
              (bankCleanRootedReferenceData ring hbank).referenceStop
              (bankCleanRootedReferenceData ring hbank).spawn
              ((bankCleanRootedReferenceData ring hbank).referenceStart seed)
              word ≤
          (bankCountWidth n - bankCountHalf n) * n +
            bankCountNominatedWord
              (bankCleanRootedReferenceData ring hbank).referenceNext
              (bankCleanRootedReferenceData ring hbank).referenceStop
              (fun x e => bankCountNom ring x.val e)
              ((bankCleanRootedReferenceData ring hbank).referenceStart seed)
              word) :
    let b := bankCountWidth n
    let h := bankCountHalf n
    let D := bankCleanRootedReferenceData ring hbank
    ∀ seed : RootedSeed ring,
      ¬ headlineGeneratedTarget ring seed.val → ∀ T : Nat,
        ((b - h) * (h + 1)) *
            Prob.originsNumerator D.referenceNext D.referenceStop
              D.spawn (D.referenceStart seed) T ≤
          ((b - h) * (h + 1)) * (n ^ T * n) +
            costNumerator D.referenceNext D.referenceStop
              (D.referenceStart seed) T := by
  dsimp only
  intro seed _ T
  apply bankCountOriginNumeratorChargeOfWordCharge
    (bankCleanRootedReferenceData ring hbank).referenceNext
    (bankCleanRootedReferenceData ring hbank).referenceStop
    (bankCleanRootedReferenceData ring hbank).spawn
    (fun x e => bankCountNom ring x.val e)
    (bankCountWidth n - bankCountHalf n)
    (bankCountHalf n + 1) n
  · intro x
    rw [← bankCountFilterLengthCount]
    exact bankCountNomPacked ring x.val
  · exact hword seed

/-- All averaging is discharged; only slot preservation and the
BANK-specific local potential inequality remain as hypotheses. -/
theorem bankCleanReferenceOriginChargeSharpOfStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hslotnext : ∀ (r : RenewalBankReference n) (e : Fin n),
      BankCountInv ring r ∧ BankSlotInv ring r →
        BankSlotInv ring (renewalBankNext ring r e))
    (hstep : BankCountStepBound ring) :
    let b := bankCountWidth n
    let h := bankCountHalf n
    let D := bankCleanRootedReferenceData ring hbank
    ∀ seed : RootedSeed ring,
      ¬ headlineGeneratedTarget ring seed.val → ∀ T : Nat,
        ((b - h) * (h + 1)) *
            Prob.originsNumerator D.referenceNext D.referenceStop
              D.spawn (D.referenceStart seed) T ≤
          ((b - h) * (h + 1)) * (n ^ T * n) +
            costNumerator D.referenceNext D.referenceStop
              (D.referenceStart seed) T := by
  apply bankCleanReferenceOriginChargeSharpOfWordCharge ring hbank
  intro seed word
  exact bankCountCleanReferenceWordChargeOfStep
    ring hn hbank hslotnext hstep
    ((bankCleanRootedReferenceData ring hbank).referenceStart seed)
    (bankCountInvStart ring hn hbank seed) word

/-- Explicit historical current-slot predicate, on a specified run.
The strict lower endpoint excludes pre-launch RESET and includes
every post-launch cut, including the present cut. This definition
does not claim continuous worker custody. -/
def bankCountCurrentSlot {n : Nat} (ring : DirectedRing n)
    (seed : RootedSeed ring) (word : List (Fin n))
    (root : Fin n) (rho : RenewalBankReceipt n) : Prop :=
  rho.root = root ∧
  rho.service < word.length ∧
  word[rho.service]? = some root ∧
  Counter.resetLaunchGuard
    ((rbRun ring (renewalBankStart ring seed)
      (word.take rho.service)).1 root)
    ((rbRun ring (renewalBankStart ring seed)
      (word.take rho.service)).1 (ring.rightNeighbor root)) = true ∧
  ∀ time : Nat, rho.service < time → time ≤ word.length →
    let s := rbRun ring (renewalBankStart ring seed) (word.take time)
    (s.1 root).pack.val = 0 ∧
    (s.1 root).mode = .RWAIT ∧
    (s.2.sites root).controller = .waiting []


/-- A logged receipt records an actual launch edge and prefix.
This does not assert uninterrupted survival of the resulting slot. -/
theorem bankCountLoggedLaunchSplit {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (word : List (Fin n)) (rho : RenewalBankReceipt n)
    (hmem : rho ∈ rbLaunches ring r word) :
    ∃ (before after : List (Fin n)),
      word = before ++ (rho.root :: after) ∧
      rho.service = (rbRun ring r before).2.service ∧
      Counter.resetLaunchGuard
        ((rbRun ring r before).1 rho.root)
        ((rbRun ring r before).1
          (ring.rightNeighbor rho.root)) = true := by
  induction word generalizing r with
  | nil =>
      simp [rbLaunches] at hmem
  | cons e tail ih =>
      change rho ∈
        (if Counter.resetLaunchGuard
            (r.1 e) (r.1 (ring.rightNeighbor e))
         then [{ service := r.2.service, root := e }]
         else []) ++
          rbLaunches ring (renewalBankNext ring r e) tail at hmem
      rcases List.mem_append.mp hmem with hhead | htail
      · by_cases hguard :
          Counter.resetLaunchGuard
            (r.1 e) (r.1 (ring.rightNeighbor e)) = true
        · have hrho :
              rho = { service := r.2.service, root := e } := by
            simpa [hguard] using hhead
          subst rho
          exact ⟨[], tail, rfl, rfl, hguard⟩
        · simp [hguard] at hhead
      · obtain ⟨before, after, hword, hservice, hguard⟩ :=
          ih (renewalBankNext ring r e) htail
        refine ⟨e :: before, after, ?_, hservice, hguard⟩
        simpa only [List.cons_append] using congrArg (List.cons e) hword

theorem bankCountStartLoggedLaunchSplit {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring)
    (word : List (Fin n)) (rho : RenewalBankReceipt n)
    (hmem :
      rho ∈ rbLaunches ring (renewalBankStart ring seed) word) :
    ∃ (before after : List (Fin n)),
      word = before ++ (rho.root :: after) ∧
      rho.service = before.length ∧
      Counter.resetLaunchGuard
        ((rbRun ring (renewalBankStart ring seed) before).1
          rho.root)
        ((rbRun ring (renewalBankStart ring seed) before).1
          (ring.rightNeighbor rho.root)) = true := by
  obtain ⟨before, after, hword, hservice, hguard⟩ :=
    bankCountLoggedLaunchSplit ring
      (renewalBankStart ring seed) word rho hmem
  refine ⟨before, after, hword, ?_, hguard⟩
  exact hservice.trans
    (rbReceiptStartCoreWord ring seed before).1

/-- U1's genuine-launch and strict-age part. The uninterrupted
post-launch interval of bankCountCurrentSlot is still separate. -/
theorem bankCountEligibleLaunchWitness {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (word : List (Fin n))
    (root : Fin n) (j : Nat) (rho : RenewalBankReceipt n)
    (helig :
      EligibleAt ring
        (rbRun ring (renewalBankStart ring seed) word) root j)
    (hpending :
      ((rbRun ring (renewalBankStart ring seed) word).2.sites
        (Counter.site ring root j)).worker = .pending rho) :
    rho.root = root ∧
      rho.service < word.length ∧
      ∃ (before after : List (Fin n)),
        word = before ++ (root :: after) ∧
        rho.service = before.length ∧
        Counter.resetLaunchGuard
          ((rbRun ring (renewalBankStart ring seed) before).1 root)
          ((rbRun ring (renewalBankStart ring seed) before).1
            (ring.rightNeighbor root)) = true := by
  have hi := rbReceiptInvBankWordOfInv ring
    (by omega : 2 ≤ n) seed hbank word
  obtain ⟨sigma, hsigma, hroot⟩ := helig.pending
  have hrho : rho = sigma :=
    RenewalBankWorker.pending.inj
      (hpending.symm.trans hsigma)
  have hroot' : rho.root = root := by
    rw [hrho]
    exact hroot
  have hlogged :=
    (hi.pending (Counter.site ring root j) rho hpending).1
  have hage :=
    (hi.pending (Counter.site ring root j) rho hpending).2.1
  have hageWord : rho.service < word.length := by
    simpa only [hi.clock] using hage
  obtain ⟨before, after, hword, hservice, hguard⟩ :=
    bankCountStartLoggedLaunchSplit ring seed word rho hlogged
  refine ⟨hroot', hageWord, before, after, ?_, hservice, ?_⟩
  · simpa only [hroot'] using hword
  · simpa only [hroot'] using hguard

/-
UNFINISHED U1: snapshot-to-current-slot identification.
The actual launch and strict age are proved above; uninterrupted
role-zero RWAIT with waiting [] is the remaining temporal clause.
The following is a goal signature, not an installed declaration.

theorem bankCountEligibleCurrentSlot {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (seed : RootedSeed ring) (word : List (Fin n))
    (root : Fin n) (j : Nat) (rho : RenewalBankReceipt n)
    (helig :
      EligibleAt ring
        (rbRun ring (renewalBankStart ring seed) word) root j)
    (hpending :
      ((rbRun ring (renewalBankStart ring seed) word).2.sites
        (Counter.site ring root j)).worker = .pending rho) :
    bankCountCurrentSlot ring seed word root rho
-/




/-
UNFINISHED U3: all-edge preservation of the exact proposed slot shape.
This is a goal signature, not a declaration.

theorem bankSlotInvNext {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hr : BankCountInv ring r) (hs : BankSlotInv ring r) :
    BankSlotInv ring (renewalBankNext ring r e)
-/

/-
UNFINISHED U3: the actual BANK local potential theorem.
The definition of BankCountStepBound requires the conjunction
BankCountInv ring r AND BankSlotInv ring r.
The following is a goal signature, not an installed declaration.

theorem bankCountPotentialStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankCountStepBound ring
-/

/-
UNFINISHED: unconditional pathwise charge, after bankSlotInvNext
and bankCountPotentialStep. The conditional theorem is installed above.
The following is a goal signature, not an installed declaration.

theorem bankCountWordCharge {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (hr : BankCountInv ring r)
    (word : List (Fin n)) :
    (bankCountWidth n - bankCountHalf n) *
        Prob.originsWord (renewalBankNext ring)
          (renewalBankStopAt (headlineCleanTarget ring))
          (renewalBankSpawn ring) r word ≤
      (bankCountWidth n - bankCountHalf n) * n +
        bankCountNominatedWord (renewalBankNext ring)
          (renewalBankStopAt (headlineCleanTarget ring))
          (bankCountNom ring) r word
-/

/-
UNFINISHED: requested unconditional final numerator theorem.
The averaging and numerator interface are supplied above by
bankCleanReferenceOriginChargeSharpOfStep. Only its two BANK
premises, slot preservation and local drift, are not discharged.
The following is a goal signature, not an installed declaration.

theorem bankCleanReferenceOriginChargeSharp {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    let b := bankCountWidth n
    let h := bankCountHalf n
    let D := bankCleanRootedReferenceData ring hbank
    ∀ seed : RootedSeed ring,
      ¬ headlineGeneratedTarget ring seed.val → ∀ T : Nat,
        ((b - h) * (h + 1)) *
            Prob.originsNumerator D.referenceNext D.referenceStop
              D.spawn (D.referenceStart seed) T ≤
          ((b - h) * (h + 1)) * (n ^ T * n) +
            costNumerator D.referenceNext D.referenceStop
              (D.referenceStart seed) T
-/

end L3.Prime

#print axioms L3.Prime.bankCountInvNext
#print axioms L3.Prime.bankCountNomPackedSum
#print axioms L3.Prime.bankCountPsiStart
#print axioms L3.Prime.bankCountCleanReferenceWordChargeOfStep
#print axioms L3.Prime.bankSlotInvStart
#print axioms L3.Prime.bankCountEligibleLaunchWitness
#print axioms L3.Prime.bankCountBirthEligible
#print axioms L3.Prime.bankCleanReferenceOriginChargeSharpOfStep

/-!
Q4678 append to Leader/L3/Prime/BankCount.lean at 448a73cc9.
UNCOMPILED. This append does not declare the full U3b target.

The actual birth branch is reduced to an exact global equality.
The remaining non-birth row classification is recorded at the end.
-/

namespace L3.Prime

open L3.HeadlineRenewal
open L3.HeadlineRenewalCleanBank
open L3.RenewalReferenceClock
open L3.BankWindow
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-! Credit and its finite read set. -/

theorem bankCountRootCreditZeroOfNoEligible {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (root : Fin n)
    (h : ¬ ∃ j : Nat, EligibleAt ring r root j) :
    bankCountRootCredit ring r root = 0 := by
  classical
  simp [bankCountRootCredit, h]

theorem bankCountRootCreditZeroOfRole {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (root : Fin n) (h : (r.1 root).pack.val ≠ 0) :
    bankCountRootCredit ring r root = 0 := by
  apply bankCountRootCreditZeroOfNoEligible ring r root
  rintro ⟨j, hj⟩
  exact h hj.rootRole

theorem bankCountRootCreditZeroOfWait {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (root : Fin n)
    (h : (r.2.sites root).controller ≠ .waiting []) :
    bankCountRootCredit ring r root = 0 := by
  apply bankCountRootCreditZeroOfNoEligible ring r root
  rintro ⟨j, hj⟩
  exact h hj.currentWait

/-- Only the prefix through the particular frontier is read by
an EligibleAt certificate. The global service clock is not read. -/
theorem bankCountEligiblePrefixTransport {n : Nat}
    (ring : DirectedRing n) (r s : RenewalBankReference n)
    (root : Fin n) (j : Nat) (hj : EligibleAt ring r root j)
    (heq : ∀ k : Nat, k ≤ j →
      r.1 (Counter.site ring root k) =
        s.1 (Counter.site ring root k) ∧
      r.2.sites (Counter.site ring root k) =
        s.2.sites (Counter.site ring root k)) :
    EligibleAt ring s root j := by
  have hpRoot : r.1 root = s.1 root :=
    (heq 0 (Nat.zero_le j)).1
  have hmRoot : r.2.sites root = s.2.sites root :=
    (heq 0 (Nat.zero_le j)).2
  have hpFront := (heq j (Nat.le_refl j)).1
  have hmFront := (heq j (Nat.le_refl j)).2
  refine {
    rootRole := ?_
    rootMode := ?_
    currentWait := ?_
    positive := hj.positive
    leWidth := hj.leWidth
    roles := ?_
    emptyPrefix := ?_
    pending := ?_
    resetToken := ?_ }
  · rw [← hpRoot]
    exact hj.rootRole
  · rw [← hpRoot]
    exact hj.rootMode
  · rw [← hmRoot]
    exact hj.currentWait
  · intro k hk
    rw [← (heq k hk).1]
    exact hj.roles k hk
  · intro k hk hkj
    rw [← (heq k (by omega)).1]
    exact hj.emptyPrefix k hk hkj
  · obtain ⟨rho, hw, hroot⟩ := hj.pending
    refine ⟨rho, ?_, hroot⟩
    rw [← hmFront]
    exact hw
  · rw [← hpFront]
    exact hj.resetToken

/-- Item 1: equal physical agents and ghost site records throughout
0,...,b give equal root credit. No equality of memory.service is
required, and no slot or reachability assumption is used. -/
theorem bankCountRootCreditLocal {n : Nat}
    (ring : DirectedRing n) (r s : RenewalBankReference n)
    (root : Fin n)
    (heq : ∀ k : Nat, k ≤ bankCountWidth n →
      r.1 (Counter.site ring root k) =
        s.1 (Counter.site ring root k) ∧
      r.2.sites (Counter.site ring root k) =
        s.2.sites (Counter.site ring root k)) :
    bankCountRootCredit ring r root =
      bankCountRootCredit ring s root := by
  classical
  by_cases hex : ∃ j : Nat, EligibleAt ring r root j
  · obtain ⟨j, hj⟩ := hex
    have hs : EligibleAt ring s root j :=
      bankCountEligiblePrefixTransport ring r s root j hj
        (fun k hk => heq k (Nat.le_trans hk hj.leWidth))
    calc
      bankCountRootCredit ring r root =
          bankCountCredit n j
            (r.1 (Counter.site ring root j)).tok :=
        bankCountRootCreditEq ring r root j hj
      _ = bankCountCredit n j
            (s.1 (Counter.site ring root j)).tok := by
        rw [(heq j hj.leWidth).1]
      _ = bankCountRootCredit ring s root :=
        (bankCountRootCreditEq ring s root j hs).symm
  · have hs : ¬ ∃ j : Nat, EligibleAt ring s root j := by
      rintro ⟨j, hj⟩
      apply hex
      refine ⟨j, bankCountEligiblePrefixTransport
        ring s r root j hj ?_⟩
      intro k hk
      have hf := heq k (Nat.le_trans hk hj.leWidth)
      exact ⟨hf.1.symm, hf.2.symm⟩
    rw [bankCountRootCreditZeroOfNoEligible ring r root hex,
      bankCountRootCreditZeroOfNoEligible ring s root hs]

/-- Item 2: the physical configuration and ghost SITE records are
framed off the two selected sites. The service clock still advances. -/
theorem renewalBankNextTwoSiteFrame {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e i : Fin n) (he : i ≠ e)
    (hd : i ≠ ring.rightNeighbor e) :
    (renewalBankNext ring r e).1 i = r.1 i ∧
      (renewalBankNext ring r e).2.sites i = r.2.sites i := by
  exact rbReferenceOutsideSiteFrame ring r e i he hd

theorem bankCountRootCreditOutsideWindow {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e root : Fin n)
    (hout : ∀ k : Nat, k ≤ bankCountWidth n →
      Counter.site ring root k ≠ e ∧
        Counter.site ring root k ≠ ring.rightNeighbor e) :
    bankCountRootCredit ring (renewalBankNext ring r e) root =
      bankCountRootCredit ring r root := by
  apply bankCountRootCreditLocal
    ring (renewalBankNext ring r e) r root
  intro k hk
  exact renewalBankNextTwoSiteFrame ring r e
    (Counter.site ring root k) (hout k hk).1 (hout k hk).2

/-! Labelled-prefix geometry, including the role-repair boundary. -/

/-- Intersecting certified prefixes have the same depth at their
intersection and the same root. This is not a claim that arbitrary
length-b read windows are disjoint. -/
theorem bankCountEligibleWindowsOverlap {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (root other : Fin n) (j depth k ell : Nat)
    (hj : EligibleAt ring r root j)
    (hd : EligibleAt ring r other depth)
    (hk : k ≤ j) (hl : ell ≤ depth)
    (hsite : Counter.site ring root k =
      Counter.site ring other ell) :
    root = other ∧ k = ell := by
  have hindex : k = ell := by
    calc
      k = (r.1 (Counter.site ring root k)).pack.val :=
        (hj.roles k hk).symm
      _ = (r.1 (Counter.site ring other ell)).pack.val :=
        congrArg (fun i : Fin n => (r.1 i).pack.val) hsite
      _ = ell := hd.roles ell hl
  have hroot : root = other := by
    apply bankCountSiteRootInjective ring k
    simpa only [← hindex] using hsite
  exact ⟨hroot, hindex⟩

/-- A responder at positive depth of an OLD eligible prefix cannot
undergo PACK repair: its selected predecessor already has role k-1. -/
theorem bankCountEligibleResponderRoleStable {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e root : Fin n) (j k : Nat)
    (hj : EligibleAt ring r root j)
    (hk : 1 ≤ k) (hkj : k ≤ j)
    (hsite : ring.rightNeighbor e = Counter.site ring root k) :
    packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (bankCountWidth n) =
      (r.1 (ring.rightNeighbor e)).pack.val := by
  cases k with
  | zero => omega
  | succ k =>
      have hpred : e = Counter.site ring root k := by
        apply bankCountRightInjective ring
        exact hsite
      have hx : (r.1 e).pack.val = k := by
        rw [hpred]
        exact hj.roles k (by omega)
      have hy : (r.1 (ring.rightNeighbor e)).pack.val = k + 1 := by
        rw [hsite]
        exact hj.roles (k + 1) hkj
      have hb : k < bankCountWidth n := by
        have hwidth := hj.leWidth
        omega
      rw [hx, hy]
      simp [packNext, hb]

theorem bankCountRepairAvoidsPositivePrefix {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e root : Fin n) (j : Nat)
    (hj : EligibleAt ring r root j)
    (hrepair : packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (bankCountWidth n) ≠
      (r.1 (ring.rightNeighbor e)).pack.val) :
    ∀ k : Nat, 1 ≤ k → k ≤ j →
      ring.rightNeighbor e ≠ Counter.site ring root k := by
  intro k hk hkj hsite
  exact hrepair
    (bankCountEligibleResponderRoleStable
      ring r e root j k hj hk hkj hsite)

/-- If a repaired responder lies in the credit-bearing prefix,
it must be the root, not a positive-depth interior digit. -/
theorem bankCountRepairTouchesOnlyRoot {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e root : Fin n) (j k : Nat)
    (hj : EligibleAt ring r root j) (hkj : k ≤ j)
    (hrepair : packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (bankCountWidth n) ≠
      (r.1 (ring.rightNeighbor e)).pack.val)
    (hsite : ring.rightNeighbor e = Counter.site ring root k) :
    k = 0 ∧ ring.rightNeighbor e = root := by
  have hz : k = 0 := by
    by_cases hk : k = 0
    · exact hk
    · have hpos : 1 ≤ k := by omega
      exact False.elim
        (bankCountRepairAvoidsPositivePrefix
          ring r e root j hj hrepair k hpos hkj hsite)
  refine ⟨hz, ?_⟩
  simpa only [hz, Counter.site] using hsite

/-- Actual PACK repair of an OLD role-zero responder destroys its
root credit. This uses the literal reference PACK frame. -/
theorem bankCountRepairKillsResponderCredit {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (hroot : (r.1 (ring.rightNeighbor e)).pack.val = 0)
    (hrepair : packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (bankCountWidth n) ≠
      (r.1 (ring.rightNeighbor e)).pack.val) :
    bankCountRootCredit ring (renewalBankNext ring r e)
      (ring.rightNeighbor e) = 0 := by
  have hpack :
      ((renewalBankNext ring r e).1
        (ring.rightNeighbor e)).pack.val =
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (bankCountWidth n) :=
    (rbBankReferencePairPack ring hn r e).2
  apply bankCountRootCreditZeroOfRole
    ring (renewalBankNext ring r e) (ring.rightNeighbor e)
  intro hz
  apply hrepair
  calc
    packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (bankCountWidth n) =
      ((renewalBankNext ring r e).1
        (ring.rightNeighbor e)).pack.val := hpack.symm
    _ = 0 := hz
    _ = (r.1 (ring.rightNeighbor e)).pack.val := hroot.symm

/-- The repaired-responder overlap with an OLD eligible prefix
can only end that slot, and its credit becomes zero. -/
theorem bankCountRepairKillsOverlappedCredit {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e root : Fin n) (j k : Nat)
    (hj : EligibleAt ring r root j) (hkj : k ≤ j)
    (hrepair : packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (bankCountWidth n) ≠
      (r.1 (ring.rightNeighbor e)).pack.val)
    (hsite : ring.rightNeighbor e = Counter.site ring root k) :
    bankCountRootCredit ring (renewalBankNext ring r e) root = 0 := by
  have hr := (bankCountRepairTouchesOnlyRoot
    ring r e root j k hj hkj hrepair hsite).2
  have hzero := bankCountRepairKillsResponderCredit
    ring hn r e (by rw [hr]; exact hj.rootRole) hrepair
  simpa only [hr] using hzero

/-! Aligned root-source geometry. These are actual-step results,
not hypothetical single-summand assumptions. -/

/-- A 0,1 selected pair cannot meet another eligible prefix. -/
theorem bankCountRootPairOutsidePrefix {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e root : Fin n) (j : Nat)
    (hx : (r.1 e).pack.val = 0)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 1)
    (hne : root ≠ e) (hj : EligibleAt ring r root j) :
    ∀ k : Nat, k ≤ j →
      Counter.site ring root k ≠ e ∧
        Counter.site ring root k ≠ ring.rightNeighbor e := by
  intro k hk
  constructor
  · intro hsite
    have hrole := hj.roles k hk
    rw [hsite, hx] at hrole
    have hz : k = 0 := by omega
    subst k
    exact hne hsite
  · intro hsite
    have hrole := hj.roles k hk
    rw [hsite, hy] at hrole
    have ho : k = 1 := by omega
    subst k
    have heq : ring.rightNeighbor root = ring.rightNeighbor e :=
      hsite
    exact hne (bankCountRightInjective ring heq)

/-- A foreign POST eligible prefix at a POST 0,1 pair existed
unchanged before the service, including its frontier agent. -/
theorem bankCountEligibleForeignPostTransport {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e root : Fin n) (j : Nat)
    (hx : ((renewalBankNext ring r e).1 e).pack.val = 0)
    (hy : ((renewalBankNext ring r e).1
      (ring.rightNeighbor e)).pack.val = 1)
    (hne : root ≠ e)
    (hj : EligibleAt ring (renewalBankNext ring r e) root j) :
    EligibleAt ring r root j ∧
      (renewalBankNext ring r e).1 (Counter.site ring root j) =
        r.1 (Counter.site ring root j) := by
  have hout := bankCountRootPairOutsidePrefix
    ring (renewalBankNext ring r e) e root j hx hy hne hj
  have hf : ∀ k : Nat, k ≤ j →
      (renewalBankNext ring r e).1 (Counter.site ring root k) =
        r.1 (Counter.site ring root k) ∧
      (renewalBankNext ring r e).2.sites
          (Counter.site ring root k) =
        r.2.sites (Counter.site ring root k) := by
    intro k hk
    exact renewalBankNextTwoSiteFrame ring r e
      (Counter.site ring root k) (hout k hk).1 (hout k hk).2
  exact ⟨bankCountEligiblePrefixTransport
    ring (renewalBankNext ring r e) r root j hj hf,
    (hf j (Nat.le_refl j)).1⟩

/-- POST 0,1 roles alone suffice to rule out any foreign credit
increase. An OLD foreign slot may have been destroyed by repair. -/
theorem bankCountForeignCreditLeOfPostRootPair {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e root : Fin n)
    (hx : ((renewalBankNext ring r e).1 e).pack.val = 0)
    (hy : ((renewalBankNext ring r e).1
      (ring.rightNeighbor e)).pack.val = 1)
    (hne : root ≠ e) :
    bankCountRootCredit ring (renewalBankNext ring r e) root ≤
      bankCountRootCredit ring r root := by
  classical
  by_cases hex : ∃ j : Nat,
      EligibleAt ring (renewalBankNext ring r e) root j
  · obtain ⟨j, hj⟩ := hex
    obtain ⟨hold, hfront⟩ := bankCountEligibleForeignPostTransport
      ring r e root j hx hy hne hj
    rw [bankCountRootCreditEq
        ring (renewalBankNext ring r e) root j hj,
      bankCountRootCreditEq ring r root j hold, hfront]
    exact Nat.le_refl _
  · rw [bankCountRootCreditZeroOfNoEligible
      ring (renewalBankNext ring r e) root hex]
    exact Nat.zero_le _

/-- With OLD and POST 0,1 roles, every foreign root has exactly
unchanged credit, including the absence of an eligible frontier. -/
theorem bankCountForeignCreditEqOfRootPair {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e root : Fin n)
    (hx : (r.1 e).pack.val = 0)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 1)
    (hx' : ((renewalBankNext ring r e).1 e).pack.val = 0)
    (hy' : ((renewalBankNext ring r e).1
      (ring.rightNeighbor e)).pack.val = 1)
    (hne : root ≠ e) :
    bankCountRootCredit ring (renewalBankNext ring r e) root =
      bankCountRootCredit ring r root := by
  classical
  by_cases hex : ∃ j : Nat, EligibleAt ring r root j
  · obtain ⟨j, hj⟩ := hex
    have hout := bankCountRootPairOutsidePrefix
      ring r e root j hx hy hne hj
    have hf : ∀ k : Nat, k ≤ j →
        (renewalBankNext ring r e).1 (Counter.site ring root k) =
          r.1 (Counter.site ring root k) ∧
        (renewalBankNext ring r e).2.sites
            (Counter.site ring root k) =
          r.2.sites (Counter.site ring root k) := by
      intro k hk
      exact renewalBankNextTwoSiteFrame ring r e
        (Counter.site ring root k) (hout k hk).1 (hout k hk).2
    have hpost : EligibleAt ring (renewalBankNext ring r e) root j :=
      bankCountEligiblePrefixTransport ring r
        (renewalBankNext ring r e) root j hj
        (fun k hk => ⟨(hf k hk).1.symm, (hf k hk).2.symm⟩)
    rw [bankCountRootCreditEq
        ring (renewalBankNext ring r e) root j hpost,
      bankCountRootCreditEq ring r root j hj,
      (hf j (Nat.le_refl j)).1]
  · have hnpost : ¬ ∃ j : Nat,
        EligibleAt ring (renewalBankNext ring r e) root j := by
      rintro ⟨j, hj⟩
      exact hex ⟨j, (bankCountEligibleForeignPostTransport
        ring r e root j hx' hy' hne hj).1⟩
    rw [bankCountRootCreditZeroOfNoEligible
        ring (renewalBankNext ring r e) root hnpost,
      bankCountRootCreditZeroOfNoEligible ring r root hex]

/-- Item 3 for every aligned root-source row: all roots other than
e have exactly unchanged credit. No slot premise is needed. -/
theorem bankCountRootSourceOnlyRootChanges {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (hx : (r.1 e).pack.val = 0)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 1) :
    ∀ root : Fin n, root ≠ e →
      bankCountRootCredit ring (renewalBankNext ring r e) root =
        bankCountRootCredit ring r root := by
  have hp := bankWindowRootSourceRoles ring hn r e hx
  intro root hne
  exact bankCountForeignCreditEqOfRootPair
    ring r e root hx hy hp.1 hp.2 hne

/-- Even a misaligned source-root service cannot increase another
root's credit; repair may end a responder-root slot. -/
theorem bankCountForeignCreditLeOfRootSource {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (hx : (r.1 e).pack.val = 0) :
    ∀ root : Fin n, root ≠ e →
      bankCountRootCredit ring (renewalBankNext ring r e) root ≤
        bankCountRootCredit ring r root := by
  have hp := bankWindowRootSourceRoles ring hn r e hx
  intro root hne
  exact bankCountForeignCreditLeOfPostRootPair
    ring r e root hp.1 hp.2 hne

/-- A role-zero selected source is never an outward nomination. -/
theorem bankCountNomFalseAtRoot {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n) (hx : (r.1 e).pack.val = 0) :
    bankCountNom ring r e = false := by
  classical
  cases he : bankCountNom ring r e with
  | false => rfl
  | true =>
      obtain ⟨root, j, hj, _, _, _, hsite⟩ :=
        (bankCountNomIff ring r e).mp he
      have hrole : (r.1 e).pack.val = j := by
        rw [hsite]
        exact hj.roles j (Nat.le_refl j)
      have hpos := hj.positive
      rw [hx] at hrole
      omega

/-! Item 4 arithmetic at certified snapshots.
These lemmas do not assert that an arbitrary actual row has the
specified POST frontier. That classification is still separate. -/

theorem bankCountLaunchRootCredit {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (root : Fin n) (hj : EligibleAt ring r root 1)
    (ht : (r.1 (Counter.site ring root 1)).tok = .RR) :
    bankCountRootCredit ring r root = 0 := by
  rw [bankCountRootCreditEq ring r root 1 hj, ht]
  exact bankCountLaunchCredit n

theorem bankCountAdvanceRootCredit {n : Nat}
    (ring : DirectedRing n) (r s : RenewalBankReference n)
    (root : Fin n) (j : Nat)
    (hr : EligibleAt ring r root j)
    (hs : EligibleAt ring s root (j + 1))
    (ht : (r.1 (Counter.site ring root j)).tok = .RR)
    (ht' : (s.1 (Counter.site ring root (j + 1))).tok = .RR) :
    bankCountRootCredit ring s root =
      bankCountRootCredit ring r root +
        (if bankCountHalf n ≤ j then 1 else 0) := by
  rw [bankCountRootCreditEq ring s root (j + 1) hs,
    bankCountRootCreditEq ring r root j hr, ht, ht']
  exact bankCountAdvanceCredit n j

theorem bankCountAdvanceNomination {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e root : Fin n) (j : Nat)
    (hj : EligibleAt ring r root j)
    (hdeep : bankCountHalf n ≤ j) (hwidth : j < bankCountWidth n)
    (ht : (r.1 (Counter.site ring root j)).tok = .RR)
    (he : e = Counter.site ring root j) :
    bankCountNom ring r e = true := by
  exact (bankCountNomIff ring r e).mpr
    ⟨root, j, hj, hdeep, hwidth, ht, he⟩

theorem bankCountAdvanceRootCreditBound {n : Nat}
    (ring : DirectedRing n) (r s : RenewalBankReference n)
    (e root : Fin n) (j : Nat)
    (hr : EligibleAt ring r root j)
    (hs : EligibleAt ring s root (j + 1))
    (hwidth : j < bankCountWidth n)
    (ht : (r.1 (Counter.site ring root j)).tok = .RR)
    (ht' : (s.1 (Counter.site ring root (j + 1))).tok = .RR)
    (he : e = Counter.site ring root j) :
    bankCountRootCredit ring s root ≤
      bankCountRootCredit ring r root +
        (if bankCountNom ring r e then 1 else 0) := by
  classical
  rw [bankCountAdvanceRootCredit ring r s root j hr hs ht ht']
  apply Nat.add_le_add_left
  by_cases hd : bankCountHalf n ≤ j
  · have hnom := bankCountAdvanceNomination
      ring r e root j hr hd hwidth ht he
    simp [hd, hnom]
  · rw [if_neg hd]
    exact Nat.zero_le _

/-- The literal bounce is b/RR to (b-1)/RL, with zero credit gain.
The preceding (b-1)/RR to b/RR advance earned the last unit. -/
theorem bankCountBounceRootCredit {n : Nat}
    (ring : DirectedRing n) (r s : RenewalBankReference n)
    (root : Fin n)
    (hr : EligibleAt ring r root (bankCountWidth n))
    (hs : EligibleAt ring s root (bankCountWidth n - 1))
    (ht : (r.1 (Counter.site ring root (bankCountWidth n))).tok = .RR)
    (ht' : (s.1 (Counter.site ring root
      (bankCountWidth n - 1))).tok = .RL) :
    bankCountRootCredit ring s root = bankCountRootCredit ring r root := by
  rw [bankCountRootCreditEq ring s root (bankCountWidth n - 1) hs,
    bankCountRootCreditEq ring r root (bankCountWidth n) hr, ht, ht']
  exact (bankCountBounceCredit n).symm

theorem bankCountReturnRootCredit {n : Nat}
    (ring : DirectedRing n) (r s : RenewalBankReference n)
    (root : Fin n) (j k : Nat)
    (hr : EligibleAt ring r root j) (hs : EligibleAt ring s root k)
    (ht : (r.1 (Counter.site ring root j)).tok = .RL)
    (ht' : (s.1 (Counter.site ring root k)).tok = .RL) :
    bankCountRootCredit ring s root = bankCountRootCredit ring r root := by
  rw [bankCountRootCreditEq ring s root k hs,
    bankCountRootCreditEq ring r root j hr, ht, ht']
  simp [bankCountCredit]

/-! Item 5: exact finite-sum assembly, including possible decreases
at other roots. All single-root assumptions are explicit here. -/

theorem bankCountSumLeExcept :
    ∀ {m : Nat} (f g : Fin m → Nat) (i : Fin m),
      (∀ j, j ≠ i → f j ≤ g j) →
      (List.ofFn f).sum + g i ≤ (List.ofFn g).sum + f i := by
  intro m
  induction m with
  | zero =>
      intro f g i _
      exact Fin.elim0 i
  | succ m ih =>
      intro f g i h
      rw [List.ofFn_succ, List.sum_cons,
        List.ofFn_succ, List.sum_cons]
      by_cases hi : i = 0
      · subst i
        have ht :
            (List.ofFn (fun j : Fin m => f j.succ)).sum ≤
              (List.ofFn (fun j : Fin m => g j.succ)).sum := by
          apply ofFn_sum_le
          intro j
          apply h
          intro hz
          have hv := congrArg Fin.val hz
          change j.val + 1 = 0 at hv
          omega
        omega
      · have hilt := i.isLt
        have hip : 0 < i.val := by
          have hv : i.val ≠ 0 := by
            intro hz
            apply hi
            apply Fin.ext
            exact hz
          omega
        obtain ⟨j, hjv⟩ : ∃ j : Fin m, j.val = i.val - 1 :=
          ⟨⟨i.val - 1, by omega⟩, rfl⟩
        have hj : j.succ = i := Fin.ext (by simp [hjv]; omega)
        have ht := ih
          (fun a : Fin m => f a.succ)
          (fun a : Fin m => g a.succ) j (by
            intro a ha
            apply h
            intro hz
            apply ha
            apply Fin.ext
            have hv := congrArg Fin.val hz
            have hv' := congrArg Fin.val hj
            simp at hv hv' ⊢
            omega)
        have hzero := h 0 (Ne.symm hi)
        simp only [hj] at ht
        omega

theorem bankCountPsiLeOfSingleRoot {n : Nat}
    (ring : DirectedRing n) (r s : RenewalBankReference n)
    (root : Fin n) (charge gain : Nat)
    (hother : ∀ other : Fin n, other ≠ root →
      bankCountRootCredit ring s other ≤
        bankCountRootCredit ring r other)
    (hlocal : bankCountRootCredit ring s root + charge ≤
      bankCountRootCredit ring r root + gain) :
    bankCountPsi ring s + charge ≤ bankCountPsi ring r + gain := by
  have hsum := bankCountSumLeExcept
    (fun i : Fin n => bankCountRootCredit ring s i)
    (fun i : Fin n => bankCountRootCredit ring r i) root hother
  change bankCountPsi ring s + bankCountRootCredit ring r root ≤
    bankCountPsi ring r + bankCountRootCredit ring s root at hsum
  omega

theorem bankCountPsiEqOfSingleRoot {n : Nat}
    (ring : DirectedRing n) (r s : RenewalBankReference n)
    (root : Fin n) (charge gain : Nat)
    (hother : ∀ other : Fin n, other ≠ root →
      bankCountRootCredit ring s other =
        bankCountRootCredit ring r other)
    (hlocal : bankCountRootCredit ring s root + charge =
      bankCountRootCredit ring r root + gain) :
    bankCountPsi ring s + charge = bankCountPsi ring r + gain := by
  apply Nat.le_antisymm
  · apply bankCountPsiLeOfSingleRoot ring r s root charge gain
    · intro other hne
      rw [hother other hne]
      exact Nat.le_refl _
    · omega
  · apply bankCountPsiLeOfSingleRoot ring s r root gain charge
    · intro other hne
      rw [hother other hne]
      exact Nat.le_refl _
    · omega

/-! Actual acceptance: no conditional row classifier is used below. -/

theorem bankCountSpawnCard {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n) :
    (renewalBankSpawn ring r e).length ≤ 1 := by
  cases hb : renewalBankBirth ring r.1 r.2 e <;>
    simp [renewalBankSpawn, hb]

theorem bankCountBirthSpawnCard {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e : Fin n) (o : RenewalBankOrigin n)
    (hb : renewalBankBirth ring r.1 r.2 e = some o) :
    (renewalBankSpawn ring r e).length = 1 := by
  simp [renewalBankSpawn, hb]

/-- Acceptance replaces the waiting controller by an active one;
the accepted root consequently has zero POST counting credit. -/
theorem bankCountBirthRootCreditZero {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (o : RenewalBankOrigin n)
    (hb : renewalBankBirth ring r.1 r.2 e = some o) :
    bankCountRootCredit ring (renewalBankNext ring r e) e = 0 := by
  obtain ⟨p, hp, _, _⟩ :=
    bankWindowClosureBirthCreatesGenuineRoot ring hn r e o hb
  apply bankCountRootCreditZeroOfWait
    ring (renewalBankNext ring r e) e
  intro hw
  rw [hp] at hw
  cases hw

/-- U2 gives the full old credit; the literal acceptance spends
exactly that credit on the singleton spawn. -/
theorem bankCountBirthPaysRootCredit {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (o : RenewalBankOrigin n) (hr : BankCountInv ring r)
    (hb : renewalBankBirth ring r.1 r.2 e = some o) :
    bankCountRootCredit ring (renewalBankNext ring r e) e +
        (bankCountWidth n - bankCountHalf n) *
          (renewalBankSpawn ring r e).length =
      bankCountRootCredit ring r e := by
  have hzero := bankCountBirthRootCreditZero
    ring (by omega : 2 ≤ n) r e o hb
  have hcard := bankCountBirthSpawnCard ring r e o hb
  have hcredit :=
    (bankCountBirthEligible ring hn hbank r e o hr hb).2.2.2.2
  rw [hzero, hcard, hcredit]
  simp

/-- Item 3 fully discharged on an actual acceptance edge:
only the accepting root's summand changes. -/
theorem bankCountBirthOnlyRootChanges {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (o : RenewalBankOrigin n) (hr : BankCountInv ring r)
    (hb : renewalBankBirth ring r.1 r.2 e = some o) :
    ∀ root : Fin n, root ≠ e →
      bankCountRootCredit ring (renewalBankNext ring r e) root =
        bankCountRootCredit ring r root := by
  have helig :=
    (bankCountBirthEligible ring hn hbank r e o hr hb).1
  have hfirst : (r.1 (ring.rightNeighbor e)).pack.val = 1 :=
    helig.roles 1 (Nat.le_refl 1)
  exact bankCountRootSourceOnlyRootChanges
    ring hn r e helig.rootRole hfirst

/-- The birth branch is exact conservation, stronger than the
requested drift bound. Neither slot-preservation premise is needed
for this branch, because the installed U2 theorem suffices. -/
theorem bankCountBirthPotentialExact {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (o : RenewalBankOrigin n) (hr : BankCountInv ring r)
    (hb : renewalBankBirth ring r.1 r.2 e = some o) :
    bankCountPsi ring (renewalBankNext ring r e) +
        (bankCountWidth n - bankCountHalf n) *
          (renewalBankSpawn ring r e).length =
      bankCountPsi ring r := by
  have hpaid := bankCountBirthPaysRootCredit
    ring hn hbank r e o hr hb
  have hsum := bankCountPsiEqOfSingleRoot
    ring r (renewalBankNext ring r e) e
    ((bankCountWidth n - bankCountHalf n) *
      (renewalBankSpawn ring r e).length) 0
    (bankCountBirthOnlyRootChanges ring hn hbank r e o hr hb)
    (by simpa only [Nat.add_zero] using hpaid)
  simpa only [Nat.add_zero] using hsum

theorem bankCountPotentialStepOfBirth {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (o : RenewalBankOrigin n) (hr : BankCountInv ring r)
    (hb : renewalBankBirth ring r.1 r.2 e = some o) :
    bankCountPsi ring (renewalBankNext ring r e) +
        (bankCountWidth n - bankCountHalf n) *
          (renewalBankSpawn ring r e).length ≤
      bankCountPsi ring r +
        (if bankCountNom ring r e then 1 else 0) := by
  rw [bankCountBirthPotentialExact ring hn hbank r e o hr hb]
  exact Nat.le_add_right _ _

/-
UNFINISHED U3b, omitted as a declaration:

bankCountPotentialStepOfSlots.

The unproved residual is the actual non-birth case under
BankCountInv ring r, BankSlotInv ring r, and
BankSlotInv ring (renewalBankNext ring r e):

  renewalBankBirth ring r.1 r.2 e = none
    -> bankCountPsi ring (renewalBankNext ring r e)
         <= bankCountPsi ring r
              + (if bankCountNom ring r e then 1 else 0).

In particular, the actual nonroot-source rows still have to produce
the appropriate old/post eligible frontiers and the global one-root
change classification. The snapshot arithmetic above is not such
a producer, and neither endpoint slot invariant alone supplies it.
-/

end L3.Prime

/-!
Q4683 append to Leader/L3/Prime/BankCount.lean at cf2a3f449.
Source-grounded Lean draft; no compiler run is claimed.
No protocol row or existing observer/credit/slot definition changes.
-/

namespace L3.Prime

open L3.HeadlineRenewal
open L3.HeadlineRenewalCleanBank
open L3.RenewalReferenceClock
open L3.BankWindow
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- `rbBankReferencePairPack` stated for `renewalBankNext` (definitionally `rbRun ring r [e]`). -/
theorem bankCountPairPackNext {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n) :
    ((renewalBankNext ring r e).1 e).pack.val = (r.1 e).pack.val ∧
      ((renewalBankNext ring r e).1
        (ring.rightNeighbor e)).pack.val =
          packNext (r.1 e).pack.val
            (r.1 (ring.rightNeighbor e)).pack.val
            (compileAdvice (ceilLogTwo n)).b :=
  rbBankReferencePairPack ring hn r e

/-- Transport exactly the fields read by one eligible certificate.
The equality orientation is POST = OLD. -/
theorem bankCountEligibleReadTransport {n : Nat}
    (ring : DirectedRing n) (r s : RenewalBankReference n)
    (root : Fin n) (j : Nat)
    (hj : EligibleAt ring r root j)
    (hpack : ∀ k : Nat, k ≤ j →
      (s.1 (Counter.site ring root k)).pack.val =
        (r.1 (Counter.site ring root k)).pack.val)
    (hmode : (s.1 root).mode = (r.1 root).mode)
    (hcontroller : (s.2.sites root).controller =
      (r.2.sites root).controller)
    (htoken : ∀ k : Nat, 1 ≤ k → k ≤ j →
      (s.1 (Counter.site ring root k)).tok =
        (r.1 (Counter.site ring root k)).tok)
    (hworker : (s.2.sites (Counter.site ring root j)).worker =
      (r.2.sites (Counter.site ring root j)).worker) :
    EligibleAt ring s root j := by
  refine {
    rootRole := ?_
    rootMode := hmode.trans hj.rootMode
    currentWait := hcontroller.trans hj.currentWait
    positive := hj.positive
    leWidth := hj.leWidth
    roles := ?_
    emptyPrefix := ?_
    pending := ?_
    resetToken := ?_ }
  · exact (hpack 0 (Nat.zero_le j)).trans hj.rootRole
  · intro k hk
    exact (hpack k hk).trans (hj.roles k hk)
  · intro k hk hkj
    rw [htoken k hk (by omega)]
    exact hj.emptyPrefix k hk hkj
  · obtain ⟨rho, hw, hroot⟩ := hj.pending
    exact ⟨rho, hworker.trans hw, hroot⟩
  · rw [htoken j hj.positive (Nat.le_refl j)]
    exact hj.resetToken

set_option maxHeartbeats 3000000 in
/-- Literal source-root RWAIT preimage.
A POST RWAIT source is either a RESET launch or a surviving OLD
RWAIT. Neither an OLD grant nor a timeout survives.
This includes a misaligned responder. -/
theorem bankCountRootRwaitCellPreimage {c : Compiled}
    (x y : Agent c)
    (hx : x.pack.val = 0)
    (hpost : (Counter.resetBankOld x y).1.mode = .RWAIT) :
    x.grant = false ∧
      ((x.mode = .RESET ∧ y.pack.val = 1) ∨
        (x.mode = .RWAIT ∧ 1 < x.lease.val ∧
          (y.pack.val = 1 → y.tok ≠ .RL))) := by
  have hb : 0 < c.b := by
    change 0 < c.s + 11
    omega
  have hone : 1 ≤ c.b := by omega
  have hbzero : c.b ≠ 0 := by omega
  have hbwide : c.b ≠ 1 := by
    change c.s + 11 ≠ 1
    omega
  by_cases hy : y.pack.val = 1
  · cases hg : x.grant <;>
      cases hm : x.mode <;>
      cases ht : y.tok <;>
      cases hbit : y.bit <;>
      by_cases hl : 1 < x.lease.val <;>
      simp_all [Counter.resetBankOld, bankPair, bankCell,
        packNext, hb, hone, hbzero, hbwide,
        isWaitMode, isRetTok, Id.run_pure, Id.run_bind]
  · have hyrev : 1 ≠ y.pack.val := Ne.symm hy
    cases hg : x.grant <;>
      cases hm : x.mode <;>
      cases ht : y.tok <;>
      cases hbit : y.bit <;>
      by_cases hl : 1 < x.lease.val <;>
      simp_all [Counter.resetBankOld, bankPair, bankCell,
        packNext, hb, hone, hbzero, hbwide,
        isWaitMode, isRetTok, Id.run_pure, Id.run_bind]

set_option maxHeartbeats 1000000 in
/-- A surviving OLD RWAIT source keeps its controller.
An aligned RL is excluded because it takes the return row. -/
theorem bankCountRootRwaitControllerKept {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = 0)
    (hg : x.grant = false)
    (hm : x.mode = .RWAIT)
    (hlong : 1 < x.lease.val)
    (hnorl : y.pack.val = 1 → y.tok ≠ .RL) :
    (renewalBankPairMemory c m e dest x y).1.controller =
      (m.sites e).controller := by
  have hb : 0 < c.b := by
    change 0 < c.s + 11
    omega
  have hone : 1 ≤ c.b := by omega
  have hbzero : c.b ≠ 0 := by omega
  have hbwide : c.b ≠ 1 := by
    change c.s + 11 ≠ 1
    omega
  by_cases hy : y.pack.val = 1
  · have htne : y.tok ≠ .RL := hnorl hy
    cases ht : y.tok <;>
      simp_all [renewalBankPairMemory, renewalBankWaitSlot,
        bankCell, packNext, hb, hone, hbzero, hbwide,
        isWaitMode, isRetTok, Id.run_pure, Id.run_bind]
  · have hyrev : 1 ≠ y.pack.val := Ne.symm hy
    cases ht : y.tok <;>
      simp_all [renewalBankPairMemory, renewalBankWaitSlot,
        bankCell, packNext, hb, hone, hbzero, hbwide,
        isWaitMode, isRetTok, Id.run_pure, Id.run_bind]

/-- The compiled LongWait read mask preserves the eligible frontier
and therefore exactly preserves the source root's credit. -/
theorem bankCountRootSourceWaitCreditEq {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n) (j : Nat)
    (hr : BankCountInv ring r)
    (hj : EligibleAt ring r e j)
    (hg : (r.1 e).grant = false)
    (hlong : 1 < (r.1 e).lease.val)
    (hret : isRetTok (r.1 (ring.rightNeighbor e)).tok = false) :
    bankCountRootCredit ring (renewalBankNext ring r e) e =
      bankCountRootCredit ring r e := by
  have hx := hj.rootRole
  have hy : (r.1 (ring.rightNeighbor e)).pack.val = 1 :=
    hj.roles 1 hj.positive
  have hreads :
      bankWindowReadPackPrefix ring r
        (renewalBankNext ring r e) e (bankCountWidth n) ∧
      bankWindowReadDigitTokens ring r
        (renewalBankNext ring r e) e ∧
      bankWindowReadDigitBits ring r
        (renewalBankNext ring r e) e ∧
      (∀ k : Fin (bankCountWidth n),
        bankWindowReadWorker r (renewalBankNext ring r e)
          (Counter.site ring e (k.val + 1))) ∧
      bankWindowReadMode r (renewalBankNext ring r e) e ∧
      bankWindowReadController r (renewalBankNext ring r e) e := by
    rcases hr with ⟨seed, pre, rfl, _, _⟩
    exact bankWindowOverlapSourceLongWaitWindowReads
      ring hn hbank seed pre e hx hy hg
      (Or.inl hj.rootMode) hlong hret
  have htokens : ∀ k : Nat, 1 ≤ k → k ≤ bankCountWidth n →
      ((renewalBankNext ring r e).1
        (Counter.site ring e k)).tok =
        (r.1 (Counter.site ring e k)).tok := by
    intro k hk hkb
    have hklt : k - 1 < bankCountWidth n := by omega
    have ht := hreads.2.1 ⟨k - 1, hklt⟩
    change ((renewalBankNext ring r e).1
        (Counter.site ring e (k - 1 + 1))).tok =
      (r.1 (Counter.site ring e (k - 1 + 1))).tok at ht
    simpa only [Nat.sub_add_cancel hk] using ht
  have hworker :
      ((renewalBankNext ring r e).2.sites
        (Counter.site ring e j)).worker =
      (r.2.sites (Counter.site ring e j)).worker := by
    have hjlt : j - 1 < bankCountWidth n := by
      have hp := hj.positive
      have hb := hj.leWidth
      omega
    have hw := hreads.2.2.2.1 ⟨j - 1, hjlt⟩
    change ((renewalBankNext ring r e).2.sites
        (Counter.site ring e (j - 1 + 1))).worker =
      (r.2.sites (Counter.site ring e (j - 1 + 1))).worker at hw
    simpa only [Nat.sub_add_cancel hj.positive] using hw
  have hpost : EligibleAt ring (renewalBankNext ring r e) e j :=
    bankCountEligibleReadTransport ring r (renewalBankNext ring r e)
      e j hj
      (fun k hk => hreads.1 k (Nat.le_trans hk hj.leWidth))
      hreads.2.2.2.2.1 hreads.2.2.2.2.2
      (fun k hk hkj =>
        htokens k hk (Nat.le_trans hkj hj.leWidth))
      hworker
  rw [bankCountRootCreditEq
      ring (renewalBankNext ring r e) e j hpost,
    bankCountRootCreditEq ring r e j hj,
    htokens j hj.positive hj.leWidth]

/-- Every source-role-zero row weakly decreases that source's credit.
A surviving POST certificate is either a depth-one launch of credit
zero or a surviving OLD slot covered by LongWait. -/
theorem bankCountRootSourceCreditLe {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hr : BankCountInv ring r)
    (hs : BankSlotInv ring r)
    (hx : (r.1 e).pack.val = 0) :
    bankCountRootCredit ring (renewalBankNext ring r e) e ≤
      bankCountRootCredit ring r e := by
  classical
  by_cases hex : ∃ j : Nat,
      EligibleAt ring (renewalBankNext ring r e) e j
  · obtain ⟨j, hjpost⟩ := hex
    have hreads := bankWindowJointSelectedPairReads
      ring hn hbank r e
    have hcellmode :
        (Counter.resetBankOld
          (r.1 e) (r.1 (ring.rightNeighbor e))).1.mode = .RWAIT :=
      hreads.1.symm.trans hjpost.rootMode
    obtain ⟨hg, hlaunch | hwait⟩ :=
      bankCountRootRwaitCellPreimage
        (r.1 e) (r.1 (ring.rightNeighbor e)) hx hcellmode
    · obtain ⟨hm, hy⟩ := hlaunch
      have hrow := bankWindowClosureResetLaunchPhysicalPair
        ring hn hbank r e hx hy hg hm
      have hone : j = 1 := by
        have hpos := hjpost.positive
        by_cases heq : j = 1
        · exact heq
        · have hlt : 1 < j := by omega
          have hempty := hjpost.emptyPrefix 1 (by omega) hlt
          change ((renewalBankNext ring r e).1
            (ring.rightNeighbor e)).tok = .E at hempty
          rw [hrow.2.2] at hempty
          cases hempty
      subst j
      rw [bankCountLaunchRootCredit
        ring (renewalBankNext ring r e) e hjpost hrow.2.2]
      exact Nat.zero_le _
    · obtain ⟨hm, hlong, hnorl⟩ := hwait
      have hmemory := bankCountRootRwaitControllerKept
        (compileAdvice (ceilLogTwo n)) r.2 e
        (ring.rightNeighbor e) (r.1 e)
        (r.1 (ring.rightNeighbor e)) hx hg hm hlong hnorl
      have hcontroller :
          (r.2.sites e).controller = .waiting [] :=
        hmemory.symm.trans
          (hreads.2.1.symm.trans hjpost.currentWait)
      obtain ⟨k, hk⟩ := hs.generated e hx hm hcontroller
      have hy : (r.1 (ring.rightNeighbor e)).pack.val = 1 :=
        hk.toEligibleAt.roles 1 hk.toEligibleAt.positive
      have hret : isRetTok (r.1 (ring.rightNeighbor e)).tok = false := by
        by_cases hone : k = 1
        · subst hone
          have ht := hk.toEligibleAt.resetToken
          change (r.1 (ring.rightNeighbor e)).tok = .RR ∨
            (r.1 (ring.rightNeighbor e)).tok = .RL at ht
          rcases ht with ht | ht
          · simp [ht, isRetTok]
          · exact False.elim (hnorl hy ht)
        · have hp := hk.toEligibleAt.positive
          have hlt : 1 < k := by omega
          have ht := hk.toEligibleAt.emptyPrefix 1 (by omega) hlt
          change (r.1 (ring.rightNeighbor e)).tok = .E at ht
          simp [ht, isRetTok]
      exact Nat.le_of_eq
        (bankCountRootSourceWaitCreditEq ring hn hbank r e k
          hr hk.toEligibleAt hg hlong hret)
  · rw [bankCountRootCreditZeroOfNoEligible
      ring (renewalBankNext ring r e) e hex]
    exact Nat.zero_le _

theorem bankCountPsiLeOfRootSource {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hr : BankCountInv ring r)
    (hs : BankSlotInv ring r)
    (hx : (r.1 e).pack.val = 0) :
    bankCountPsi ring (renewalBankNext ring r e) ≤
      bankCountPsi ring r := by
  have hlocal := bankCountRootSourceCreditLe
    ring hn hbank r e hr hs hx
  have hsum := bankCountPsiLeOfSingleRoot
    ring r (renewalBankNext ring r e) e 0 0
    (bankCountForeignCreditLeOfRootSource ring hn r e hx)
    (by simpa only [Nat.add_zero] using hlocal)
  simpa only [Nat.add_zero] using hsum

/-- Class one: the literal aligned root-source rows. -/
theorem bankCountPotentialStepOfRootSource {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hr : BankCountInv ring r)
    (hs : BankSlotInv ring r)
    (hs' : BankSlotInv ring (renewalBankNext ring r e))
    (hnb : renewalBankBirth ring r.1 r.2 e = none)
    (hx : (r.1 e).pack.val = 0)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = 1) :
    bankCountPsi ring (renewalBankNext ring r e) ≤
      bankCountPsi ring r +
        (if bankCountNom ring r e then 1 else 0) := by
  exact Nat.le_trans
    (bankCountPsiLeOfRootSource ring hn hbank r e hr hs hx)
    (Nat.le_add_right _ _)

/-! Labelled-pair geometry and the moving-frontier classes. -/

theorem bankCountAlignedPairOutsidePrefix {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e owner other : Fin n) (j depth : Nat)
    (hx : (r.1 e).pack.val = j)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1)
    (he : e = Counter.site ring owner j)
    (hne : other ≠ owner)
    (hd : EligibleAt ring r other depth) :
    ∀ k : Nat, k ≤ depth →
      Counter.site ring other k ≠ e ∧
        Counter.site ring other k ≠ ring.rightNeighbor e := by
  have hdest : ring.rightNeighbor e =
      Counter.site ring owner (j + 1) := by
    rw [he]
    rfl
  intro k hk
  constructor
  · intro hsite
    have hrole := hd.roles k hk
    rw [hsite, hx] at hrole
    have hkj : k = j := by omega
    have hsym := hkj.symm
    subst hsym
    exact hne (bankCountSiteRootInjective ring j (hsite.trans he))
  · intro hsite
    have hrole := hd.roles k hk
    rw [hsite, hy] at hrole
    have hkj : k = j + 1 := by omega
    subst hkj
    exact hne
      (bankCountSiteRootInjective ring (j + 1) (hsite.trans hdest))

theorem bankCountForeignCreditLeOfPostAlignedPair {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e owner other : Fin n) (j : Nat)
    (hx : ((renewalBankNext ring r e).1 e).pack.val = j)
    (hy : ((renewalBankNext ring r e).1
      (ring.rightNeighbor e)).pack.val = j + 1)
    (he : e = Counter.site ring owner j)
    (hne : other ≠ owner) :
    bankCountRootCredit ring (renewalBankNext ring r e) other ≤
      bankCountRootCredit ring r other := by
  classical
  by_cases hex : ∃ depth : Nat,
      EligibleAt ring (renewalBankNext ring r e) other depth
  · obtain ⟨depth, hd⟩ := hex
    have hout := bankCountAlignedPairOutsidePrefix ring
      (renewalBankNext ring r e) e owner other j depth hx hy he hne hd
    have hf : ∀ k : Nat, k ≤ depth →
        (renewalBankNext ring r e).1 (Counter.site ring other k) =
          r.1 (Counter.site ring other k) ∧
        (renewalBankNext ring r e).2.sites (Counter.site ring other k) =
          r.2.sites (Counter.site ring other k) := by
      intro k hk
      exact renewalBankNextTwoSiteFrame ring r e
        (Counter.site ring other k) (hout k hk).1 (hout k hk).2
    have hold := bankCountEligiblePrefixTransport ring
      (renewalBankNext ring r e) r other depth hd hf
    rw [bankCountRootCreditEq ring (renewalBankNext ring r e) other depth hd,
      bankCountRootCreditEq ring r other depth hold,
      (hf depth (Nat.le_refl depth)).1]
    exact Nat.le_refl _
  · rw [bankCountRootCreditZeroOfNoEligible
      ring (renewalBankNext ring r e) other hex]
    exact Nat.zero_le _

theorem bankCountForeignCreditEqOfAlignedPair {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalBankReference n) (e owner : Fin n) (j : Nat)
    (hbelow : j < bankCountWidth n)
    (hx : (r.1 e).pack.val = j)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1)
    (he : e = Counter.site ring owner j) :
    ∀ other : Fin n, other ≠ owner →
      bankCountRootCredit ring (renewalBankNext ring r e) other =
        bankCountRootCredit ring r other := by
  classical
  have hpack := bankCountPairPackNext ring (by omega : 2 ≤ n) r e
  have hx' : ((renewalBankNext ring r e).1 e).pack.val = j :=
    hpack.1.trans hx
  have hy' : ((renewalBankNext ring r e).1
      (ring.rightNeighbor e)).pack.val = j + 1 := by
    rw [hpack.2, hx, hy]
    simp [packNext, hbelow]
  intro other hne
  by_cases hex : ∃ depth : Nat, EligibleAt ring r other depth
  · obtain ⟨depth, hd⟩ := hex
    have hout := bankCountAlignedPairOutsidePrefix
      ring r e owner other j depth hx hy he hne hd
    have hf : ∀ k : Nat, k ≤ depth →
        (renewalBankNext ring r e).1 (Counter.site ring other k) =
          r.1 (Counter.site ring other k) ∧
        (renewalBankNext ring r e).2.sites (Counter.site ring other k) =
          r.2.sites (Counter.site ring other k) := by
      intro k hk
      exact renewalBankNextTwoSiteFrame ring r e
        (Counter.site ring other k) (hout k hk).1 (hout k hk).2
    have hpost := bankCountEligiblePrefixTransport ring r
      (renewalBankNext ring r e) other depth hd
      (fun k hk => ⟨(hf k hk).1.symm, (hf k hk).2.symm⟩)
    rw [bankCountRootCreditEq ring (renewalBankNext ring r e) other depth hpost,
      bankCountRootCreditEq ring r other depth hd,
      (hf depth (Nat.le_refl depth)).1]
  · have hle := bankCountForeignCreditLeOfPostAlignedPair
      ring r e owner other j hx' hy' he hne
    rw [bankCountRootCreditZeroOfNoEligible ring r other hex] at hle
    rw [bankCountRootCreditZeroOfNoEligible ring r other hex]
    exact Nat.eq_zero_of_le_zero hle

/-- The literal RR row and its observer transfer produce the next
eligible frontier, rather than assuming that frontier. -/
theorem bankCountAdvanceEligible {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e root : Fin n) (j : Nat)
    (hj : EligibleAt ring r root j)
    (hbelow : j < bankCountWidth n)
    (ht : (r.1 (Counter.site ring root j)).tok = .RR)
    (he : e = Counter.site ring root j)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1) :
    EligibleAt ring (renewalBankNext ring r e) root (j + 1) ∧
      ((renewalBankNext ring r e).1
        (Counter.site ring root (j + 1))).tok = .RR := by
  have hx : (r.1 e).pack.val = j := by
    rw [he]
    exact hj.roles j (Nat.le_refl j)
  have hrr : (r.1 e).tok = .RR := by
    rw [he]
    exact ht
  have hd : ring.rightNeighbor e =
      Counter.site ring root (j + 1) := by
    rw [he]
    rfl
  have hrootE : root ≠ e := by
    intro h
    have hzero := hj.rootRole
    rw [h, hx] at hzero
    have hpos := hj.positive
    omega
  have hrootD : root ≠ ring.rightNeighbor e := by
    intro h
    have hzero := hj.rootRole
    rw [h, hy] at hzero
    omega
  have hroot := renewalBankNextTwoSiteFrame ring r e root hrootE hrootD
  have hp := bankCountPairPackNext ring (by omega : 2 ≤ n) r e
  have hpackAll : ∀ i : Fin n,
      ((renewalBankNext ring r e).1 i).pack.val = (r.1 i).pack.val := by
    intro i
    by_cases hi : i = e
    · subst i
      exact hp.1
    · by_cases hiD : i = ring.rightNeighbor e
      · subst i
        rw [hp.2, hx, hy]
        simp [packNext, hbelow]
      · rw [(renewalBankNextTwoSiteFrame ring r e i hi hiD).1]
  have hoff : ∀ k : Nat, k ≤ j → k ≠ j →
      (renewalBankNext ring r e).1 (Counter.site ring root k) =
        r.1 (Counter.site ring root k) ∧
      (renewalBankNext ring r e).2.sites (Counter.site ring root k) =
        r.2.sites (Counter.site ring root k) := by
    intro k hk hkj
    have hrole := hj.roles k hk
    apply renewalBankNextTwoSiteFrame ring r e (Counter.site ring root k)
    · intro h
      rw [h, hx] at hrole
      omega
    · intro h
      rw [h, hy] at hrole
      omega
  have hcells := bankWindowJointAlignedRrForwardCells r.2 e
    (ring.rightNeighbor e) (r.1 e) (r.1 (ring.rightNeighbor e))
    j hj.positive hbelow hx hy hrr
  have htrip := bankWindowClosureSelectedBankTrip ring hn hbank r e
  simp only [Counter.resetAgentBankTrip, Counter.resetCellBankTrip,
    Prod.mk.injEq] at htrip
  have hf := rbReferenceSelectedPairFrame ring (by omega : 2 ≤ n) r e
  have hwD := congrArg (fun s : RenewalBankSite n => s.worker) hf.2.2.2
  have hxe : ((renewalBankNext ring r e).1 e).tok = .E :=
    htrip.1.2.2.trans hcells.1
  have hyr : ((renewalBankNext ring r e).1
      (ring.rightNeighbor e)).tok = .RR :=
    htrip.2.2.2.trans hcells.2.2.1
  have hnew : EligibleAt ring (renewalBankNext ring r e) root (j + 1) := by
    refine {
      rootRole := ?_
      rootMode := ?_
      currentWait := ?_
      positive := by omega
      leWidth := by omega
      roles := ?_
      emptyPrefix := ?_
      pending := ?_
      resetToken := ?_ }
    · rw [hroot.1]
      exact hj.rootRole
    · rw [hroot.1]
      exact hj.rootMode
    · rw [hroot.2]
      exact hj.currentWait
    · intro k hk
      rw [hpackAll]
      by_cases hkj : k = j + 1
      · subst hkj
        rw [← hd]
        exact hy
      · exact hj.roles k (by omega)
    · intro k hk hkj
      by_cases hke : k = j
      · have hsym := hke.symm
        subst hsym
        rw [← he]
        exact hxe
      · rw [(hoff k (by omega) hke).1]
        exact hj.emptyPrefix k hk (by omega)
    · obtain ⟨rho, hw, hown⟩ := hj.pending
      rw [← he] at hw
      refine ⟨rho, ?_, hown⟩
      rw [← hd]
      exact (hwD.trans hcells.2.2.2.2).trans hw
    · left
      rw [← hd]
      exact hyr
  refine ⟨hnew, ?_⟩
  rw [← hd]
  exact hyr

/-- Class two: outward RR advance of an OLD eligible frontier. -/
theorem bankCountPotentialStepOfAdvance {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hr : BankCountInv ring r)
    (hs : BankSlotInv ring r)
    (hs' : BankSlotInv ring (renewalBankNext ring r e))
    (hnb : renewalBankBirth ring r.1 r.2 e = none)
    (root : Fin n) (j : Nat)
    (hj : EligibleAt ring r root j)
    (hbelow : j < bankCountWidth n)
    (ht : (r.1 (Counter.site ring root j)).tok = .RR)
    (he : e = Counter.site ring root j)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1) :
    bankCountPsi ring (renewalBankNext ring r e) ≤
      bankCountPsi ring r + (if bankCountNom ring r e then 1 else 0) := by
  have hx : (r.1 e).pack.val = j := by
    rw [he]
    exact hj.roles j (Nat.le_refl j)
  obtain ⟨hpost, htpost⟩ :=
    bankCountAdvanceEligible ring hn hbank r e root j hj hbelow ht he hy
  have hlocal := bankCountAdvanceRootCreditBound ring r
    (renewalBankNext ring r e) e root j hj hpost hbelow ht htpost he
  have hforeign := bankCountForeignCreditEqOfAlignedPair
    ring hn r e root j hbelow hx hy he
  have hsum := bankCountPsiLeOfSingleRoot ring r
    (renewalBankNext ring r e) root 0
    (if bankCountNom ring r e then 1 else 0)
    (fun other hne => Nat.le_of_eq (hforeign other hne))
    (by simpa only [Nat.add_zero] using hlocal)
  simpa only [Nat.add_zero] using hsum

/-- The literal top-turn/RL row produces the inward frontier. -/
theorem bankCountBackEligible {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e root : Fin n) (k : Nat)
    (hk : 1 ≤ k)
    (hj : EligibleAt ring r root (k + 1))
    (he : e = Counter.site ring root k)
    (hmove : (r.1 (Counter.site ring root (k + 1))).tok = .RL ∨
      ((r.1 (Counter.site ring root (k + 1))).tok = .RR ∧
        k + 1 = bankCountWidth n)) :
    EligibleAt ring (renewalBankNext ring r e) root k ∧
      ((renewalBankNext ring r e).1 (Counter.site ring root k)).tok = .RL := by
  have hwidth := hj.leWidth
  have hbelow : k < bankCountWidth n := by omega
  have hd : ring.rightNeighbor e =
      Counter.site ring root (k + 1) := by
    rw [he]
    rfl
  have hx : (r.1 e).pack.val = k := by
    rw [he]
    exact hj.roles k (by omega)
  have hy : (r.1 (ring.rightNeighbor e)).pack.val = k + 1 := by
    rw [hd]
    exact hj.roles (k + 1) (Nat.le_refl _)
  have hxe : (r.1 e).tok = .E := by
    rw [he]
    exact hj.emptyPrefix k hk (by omega)
  have hq : (r.1 (ring.rightNeighbor e)).tok = .RL ∨
      ((r.1 (ring.rightNeighbor e)).tok = .RR ∧
        k + 1 = bankCountWidth n) := by
    simpa only [hd] using hmove
  have hrootE : root ≠ e := by
    intro h
    have hzero := hj.rootRole
    rw [h, hx] at hzero
    omega
  have hrootD : root ≠ ring.rightNeighbor e := by
    intro h
    have hzero := hj.rootRole
    rw [h, hy] at hzero
    omega
  have hroot := renewalBankNextTwoSiteFrame ring r e root hrootE hrootD
  have hp := bankCountPairPackNext ring (by omega : 2 ≤ n) r e
  have hpackAll : ∀ i : Fin n,
      ((renewalBankNext ring r e).1 i).pack.val = (r.1 i).pack.val := by
    intro i
    by_cases hi : i = e
    · subst i
      exact hp.1
    · by_cases hiD : i = ring.rightNeighbor e
      · subst i
        rw [hp.2, hx, hy]
        simp [packNext, hbelow]
      · rw [(renewalBankNextTwoSiteFrame ring r e i hi hiD).1]
  have hoff : ∀ a : Nat, a < k →
      (renewalBankNext ring r e).1 (Counter.site ring root a) =
        r.1 (Counter.site ring root a) ∧
      (renewalBankNext ring r e).2.sites (Counter.site ring root a) =
        r.2.sites (Counter.site ring root a) := by
    intro a ha
    have hrole := hj.roles a (by omega)
    apply renewalBankNextTwoSiteFrame ring r e (Counter.site ring root a)
    · intro h
      rw [h, hx] at hrole
      omega
    · intro h
      rw [h, hy] at hrole
      omega
  have hcells := bankWindowJointAlignedRlBackCells r.2 e
    (ring.rightNeighbor e) (r.1 e) (r.1 (ring.rightNeighbor e))
    k hk hbelow hx hy hxe hq
  have htrip := bankWindowClosureSelectedBankTrip ring hn hbank r e
  simp only [Counter.resetAgentBankTrip, Counter.resetCellBankTrip,
    Prod.mk.injEq] at htrip
  have hf := rbReferenceSelectedPairFrame ring (by omega : 2 ≤ n) r e
  have hwS := congrArg (fun s : RenewalBankSite n => s.worker) hf.2.2.1
  have hxl : ((renewalBankNext ring r e).1 e).tok = .RL :=
    htrip.1.2.2.trans hcells.1
  have hnew : EligibleAt ring (renewalBankNext ring r e) root k := by
    refine {
      rootRole := ?_
      rootMode := ?_
      currentWait := ?_
      positive := hk
      leWidth := by omega
      roles := ?_
      emptyPrefix := ?_
      pending := ?_
      resetToken := ?_ }
    · rw [hroot.1]
      exact hj.rootRole
    · rw [hroot.1]
      exact hj.rootMode
    · rw [hroot.2]
      exact hj.currentWait
    · intro a ha
      rw [hpackAll]
      exact hj.roles a (by omega)
    · intro a ha hak
      rw [(hoff a hak).1]
      exact hj.emptyPrefix a ha (by omega)
    · obtain ⟨rho, hw, hown⟩ := hj.pending
      rw [← hd] at hw
      refine ⟨rho, ?_, hown⟩
      rw [← he]
      exact (hwS.trans hcells.2.2.2.2).trans hw
    · right
      rw [← he]
      exact hxl
  refine ⟨hnew, ?_⟩
  rw [← he]
  exact hxl

theorem bankCountBackPotentialExact {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e root : Fin n) (k : Nat)
    (hk : 1 ≤ k)
    (hj : EligibleAt ring r root (k + 1))
    (he : e = Counter.site ring root k)
    (hmove : (r.1 (Counter.site ring root (k + 1))).tok = .RL ∨
      ((r.1 (Counter.site ring root (k + 1))).tok = .RR ∧
        k + 1 = bankCountWidth n)) :
    bankCountPsi ring (renewalBankNext ring r e) = bankCountPsi ring r := by
  have hwidth := hj.leWidth
  have hbelow : k < bankCountWidth n := by omega
  have hd : ring.rightNeighbor e =
      Counter.site ring root (k + 1) := by
    rw [he]
    rfl
  have hx : (r.1 e).pack.val = k := by
    rw [he]
    exact hj.roles k (by omega)
  have hy : (r.1 (ring.rightNeighbor e)).pack.val = k + 1 := by
    rw [hd]
    exact hj.roles (k + 1) (Nat.le_refl _)
  obtain ⟨hpost, htpost⟩ :=
    bankCountBackEligible ring hn hbank r e root k hk hj he hmove
  have hlocal : bankCountRootCredit ring (renewalBankNext ring r e) root =
      bankCountRootCredit ring r root := by
    rcases hmove with hrl | ⟨hrr, htop⟩
    · exact bankCountReturnRootCredit ring r (renewalBankNext ring r e)
        root (k + 1) k hj hpost hrl htpost
    · rw [bankCountRootCreditEq ring (renewalBankNext ring r e) root k hpost,
        bankCountRootCreditEq ring r root (k + 1) hj, htpost, hrr]
      simp [bankCountCredit, htop]
  have hforeign := bankCountForeignCreditEqOfAlignedPair
    ring hn r e root k hbelow hx hy he
  have hsum := bankCountPsiEqOfSingleRoot ring r
    (renewalBankNext ring r e) root 0 0 hforeign
    (by simpa only [Nat.add_zero] using hlocal)
  simpa only [Nat.add_zero] using hsum

/-- Class four: top RR bounce or an inward RL move. -/
theorem bankCountPotentialStepOfBack {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hr : BankCountInv ring r)
    (hs : BankSlotInv ring r)
    (hs' : BankSlotInv ring (renewalBankNext ring r e))
    (hnb : renewalBankBirth ring r.1 r.2 e = none)
    (root : Fin n) (k : Nat)
    (hk : 1 ≤ k)
    (hj : EligibleAt ring r root (k + 1))
    (he : e = Counter.site ring root k)
    (hmove : (r.1 (Counter.site ring root (k + 1))).tok = .RL ∨
      ((r.1 (Counter.site ring root (k + 1))).tok = .RR ∧
        k + 1 = bankCountWidth n)) :
    bankCountPsi ring (renewalBankNext ring r e) ≤
      bankCountPsi ring r + (if bankCountNom ring r e then 1 else 0) := by
  rw [bankCountBackPotentialExact ring hn hbank r e root k hk hj he hmove]
  exact Nat.le_add_right _ _

/-! Responder repair. -/

/-- The changed nonroot row keeps an E/RR/RL source in the digit
range, including its worker. -/
theorem bankCountRepairSourceCells {n : Nat} {c : Compiled}
    (m : RenewalBankMemory n) (e dest : Fin n)
    (x y : Agent c)
    (hlo : 1 ≤ x.pack.val)
    (hhi : x.pack.val ≤ c.b)
    (hrepair : packNext x.pack.val y.pack.val c.b ≠ y.pack.val)
    (ht : x.tok = .E ∨ x.tok = .RR ∨ x.tok = .RL) :
    (Counter.resetBankOld x y).1.tok = x.tok ∧
      (renewalBankPairMemory c m e dest x y).1.worker =
        (m.sites e).worker := by
  have hx : x.pack.val ≠ 0 := by omega
  rw [Counter.resetBankOld,
    bankPair_nonroot _ _ _ _ _ (by change x.pack.val ≠ 0; exact hx)]
  rw [renewalBankPairMemory_nonroot c m e dest x y hx]
  rcases ht with ht | ht | ht <;>
    simp [bankPairNR, bankMemoryNRW, bankCell,
      hrepair, hlo, hhi, hx, ht,
      Id.run_pure, Id.run_bind,
      apply_ite Id.run, apply_ite Prod.fst,
      apply_ite BankCell.tok, ite_self]

theorem bankCountEligibleRepairTransport {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e root : Fin n) (j : Nat)
    (hx : (r.1 e).pack.val ≠ 0)
    (hrepair : packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (bankCountWidth n) ≠
      (r.1 (ring.rightNeighbor e)).pack.val)
    (hne : root ≠ e)
    (hnd : root ≠ ring.rightNeighbor e)
    (hj : EligibleAt ring r root j) :
    EligibleAt ring (renewalBankNext ring r e) root j ∧
      ((renewalBankNext ring r e).1
        (Counter.site ring root j)).tok =
      (r.1 (Counter.site ring root j)).tok := by
  have havoid : ∀ k : Nat, k ≤ j →
      Counter.site ring root k ≠ ring.rightNeighbor e := by
    intro k hk
    cases k with
    | zero =>
        exact hnd
    | succ k =>
        exact Ne.symm
          (bankCountRepairAvoidsPositivePrefix
            ring r e root j hj hrepair (k + 1) (by omega) hk)
  have hpack := rbBankReferencePairPack ring (by omega : 2 ≤ n) r e
  have htrip := bankWindowClosureSelectedBankTrip ring hn hbank r e
  simp only [Counter.resetAgentBankTrip, Counter.resetCellBankTrip,
    Prod.mk.injEq] at htrip
  have hframe := rbReferenceSelectedPairFrame
    ring (by omega : 2 ≤ n) r e
  have hworker := congrArg
    (fun q : RenewalBankSite n => q.worker) hframe.2.2.1
  have hread : ∀ k : Nat, k ≤ j →
      ((renewalBankNext ring r e).1
        (Counter.site ring root k)).pack.val =
        (r.1 (Counter.site ring root k)).pack.val ∧
      ((renewalBankNext ring r e).1
        (Counter.site ring root k)).tok =
        (r.1 (Counter.site ring root k)).tok ∧
      ((renewalBankNext ring r e).2.sites
        (Counter.site ring root k)).worker =
        (r.2.sites (Counter.site ring root k)).worker := by
    intro k hk
    by_cases hke : Counter.site ring root k = e
    · have hrole : (r.1 e).pack.val = k := by
        rw [← hke]
        exact hj.roles k hk
      have hkn : k ≠ 0 := by
        intro hz
        exact hx (hrole.trans hz)
      have hkpos : 1 ≤ k := by omega
      have htok : (r.1 e).tok = .E ∨
          (r.1 e).tok = .RR ∨ (r.1 e).tok = .RL := by
        by_cases hkj : k = j
        · have ht := hj.resetToken
          rw [← hkj, hke] at ht
          exact Or.inr ht
        · apply Or.inl
          rw [← hke]
          exact hj.emptyPrefix k hkpos (by omega)
      have hc := bankCountRepairSourceCells
        r.2 e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))
        (by omega)
        (by
          change (r.1 e).pack.val ≤ bankCountWidth n
          have hw := hj.leWidth
          omega)
        hrepair htok
      rw [hke]
      exact ⟨hpack.1, htrip.1.2.2.trans hc.1,
        hworker.trans hc.2⟩
    · have hf := renewalBankNextTwoSiteFrame
        ring r e (Counter.site ring root k) hke (havoid k hk)
      refine ⟨?_, ?_, ?_⟩
      · rw [hf.1]
      · rw [hf.1]
      · rw [hf.2]
  have hroot := renewalBankNextTwoSiteFrame ring r e root hne hnd
  refine ⟨?_, (hread j (Nat.le_refl j)).2.1⟩
  refine {
    rootRole := ?_
    rootMode := ?_
    currentWait := ?_
    positive := hj.positive
    leWidth := hj.leWidth
    roles := ?_
    emptyPrefix := ?_
    pending := ?_
    resetToken := ?_ }
  · rw [hroot.1]
    exact hj.rootRole
  · rw [hroot.1]
    exact hj.rootMode
  · rw [hroot.2]
    exact hj.currentWait
  · intro k hk
    exact (hread k hk).1.trans (hj.roles k hk)
  · intro k hk hkj
    exact (hread k (by omega)).2.1.trans
      (hj.emptyPrefix k hk hkj)
  · obtain ⟨rho, hw, hown⟩ := hj.pending
    exact ⟨rho, (hread j (Nat.le_refl j)).2.2.trans hw, hown⟩
  · rcases hj.resetToken with ht | ht
    · exact Or.inl ((hread j (Nat.le_refl j)).2.1.trans ht)
    · exact Or.inr ((hread j (Nat.le_refl j)).2.1.trans ht)

/-- A POST eligible root cannot be the nonroot source or the repaired
responder. Its framed root fields and the OLD slot invariant produce
the OLD frontier needed to exclude newly uncovered credit. -/
theorem bankCountRootCreditLeOfNonrootRepair {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hs : BankSlotInv ring r)
    (hx : (r.1 e).pack.val ≠ 0)
    (hrepair : packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (bankCountWidth n) ≠
      (r.1 (ring.rightNeighbor e)).pack.val)
    (root : Fin n) :
    bankCountRootCredit ring (renewalBankNext ring r e) root ≤
      bankCountRootCredit ring r root := by
  classical
  by_cases hex : ∃ j : Nat,
      EligibleAt ring (renewalBankNext ring r e) root j
  · obtain ⟨j, hj⟩ := hex
    have hpack := bankCountPairPackNext
      ring (by omega : 2 ≤ n) r e
    have hne : root ≠ e := by
      intro heq
      apply hx
      have hz := hj.rootRole
      rw [heq, hpack.1] at hz
      exact hz
    have hframe := rbReferenceSelectedPairFrame
      ring (by omega : 2 ≤ n) r e
    have hctl :
        ((renewalBankNext ring r e).2.sites
          (ring.rightNeighbor e)).controller = .empty := by
      exact
        (congrArg (fun q : RenewalBankSite n => q.controller)
          hframe.2.2.2).trans
        (bankWindowJointResponderChangedControllerEmpty
          (compileAdvice (ceilLogTwo n)) r.2
          e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e)) hrepair)
    have hnd : root ≠ ring.rightNeighbor e := by
      intro heq
      have hw := hj.currentWait
      rw [heq, hctl] at hw
      cases hw
    have hf := renewalBankNextTwoSiteFrame ring r e root hne hnd
    have hrole : (r.1 root).pack.val = 0 := by
      rw [← hf.1]
      exact hj.rootRole
    have hmode : (r.1 root).mode = .RWAIT := by
      rw [← hf.1]
      exact hj.rootMode
    have hwait : (r.2.sites root).controller = .waiting [] := by
      rw [← hf.2]
      exact hj.currentWait
    obtain ⟨k, hk⟩ := hs.generated root hrole hmode hwait
    obtain ⟨hk', htok⟩ := bankCountEligibleRepairTransport
      ring hn hbank r e root k hx hrepair hne hnd hk.toEligibleAt
    rw [bankCountRootCreditEq
        ring (renewalBankNext ring r e) root k hk',
      bankCountRootCreditEq ring r root k hk.toEligibleAt, htok]
    exact Nat.le_refl _
  · rw [bankCountRootCreditZeroOfNoEligible
      ring (renewalBankNext ring r e) root hex]
    exact Nat.zero_le _

theorem bankCountPotentialStepOfNonrootRepair {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hr : BankCountInv ring r)
    (hs : BankSlotInv ring r)
    (hs' : BankSlotInv ring (renewalBankNext ring r e))
    (hnb : renewalBankBirth ring r.1 r.2 e = none)
    (hx : (r.1 e).pack.val ≠ 0)
    (hrepair : packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (bankCountWidth n) ≠
      (r.1 (ring.rightNeighbor e)).pack.val) :
    bankCountPsi ring (renewalBankNext ring r e) ≤
      bankCountPsi ring r +
        (if bankCountNom ring r e then 1 else 0) := by
  have hmono := bankCountRootCreditLeOfNonrootRepair
    ring hn hbank r e hs hx hrepair
  have hp := bankCountPsiLeOfSingleRoot
    ring r (renewalBankNext ring r e) e 0 0
    (fun other _ => hmono other)
    (by simpa only [Nat.add_zero] using hmono e)
  simp only [Nat.add_zero] at hp
  exact Nat.le_trans hp (Nat.le_add_right _ _)

/-- Class three, including a repaired responder behind a root source. -/
theorem bankCountPotentialStepOfRepair {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hr : BankCountInv ring r)
    (hs : BankSlotInv ring r)
    (hs' : BankSlotInv ring (renewalBankNext ring r e))
    (hnb : renewalBankBirth ring r.1 r.2 e = none)
    (hrepair : packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (bankCountWidth n) ≠
      (r.1 (ring.rightNeighbor e)).pack.val) :
    bankCountPsi ring (renewalBankNext ring r e) ≤
      bankCountPsi ring r +
        (if bankCountNom ring r e then 1 else 0) := by
  by_cases hx : (r.1 e).pack.val = 0
  · exact Nat.le_trans
      (bankCountPsiLeOfRootSource ring hn hbank r e hr hs hx)
      (Nat.le_add_right _ _)
  · exact bankCountPotentialStepOfNonrootRepair
      ring hn hbank r e hr hs hs' hnb hx hrepair

/-! Stable rows: read masks and the exhaustive no-move case. -/

theorem bankCountStablePackFrame {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (hstable : packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val (bankCountWidth n) =
      (r.1 (ring.rightNeighbor e)).pack.val) :
    ∀ i : Fin n, ((renewalBankNext ring r e).1 i).pack.val =
      (r.1 i).pack.val := by
  have hp := rbBankReferencePairPack ring (by omega : 2 ≤ n) r e
  intro i
  by_cases he : i = e
  · subst i
    exact hp.1
  · by_cases hd : i = ring.rightNeighbor e
    · subst i
      exact hp.2.trans hstable
    · exact congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.pack.val)
        (renewalBankNextTwoSiteFrame ring r e i he hd).1

theorem bankCountWaitSlotWaitingPreimage {n : Nat}
    (mode : Mode) (lease : Nat) (controller : RenewalBankController n)
    (h : renewalBankWaitSlot mode lease controller = .waiting []) :
    controller = .waiting [] := by
  unfold renewalBankWaitSlot at h
  split at h
  · split at h
    · exact h
    · cases h
  · exact h

theorem bankCountStablePostEligibleRootFields {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e root : Fin n) (depth : Nat)
    (hnonroot : (r.1 e).pack.val ≠ 0)
    (hstable : packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val (bankCountWidth n) =
      (r.1 (ring.rightNeighbor e)).pack.val)
    (hd : EligibleAt ring (renewalBankNext ring r e) root depth) :
    (r.1 root).pack.val = 0 ∧
      (r.1 root).mode = .RWAIT ∧
      (r.2.sites root).controller = .waiting [] := by
  have hp := bankCountStablePackFrame ring hn r e hstable
  have hrole : (r.1 root).pack.val = 0 :=
    (hp root).symm.trans hd.rootRole
  have hne : root ≠ e := by
    intro he
    rw [he] at hrole
    exact hnonroot hrole
  refine ⟨hrole, ?_⟩
  by_cases hdest : root = ring.rightNeighbor e
  · subst root
    have hmode :
        ((renewalBankNext ring r e).1 (ring.rightNeighbor e)).mode =
          (r.1 (ring.rightNeighbor e)).mode := by
      rcases bankWindowJointIncomingModeKeepOrReset ring hn hbank r e
          hrole hd.rootRole with hkeep | hreset
      · exact hkeep
      · rw [hd.rootMode] at hreset
        cases hreset
    have hframe := rbReferenceSelectedPairFrame
      ring (by omega : 2 ≤ n) r e
    have hcontroller := congrArg
      (fun s : RenewalBankSite n => s.controller) hframe.2.2.2
    have hraw :
        (renewalBankPairMemory (compileAdvice (ceilLogTwo n)) r.2
          e (ring.rightNeighbor e) (r.1 e)
          (r.1 (ring.rightNeighbor e))).2.controller = .waiting [] :=
      hcontroller.symm.trans hd.currentWait
    have hwait : (r.2.sites (ring.rightNeighbor e)).controller =
        .waiting [] := by
      rcases bankWindowJointResponderZeroControllerSlot
          (compileAdvice (ceilLogTwo n)) r.2 e
          (ring.rightNeighbor e) (r.1 e)
          (r.1 (ring.rightNeighbor e)) hnonroot hrole
          (hstable.trans hrole) with hempty | hslot
      · rw [hempty] at hraw
        cases hraw
      · exact bankCountWaitSlotWaitingPreimage
          (r.1 (ring.rightNeighbor e)).mode
          (r.1 (ring.rightNeighbor e)).lease.val
          (r.2.sites (ring.rightNeighbor e)).controller
          (hslot.symm.trans hraw)
    exact ⟨hmode.symm.trans hd.rootMode, hwait⟩
  · have hf := renewalBankNextTwoSiteFrame ring r e root hne hdest
    constructor
    · rw [← hf.1]
      exact hd.rootMode
    · rw [← hf.2]
      exact hd.currentWait

/-- These predicates identify actual advancing/returning rows carrying
an OLD eligible frontier. The residual includes moving tokens that do
not carry an eligible frontier. -/
def BankCountAdvanceRow {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n) (e : Fin n) : Prop :=
  ∃ (root : Fin n) (j : Nat),
    EligibleAt ring r root j ∧
    j < bankCountWidth n ∧
    (r.1 (Counter.site ring root j)).tok = .RR ∧
    e = Counter.site ring root j ∧
    (r.1 (ring.rightNeighbor e)).pack.val = j + 1

def BankCountBackRow {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n) (e : Fin n) : Prop :=
  ∃ (root : Fin n) (k : Nat),
    1 ≤ k ∧ EligibleAt ring r root (k + 1) ∧
    e = Counter.site ring root k ∧
    ((r.1 (Counter.site ring root (k + 1))).tok = .RL ∨
      ((r.1 (Counter.site ring root (k + 1))).tok = .RR ∧
        k + 1 = bankCountWidth n))

theorem bankCountPairReadFrame {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n) (e : Fin n)
    (hpair : ∀ i : Fin n, (i = e ∨ i = ring.rightNeighbor e) →
      bankWindowReadTok r (renewalBankNext ring r e) i ∧
      bankWindowReadBit r (renewalBankNext ring r e) i ∧
      bankWindowReadWorker r (renewalBankNext ring r e) i) :
    ∀ i : Fin n,
      ((renewalBankNext ring r e).1 i).tok = (r.1 i).tok ∧
      ((renewalBankNext ring r e).2.sites i).worker =
        (r.2.sites i).worker := by
  intro i
  by_cases he : i = e
  · have h := hpair i (Or.inl he)
    exact ⟨h.1, h.2.2⟩
  · by_cases hd : i = ring.rightNeighbor e
    · have h := hpair i (Or.inr hd)
      exact ⟨h.1, h.2.2⟩
    · have hf := renewalBankNextTwoSiteFrame ring r e i he hd
      exact ⟨congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok) hf.1,
        congrArg (fun s : RenewalBankSite n => s.worker) hf.2⟩

/-- On a stable nonroot row that is neither an eligible advance nor an
eligible inward/top move, every OLD slot keeps the token reads through
its frontier and that frontier's worker. Root mode/controller reads
are deliberately not asserted here: an incoming root service can
expire its lease. -/
theorem bankCountStableNoMovePrefixReads {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e root : Fin n) (j : Nat)
    (hJ : BankWindowExact ring r)
    (hs : BankSlotAt ring r root j)
    (hnonroot : (r.1 e).pack.val ≠ 0)
    (hstable : packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val (bankCountWidth n) =
      (r.1 (ring.rightNeighbor e)).pack.val)
    (hnoAdvance : ¬ BankCountAdvanceRow ring r e)
    (hnoBack : ¬ BankCountBackRow ring r e) :
    (∀ a : Nat, 1 ≤ a → a ≤ j →
      ((renewalBankNext ring r e).1 (Counter.site ring root a)).tok =
        (r.1 (Counter.site ring root a)).tok) ∧
    ((renewalBankNext ring r e).2.sites
        (Counter.site ring root j)).worker =
      (r.2.sites (Counter.site ring root j)).worker := by
  classical
  have hj := hs.toEligibleAt
  have hjpos := hj.positive
  have hjb := hj.leWidth
  have hfinish :
      (∀ i : Fin n,
        ((renewalBankNext ring r e).1 i).tok = (r.1 i).tok ∧
        ((renewalBankNext ring r e).2.sites i).worker =
          (r.2.sites i).worker) →
      (∀ a : Nat, 1 ≤ a → a ≤ j →
        ((renewalBankNext ring r e).1 (Counter.site ring root a)).tok =
          (r.1 (Counter.site ring root a)).tok) ∧
      ((renewalBankNext ring r e).2.sites
          (Counter.site ring root j)).worker =
        (r.2.sites (Counter.site ring root j)).worker := by
    intro hreads
    exact ⟨fun a _ _ => (hreads (Counter.site ring root a)).1,
      (hreads (Counter.site ring root j)).2⟩
  by_cases hhit : ∃ k : Nat, k ≤ j ∧ e = Counter.site ring root k
  · obtain ⟨k, hkj, he⟩ := hhit
    have hx : (r.1 e).pack.val = k := by
      rw [he]
      exact hj.roles k hkj
    have hk : 1 ≤ k := by
      by_cases hkz : k = 0
      · exact False.elim (hnonroot (hx.trans hkz))
      · omega
    have hdest : ring.rightNeighbor e =
        Counter.site ring root (k + 1) := by
      rw [he]
      rfl
    by_cases hbefore : k < j
    · have hbelow : k < bankCountWidth n := by omega
      have hy : (r.1 (ring.rightNeighbor e)).pack.val = k + 1 := by
        rw [hdest]
        exact hj.roles (k + 1) (by omega)
      have hxe : (r.1 e).tok = .E := by
        rw [he]
        exact hj.emptyPrefix k hk hbefore
      by_cases hstrict : k + 1 < j
      · have hye : (r.1 (ring.rightNeighbor e)).tok = .E := by
          rw [hdest]
          exact hj.emptyPrefix (k + 1) (by omega) hstrict
        apply hfinish
        exact bankCountPairReadFrame ring r e
          (bankWindowJointIdlePairReads ring hn hbank r e hJ
            hnonroot hstable hxe hye)
      · have hdepth : j = k + 1 := by omega
        have hfront : EligibleAt ring r root (k + 1) := by
          simpa only [hdepth] using hj
        have hnotmove :
            ¬ ((r.1 (Counter.site ring root (k + 1))).tok = .RL ∨
              ((r.1 (Counter.site ring root (k + 1))).tok = .RR ∧
                k + 1 = bankCountWidth n)) := by
          intro hm
          exact hnoBack ⟨root, k, hk, hfront, he, hm⟩
        have hrr : (r.1 (ring.rightNeighbor e)).tok = .RR := by
          rcases hfront.resetToken with hrr | hrl
          · rw [hdest]
            exact hrr
          · exact False.elim (hnotmove (Or.inl hrl))
        have hnotTop : k + 1 ≠ bankCountWidth n := by
          intro htop
          apply hnotmove
          right
          refine ⟨?_, htop⟩
          rw [← hdest]
          exact hrr
        apply hfinish
        exact bankCountPairReadFrame ring r e
          (bankWindowOverlapStableCellsUnchangedReads ring hn hbank r e
            (bankWindowJointAlignedQuietWaitCells r.2 e
              (ring.rightNeighbor e) (r.1 e)
              (r.1 (ring.rightNeighbor e)) k hk hbelow hx hy
              (Or.inr ⟨hxe, Or.inl hrr, hnotTop⟩)))
    · have hkjEq : k = j := by omega
      have hsym := hkjEq.symm
      subst hsym
      by_cases hbelow : j < bankCountWidth n
      · have hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1 := by
          have hh := hstable
          rw [hx] at hh
          simpa [packNext, hbelow] using hh.symm
        have hrl : (r.1 (Counter.site ring root j)).tok = .RL := by
          rcases hj.resetToken with hrr | hrl
          · exact False.elim
              (hnoAdvance ⟨root, j, hj, hbelow, hrr, he, hy⟩)
          · exact hrl
        have hye : (r.1 (ring.rightNeighbor e)).tok = .E := by
          rcases hs.phase with hrrPhase | hrlPhase
          · have hbad := hrrPhase.1
            rw [hrl] at hbad
            cases hbad
          · rw [hdest]
            exact hrlPhase.2.2.2 (j + 1) (by omega) (by omega) (by omega)
        have hxl : (r.1 e).tok = .RL := by
          rw [he]
          exact hrl
        apply hfinish
        exact bankCountPairReadFrame ring r e
          (bankWindowOverlapStableCellsUnchangedReads ring hn hbank r e
            (bankWindowJointAlignedQuietWaitCells r.2 e
              (ring.rightNeighbor e) (r.1 e)
              (r.1 (ring.rightNeighbor e)) j hk hbelow hx hy
              (Or.inl ⟨Or.inl hxl, hye⟩)))
      · have htop : j = bankCountWidth n := by omega
        have htopSource : (r.1 e).pack.val = bankCountWidth n :=
          hx.trans htop
        have hnoIR : (r.1 e).tok ≠ .IR := by
          intro h
          rw [he] at h
          rcases hj.resetToken with ht | ht <;>
            rw [ht] at h <;> cases h
        have hreads := bankWindowOverlapTopGhostStableSourceReads
          ring hn hbank r e htopSource hstable hnoIR
        have hdestRole :
            (r.1 (ring.rightNeighbor e)).pack.val = 0 ∨
            (r.1 (ring.rightNeighbor e)).pack.val = bankCountWidth n + 1 := by
          rcases bankWindowJointStableEdgeShape (r.1 e).pack.val
              (r.1 (ring.rightNeighbor e)).pack.val
              (bankCountWidth n) hstable with hh | hh | hh
          · have hbad := hh.1
            rw [htopSource] at hbad
            omega
          · exact hh.2
          · have hbad := hh.1
            rw [htopSource] at hbad
            omega
        have hdifferent : ∀ a : Nat, 1 ≤ a → a ≤ j →
            Counter.site ring root a ≠ ring.rightNeighbor e := by
          intro a ha haj hsite
          have hrole := hj.roles a haj
          rw [hsite] at hrole
          rcases hdestRole with hz | hz <;> rw [hz] at hrole <;> omega
        constructor
        · intro a ha haj
          by_cases hae : Counter.site ring root a = e
          · rw [hae]
            exact hreads.2.1
          · exact congrArg (fun x : Agent (compileAdvice (ceilLogTwo n)) => x.tok)
              (renewalBankNextTwoSiteFrame ring r e
                (Counter.site ring root a) hae
                (hdifferent a ha haj)).1
        · rw [← he]
          exact hreads.2.2.2
  · have hoffE : ∀ a : Nat, a ≤ j →
        Counter.site ring root a ≠ e := by
      intro a haj hsite
      exact hhit ⟨a, haj, hsite.symm⟩
    have hoffD : ∀ a : Nat, 1 ≤ a → a ≤ j →
        Counter.site ring root a ≠ ring.rightNeighbor e := by
      intro a ha haj hsite
      cases a with
      | zero => omega
      | succ a =>
          apply hoffE a (by omega)
          apply bankCountRightInjective ring
          exact hsite
    constructor
    · intro a ha haj
      exact congrArg (fun x : Agent (compileAdvice (ceilLogTwo n)) => x.tok)
        (renewalBankNextTwoSiteFrame ring r e
          (Counter.site ring root a) (hoffE a haj)
          (hoffD a ha haj)).1
    · exact congrArg (fun s : RenewalBankSite n => s.worker)
        (renewalBankNextTwoSiteFrame ring r e
          (Counter.site ring root j) (hoffE j (Nat.le_refl j))
          (hoffD j hjpos (Nat.le_refl j))).2

theorem bankCountRootCreditLeOfOtherRows {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hr : BankCountInv ring r) (hs : BankSlotInv ring r)
    (hnonroot : (r.1 e).pack.val ≠ 0)
    (hstable : packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val (bankCountWidth n) =
      (r.1 (ring.rightNeighbor e)).pack.val)
    (hnoAdvance : ¬ BankCountAdvanceRow ring r e)
    (hnoBack : ¬ BankCountBackRow ring r e)
    (root : Fin n) :
    bankCountRootCredit ring (renewalBankNext ring r e) root ≤
      bankCountRootCredit ring r root := by
  classical
  by_cases hpost : ∃ depth : Nat,
      EligibleAt ring (renewalBankNext ring r e) root depth
  · obtain ⟨depth, hd⟩ := hpost
    obtain ⟨hrole, hmode, hwait⟩ :=
      bankCountStablePostEligibleRootFields ring hn hbank r e root depth
        hnonroot hstable hd
    obtain ⟨j, hj⟩ := hs.generated root hrole hmode hwait
    have hJ : BankWindowExact ring r := by
      obtain ⟨seed, pre, _, _, hJ⟩ := hr
      exact hJ
    obtain ⟨htokens, hworker⟩ :=
      bankCountStableNoMovePrefixReads ring hn hbank r e root j hJ hj
        hnonroot hstable hnoAdvance hnoBack
    have hpack := bankCountStablePackFrame ring hn r e hstable
    have helig := bankCountEligibleReadTransport ring r
      (renewalBankNext ring r e) root j hj.toEligibleAt
      (fun k _ => hpack (Counter.site ring root k))
      (hd.rootMode.trans hmode.symm)
      (hd.currentWait.trans hwait.symm) htokens hworker
    rw [bankCountRootCreditEq ring (renewalBankNext ring r e) root j helig,
      bankCountRootCreditEq ring r root j hj.toEligibleAt,
      htokens j hj.toEligibleAt.positive (Nat.le_refl j)]
    exact Nat.le_refl _
  · rw [bankCountRootCreditZeroOfNoEligible
      ring (renewalBankNext ring r e) root hpost]
    exact Nat.zero_le _

theorem bankCountPotentialStepOfOtherRows {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hr : BankCountInv ring r)
    (hs : BankSlotInv ring r)
    (hs' : BankSlotInv ring (renewalBankNext ring r e))
    (hnb : renewalBankBirth ring r.1 r.2 e = none)
    (hnonroot : (r.1 e).pack.val ≠ 0)
    (hstable : packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val (bankCountWidth n) =
      (r.1 (ring.rightNeighbor e)).pack.val)
    (hnoAdvance : ¬ BankCountAdvanceRow ring r e)
    (hnoBack : ¬ BankCountBackRow ring r e) :
    bankCountPsi ring (renewalBankNext ring r e) ≤
      bankCountPsi ring r + (if bankCountNom ring r e then 1 else 0) := by
  have hsum : bankCountPsi ring (renewalBankNext ring r e) ≤
      bankCountPsi ring r := by
    unfold bankCountPsi
    apply ofFn_sum_le
    intro root
    exact bankCountRootCreditLeOfOtherRows ring hn hbank r e hr hs
      hnonroot hstable hnoAdvance hnoBack root
  exact Nat.le_trans hsum (Nat.le_add_right _ _)

/-! Exhaustive assembly. Repair is tested first, so a stable
role-zero source necessarily has old responder role one. -/

theorem bankCountPotentialStepOfNoBirth {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hr : BankCountInv ring r)
    (hs : BankSlotInv ring r)
    (hs' : BankSlotInv ring (renewalBankNext ring r e))
    (hnb : renewalBankBirth ring r.1 r.2 e = none) :
    bankCountPsi ring (renewalBankNext ring r e) ≤
      bankCountPsi ring r + (if bankCountNom ring r e then 1 else 0) := by
  classical
  by_cases hstable : packNext (r.1 e).pack.val
      (r.1 (ring.rightNeighbor e)).pack.val (bankCountWidth n) =
    (r.1 (ring.rightNeighbor e)).pack.val
  · by_cases hx : (r.1 e).pack.val = 0
    · have hb : 0 < bankCountWidth n := by
        change 0 < (compileAdvice (ceilLogTwo n)).s + 11
        omega
      have hy : (r.1 (ring.rightNeighbor e)).pack.val = 1 := by
        have hp := hstable
        rw [hx] at hp
        simpa [packNext, hb] using hp.symm
      exact bankCountPotentialStepOfRootSource
        ring hn hbank r e hr hs hs' hnb hx hy
    · by_cases ha : BankCountAdvanceRow ring r e
      · obtain ⟨root, j, hj, hbelow, ht, he, hy⟩ := ha
        exact bankCountPotentialStepOfAdvance
          ring hn hbank r e hr hs hs' hnb root j hj hbelow ht he hy
      · by_cases hb : BankCountBackRow ring r e
        · obtain ⟨root, k, hk, hj, he, hmove⟩ := hb
          exact bankCountPotentialStepOfBack
            ring hn hbank r e hr hs hs' hnb root k hk hj he hmove
        · exact bankCountPotentialStepOfOtherRows
            ring hn hbank r e hr hs hs' hnb hx hstable ha hb
  · exact bankCountPotentialStepOfRepair
      ring hn hbank r e hr hs hs' hnb hstable

/-- U3b, with the requested explicit OLD and POST slot hypotheses.
The birth branch is the already installed Q4678 theorem. -/
theorem bankCountPotentialStepOfSlots {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hr : BankCountInv ring r)
    (hs : BankSlotInv ring r)
    (hs' : BankSlotInv ring (renewalBankNext ring r e)) :
    bankCountPsi ring (renewalBankNext ring r e) +
        (bankCountWidth n - bankCountHalf n) *
          (renewalBankSpawn ring r e).length ≤
      bankCountPsi ring r + (if bankCountNom ring r e then 1 else 0) := by
  classical
  cases hb : renewalBankBirth ring r.1 r.2 e with
  | none =>
      have h := bankCountPotentialStepOfNoBirth
        ring hn hbank r e hr hs hs' hb
      simpa only [renewalBankSpawn, hb, List.length_nil,
        Nat.mul_zero, Nat.add_zero] using h
  | some o =>
      exact bankCountPotentialStepOfBirth ring hn hbank r e o hr hb

/-
Outside this round, no declarations are supplied here for
bankSlotInvNext, bankCountPotentialStep, or the unconditional
headline theorem. This append proves neither slot preservation
nor the historical uninterrupted-current-slot obligation U1.
-/

end L3.Prime

#print axioms L3.Prime.bankCountPotentialStepOfRootSource
#print axioms L3.Prime.bankCountPotentialStepOfAdvance
#print axioms L3.Prime.bankCountPotentialStepOfRepair
#print axioms L3.Prime.bankCountPotentialStepOfBack
#print axioms L3.Prime.bankCountPotentialStepOfOtherRows
#print axioms L3.Prime.bankCountPotentialStepOfNoBirth
#print axioms L3.Prime.bankCountPotentialStepOfSlots

namespace L3.Prime

open L3.HeadlineRenewal
open L3.HeadlineRenewalCleanBank
open L3.RenewalReferenceClock
open L3.BankWindow
open Classical

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 8000000


/-- Bridge from the existing singleton-run frame lemmas. -/
theorem bankSlotSingletonRun {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n) (e : Fin n) :
    rbRun ring r [e] = renewalBankNext ring r e := by
  rfl

/-- Only the selected endpoints can change their physical agent or
ghost site record. The global service clock is not framed. -/
theorem bankSlotNextOutsideFrame {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e x : Fin n) (hx : x ≠ e) (hy : x ≠ ring.rightNeighbor e) :
    (renewalBankNext ring r e).1 x = r.1 x ∧
      (renewalBankNext ring r e).2.sites x = r.2.sites x := by
  simpa only [bankSlotSingletonRun] using
    (rbReferenceOutsideSiteFrame ring r e x hx hy)

theorem bankSlotNextSourceFrame {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n) (e : Fin n) :
    (renewalBankNext ring r e).1 e =
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalBankCut ring r.1 r.2 e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).1 ∧
      (renewalBankNext ring r e).2.sites e =
        (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
          r.2 e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).1 := by
  simpa only [bankSlotSingletonRun] using
    (rbReferenceSourcePairFrame ring r e)

theorem bankSlotNextResponderFrame {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n) :
    (renewalBankNext ring r e).1 (ring.rightNeighbor e) =
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalBankCut ring r.1 r.2 e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).2 ∧
      (renewalBankNext ring r e).2.sites (ring.rightNeighbor e) =
        (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
          r.2 e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).2 := by
  have hne : e ≠ ring.rightNeighbor e :=
    Ne.symm (Counter.resetRootPortDistinct ring e hn)
  simpa only [bankSlotSingletonRun] using
    (rbReferenceResponderPairFrame ring r e hne)

/-- A physical site has at most one owner among windows that label
the site by its actual role. -/
theorem bankSlotLabelledOwnerUnique {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (x root other : Fin n) (k l : Nat)
    (hroot : x = Counter.site ring root k)
    (hother : x = Counter.site ring other l)
    (hk : (r.1 x).pack.val = k)
    (hl : (r.1 x).pack.val = l) :
    root = other := by
  have hkl : k = l := hk.symm.trans hl
  have hotherAtK : x = Counter.site ring other k :=
    hother.trans
      (congrArg (fun t : Nat => Counter.site ring other t) hkl.symm)
  exact bankCountSiteRootInjective ring k
    (hroot.symm.trans hotherAtK)

/-- Framing the correctly labelled footprint transfers a slot.
Outward slots read only their prefix; returning slots read 0..b. -/
theorem bankSlotAtOfLabelledFrame {n : Nat}
    (ring : DirectedRing n) (r s : RenewalBankReference n)
    (root : Fin n) (j : Nat) (hj : BankSlotAt ring r root j)
    (hframe : ∀ k : Nat, k ≤ bankCountWidth n →
      (r.1 (Counter.site ring root k)).pack.val = k →
      s.1 (Counter.site ring root k) =
          r.1 (Counter.site ring root k) ∧
        s.2.sites (Counter.site ring root k) =
          r.2.sites (Counter.site ring root k)) :
    BankSlotAt ring s root j := by
  have hprefix : ∀ k : Nat, k ≤ j →
      s.1 (Counter.site ring root k) =
          r.1 (Counter.site ring root k) ∧
        s.2.sites (Counter.site ring root k) =
          r.2.sites (Counter.site ring root k) := by
    intro k hk
    exact hframe k (Nat.le_trans hk hj.toEligibleAt.leWidth)
      (hj.toEligibleAt.roles k hk)
  have hrootPhysical : s.1 root = r.1 root :=
    (hprefix 0 (Nat.zero_le j)).1
  have hrootGhost : s.2.sites root = r.2.sites root :=
    (hprefix 0 (Nat.zero_le j)).2
  have hfrontPhysical :
      s.1 (Counter.site ring root j) = r.1 (Counter.site ring root j) :=
    (hprefix j (Nat.le_refl j)).1
  have hfrontGhost :
      s.2.sites (Counter.site ring root j) = r.2.sites (Counter.site ring root j) :=
    (hprefix j (Nat.le_refl j)).2
  refine { toEligibleAt := ?_, phase := ?_ }
  · refine {
      rootRole := ?_
      rootMode := ?_
      currentWait := ?_
      positive := hj.toEligibleAt.positive
      leWidth := hj.toEligibleAt.leWidth
      roles := ?_
      emptyPrefix := ?_
      pending := ?_
      resetToken := ?_ }
    · rw [hrootPhysical]
      exact hj.toEligibleAt.rootRole
    · rw [hrootPhysical]
      exact hj.toEligibleAt.rootMode
    · rw [hrootGhost]
      exact hj.toEligibleAt.currentWait
    · intro k hk
      rw [(hprefix k hk).1]
      exact hj.toEligibleAt.roles k hk
    · intro k hk hkj
      rw [(hprefix k (Nat.le_of_lt hkj)).1]
      exact hj.toEligibleAt.emptyPrefix k hk hkj
    · obtain ⟨rho, hw, howner⟩ := hj.toEligibleAt.pending
      exact ⟨rho, by rw [hfrontGhost]; exact hw, howner⟩
    · rw [hfrontPhysical]
      exact hj.toEligibleAt.resetToken
  · rcases hj.phase with hout | hin
    · left
      constructor
      · rw [hfrontPhysical]
        exact hout.1
      · intro k hk hkj rho
        rw [(hprefix k (Nat.le_of_lt hkj)).2]
        exact hout.2 k hk hkj rho
    · right
      refine ⟨hin.1, ?_, ?_, ?_⟩
      · rw [hfrontPhysical]
        exact hin.2.1
      · intro k hk
        rw [(hframe k hk (hin.2.2.1 k hk)).1]
        exact hin.2.2.1 k hk
      · intro k hk hkb hkj
        rw [(hframe k hkb (hin.2.2.1 k hkb)).1]
        exact hin.2.2.2 k hk hkb hkj

theorem bankSlotAtNextOfUntouchedOwner {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (root e : Fin n) (j : Nat) (hj : BankSlotAt ring r root j)
    (hsource : ¬ ∃ k : Nat,
      k ≤ bankCountWidth n ∧ e = Counter.site ring root k ∧
        (r.1 e).pack.val = k)
    (hresponder : ¬ ∃ k : Nat,
      k ≤ bankCountWidth n ∧
        ring.rightNeighbor e = Counter.site ring root k ∧
        (r.1 (ring.rightNeighbor e)).pack.val = k) :
    BankSlotAt ring (renewalBankNext ring r e) root j := by
  apply bankSlotAtOfLabelledFrame ring r
    (renewalBankNext ring r e) root j hj
  intro k hkb hrole
  apply bankSlotNextOutsideFrame ring r e (Counter.site ring root k)
  · intro h
    apply hsource
    refine ⟨k, hkb, h.symm, ?_⟩
    exact
      (congrArg (fun x : Fin n => (r.1 x).pack.val) h).symm.trans hrole
  · intro h
    apply hresponder
    refine ⟨k, hkb, h.symm, ?_⟩
    exact
      (congrArg (fun x : Fin n => (r.1 x).pack.val) h).symm.trans hrole


/-- Ownership here includes the actual role at the physical endpoint. -/
def BankSlotOwnsSite {n : Nat} (ring : DirectedRing n)
    (r : RenewalBankReference n) (root x : Fin n) : Prop :=
  ∃ k : Nat, k ≤ bankCountWidth n ∧
    x = Counter.site ring root k ∧ (r.1 x).pack.val = k

theorem bankSlotOwnsSiteUnique {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (x a b : Fin n)
    (ha : BankSlotOwnsSite ring r a x)
    (hb : BankSlotOwnsSite ring r b x) :
    a = b := by
  obtain ⟨k, _, hka, hk⟩ := ha
  obtain ⟨l, _, hlb, hl⟩ := hb
  exact bankSlotLabelledOwnerUnique ring r x a b k l hka hlb hk hl

/-- Among three roots whose labelled windows touch the selected
pair, two must coincide. Thus the pair has at most two owners. -/
theorem bankSlotTouchedRootsAtMostTwo {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e a b c : Fin n)
    (ha : BankSlotOwnsSite ring r a e ∨
      BankSlotOwnsSite ring r a (ring.rightNeighbor e))
    (hb : BankSlotOwnsSite ring r b e ∨
      BankSlotOwnsSite ring r b (ring.rightNeighbor e))
    (hc : BankSlotOwnsSite ring r c e ∨
      BankSlotOwnsSite ring r c (ring.rightNeighbor e)) :
    a = b ∨ a = c ∨ b = c := by
  rcases ha with ha | ha <;>
    rcases hb with hb | hb <;>
    rcases hc with hc | hc
  all_goals
    first
    | exact Or.inl (bankSlotOwnsSiteUnique ring r _ a b ha hb)
    | exact Or.inr (Or.inl (bankSlotOwnsSiteUnique ring r _ a c ha hc))
    | exact Or.inr (Or.inr (bankSlotOwnsSiteUnique ring r _ b c hb hc))


/-- Correct role labels make indices in a certified prefix unique. -/
theorem bankSlotPrefixIndex {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (root : Fin n) (m : Nat)
    (hroles : ∀ k : Nat, k ≤ m →
      (r.1 (Counter.site ring root k)).pack.val = k)
    (i k : Nat) (hi : i ≤ m) (hk : k ≤ m)
    (he : Counter.site ring root i = Counter.site ring root k) :
    i = k := by
  have hp := congrArg (fun x : Fin n => (r.1 x).pack.val) he
  rw [hroles i hi, hroles k hk] at hp
  exact hp

/-- A positive responder position determines the source position. -/
theorem bankSlotResponderPredecessor {n : Nat}
    (ring : DirectedRing n) (root e : Fin n) (k : Nat)
    (hk : 1 ≤ k)
    (hd : ring.rightNeighbor e = Counter.site ring root k) :
    e = Counter.site ring root (k - 1) := by
  have hsucc : k - 1 + 1 = k := by omega
  apply bankCountRightInjective ring
  change ring.rightNeighbor e =
    Counter.site ring root (k - 1 + 1)
  rw [hsucc]
  exact hd

/-- A role prefix survives every edge on which its root remains
role zero. This uses the literal PACK row, including repairs. -/
theorem bankSlotPrefixRolesNext {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e root : Fin n) (m : Nat)
    (hmb : m ≤ bankCountWidth n)
    (hroles : ∀ k : Nat, k ≤ m →
      (r.1 (Counter.site ring root k)).pack.val = k)
    (hroot : ((renewalBankNext ring r e).1 root).pack.val = 0) :
    ∀ k : Nat, k ≤ m →
      ((renewalBankNext ring r e).1
        (Counter.site ring root k)).pack.val = k := by
  have hp := rbBankReferencePairPack ring hn r e
  simp only [bankSlotSingletonRun] at hp
  intro k hkm
  by_cases hkzero : k = 0
  · subst k
    exact hroot
  · have hkpos : 1 ≤ k := by omega
    by_cases hsource : Counter.site ring root k = e
    · rw [hsource]
      exact hp.1.trans (by
        rw [← hsource]
        exact hroles k hkm)
    · by_cases hdest :
          Counter.site ring root k = ring.rightNeighbor e
      · have he := bankSlotResponderPredecessor
          ring root e k hkpos hdest.symm
        have hx : (r.1 e).pack.val = k - 1 := by
          rw [he]
          exact hroles (k - 1) (by omega)
        have hlt : k - 1 < bankCountWidth n := by omega
        have hs : k - 1 + 1 = k := by omega
        rw [hdest]
        rw [hp.2, hx]
        change packNext (k - 1)
          (r.1 (ring.rightNeighbor e)).pack.val (bankCountWidth n) = k
        simp only [packNext, if_pos hlt, hs]
      · rw [(bankSlotNextOutsideFrame ring r e
          (Counter.site ring root k) hsource hdest).1]
        exact hroles k hkm

/-- Physical BANK tokens are the literal pair outputs, including
when the reference masks fresh grants. -/
theorem bankSlotNextBankTokens {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    ((renewalBankNext ring r e).1 e).tok =
        (Counter.resetBankOld
          (r.1 e) (r.1 (ring.rightNeighbor e))).1.tok ∧
    ((renewalBankNext ring r e).1
        (ring.rightNeighbor e)).tok =
        (Counter.resetBankOld
          (r.1 e) (r.1 (ring.rightNeighbor e))).2.tok := by
  have h := rbOutwardSelectedBankBitTok ring hn r e hbank
  exact ⟨h.2.1, h.2.2.2⟩

/-- On an actual successor, an empty BANK token cannot carry a
pending receipt. -/
theorem bankSlotNextEmptyNotPending {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hr : BankCountInv ring r) :
    ∀ (i : Fin n) (rho : RenewalBankReceipt n),
      ((renewalBankNext ring r e).1 i).tok = .E →
      ((renewalBankNext ring r e).2.sites i).worker ≠
        .pending rho := by
  obtain ⟨seed, pre, _, hi, _⟩ :=
    bankCountInvNext ring hn hbank r e hr
  intro i rho ht
  exact bankCountEmptyNotPending ring seed pre
    (renewalBankNext ring r e) hi i ht rho

/-- Build an outward slot from the exact next-cut fields. -/
theorem bankSlotOutwardBuild {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (hE : ∀ (i : Fin n) (rho : RenewalBankReceipt n),
      (r.1 i).tok = .E →
      (r.2.sites i).worker ≠ .pending rho)
    (root : Fin n) (j : Nat)
    (hrootRole : (r.1 root).pack.val = 0)
    (hrootMode : (r.1 root).mode = .RWAIT)
    (hctl : (r.2.sites root).controller = .waiting [])
    (hj : 1 ≤ j) (hjb : j ≤ bankCountWidth n)
    (hroles : ∀ k : Nat, k ≤ j →
      (r.1 (Counter.site ring root k)).pack.val = k)
    (hclear : ∀ k : Nat, 1 ≤ k → k < j →
      (r.1 (Counter.site ring root k)).tok = .E)
    (hpending : ∃ rho : RenewalBankReceipt n,
      (r.2.sites (Counter.site ring root j)).worker = .pending rho ∧
      rho.root = root)
    (hrr : (r.1 (Counter.site ring root j)).tok = .RR) :
    BankSlotAt ring r root j := by
  refine {
    toEligibleAt := {
      rootRole := hrootRole
      rootMode := hrootMode
      currentWait := hctl
      positive := hj
      leWidth := hjb
      roles := hroles
      emptyPrefix := hclear
      pending := hpending
      resetToken := Or.inl hrr }
    phase := Or.inl ⟨hrr, ?_⟩ }
  intro k hk hkj rho
  exact hE (Counter.site ring root k) rho (hclear k hk hkj)

/-- Build a returning slot; the strict upper bound is explicit. -/
theorem bankSlotReturnBuild {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (root : Fin n) (j : Nat)
    (hrootRole : (r.1 root).pack.val = 0)
    (hrootMode : (r.1 root).mode = .RWAIT)
    (hctl : (r.2.sites root).controller = .waiting [])
    (hj : 1 ≤ j) (hjb : j < bankCountWidth n)
    (hroles : ∀ k : Nat, k ≤ bankCountWidth n →
      (r.1 (Counter.site ring root k)).pack.val = k)
    (hclear : ∀ k : Nat, 1 ≤ k → k ≤ bankCountWidth n → k ≠ j →
      (r.1 (Counter.site ring root k)).tok = .E)
    (hpending : ∃ rho : RenewalBankReceipt n,
      (r.2.sites (Counter.site ring root j)).worker = .pending rho ∧
      rho.root = root)
    (hrl : (r.1 (Counter.site ring root j)).tok = .RL) :
    BankSlotAt ring r root j := by
  refine {
    toEligibleAt := {
      rootRole := hrootRole
      rootMode := hrootMode
      currentWait := hctl
      positive := hj
      leWidth := Nat.le_of_lt hjb
      roles := fun k hk => hroles k (Nat.le_trans hk (Nat.le_of_lt hjb))
      emptyPrefix := ?_
      pending := hpending
      resetToken := Or.inr hrl }
    phase := Or.inr ⟨hjb, hrl, hroles, hclear⟩ }
  intro k hk hkj
  exact hclear k hk (by omega) (by omega)

/-- Transport the fields actually read by a slot. Nonroot mode,
lease, bit, and grant may change; none is a slot premise. -/
theorem bankSlotAtTransport {n : Nat}
    (ring : DirectedRing n) (r s : RenewalBankReference n)
    (root : Fin n) (j m : Nat)
    (hs : BankSlotAt ring r root j)
    (hE : ∀ (i : Fin n) (rho : RenewalBankReceipt n),
      (s.1 i).tok = .E →
      (s.2.sites i).worker ≠ .pending rho)
    (hjm : j ≤ m) (hmb : m ≤ bankCountWidth n)
    (hlimit : (r.1 (Counter.site ring root j)).tok = .RL →
      m = bankCountWidth n)
    (hrootRole : (s.1 root).pack.val = 0)
    (hrootMode : (s.1 root).mode = .RWAIT)
    (hctl : (s.2.sites root).controller = .waiting [])
    (hroles : ∀ k : Nat, k ≤ m →
      (s.1 (Counter.site ring root k)).pack.val = k)
    (htokens : ∀ k : Nat, 1 ≤ k → k ≤ m →
      (s.1 (Counter.site ring root k)).tok =
        (r.1 (Counter.site ring root k)).tok)
    (hpending : ∃ rho : RenewalBankReceipt n,
      (s.2.sites (Counter.site ring root j)).worker = .pending rho ∧
      rho.root = root) :
    BankSlotAt ring s root j := by
  rcases hs.phase with hout | hin
  · apply bankSlotOutwardBuild ring s hE root j
      hrootRole hrootMode hctl hs.toEligibleAt.positive
      hs.toEligibleAt.leWidth
    · intro k hk
      exact hroles k (Nat.le_trans hk hjm)
    · intro k hk hkj
      rw [htokens k hk (by omega)]
      exact hs.toEligibleAt.emptyPrefix k hk hkj
    · exact hpending
    · rw [htokens j hs.toEligibleAt.positive hjm]
      exact hout.1
  · have hm := hlimit hin.2.1
    apply bankSlotReturnBuild ring s root j
      hrootRole hrootMode hctl hs.toEligibleAt.positive hin.1
    · intro k hk
      exact hroles k (by omega)
    · intro k hk hkb hkj
      rw [htokens k hk (by omega)]
      exact hin.2.2.2 k hk hkb hkj
    · exact hpending
    · rw [htokens j hs.toEligibleAt.positive hjm]
      exact hin.2.1


/-- Literal root RESET launch, including the ghost receipt mint. -/
theorem bankSlotPairLaunch {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b) (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false) (hm : x.mode = .RESET) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty, controller := .waiting [] },
       { worker := .pending { service := m.service, root := e },
         controller := .empty }) ∧
    (Counter.resetBankOld x y).1.mode = .RWAIT ∧
    (Counter.resetBankOld x y).2.tok = .RR := by
  refine ⟨rbResetLaunchMemoryExact c m e dest x y hb hx hy hg hm, ?_⟩
  have hp : packNext 0 1 c.b = 1 := by simp [packNext, hb]
  simp [Counter.resetBankOld, bankPair, bankCell, hx, hy, hg, hm, hb, hp]

/-- Source RR has priority over every OLD responder token. -/
theorem bankSlotPairAdvance {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (j : Nat)
    (hj : 1 ≤ j) (hjtop : j < c.b)
    (hx : x.pack.val = j) (hy : y.pack.val = j + 1)
    (hrr : x.tok = .RR) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty, controller := .empty },
       { worker := (m.sites e).worker, controller := .empty }) ∧
    (Counter.resetBankOld x y).1.tok = .E ∧
    (Counter.resetBankOld x y).2.tok = .RR := by
  have hle : j ≤ c.b := by omega
  have hnz : j ≠ 0 := by omega
  have hne : j ≠ c.b := by omega
  have hnextLe : j + 1 ≤ c.b := by omega
  have hnextPos : 1 ≤ j + 1 := by omega
  have hnextNz : j + 1 ≠ 0 := by omega
  have hbz : c.b ≠ 0 := by omega
  have hp : packNext j (j + 1) c.b = j + 1 := by simp [packNext, hjtop]
  by_cases htop : j + 1 = c.b
  · have hpTop : packNext j c.b c.b = c.b := by
      simpa only [htop] using hp
    by_cases hir : y.tok = .IR <;>
      simp [renewalBankPairMemory, Counter.resetBankOld, bankPair,
        bankCell, hx, hy, hj, hjtop, hle, hnz, hne, hnextLe,
        hnextPos, hnextNz, hp, hpTop, hbz, htop, hrr, hir]
  · simp [renewalBankPairMemory, Counter.resetBankOld, bankPair,
      bankCell, hx, hy, hj, hjtop, hle, hnz, hne, hnextLe,
      hnextPos, hnextNz, hp, hbz, htop, hrr]

/-- Responder role repair erases the responder and retains source RR. -/
theorem bankSlotPairRepair {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hlow : 1 ≤ x.pack.val) (hhigh : x.pack.val ≤ c.b)
    (hchanged : packNext x.pack.val y.pack.val c.b ≠ y.pack.val)
    (hrr : x.tok = .RR) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := (m.sites e).worker, controller := .empty },
       { worker := .empty, controller := .empty }) ∧
    (Counter.resetBankOld x y).1.tok = .RR ∧
    (Counter.resetBankOld x y).2.tok = .E := by
  have hnz : x.pack.val ≠ 0 := by omega
  simp [renewalBankPairMemory, Counter.resetBankOld, bankPair,
    bankCell, hnz, hlow, hhigh, hchanged, hrr]

/-- The top RR turns on its predecessor edge and becomes RL below b. -/
theorem bankSlotPairBounce {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (j : Nat)
    (hj : 1 ≤ j) (hjtop : j < c.b)
    (hx : x.pack.val = j) (hy : y.pack.val = j + 1)
    (htop : j + 1 = c.b) (hnorr : x.tok ≠ .RR) (hrr : y.tok = .RR) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := (m.sites dest).worker, controller := .empty },
       { worker := .empty, controller := .empty }) ∧
    (Counter.resetBankOld x y).1.tok = .RL ∧
    (Counter.resetBankOld x y).2.tok = .E := by
  have hle : j ≤ c.b := by omega
  have hnz : j ≠ 0 := by omega
  have hne : j ≠ c.b := by omega
  have hnextLe : j + 1 ≤ c.b := by omega
  have hnextPos : 1 ≤ j + 1 := by omega
  have hnextNz : j + 1 ≠ 0 := by omega
  have hbz : c.b ≠ 0 := by omega
  have hp : packNext j (j + 1) c.b = j + 1 := by simp [packNext, hjtop]
  have hpTop : packNext j c.b c.b = c.b := by simpa only [htop] using hp
  simp [renewalBankPairMemory, Counter.resetBankOld, bankPair,
    bankCell, hx, hy, hj, hjtop, htop, hle, hnz, hne,
    hnextLe, hnextPos, hnextNz, hp, hpTop, hbz, hnorr, hrr]

theorem bankSlotPairRetreat {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (j : Nat)
    (hj : 1 ≤ j) (hjtop : j < c.b)
    (hx : x.pack.val = j) (hy : y.pack.val = j + 1)
    (hnorr : x.tok ≠ .RR) (hrl : y.tok = .RL) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := (m.sites dest).worker, controller := .empty },
       { worker := .empty, controller := .empty }) ∧
    (Counter.resetBankOld x y).1.tok = .RL ∧
    (Counter.resetBankOld x y).2.tok = .E := by
  have hle : j ≤ c.b := by omega
  have hnz : j ≠ 0 := by omega
  have hne : j ≠ c.b := by omega
  have hnextLe : j + 1 ≤ c.b := by omega
  have hnextPos : 1 ≤ j + 1 := by omega
  have hnextNz : j + 1 ≠ 0 := by omega
  have hbz : c.b ≠ 0 := by omega
  have hp : packNext j (j + 1) c.b = j + 1 := by simp [packNext, hjtop]
  simp [renewalBankPairMemory, Counter.resetBankOld, bankPair,
    bankCell, hx, hy, hj, hjtop, hle, hnz, hne,
    hnextLe, hnextPos, hnextNz, hp, hbz, hnorr, hrl]

/-- The three relevant nonmoving interior shapes, including E/E. -/
theorem bankSlotPairInteriorHold {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (j : Nat)
    (hj : 1 ≤ j) (hjtop : j < c.b)
    (hx : x.pack.val = j) (hy : y.pack.val = j + 1)
    (hshape : (x.tok = .E ∧ y.tok = .E) ∨
      (x.tok = .RL ∧ y.tok = .E) ∨
      (x.tok = .E ∧ y.tok = .RR ∧ j + 1 ≠ c.b)) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := (m.sites e).worker, controller := .empty },
       { worker := (m.sites dest).worker, controller := .empty }) ∧
    (Counter.resetBankOld x y).1.tok = x.tok ∧
    (Counter.resetBankOld x y).2.tok = y.tok := by
  have hle : j ≤ c.b := by omega
  have hnz : j ≠ 0 := by omega
  have hne : j ≠ c.b := by omega
  have hnextLe : j + 1 ≤ c.b := by omega
  have hnextPos : 1 ≤ j + 1 := by omega
  have hnextNz : j + 1 ≠ 0 := by omega
  have hbz : c.b ≠ 0 := by omega
  have hp : packNext j (j + 1) c.b = j + 1 := by simp [packNext, hjtop]
  rcases hshape with ⟨hxe, hye⟩ | ⟨hxl, hye⟩ | ⟨hxe, hyr, hnt⟩
  · simp [renewalBankPairMemory, Counter.resetBankOld, bankPair,
      bankCell, hx, hy, hj, hjtop, hle, hnz, hne,
      hnextLe, hnextPos, hnextNz, hp, hbz, hxe, hye]
  · simp [renewalBankPairMemory, Counter.resetBankOld, bankPair,
      bankCell, hx, hy, hj, hjtop, hle, hnz, hne,
      hnextLe, hnextPos, hnextNz, hp, hbz, hxl, hye]
  · simp [renewalBankPairMemory, Counter.resetBankOld, bankPair,
      bankCell, hx, hy, hj, hjtop, hle, hnz, hne,
      hnextLe, hnextPos, hnextNz, hp, hbz, hxe, hyr, hnt]

theorem bankSlotPairClean {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c) (j : Nat)
    (hj : 1 ≤ j) (hjtop : j < c.b)
    (hx : x.pack.val = j) (hy : y.pack.val = j + 1)
    (hxe : x.tok = .E) (hye : y.tok = .E) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := (m.sites e).worker, controller := .empty },
       { worker := (m.sites dest).worker, controller := .empty }) ∧
    (Counter.resetBankOld x y).1.tok = .E ∧
    (Counter.resetBankOld x y).2.tok = .E := by
  have h := bankSlotPairInteriorHold c m e dest x y j hj hjtop hx hy
    (Or.inl ⟨hxe, hye⟩)
  exact ⟨h.1, h.2.1.trans hxe, h.2.2.trans hye⟩

/-- Root nonreturn tick: timeout ends the physical RWAIT slot. -/
theorem bankSlotPairRootWait {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 1 < c.b) (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false) (hm : x.mode = .RWAIT)
    (ht : y.tok = .E ∨ y.tok = .RR) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty,
         controller := if 1 < x.lease.val then (m.sites e).controller else .empty },
       { worker := (m.sites dest).worker, controller := .empty }) ∧
    (Counter.resetBankOld x y).1.mode =
      (if 1 < x.lease.val then .RWAIT else .RESET) ∧
    (Counter.resetBankOld x y).2.tok = y.tok := by
  have hbpos : 0 < c.b := by omega
  have hbz : c.b ≠ 0 := by omega
  have hbwide : c.b ≠ 1 := by omega
  have hp : packNext 0 1 c.b = 1 := by simp [packNext, hbpos]
  rcases ht with he | hrr
  · by_cases hl : 1 < x.lease.val <;>
      simp [renewalBankPairMemory, renewalBankWaitSlot,
        Counter.resetBankOld, bankPair, bankCell, hx, hy,
        hg, hm, he, hbpos, hbz, hbwide, hp, hl, isWaitMode, isRetTok]
  · by_cases hl : 1 < x.lease.val <;>
      simp [renewalBankPairMemory, renewalBankWaitSlot,
        Counter.resetBankOld, bankPair, bankCell, hx, hy,
        hg, hm, hrr, hbpos, hbz, hbwide, hp, hl, isWaitMode, isRetTok]

theorem bankSlotPairOldGrant {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b) (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = true) :
    renewalBankPairMemory c m e dest x y =
      ({ worker := .empty, controller := .empty },
       { worker := .empty, controller := .empty }) ∧
    (Counter.resetBankOld x y).1.mode = .RESET := by
  have hbz : c.b ≠ 0 := by omega
  have hp : packNext 0 1 c.b = 1 := by simp [packNext, hb]
  simp [renewalBankPairMemory, Counter.resetBankOld, bankPair,
    bankCell, hx, hy, hg, hb, hbz, hp]

theorem bankSlotPairAccept
    (c : Compiled) (x y : Agent c)
    (hb : 0 < c.b) (hx : x.pack.val = 0) (hy : y.pack.val = 1)
    (hg : x.grant = false) (hm : x.mode = .RWAIT) (ht : y.tok = .RL) :
    (Counter.resetBankOld x y).1.mode = .ARMED ∧
    (Counter.resetBankOld x y).2.tok = .E := by
  have hbz : c.b ≠ 0 := by omega
  have hp : packNext 0 1 c.b = 1 := by simp [packNext, hb]
  simp [Counter.resetBankOld, bankPair, bankCell,
    hx, hy, hg, hm, ht, hb, hbz, hp, isRetTok]


/-- A surviving waiting controller is the old controller. -/
theorem bankSlotWaitControllerBack {n : Nat}
    (mode : Mode) (lease : Nat)
    (controller : RenewalBankController n)
    (atoms : List (RenewalBankAtom n))
    (h : renewalBankWaitSlot mode lease controller = .waiting atoms) :
    controller = .waiting atoms := by
  unfold renewalBankWaitSlot at h
  split at h
  · split at h
    · exact h
    · cases h
  · exact h

theorem bankSlotPairSourceInheritedBack {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (atoms : List (RenewalBankAtom n)) (hne : atoms ≠ [])
    (h : (renewalBankPairMemory c m e dest x y).1.controller =
      .waiting atoms) :
    (m.sites e).controller = .waiting atoms := by
  by_cases hx : x.pack.val = 0
  · exact bankWindowJointSourceRootWaitingKept
      c m e dest x y hx atoms hne h
  · have hzero := (rbBankNonrootControllerPair c m e dest x y hx).1
    rw [hzero] at h
    cases h

/-- The responder never allocates a waiting controller. -/
theorem bankSlotPairResponderInheritedBack {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (atoms : List (RenewalBankAtom n))
    (h : (renewalBankPairMemory c m e dest x y).2.controller =
      .waiting atoms) :
    (m.sites dest).controller = .waiting atoms := by
  by_cases hx : x.pack.val = 0
  · have hzero := rbBankRootResponderControllerEmpty c m e dest x y hx
    rw [hzero] at h
    cases h
  · rcases (rbBankNonrootControllerPair c m e dest x y hx).2 with
        hzero | hwait
    · rw [hzero] at h
      cases h
    · rw [hwait] at h
      exact bankSlotWaitControllerBack
        y.mode y.lease.val (m.sites dest).controller atoms h

theorem bankSlotInheritedControllerBack {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e root : Fin n)
    (atoms : List (RenewalBankAtom n)) (hne : atoms ≠ [])
    (h : ((renewalBankNext ring r e).2.sites root).controller =
      .waiting atoms) :
    (r.2.sites root).controller = .waiting atoms := by
  change ((rbRun ring r [e]).2.sites root).controller = .waiting atoms at h
  by_cases he : root = e
  · subst root
    rw [(rbReferenceSourcePairFrame ring r e).2] at h
    exact bankSlotPairSourceInheritedBack
      (compileAdvice (ceilLogTwo n)) r.2 e (ring.rightNeighbor e)
      (r.1 e) (r.1 (ring.rightNeighbor e)) atoms hne h
  · by_cases hd : root = ring.rightNeighbor e
    · subst root
      rw [(rbReferenceSelectedPairFrame ring hn r e).2.2.2] at h
      exact bankSlotPairResponderInheritedBack
        (compileAdvice (ceilLogTwo n)) r.2 e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e)) atoms h
    · rw [(rbReferenceOutsideSiteFrame ring r e root he hd).2] at h
      exact h

/-- A stronger inherited clause, requiring no physical role or mode. -/
def BankInheritedReceiptFree {n : Nat}
    (r : RenewalBankReference n) : Prop :=
  ∀ (root : Fin n) (atoms : List (RenewalBankAtom n)),
    atoms ≠ [] →
    (r.2.sites root).controller = .waiting atoms →
    ∀ (i : Fin n) (rho : RenewalBankReceipt n),
      rho.root = root →
      (r.2.sites i).worker ≠ .pending rho

theorem bankInheritedReceiptFreeStart {n : Nat}
    (ring : DirectedRing n) (seed : RootedSeed ring) :
    BankInheritedReceiptFree (renewalBankStart ring seed) := by
  intro root atoms _ _ i rho _
  exact bankCountInitialWorkerNotPending seed.val i rho

/-- All old same-root pending workers are excluded by induction;
the sole fresh-mint row would replace the controller by waiting []. -/
theorem bankInheritedReceiptFreeNext {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (hr : BankInheritedReceiptFree r) :
    BankInheritedReceiptFree (renewalBankNext ring r e) := by
  intro root atoms hnonempty hcontroller i rho hroot
  have hbefore := bankSlotInheritedControllerBack
    ring hn r e root atoms hnonempty hcontroller
  have hold : ∀ sigma : RenewalBankReceipt n, sigma.root = root →
      (r.2.sites e).worker ≠ .pending sigma ∧
      (r.2.sites (ring.rightNeighbor e)).worker ≠ .pending sigma := by
    intro sigma hsigma
    exact ⟨hr root atoms hnonempty hbefore e sigma hsigma,
      hr root atoms hnonempty hbefore (ring.rightNeighbor e) sigma hsigma⟩
  have hquiet :
      root ≠ e ∨ (r.1 e).pack.val ≠ 0 ∨
      renewalBankPairMemory (compileAdvice (ceilLogTwo n))
        r.2 e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e)) ≠ rbRootLaunchPair r.2 e := by
    by_cases he : root = e
    · right
      right
      intro hpair
      have hsource : ((rbRun ring r [e]).2.sites e).controller =
          .waiting atoms := by
        rw [bankSlotSingletonRun]
        simpa only [he] using hcontroller
      rw [(rbReferenceSourcePairFrame ring r e).2, hpair] at hsource
      change RenewalBankController.waiting [] = .waiting atoms at hsource
      exact hnonempty (RenewalBankController.waiting.inj hsource).symm
    · exact Or.inl he
  have hframe := rbGhostSameRootNoMintAndFrame ring hn r e root hold hquiet
  simp only [bankSlotSingletonRun] at hframe
  by_cases hie : i = e
  · subst i
    exact (hframe.1 rho hroot).1
  · by_cases hid : i = ring.rightNeighbor e
    · subst i
      exact (hframe.1 rho hroot).2
    · intro hp
      have hpold := (hframe.2 i hie hid rho hroot).mp hp
      exact hr root atoms hnonempty hbefore i rho hroot hpold

theorem bankInheritedReceiptFreeRun {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (word : List (Fin n)) (r : RenewalBankReference n)
    (hr : BankInheritedReceiptFree r) :
    BankInheritedReceiptFree (rbRun ring r word) := by
  induction word generalizing r with
  | nil => exact hr
  | cons e word ih =>
      exact ih (renewalBankNext ring r e)
        (bankInheritedReceiptFreeNext ring hn r e hr)

theorem bankInheritedReceiptFreeOfCount {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (hr : BankCountInv ring r) :
    BankInheritedReceiptFree r := by
  rcases hr with ⟨seed, pre, rfl, _, _⟩
  exact bankInheritedReceiptFreeRun ring hn pre
    (renewalBankStart ring seed) (bankInheritedReceiptFreeStart ring seed)

theorem bankSlotInheritedNext {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalBankReference n) (e : Fin n) (hr : BankCountInv ring r) :
    ∀ (root inheritedAt : Fin n),
      ((renewalBankNext ring r e).1 root).pack.val = 0 →
      ((renewalBankNext ring r e).1 root).mode = .RWAIT →
      ((renewalBankNext ring r e).2.sites root).controller =
        .waiting [(inheritedAt, true)] →
      ∀ (i : Fin n) (rho : RenewalBankReceipt n), rho.root = root →
        ((renewalBankNext ring r e).2.sites i).worker ≠ .pending rho := by
  have hfree := bankInheritedReceiptFreeNext ring (by omega : 2 ≤ n) r e
    (bankInheritedReceiptFreeOfCount ring (by omega : 2 ≤ n) r hr)
  intro root inheritedAt _ _ hwait i rho hroot
  exact hfree root [(inheritedAt, true)] (by intro h; cases h)
    hwait i rho hroot


/-- A role-zero source enters RWAIT only by launch or by retaining
its OLD RWAIT mode. -/
theorem bankSlotSourceRwaitModeBack {c : Compiled}
    (x y : Agent c) (hx : x.pack.val = 0)
    (hpost : (Counter.resetBankOld x y).1.mode = .RWAIT) :
    (x.mode = .RESET ∧ x.grant = false ∧ y.pack.val = 1) ∨
      x.mode = .RWAIT := by
  have hb : 0 < c.b := by change 0 < c.s + 11; omega
  have hbz : c.b ≠ 0 := by omega
  have hwide : c.b ≠ 1 := by change c.s + 11 ≠ 1; omega
  by_cases hy : y.pack.val = 1
  · have hp : packNext 0 1 c.b = 1 := by simp [packNext, hb]
    cases hm : x.mode <;> cases hg : x.grant <;>
      cases ht : y.tok <;> by_cases hl : 1 < x.lease.val <;>
      simp [Counter.resetBankOld, bankPair, bankCell,
        hx, hy, hp, hb, hbz, hwide, hm, hg, ht, hl,
        isWaitMode, isRetTok, Id.run_pure, Id.run_bind,
        apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd,
        apply_ite BankCell.tok, apply_ite BankCell.role,
        apply_ite BankCell.mode, ite_self] at hpost ⊢ <;>
      (repeat' split at hpost) <;> simp_all
  · have hp : packNext 0 y.pack.val c.b = 1 := by simp [packNext, hb]
    cases hm : x.mode <;> cases hg : x.grant <;>
      cases ht : y.tok <;> by_cases hl : 1 < x.lease.val <;>
      simp [Counter.resetBankOld, bankPair, bankCell,
        hx, hp, hb, hbz, hwide, hy, Ne.symm hy,
        hm, hg, ht, hl, isWaitMode, isRetTok,
        Id.run_pure, Id.run_bind,
        apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd,
        apply_ite BankCell.tok, apply_ite BankCell.role,
        apply_ite BankCell.mode, ite_self] at hpost ⊢ <;>
      (repeat' split at hpost) <;> simp_all

/-- At an OLD RWAIT source every surviving waiting controller,
including waiting [], is the OLD controller. -/
theorem bankSlotSourceRwaitControllerBack {n : Nat} {c : Compiled}
    (m : RenewalBankMemory n) (e dest : Fin n) (x y : Agent c)
    (hx : x.pack.val = 0) (hm : x.mode = .RWAIT)
    (atoms : List (RenewalBankAtom n))
    (h : (renewalBankPairMemory c m e dest x y).1.controller =
      .waiting atoms) :
    (m.sites e).controller = .waiting atoms := by
  have hb : 0 < c.b := by change 0 < c.s + 11; omega
  have hbz : c.b ≠ 0 := by omega
  have hwide : c.b ≠ 1 := by change c.s + 11 ≠ 1; omega
  by_cases hy : y.pack.val = 1
  · have hp : packNext 0 1 c.b = 1 := by simp [packNext, hb]
    cases hg : x.grant <;> cases ht : y.tok <;>
      by_cases hl : 1 < x.lease.val <;>
      simp [renewalBankPairMemory, renewalBankWaitSlot, bankCell,
        hx, hy, hp, hb, hbz, hwide, hm, hg, ht, hl,
        isWaitMode, isRetTok, Id.run_pure, Id.run_bind] at h ⊢ <;>
      (repeat' split at h) <;> simp_all
  · have hp : packNext 0 y.pack.val c.b = 1 := by simp [packNext, hb]
    cases hg : x.grant <;> cases ht : y.tok <;>
      by_cases hl : 1 < x.lease.val <;>
      simp [renewalBankPairMemory, renewalBankWaitSlot, bankCell,
        hx, hp, hb, hbz, hwide, hy, Ne.symm hy,
        hm, hg, ht, hl, isWaitMode, isRetTok,
        Id.run_pure, Id.run_bind] at h ⊢ <;>
      (repeat' split at h) <;> simp_all

/-- Every POST generated root either launched on this edge, or was
already the same generated RWAIT controller at the same site. -/
theorem bankSlotGeneratedRootBack {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e root : Fin n)
    (hrole : ((renewalBankNext ring r e).1 root).pack.val = 0)
    (hmode : ((renewalBankNext ring r e).1 root).mode = .RWAIT)
    (hcontroller : ((renewalBankNext ring r e).2.sites root).controller =
      .waiting []) :
    (root = e ∧ Counter.resetLaunchGuard
      (r.1 e) (r.1 (ring.rightNeighbor e)) = true) ∨
    ((r.1 root).pack.val = 0 ∧ (r.1 root).mode = .RWAIT ∧
      (r.2.sites root).controller = .waiting []) := by
  have hdiff : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) e
  have hf := rbReferenceSelectedPairFrame ring (by omega : 2 ≤ n) r e
  by_cases he : root = e
  · subst root
    have hx : (r.1 e).pack.val = 0 := by
      rw [← bankWindowClosureRepairNonresponderPackFixed
        ring (by omega : 2 ≤ n) r e e (Ne.symm hdiff)]
      exact hrole
    have htrip := (bankWindowClosureSelectedBankTrip ring hn hbank r e).1
    have hmodePair := congrArg (fun t : Mode × Bool × BTok => t.1) htrip
    change ((renewalBankNext ring r e).1 e).mode =
      (Counter.resetBankOld (r.1 e) (r.1 (ring.rightNeighbor e))).1.mode
      at hmodePair
    have hpost : (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.mode = .RWAIT :=
      hmodePair.symm.trans hmode
    rcases bankSlotSourceRwaitModeBack
        (r.1 e) (r.1 (ring.rightNeighbor e)) hx hpost with hlaunch | hwait
    · obtain ⟨hm, hg, hy⟩ := hlaunch
      refine Or.inl ⟨rfl, ?_⟩
      have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
        change 0 < (compileAdvice (ceilLogTwo n)).s + 11
        omega
      have hp : packNext 0 1 (compileAdvice (ceilLogTwo n)).b = 1 := by
        simp [packNext, hb]
      simp [Counter.resetLaunchGuard, hbank, hx, hy, hg, hm, hp]
    · refine Or.inr ⟨hx, hwait, ?_⟩
      have hpair : (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
          r.2 e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).1.controller = .waiting [] := by
        have h := congrArg (fun s : RenewalBankSite n => s.controller) hf.2.2.1
        exact h.symm.trans hcontroller
      exact bankSlotSourceRwaitControllerBack r.2 e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e)) hx hwait [] hpair
  · by_cases hd : root = ring.rightNeighbor e
    · subst root
      have hpair : (renewalBankPairMemory (compileAdvice (ceilLogTwo n))
          r.2 e (ring.rightNeighbor e)
          (r.1 e) (r.1 (ring.rightNeighbor e))).2.controller = .waiting [] := by
        have h := congrArg (fun s : RenewalBankSite n => s.controller) hf.2.2.2
        exact h.symm.trans hcontroller
      have hsame : packNext (r.1 e).pack.val
          (r.1 (ring.rightNeighbor e)).pack.val
          (compileAdvice (ceilLogTwo n)).b =
            (r.1 (ring.rightNeighbor e)).pack.val := by
        by_cases hs : packNext (r.1 e).pack.val
            (r.1 (ring.rightNeighbor e)).pack.val
            (compileAdvice (ceilLogTwo n)).b =
              (r.1 (ring.rightNeighbor e)).pack.val
        · exact hs
        · rw [bankWindowJointResponderChangedControllerEmpty
            (compileAdvice (ceilLogTwo n)) r.2 e (ring.rightNeighbor e)
            (r.1 e) (r.1 (ring.rightNeighbor e)) hs] at hpair
          cases hpair
      have hresp := bankWindowExactResponderPack ring r e hdiff
      have hy : (r.1 (ring.rightNeighbor e)).pack.val = 0 := by
        rw [← hsame, ← hresp]
        exact hrole
      have hm : (r.1 (ring.rightNeighbor e)).mode = .RWAIT := by
        rcases bankWindowJointIncomingModeKeepOrReset
            ring hn hbank r e hy hrole with hkeep | hreset
        · exact hkeep.symm.trans hmode
        · rw [hreset] at hmode
          cases hmode
      refine Or.inr ⟨hy, hm, ?_⟩
      exact bankSlotPairResponderInheritedBack
        (compileAdvice (ceilLogTwo n)) r.2 e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e)) [] hpair
    · have hframe := bankWindowExactOffPairFrame ring r e root he hd
      rw [hframe.1] at hrole hmode
      rw [hframe.2] at hcontroller
      exact Or.inr ⟨hrole, hmode, hcontroller⟩


theorem bankSlotResponderIndex {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e root : Fin n) (m a k : Nat)
    (hroles : ∀ t : Nat, t ≤ m →
      (r.1 (Counter.site ring root t)).pack.val = t)
    (ha : a ≤ m) (hk : k ≤ m)
    (he : e = Counter.site ring root a)
    (hrd : root ≠ ring.rightNeighbor e)
    (hd : Counter.site ring root k = ring.rightNeighbor e) :
    k = a + 1 := by
  cases k with
  | zero => exact False.elim (hrd hd)
  | succ k =>
      have hprev : Counter.site ring root k = e :=
        bankCountRightInjective ring hd
      have hidx := bankSlotPrefixIndex ring r root m hroles k a
        (by omega) ha (hprev.trans he)
      omega

/-- Reconstruct the whole clean returning window after a left move. -/
theorem bankSlotBackwardAt {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e root : Fin n) (k : Nat)
    (hk : 1 ≤ k) (hkb : k + 1 ≤ bankCountWidth n)
    (he : e = Counter.site ring root k)
    (hroles : ∀ t : Nat, t ≤ bankCountWidth n →
      (r.1 (Counter.site ring root t)).pack.val = t)
    (hclear : ∀ t : Nat, 1 ≤ t → t ≤ bankCountWidth n → t ≠ k + 1 →
      (r.1 (Counter.site ring root t)).tok = .E)
    (hrootRole : ((renewalBankNext ring r e).1 root).pack.val = 0)
    (hrootMode : ((renewalBankNext ring r e).1 root).mode = .RWAIT)
    (hctl : ((renewalBankNext ring r e).2.sites root).controller = .waiting [])
    (hsrc : ((renewalBankNext ring r e).1 e).tok = .RL)
    (hdst : ((renewalBankNext ring r e).1 (ring.rightNeighbor e)).tok = .E)
    (hpending : ∃ rho : RenewalBankReceipt n,
      ((renewalBankNext ring r e).2.sites (Counter.site ring root k)).worker =
        .pending rho ∧ rho.root = root) :
    BankSlotAt ring (renewalBankNext ring r e) root k := by
  have hright : ring.rightNeighbor e = Counter.site ring root (k + 1) := by
    rw [he]
    rfl
  apply bankSlotReturnBuild ring (renewalBankNext ring r e) root k
    hrootRole hrootMode hctl hk (by omega)
    (bankSlotPrefixRolesNext ring hn r e root (bankCountWidth n)
      (Nat.le_refl _) hroles hrootRole)
  · intro t ht htb htk
    by_cases hte : Counter.site ring root t = e
    · have hidx := bankSlotPrefixIndex ring r root (bankCountWidth n)
        hroles t k htb (by omega) (hte.trans he)
      exact False.elim (htk hidx)
    · by_cases htd : Counter.site ring root t = ring.rightNeighbor e
      · rw [htd]
        exact hdst
      · have hf := (rbReferenceOutsideSiteFrame ring r e
          (Counter.site ring root t) hte htd).1
        change (renewalBankNext ring r e).1 (Counter.site ring root t) =
          r.1 (Counter.site ring root t) at hf
        rw [hf]
        apply hclear t ht htb
        intro htop
        apply htd
        rw [htop, ← hright]
  · exact hpending
  · rw [← he]
    exact hsrc

/-- Reconstruct the extended correct prefix after an actual RR move. -/
theorem bankSlotOutwardAdvanceAt {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e root : Fin n) (j : Nat)
    (hs : BankSlotAt ring r root j) (hjtop : j < bankCountWidth n)
    (he : e = Counter.site ring root j)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1)
    (hE : ∀ (i : Fin n) (rho : RenewalBankReceipt n),
      ((renewalBankNext ring r e).1 i).tok = .E →
      ((renewalBankNext ring r e).2.sites i).worker ≠ .pending rho)
    (hrootRole : ((renewalBankNext ring r e).1 root).pack.val = 0)
    (hrootMode : ((renewalBankNext ring r e).1 root).mode = .RWAIT)
    (hctl : ((renewalBankNext ring r e).2.sites root).controller = .waiting [])
    (hsrc : ((renewalBankNext ring r e).1 e).tok = .E)
    (hdst : ((renewalBankNext ring r e).1 (ring.rightNeighbor e)).tok = .RR)
    (hpending : ∃ rho : RenewalBankReceipt n,
      ((renewalBankNext ring r e).2.sites (ring.rightNeighbor e)).worker =
        .pending rho ∧ rho.root = root) :
    BankSlotAt ring (renewalBankNext ring r e) root (j + 1) := by
  have hright : ring.rightNeighbor e = Counter.site ring root (j + 1) := by
    rw [he]
    rfl
  have hroles : ∀ t : Nat, t ≤ j + 1 →
      (r.1 (Counter.site ring root t)).pack.val = t := by
    intro t ht
    by_cases htj : t ≤ j
    · exact hs.toEligibleAt.roles t htj
    · have hteq : t = j + 1 := by omega
      subst t
      rw [← hright]
      exact hy
  apply bankSlotOutwardBuild ring (renewalBankNext ring r e) hE root (j + 1)
    hrootRole hrootMode hctl (by omega) (by omega)
    (bankSlotPrefixRolesNext ring hn r e root (j + 1) (by omega) hroles hrootRole)
  · intro t ht htj
    by_cases hte : Counter.site ring root t = e
    · rw [hte]
      exact hsrc
    · by_cases htd : Counter.site ring root t = ring.rightNeighbor e
      · have hidx := bankSlotPrefixIndex ring r root (j + 1) hroles
          t (j + 1) (by omega) (Nat.le_refl _) (htd.trans hright)
        omega
      · have hf := (rbReferenceOutsideSiteFrame ring r e
          (Counter.site ring root t) hte htd).1
        change (renewalBankNext ring r e).1 (Counter.site ring root t) =
          r.1 (Counter.site ring root t) at hf
        rw [hf]
        apply hs.toEligibleAt.emptyPrefix t ht
        have hne : t ≠ j := by
          intro hsame
          apply hte
          rw [hsame, ← he]
        omega
  · rw [← hright]
    exact hpending
  · rw [← hright]
    exact hdst

theorem bankSlotOutwardSourceHoldAt {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e root : Fin n) (j : Nat)
    (hs : BankSlotAt ring r root j)
    (he : e = Counter.site ring root j)
    (hrd : root ≠ ring.rightNeighbor e)
    (hE : ∀ (i : Fin n) (rho : RenewalBankReceipt n),
      ((renewalBankNext ring r e).1 i).tok = .E →
      ((renewalBankNext ring r e).2.sites i).worker ≠ .pending rho)
    (hrootRole : ((renewalBankNext ring r e).1 root).pack.val = 0)
    (hrootMode : ((renewalBankNext ring r e).1 root).mode = .RWAIT)
    (hctl : ((renewalBankNext ring r e).2.sites root).controller = .waiting [])
    (hsrc : ((renewalBankNext ring r e).1 e).tok = .RR)
    (hpending : ∃ rho : RenewalBankReceipt n,
      ((renewalBankNext ring r e).2.sites (Counter.site ring root j)).worker =
        .pending rho ∧ rho.root = root) :
    BankSlotAt ring (renewalBankNext ring r e) root j := by
  apply bankSlotOutwardBuild ring (renewalBankNext ring r e) hE root j
    hrootRole hrootMode hctl hs.toEligibleAt.positive hs.toEligibleAt.leWidth
    (bankSlotPrefixRolesNext ring hn r e root j hs.toEligibleAt.leWidth
      hs.toEligibleAt.roles hrootRole)
  · intro t ht htj
    have hte : Counter.site ring root t ≠ e := by
      intro hh
      have hi := bankSlotPrefixIndex ring r root j hs.toEligibleAt.roles
        t j (by omega) (Nat.le_refl _) (hh.trans he)
      omega
    have htd : Counter.site ring root t ≠ ring.rightNeighbor e := by
      intro hh
      have hi := bankSlotResponderIndex ring r e root j j t
        hs.toEligibleAt.roles (Nat.le_refl _) (by omega) he hrd hh
      omega
    have hf := (rbReferenceOutsideSiteFrame ring r e
      (Counter.site ring root t) hte htd).1
    change (renewalBankNext ring r e).1 (Counter.site ring root t) =
      r.1 (Counter.site ring root t) at hf
    rw [hf]
    exact hs.toEligibleAt.emptyPrefix t ht htj
  · exact hpending
  · rw [← he]
    exact hsrc

theorem bankSlotInteriorHoldNext {n : Nat}
    (ring : DirectedRing n) (hn : 2 ≤ n)
    (r : RenewalBankReference n) (e : Fin n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (k : Nat) (hk : 1 ≤ k) (hkb : k < bankCountWidth n)
    (hx : (r.1 e).pack.val = k)
    (hy : (r.1 (ring.rightNeighbor e)).pack.val = k + 1)
    (hshape :
      ((r.1 e).tok = .E ∧ (r.1 (ring.rightNeighbor e)).tok = .E) ∨
      ((r.1 e).tok = .RL ∧ (r.1 (ring.rightNeighbor e)).tok = .E) ∨
      ((r.1 e).tok = .E ∧ (r.1 (ring.rightNeighbor e)).tok = .RR ∧
        k + 1 ≠ bankCountWidth n)) :
    ∀ i : Fin n,
      ((renewalBankNext ring r e).1 i).tok = (r.1 i).tok ∧
      ((renewalBankNext ring r e).2.sites i).worker = (r.2.sites i).worker := by
  have hrow := bankSlotPairInteriorHold (compileAdvice (ceilLogTwo n))
    r.2 e (ring.rightNeighbor e) (r.1 e) (r.1 (ring.rightNeighbor e))
    k hk hkb hx hy hshape
  have ht := bankSlotNextBankTokens ring hn r e hbank
  have hf := rbReferenceSelectedPairFrame ring hn r e
  intro i
  by_cases hie : i = e
  · subst i
    constructor
    · exact ht.1.trans hrow.2.1
    · change ((rbRun ring r [e]).2.sites e).worker = (r.2.sites e).worker
      rw [hf.2.2.1, hrow.1]
  · by_cases hid : i = ring.rightNeighbor e
    · subst i
      constructor
      · exact ht.2.trans hrow.2.2
      · change ((rbRun ring r [e]).2.sites (ring.rightNeighbor e)).worker =
          (r.2.sites (ring.rightNeighbor e)).worker
        rw [hf.2.2.2, hrow.1]
    · have h := rbReferenceOutsideSiteFrame ring r e i hie hid
      exact ⟨congrArg Agent.tok h.1, congrArg RenewalBankSite.worker h.2⟩

/-- A top source retains E or RR and its worker, even when the
responder is the root after wrapping around the ring. -/
theorem bankSlotPairTopHold {n : Nat}
    (c : Compiled) (m : RenewalBankMemory n)
    (e dest : Fin n) (x y : Agent c)
    (hb : 0 < c.b) (hx : x.pack.val = c.b)
    (ht : x.tok = .E ∨ x.tok = .RR) :
    (renewalBankPairMemory c m e dest x y).1.worker = (m.sites e).worker ∧
    (Counter.resetBankOld x y).1.tok = x.tok := by
  have hbz : c.b ≠ 0 := by omega
  have hbpos : 1 ≤ c.b := by omega
  by_cases hy : y.pack.val = 0
  · rcases ht with he | hrr
    · cases hg : y.grant <;> cases hm : y.mode <;>
        by_cases hl : 1 < y.lease.val <;>
        simp [renewalBankPairMemory, renewalBankWaitSlot,
          Counter.resetBankOld, bankPair, bankCell, packNext,
          hx, hy, hbz, hbpos, he, hg, hm, hl, isWaitMode]
    · cases hg : y.grant <;> cases hm : y.mode <;>
        by_cases hl : 1 < y.lease.val <;>
        simp [renewalBankPairMemory, renewalBankWaitSlot,
          Counter.resetBankOld, bankPair, bankCell, packNext,
          hx, hy, hbz, hbpos, hrr, hg, hm, hl, isWaitMode]
  · by_cases hsp : y.pack.val = c.b + 1
    · rcases ht with he | hrr
      · simp [renewalBankPairMemory, Counter.resetBankOld, bankPair,
          bankCell, packNext, hx, hy, hsp, hbz, hbpos, he]
      · simp [renewalBankPairMemory, Counter.resetBankOld, bankPair,
          bankCell, packNext, hx, hy, hsp, hbz, hbpos, hrr]
    · have hchanged : c.b + 1 ≠ y.pack.val := Ne.symm hsp
      rcases ht with he | hrr
      · simp [renewalBankPairMemory, Counter.resetBankOld, bankPair,
          bankCell, packNext, hx, hy, hsp, hchanged, hbz, hbpos, he]
      · simp [renewalBankPairMemory, Counter.resetBankOld, bankPair,
          bankCell, packNext, hx, hy, hsp, hchanged, hbz, hbpos, hrr]

theorem bankSlotOutsidePrefixDigitsFrame {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (e root : Fin n) (m : Nat)
    (hout : ¬ ∃ k : Nat, k ≤ m ∧ e = Counter.site ring root k) :
    ∀ t : Nat, 1 ≤ t → t ≤ m →
      (renewalBankNext ring r e).1 (Counter.site ring root t) =
        r.1 (Counter.site ring root t) ∧
      (renewalBankNext ring r e).2.sites (Counter.site ring root t) =
        r.2.sites (Counter.site ring root t) := by
  intro t ht htm
  cases t with
  | zero => omega
  | succ t =>
      have hte : Counter.site ring root (t + 1) ≠ e := by
        intro hh
        exact hout ⟨t + 1, htm, hh.symm⟩
      have htd : Counter.site ring root (t + 1) ≠ ring.rightNeighbor e := by
        intro hh
        have hp : Counter.site ring root t = e :=
          bankCountRightInjective ring hh
        exact hout ⟨t, by omega, hp.symm⟩
      exact rbReferenceOutsideSiteFrame ring r e
        (Counter.site ring root (t + 1)) hte htd


/-- A literal RESET launch creates the depth-one slot immediately,
including when an OLD grant moves onto the root later in tokenStep. -/
theorem bankSlotLaunchNext {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hr : BankCountInv ring r)
    (hguard : Counter.resetLaunchGuard
      (r.1 e) (r.1 (ring.rightNeighbor e)) = true) :
    BankSlotAt ring (renewalBankNext ring r e) e 1 := by
  have hfields :
      (compileAdvice (ceilLogTwo n)).useSmall = false ∧
      (r.1 e).pack.val = 0 ∧ (r.1 e).grant = false ∧
      (r.1 e).mode = .RESET ∧
      (r.1 (ring.rightNeighbor e)).pack.val = 1 ∧
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b = 1 := by
    exact of_decide_eq_true hguard
  obtain ⟨_, hx, hg, hm, hy, hp⟩ := hfields
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hwidth : 1 ≤ bankCountWidth n := by
    change 1 ≤ (compileAdvice (ceilLogTwo n)).b
    omega
  have hrow := bankSlotPairLaunch
    (compileAdvice (ceilLogTwo n)) r.2 e (ring.rightNeighbor e)
    (r.1 e) (r.1 (ring.rightNeighbor e)) hb hx hy hg hm
  have hpair := rbReferenceSelectedPairFrame
    ring (by omega : 2 ≤ n) r e
  have hpack := rbBankReferencePairPack
    ring (by omega : 2 ≤ n) r e
  simp only [bankSlotSingletonRun] at hpair hpack
  have hrootRole : ((renewalBankNext ring r e).1 e).pack.val = 0 :=
    hpack.1.trans hx
  have hfirstRole :
      ((renewalBankNext ring r e).1
        (ring.rightNeighbor e)).pack.val = 1 :=
    hpack.2.trans hp
  have htrip := rbBankMaskedSourceTrip
    (compileAdvice (ceilLogTwo n))
    (renewalBankCut ring r.1 r.2 e)
    (r.1 e) (r.1 (ring.rightNeighbor e)) hbank
  have hmodePair := congrArg (fun t : Mode × Bool × BTok => t.1) htrip
  have hrootMode : ((renewalBankNext ring r e).1 e).mode = .RWAIT := by
    rw [hpair.1]
    exact hmodePair.trans hrow.2.1
  have hctl :
      ((renewalBankNext ring r e).2.sites e).controller = .waiting [] := by
    rw [hpair.2.2.1, hrow.1]
  have hpending : ∃ rho : RenewalBankReceipt n,
      ((renewalBankNext ring r e).2.sites
        (Counter.site ring e 1)).worker = .pending rho ∧
      rho.root = e := by
    refine ⟨{ service := r.2.service, root := e }, ?_, rfl⟩
    change ((renewalBankNext ring r e).2.sites
      (ring.rightNeighbor e)).worker = _
    rw [hpair.2.2.2, hrow.1]
  have hrr :
      ((renewalBankNext ring r e).1
        (Counter.site ring e 1)).tok = .RR :=
    (bankSlotNextBankTokens ring (by omega) r e hbank).2.trans hrow.2.2
  apply bankSlotOutwardBuild ring (renewalBankNext ring r e)
    (bankSlotNextEmptyNotPending ring hn hbank r e hr)
    e 1 hrootRole hrootMode hctl (by omega) hwidth
  · intro k hk
    have hkcases : k = 0 ∨ k = 1 := by omega
    rcases hkcases with hkzero | hkone
    · subst k
      exact hrootRole
    · subst k
      exact hfirstRole
  · intro k hk hlt
    omega
  · exact hpending
  · exact hrr

/-- Grant/request recomputation leaves every slot-relevant physical
field equal to the literal transition's output. -/
theorem bankSlotMaskedPairFields
    (c : Compiled) (suppress : Bool) (x y : Agent c) :
    ((renewalMaskedPair c suppress x y).1.pack,
      (renewalMaskedPair c suppress x y).1.mode,
      (renewalMaskedPair c suppress x y).1.tok) =
      ((transition c x y).1.pack,
        (transition c x y).1.mode,
        (transition c x y).1.tok) ∧
    ((renewalMaskedPair c suppress x y).2.pack,
      (renewalMaskedPair c suppress x y).2.mode,
      (renewalMaskedPair c suppress x y).2.tok) =
      ((transition c x y).2.pack,
        (transition c x y).2.mode,
        (transition c x y).2.tok) := by
  cases suppress <;> constructor <;> rfl


/-- Every non-root-incident edge is classified against the actual
outward prefix or the full returning window. -/
theorem bankSlotRetainedNonincident {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e root : Fin n) (j : Nat)
    (hr : BankCountInv ring r) (hs : BankSlotAt ring r root j)
    (hre : root ≠ e) (hrd : root ≠ ring.rightNeighbor e) :
    ∃ j' : Nat, BankSlotAt ring (renewalBankNext ring r e) root j' := by
  classical
  have htwo : 2 ≤ n := by omega
  have hroot := rbReferenceOutsideSiteFrame ring r e root hre hrd
  have hrootRole : ((renewalBankNext ring r e).1 root).pack.val = 0 :=
    (congrArg (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.pack.val)
      hroot.1).trans hs.toEligibleAt.rootRole
  have hrootMode : ((renewalBankNext ring r e).1 root).mode = .RWAIT :=
    (congrArg Agent.mode hroot.1).trans hs.toEligibleAt.rootMode
  have hctl : ((renewalBankNext ring r e).2.sites root).controller = .waiting [] :=
    (congrArg RenewalBankSite.controller hroot.2).trans hs.toEligibleAt.currentWait
  have hE := bankSlotNextEmptyNotPending ring hn hbank r e hr
  have htok := bankSlotNextBankTokens ring htwo r e hbank
  have hpair := rbReferenceSelectedPairFrame ring htwo r e
  obtain ⟨rho, hp, ho⟩ := hs.toEligibleAt.pending
  rcases hs.phase with ⟨hrr, _⟩ | ⟨hjtop, hrl, hfull, hclean⟩
  · have keep
        (ht : ∀ t : Nat, 1 ≤ t → t ≤ j →
          ((renewalBankNext ring r e).1 (Counter.site ring root t)).tok =
            (r.1 (Counter.site ring root t)).tok)
        (hw : ((renewalBankNext ring r e).2.sites
          (Counter.site ring root j)).worker = .pending rho) :
        ∃ j' : Nat, BankSlotAt ring (renewalBankNext ring r e) root j' := by
      refine ⟨j, ?_⟩
      apply bankSlotOutwardBuild ring (renewalBankNext ring r e) hE root j
        hrootRole hrootMode hctl hs.toEligibleAt.positive hs.toEligibleAt.leWidth
        (bankSlotPrefixRolesNext ring htwo r e root j hs.toEligibleAt.leWidth
          hs.toEligibleAt.roles hrootRole)
      · intro t htpos htj
        rw [ht t htpos (by omega)]
        exact hs.toEligibleAt.emptyPrefix t htpos htj
      · exact ⟨rho, hw, ho⟩
      · exact (ht j hs.toEligibleAt.positive (Nat.le_refl _)).trans hrr
    by_cases hex : ∃ k : Nat, k ≤ j ∧ e = Counter.site ring root k
    · obtain ⟨k, hkj, he⟩ := hex
      have hkpos : 1 ≤ k := by
        by_cases hkzero : k = 0
        · have hezero : e = root := by
            change e = Counter.site ring root 0
            exact he.trans (congrArg (Counter.site ring root) hkzero)
          exact False.elim (hre hezero.symm)
        · omega
      have hx : (r.1 e).pack.val = k := by
        rw [he]
        exact hs.toEligibleAt.roles k hkj
      have hright : ring.rightNeighbor e = Counter.site ring root (k + 1) := by
        rw [he]
        rfl
      by_cases hfront : k = j
      · have heFront : e = Counter.site ring root j :=
          he.trans (congrArg (Counter.site ring root) hfront)
        have hxFront : (r.1 e).pack.val = j := hx.trans hfront
        have hrrSrc : (r.1 e).tok = .RR := by rw [heFront]; exact hrr
        have hpSrc : (r.2.sites e).worker = .pending rho := by rw [heFront]; exact hp
        by_cases hjlt : j < bankCountWidth n
        · by_cases hy : (r.1 (ring.rightNeighbor e)).pack.val = j + 1
          · have hrow := bankSlotPairAdvance (compileAdvice (ceilLogTwo n))
              r.2 e (ring.rightNeighbor e) (r.1 e) (r.1 (ring.rightNeighbor e))
              j hs.toEligibleAt.positive hjlt hxFront hy hrrSrc
            have hpNew : ((renewalBankNext ring r e).2.sites
                (ring.rightNeighbor e)).worker = .pending rho := by
              change ((rbRun ring r [e]).2.sites (ring.rightNeighbor e)).worker =
                .pending rho
              rw [hpair.2.2.2, hrow.1]
              exact hpSrc
            exact ⟨j + 1, bankSlotOutwardAdvanceAt ring htwo r e root j hs hjlt
              heFront hy hE hrootRole hrootMode hctl
              (htok.1.trans hrow.2.1) (htok.2.trans hrow.2.2)
              ⟨rho, hpNew, ho⟩⟩
          · have hpost : packNext (r.1 e).pack.val
                (r.1 (ring.rightNeighbor e)).pack.val
                (compileAdvice (ceilLogTwo n)).b = j + 1 := by
              rw [hxFront]
              simp [packNext, hjlt]
            have hchanged : packNext (r.1 e).pack.val
                (r.1 (ring.rightNeighbor e)).pack.val
                (compileAdvice (ceilLogTwo n)).b ≠
                  (r.1 (ring.rightNeighbor e)).pack.val := by
              intro hh
              exact hy (hh.symm.trans hpost)
            have hstation := rbTrackedChangedRoleRRSourceStationary ring htwo r e
              hbank (by rw [hxFront]; exact hs.toEligibleAt.positive)
              (by rw [hxFront]; exact hs.toEligibleAt.leWidth)
              hchanged hrrSrc rho hpSrc
            refine ⟨j, bankSlotOutwardSourceHoldAt ring htwo r e root j hs heFront hrd
              hE hrootRole hrootMode hctl hstation.1 ⟨rho, ?_, ho⟩⟩
            rw [← heFront]
            exact hstation.2.2
        · have hjb : j = bankCountWidth n := by
            have hh := hs.toEligibleAt.leWidth
            omega
          have hxTop : (r.1 e).pack.val = (compileAdvice (ceilLogTwo n)).b := by
            rw [hxFront, hjb]
          have hrow := bankSlotPairTopHold (compileAdvice (ceilLogTwo n)) r.2
            e (ring.rightNeighbor e) (r.1 e) (r.1 (ring.rightNeighbor e))
            (by change 0 < (compileAdvice (ceilLogTwo n)).s + 11; omega)
            hxTop (Or.inr hrrSrc)
          have hpNew : ((renewalBankNext ring r e).2.sites e).worker =
              .pending rho := by
            change ((rbRun ring r [e]).2.sites e).worker = .pending rho
            rw [hpair.2.2.1]
            exact hrow.1.trans hpSrc
          refine ⟨j, bankSlotOutwardSourceHoldAt ring htwo r e root j hs heFront hrd
            hE hrootRole hrootMode hctl ((htok.1.trans hrow.2).trans hrrSrc)
            ⟨rho, ?_, ho⟩⟩
          rw [← heFront]
          exact hpNew
      · have hkjlt : k < j := by omega
        have hklt : k < bankCountWidth n := by
          have hh := hs.toEligibleAt.leWidth
          omega
        have hy : (r.1 (ring.rightNeighbor e)).pack.val = k + 1 := by
          rw [hright]
          exact hs.toEligibleAt.roles (k + 1) (by omega)
        have hxE : (r.1 e).tok = .E := by
          rw [he]
          exact hs.toEligibleAt.emptyPrefix k hkpos hkjlt
        by_cases hbounce : k + 1 = bankCountWidth n
        · have hlast : k + 1 = j := by
            have hh := hs.toEligibleAt.leWidth
            omega
          have hjb : j = bankCountWidth n := by omega
          have hyRR : (r.1 (ring.rightNeighbor e)).tok = .RR := by
            rw [hright, hlast]
            exact hrr
          have hnorr : (r.1 e).tok ≠ .RR := by rw [hxE]; intro h; cases h
          have hrow := bankSlotPairBounce (compileAdvice (ceilLogTwo n))
            r.2 e (ring.rightNeighbor e) (r.1 e) (r.1 (ring.rightNeighbor e))
            k hkpos hklt hx hy hbounce hnorr hyRR
          have hpDst : (r.2.sites (ring.rightNeighbor e)).worker = .pending rho := by
            rw [hright, hlast]
            exact hp
          have hpNew : ((renewalBankNext ring r e).2.sites e).worker =
              .pending rho := by
            change ((rbRun ring r [e]).2.sites e).worker = .pending rho
            rw [hpair.2.2.1, hrow.1]
            exact hpDst
          refine ⟨k, bankSlotBackwardAt ring htwo r e root k hkpos (by omega) he
            (fun t ht => hs.toEligibleAt.roles t (by omega))
            (fun t ht htb hne => hs.toEligibleAt.emptyPrefix t ht (by omega))
            hrootRole hrootMode hctl (htok.1.trans hrow.2.1)
            (htok.2.trans hrow.2.2) ⟨rho, ?_, ho⟩⟩
          rw [← he]
          exact hpNew
        · have hshape :
              ((r.1 e).tok = .E ∧ (r.1 (ring.rightNeighbor e)).tok = .E) ∨
              ((r.1 e).tok = .RL ∧ (r.1 (ring.rightNeighbor e)).tok = .E) ∨
              ((r.1 e).tok = .E ∧ (r.1 (ring.rightNeighbor e)).tok = .RR ∧
                k + 1 ≠ bankCountWidth n) := by
            by_cases hlast : k + 1 = j
            · refine Or.inr (Or.inr ⟨hxE, ?_, hbounce⟩)
              rw [hright, hlast]
              exact hrr
            · refine Or.inl ⟨hxE, ?_⟩
              rw [hright]
              exact hs.toEligibleAt.emptyPrefix (k + 1) (by omega) (by omega)
          have hhold := bankSlotInteriorHoldNext ring htwo r e hbank
            k hkpos hklt hx hy hshape
          exact keep (fun t _ _ => (hhold (Counter.site ring root t)).1)
            ((hhold (Counter.site ring root j)).2.trans hp)
    · have hf := bankSlotOutsidePrefixDigitsFrame ring r e root j hex
      exact keep (fun t ht htm => congrArg Agent.tok (hf t ht htm).1)
        ((congrArg RenewalBankSite.worker
          (hf j hs.toEligibleAt.positive (Nat.le_refl _)).2).trans hp)
  · have keep
        (ht : ∀ t : Nat, 1 ≤ t → t ≤ bankCountWidth n →
          ((renewalBankNext ring r e).1 (Counter.site ring root t)).tok =
            (r.1 (Counter.site ring root t)).tok)
        (hw : ((renewalBankNext ring r e).2.sites
          (Counter.site ring root j)).worker = .pending rho) :
        ∃ j' : Nat, BankSlotAt ring (renewalBankNext ring r e) root j' := by
      refine ⟨j, ?_⟩
      apply bankSlotReturnBuild ring (renewalBankNext ring r e) root j
        hrootRole hrootMode hctl hs.toEligibleAt.positive hjtop
        (bankSlotPrefixRolesNext ring htwo r e root (bankCountWidth n)
          (Nat.le_refl _) hfull hrootRole)
      · intro t htpos htb htj
        rw [ht t htpos htb]
        exact hclean t htpos htb htj
      · exact ⟨rho, hw, ho⟩
      · exact (ht j hs.toEligibleAt.positive (by omega)).trans hrl
    by_cases hex : ∃ k : Nat, k ≤ bankCountWidth n ∧ e = Counter.site ring root k
    · obtain ⟨k, hkb, he⟩ := hex
      have hkpos : 1 ≤ k := by
        by_cases hkzero : k = 0
        · have hezero : e = root := by
            change e = Counter.site ring root 0
            exact he.trans (congrArg (Counter.site ring root) hkzero)
          exact False.elim (hre hezero.symm)
        · omega
      have hx : (r.1 e).pack.val = k := by rw [he]; exact hfull k hkb
      have hright : ring.rightNeighbor e = Counter.site ring root (k + 1) := by
        rw [he]
        rfl
      by_cases htop : k = bankCountWidth n
      · have heTop : e = Counter.site ring root (bankCountWidth n) :=
          he.trans (congrArg (Counter.site ring root) htop)
        have hxTop : (r.1 e).pack.val = bankCountWidth n := hx.trans htop
        have hxE : (r.1 e).tok = .E := by
          rw [heTop]
          exact hclean (bankCountWidth n) (by omega) (Nat.le_refl _) (by omega)
        have hrow := bankSlotPairTopHold (compileAdvice (ceilLogTwo n)) r.2
          e (ring.rightNeighbor e) (r.1 e) (r.1 (ring.rightNeighbor e))
          (by change 0 < (compileAdvice (ceilLogTwo n)).s + 11; omega)
          hxTop (Or.inl hxE)
        have hsrcE : ((renewalBankNext ring r e).1 e).tok = .E :=
          (htok.1.trans hrow.2).trans hxE
        have hwindow : ∀ t : Nat, 1 ≤ t → t ≤ bankCountWidth n →
            ((renewalBankNext ring r e).1 (Counter.site ring root t)).tok =
              (r.1 (Counter.site ring root t)).tok := by
          intro t ht htb
          by_cases hte : Counter.site ring root t = e
          · rw [hte]
            exact hsrcE.trans hxE.symm
          · by_cases htd : Counter.site ring root t = ring.rightNeighbor e
            · have hi := bankSlotResponderIndex ring r e root (bankCountWidth n)
                (bankCountWidth n) t hfull (Nat.le_refl _) htb heTop hrd htd
              omega
            · exact congrArg Agent.tok
                (rbReferenceOutsideSiteFrame ring r e
                  (Counter.site ring root t) hte htd).1
        have hfe : Counter.site ring root j ≠ e := by
          intro hh
          have hi := bankSlotPrefixIndex ring r root (bankCountWidth n)
            hfull j (bankCountWidth n) (by omega) (Nat.le_refl _) (hh.trans heTop)
          omega
        have hfd : Counter.site ring root j ≠ ring.rightNeighbor e := by
          intro hh
          have hi := bankSlotResponderIndex ring r e root (bankCountWidth n)
            (bankCountWidth n) j hfull (Nat.le_refl _) (by omega) heTop hrd hh
          omega
        have hf := (rbReferenceOutsideSiteFrame ring r e
          (Counter.site ring root j) hfe hfd).2
        exact keep hwindow ((congrArg RenewalBankSite.worker hf).trans hp)
      · have hklt : k < bankCountWidth n := by omega
        have hy : (r.1 (ring.rightNeighbor e)).pack.val = k + 1 := by
          rw [hright]
          exact hfull (k + 1) (by omega)
        by_cases hretreat : k + 1 = j
        · have hxE : (r.1 e).tok = .E := by
            rw [he]
            exact hclean k hkpos hkb (by omega)
          have hyRL : (r.1 (ring.rightNeighbor e)).tok = .RL := by
            rw [hright, hretreat]
            exact hrl
          have hnorr : (r.1 e).tok ≠ .RR := by rw [hxE]; intro h; cases h
          have hrow := bankSlotPairRetreat (compileAdvice (ceilLogTwo n))
            r.2 e (ring.rightNeighbor e) (r.1 e) (r.1 (ring.rightNeighbor e))
            k hkpos hklt hx hy hnorr hyRL
          have hpDst : (r.2.sites (ring.rightNeighbor e)).worker = .pending rho := by
            rw [hright, hretreat]
            exact hp
          have hpNew : ((renewalBankNext ring r e).2.sites e).worker =
              .pending rho := by
            change ((rbRun ring r [e]).2.sites e).worker = .pending rho
            rw [hpair.2.2.1, hrow.1]
            exact hpDst
          refine ⟨k, bankSlotBackwardAt ring htwo r e root k hkpos (by omega) he hfull
            (fun t ht htb hne => hclean t ht htb (by omega))
            hrootRole hrootMode hctl (htok.1.trans hrow.2.1)
            (htok.2.trans hrow.2.2) ⟨rho, ?_, ho⟩⟩
          rw [← he]
          exact hpNew
        · have hyE : (r.1 (ring.rightNeighbor e)).tok = .E := by
            rw [hright]
            exact hclean (k + 1) (by omega) (by omega) hretreat
          have hshape :
              ((r.1 e).tok = .E ∧ (r.1 (ring.rightNeighbor e)).tok = .E) ∨
              ((r.1 e).tok = .RL ∧ (r.1 (ring.rightNeighbor e)).tok = .E) ∨
              ((r.1 e).tok = .E ∧ (r.1 (ring.rightNeighbor e)).tok = .RR ∧
                k + 1 ≠ bankCountWidth n) := by
            by_cases hkj : k = j
            · refine Or.inr (Or.inl ⟨?_, hyE⟩)
              rw [he, hkj]
              exact hrl
            · refine Or.inl ⟨?_, hyE⟩
              rw [he]
              exact hclean k hkpos hkb hkj
          have hhold := bankSlotInteriorHoldNext ring htwo r e hbank
            k hkpos hklt hx hy hshape
          exact keep (fun t _ _ => (hhold (Counter.site ring root t)).1)
            ((hhold (Counter.site ring root j)).2.trans hp)
    · have hf := bankSlotOutsidePrefixDigitsFrame
        ring r e root (bankCountWidth n) hex
      exact keep (fun t ht htm => congrArg Agent.tok (hf t ht htm).1)
        ((congrArg RenewalBankSite.worker
          (hf j hs.toEligibleAt.positive (by omega)).2).trans hp)

/-- Select precisely the span whose fields the current phase needs.
When that span reaches the top, its top token is E or RR. -/
theorem bankSlotSpanData {n : Nat}
    (ring : DirectedRing n) (r : RenewalBankReference n)
    (root : Fin n) (j : Nat)
    (hs : BankSlotAt ring r root j) :
    ∃ m : Nat,
      j ≤ m ∧
      m ≤ bankCountWidth n ∧
      ((r.1 (Counter.site ring root j)).tok = .RL →
        m = bankCountWidth n) ∧
      (∀ k : Nat, k ≤ m →
        (r.1 (Counter.site ring root k)).pack.val = k) ∧
      (m = bankCountWidth n →
        (r.1 (Counter.site ring root (bankCountWidth n))).tok = .E ∨
        (r.1 (Counter.site ring root (bankCountWidth n))).tok = .RR) := by
  rcases hs.phase with hout | hreturn
  · refine ⟨j, Nat.le_refl _, hs.toEligibleAt.leWidth,
      ?_, hs.toEligibleAt.roles, ?_⟩
    · intro hrl
      rw [hout.1] at hrl
      cases hrl
    · intro hjb
      right
      simpa only [hjb] using hout.1
  · rcases hreturn with ⟨hjb, _, hroles, hclean⟩
    refine ⟨bankCountWidth n, hs.toEligibleAt.leWidth,
      Nat.le_refl _, ?_, hroles, ?_⟩
    · intro _
      rfl
    · intro _
      left
      exact hclean (bankCountWidth n)
        (by
          change 1 ≤ (compileAdvice (ceilLogTwo n)).s + 11
          omega)
        (Nat.le_refl _)
        (by omega)

/-- A surviving generated slot at the selected source keeps its
frontier. OLD grant and first-digit RL cannot survive in RWAIT;
the remaining first-digit E/RR rows retain that worker and token. -/
theorem bankSlotRetainedSource {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e root : Fin n) (j : Nat)
    (hr : BankCountInv ring r)
    (hs : BankSlotAt ring r root j)
    (hsource : root = e)
    (hrole : ((renewalBankNext ring r e).1 root).pack.val = 0)
    (hmode : ((renewalBankNext ring r e).1 root).mode = .RWAIT)
    (hcontroller :
      ((renewalBankNext ring r e).2.sites root).controller =
        .waiting []) :
    BankSlotAt ring (renewalBankNext ring r e) root j := by
  subst root
  obtain ⟨m, hjm, hmb, hlimit, hroles, _⟩ :=
    bankSlotSpanData ring r e j hs
  have hx : (r.1 e).pack.val = 0 := hs.toEligibleAt.rootRole
  have hy : (r.1 (ring.rightNeighbor e)).pack.val = 1 := by
    have h := hs.toEligibleAt.roles 1 hs.toEligibleAt.positive
    exact h
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hwide : 1 < (compileAdvice (ceilLogTwo n)).b := by
    change 1 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have htrip :=
    (bankWindowClosureSelectedBankTrip ring hn hbank r e).1
  have hpairMode :=
    congrArg (fun t : Mode × Bool × BTok => t.1) htrip
  change ((renewalBankNext ring r e).1 e).mode =
    (Counter.resetBankOld
      (r.1 e) (r.1 (ring.rightNeighbor e))).1.mode at hpairMode
  have hpairWait :
      (Counter.resetBankOld
        (r.1 e) (r.1 (ring.rightNeighbor e))).1.mode = .RWAIT :=
    hpairMode.symm.trans hmode
  have hg : (r.1 e).grant = false := by
    cases hgrant : (r.1 e).grant with
    | false =>
        rfl
    | true =>
        have hbad :=
          (bankSlotPairOldGrant
            (compileAdvice (ceilLogTwo n)) r.2
            e (ring.rightNeighbor e)
            (r.1 e) (r.1 (ring.rightNeighbor e))
            hb hx hy hgrant).2
        have hfalse := hbad.symm.trans hpairWait
        cases hfalse
  have hnotReturn :
      (r.1 (ring.rightNeighbor e)).tok ≠ .RL := by
    intro hrl
    have hbad :=
      (bankSlotPairAccept
        (compileAdvice (ceilLogTwo n))
        (r.1 e) (r.1 (ring.rightNeighbor e))
        hb hx hy hg hs.toEligibleAt.rootMode hrl).1
    have hfalse := hbad.symm.trans hpairWait
    cases hfalse
  have hfirst :
      (r.1 (ring.rightNeighbor e)).tok = .E ∨
      (r.1 (ring.rightNeighbor e)).tok = .RR := by
    by_cases hjone : j = 1
    · have ht :
          (r.1 (ring.rightNeighbor e)).tok = .RR ∨
          (r.1 (ring.rightNeighbor e)).tok = .RL := by
        simpa only [hjone, Counter.site] using hs.toEligibleAt.resetToken
      rcases ht with hrr | hrl
      · exact Or.inr hrr
      · exact False.elim (hnotReturn hrl)
    · left
      exact hs.toEligibleAt.emptyPrefix 1 (by omega)
        (by
          have hpos := hs.toEligibleAt.positive
          omega)
  have hrow :=
    bankSlotPairRootWait
      (compileAdvice (ceilLogTwo n)) r.2
      e (ring.rightNeighbor e)
      (r.1 e) (r.1 (ring.rightNeighbor e))
      hwide hx hy hg hs.toEligibleAt.rootMode hfirst
  have hf := rbReferenceSelectedPairFrame
    ring (by omega : 2 ≤ n) r e
  have hfirstWorker :
      ((renewalBankNext ring r e).2.sites
        (ring.rightNeighbor e)).worker =
        (r.2.sites (ring.rightNeighbor e)).worker := by
    have h := congrArg
      (fun s : RenewalBankSite n => s.worker) hf.2.2.2
    rw [hrow.1] at h
    exact h
  have hfirstToken :
      ((renewalBankNext ring r e).1 (ring.rightNeighbor e)).tok =
        (r.1 (ring.rightNeighbor e)).tok :=
    (bankSlotNextBankTokens ring (by omega : 2 ≤ n) r e hbank).2.trans
      hrow.2.2
  have hnotSource :
      ∀ k : Nat, 1 ≤ k → k ≤ m →
        Counter.site ring e k ≠ e := by
    intro k hk hkm heq
    have hpk := hroles k hkm
    rw [heq, hx] at hpk
    omega
  have hnotFirst :
      ∀ k : Nat, k ≤ m → k ≠ 1 →
        Counter.site ring e k ≠ ring.rightNeighbor e := by
    intro k hkm hk heq
    have hpk := hroles k hkm
    rw [heq, hy] at hpk
    omega
  refine bankSlotAtTransport ring r (renewalBankNext ring r e)
    e j m hs
    (bankSlotNextEmptyNotPending ring hn hbank r e hr)
    hjm hmb hlimit hrole hmode hcontroller ?_ ?_ ?_
  · exact bankSlotPrefixRolesNext ring (by omega : 2 ≤ n)
      r e e m hmb hroles hrole
  · intro k hk hkm
    by_cases hkone : k = 1
    · subst k
      exact hfirstToken
    · have hframe := rbReferenceOutsideSiteFrame ring r e
        (Counter.site ring e k)
        (hnotSource k hk hkm)
        (hnotFirst k hkm hkone)
      exact congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
        hframe.1
  · obtain ⟨rho, hw, hroot⟩ := hs.toEligibleAt.pending
    refine ⟨rho, ?_, hroot⟩
    by_cases hjone : j = 1
    · subst j
      exact hfirstWorker.trans hw
    · have hframe := rbReferenceOutsideSiteFrame ring r e
        (Counter.site ring e j)
        (hnotSource j hs.toEligibleAt.positive hjm)
        (hnotFirst j hjm hjone)
      exact
        (congrArg (fun s : RenewalBankSite n => s.worker)
          hframe.2).trans hw

/-- A surviving generated slot at the selected responder keeps its
frontier. A positive digit touched as source must be the top digit:
post-PACK zero excludes every source role below b. Its E/RR token
and worker are retained even when the full window wraps to the root. -/
theorem bankSlotRetainedResponder {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e root : Fin n) (j : Nat)
    (hr : BankCountInv ring r)
    (hs : BankSlotAt ring r root j)
    (hresponder : root = ring.rightNeighbor e)
    (hrole : ((renewalBankNext ring r e).1 root).pack.val = 0)
    (hmode : ((renewalBankNext ring r e).1 root).mode = .RWAIT)
    (hcontroller :
      ((renewalBankNext ring r e).2.sites root).controller =
        .waiting []) :
    BankSlotAt ring (renewalBankNext ring r e) root j := by
  subst root
  obtain ⟨m, hjm, hmb, hlimit, hroles, htop⟩ :=
    bankSlotSpanData ring r (ring.rightNeighbor e) j hs
  have hy : (r.1 (ring.rightNeighbor e)).pack.val = 0 :=
    hs.toEligibleAt.rootRole
  have hdiff : ring.rightNeighbor e ≠ e :=
    clockNeighborDifferent ring (by omega : 2 ≤ n) e
  have hresp := bankWindowExactResponderPack ring r e hdiff
  have hpack :
      packNext (r.1 e).pack.val
        (r.1 (ring.rightNeighbor e)).pack.val
        (compileAdvice (ceilLogTwo n)).b = 0 :=
    hresp.symm.trans hrole
  have hb : 0 < (compileAdvice (ceilLogTwo n)).b := by
    change 0 < (compileAdvice (ceilLogTwo n)).s + 11
    omega
  have hf := rbReferenceSelectedPairFrame
    ring (by omega : 2 ≤ n) r e
  have hsourceHold :
      (∃ k : Nat, 1 ≤ k ∧ k ≤ m ∧
        Counter.site ring (ring.rightNeighbor e) k = e) →
      (((renewalBankNext ring r e).1 e).tok = (r.1 e).tok ∧
        ((renewalBankNext ring r e).2.sites e).worker =
          (r.2.sites e).worker) := by
    rintro ⟨k, hk, hkm, hsite⟩
    have hx : (r.1 e).pack.val = k := by
      simpa only [hsite] using hroles k hkm
    have hzero :
        packNext k 0 (compileAdvice (ceilLogTwo n)).b = 0 := by
      simpa only [hx, hy] using hpack
    have hkb : k = bankCountWidth n := by
      by_cases hlt : k < (compileAdvice (ceilLogTwo n)).b
      · have hbad : k + 1 = 0 := by
          simpa only [packNext, if_pos hlt] using hzero
        omega
      · change k = (compileAdvice (ceilLogTwo n)).b
        change m ≤ (compileAdvice (ceilLogTwo n)).b at hmb
        omega
    have hmbEq : m = bankCountWidth n := by omega
    have htopSite :
        Counter.site ring (ring.rightNeighbor e)
          (bankCountWidth n) = e := by
      simpa only [hkb] using hsite
    have htoken : (r.1 e).tok = .E ∨ (r.1 e).tok = .RR := by
      simpa only [htopSite] using htop hmbEq
    have hxTop : (r.1 e).pack.val =
        (compileAdvice (ceilLogTwo n)).b := hx.trans hkb
    have hrow :=
      bankSlotPairTopHold
        (compileAdvice (ceilLogTwo n)) r.2
        e (ring.rightNeighbor e)
        (r.1 e) (r.1 (ring.rightNeighbor e))
        hb hxTop htoken
    constructor
    · exact
        (bankSlotNextBankTokens
          ring (by omega : 2 ≤ n) r e hbank).1.trans hrow.2
    · have h := congrArg
        (fun s : RenewalBankSite n => s.worker) hf.2.2.1
      exact h.trans hrow.1
  have hnotRoot :
      ∀ k : Nat, 1 ≤ k → k ≤ m →
        Counter.site ring (ring.rightNeighbor e) k ≠
          ring.rightNeighbor e := by
    intro k hk hkm heq
    have hpk := hroles k hkm
    rw [heq, hy] at hpk
    omega
  refine bankSlotAtTransport ring r (renewalBankNext ring r e)
    (ring.rightNeighbor e) j m hs
    (bankSlotNextEmptyNotPending ring hn hbank r e hr)
    hjm hmb hlimit hrole hmode hcontroller ?_ ?_ ?_
  · exact bankSlotPrefixRolesNext ring (by omega : 2 ≤ n)
      r e (ring.rightNeighbor e) m hmb hroles hrole
  · intro k hk hkm
    by_cases heq :
        Counter.site ring (ring.rightNeighbor e) k = e
    · have hhold := hsourceHold ⟨k, hk, hkm, heq⟩
      simpa only [heq] using hhold.1
    · have hframe := rbReferenceOutsideSiteFrame ring r e
        (Counter.site ring (ring.rightNeighbor e) k)
        heq (hnotRoot k hk hkm)
      exact congrArg
        (fun a : Agent (compileAdvice (ceilLogTwo n)) => a.tok)
        hframe.1
  · obtain ⟨rho, hw, hroot⟩ := hs.toEligibleAt.pending
    refine ⟨rho, ?_, hroot⟩
    by_cases heq :
        Counter.site ring (ring.rightNeighbor e) j = e
    · have hhold :=
        hsourceHold ⟨j, hs.toEligibleAt.positive, hjm, heq⟩
      have hwOld : (r.2.sites e).worker = .pending rho := by
        simpa only [heq] using hw
      have hwNew :
          ((renewalBankNext ring r e).2.sites e).worker =
            .pending rho := hhold.2.trans hwOld
      simpa only [heq] using hwNew
    · have hframe := rbReferenceOutsideSiteFrame ring r e
        (Counter.site ring (ring.rightNeighbor e) j)
        heq (hnotRoot j hs.toEligibleAt.positive hjm)
      exact
        (congrArg (fun s : RenewalBankSite n => s.worker)
          hframe.2).trans hw

/-- The generated clause, with every edge classified by its literal
row and its position relative to the certified slot. -/
theorem bankSlotGeneratedNext {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hr : BankCountInv ring r) (hs : BankSlotInv ring r) :
    ∀ root : Fin n,
      ((renewalBankNext ring r e).1 root).pack.val = 0 →
      ((renewalBankNext ring r e).1 root).mode = .RWAIT →
      ((renewalBankNext ring r e).2.sites root).controller =
        .waiting [] →
      ∃ j : Nat, BankSlotAt ring (renewalBankNext ring r e) root j := by
  classical
  intro root hrole hmode hcontroller
  rcases bankSlotGeneratedRootBack ring hn hbank r e root
      hrole hmode hcontroller with hlaunch | hretained
  · obtain ⟨hsource, hguard⟩ := hlaunch
    subst root
    exact ⟨1, bankSlotLaunchNext ring hn hbank r e hr hguard⟩
  · obtain ⟨hroleOld, hmodeOld, hcontrollerOld⟩ := hretained
    obtain ⟨j, hslot⟩ :=
      hs.generated root hroleOld hmodeOld hcontrollerOld
    by_cases htouch :
        BankSlotOwnsSite ring r root e ∨
        BankSlotOwnsSite ring r root (ring.rightNeighbor e)
    · by_cases hsource : root = e
      · exact ⟨j, bankSlotRetainedSource ring hn hbank r e root j
          hr hslot hsource hrole hmode hcontroller⟩
      · by_cases hresponder : root = ring.rightNeighbor e
        · exact ⟨j, bankSlotRetainedResponder ring hn hbank r e root j
            hr hslot hresponder hrole hmode hcontroller⟩
        · exact bankSlotRetainedNonincident ring hn hbank r e root j
            hr hslot hsource hresponder
    · refine ⟨j, bankSlotAtNextOfUntouchedOwner ring r root e j hslot ?_ ?_⟩
      · intro howner
        exact htouch (Or.inl howner)
      · intro howner
        exact htouch (Or.inr howner)

theorem bankSlotInvNext {n : Nat} (ring : DirectedRing n)
    (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (r : RenewalBankReference n) (e : Fin n)
    (hr : BankCountInv ring r) (hs : BankSlotInv ring r) :
    BankSlotInv ring (renewalBankNext ring r e) := by
  exact {
    generated := bankSlotGeneratedNext ring hn hbank r e hr hs
    inherited := bankSlotInheritedNext ring hn r e hr }

end L3.Prime

#print axioms L3.Prime.bankSlotNextOutsideFrame
#print axioms L3.Prime.bankSlotTouchedRootsAtMostTwo
#print axioms L3.Prime.bankInheritedReceiptFreeOfCount
#print axioms L3.Prime.bankSlotGeneratedNext
#print axioms L3.Prime.bankSlotInvNext


namespace L3.Prime

open L3.HeadlineRenewal
open L3.HeadlineRenewalCleanBank
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- **U3 closed.** The BANK local potential step (`BankCountStepBound`), from slot
preservation (`bankSlotInvNext`, U3a) and the drift under slots at both ends
(`bankCountPotentialStepOfSlots`, U3b). -/
theorem bankCountPotentialStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankCountStepBound ring := by
  intro r e h
  exact bankCountPotentialStepOfSlots ring hn hbank r e h.1 h.2
    (bankSlotInvNext ring hn hbank r e h.1 h.2)

/-- **T2.1 on the clean BANK reference (`lem:l3prime-count`), unconditional.**
`(b-h)(h+1) * originsNumerator ≤ (b-h)(h+1) * n^T n + costNumerator`. -/
theorem bankCleanReferenceOriginChargeSharp {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    let b := bankCountWidth n
    let h := bankCountHalf n
    let D := bankCleanRootedReferenceData ring hbank
    ∀ seed : RootedSeed ring,
      ¬ headlineGeneratedTarget ring seed.val → ∀ T : Nat,
        ((b - h) * (h + 1)) *
            Prob.originsNumerator D.referenceNext D.referenceStop
              D.spawn (D.referenceStart seed) T ≤
          ((b - h) * (h + 1)) * (n ^ T * n) +
            costNumerator D.referenceNext D.referenceStop
              (D.referenceStart seed) T :=
  bankCleanReferenceOriginChargeSharpOfStep ring hn hbank
    (fun r e h => bankSlotInvNext ring hn hbank r e h.1 h.2)
    (bankCountPotentialStep ring hn hbank)

end L3.Prime

#print axioms L3.Prime.bankCountPotentialStep
#print axioms L3.Prime.bankCleanReferenceOriginChargeSharp
