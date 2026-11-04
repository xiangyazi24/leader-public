import Leader.L3.Bank.RepairReaderWordValues

/-!
R10 finish with every producer discharged.

Premise map: research/lean-l3/ledgers/R10-finish-map.md.

* Receipt preservation.  The installed `BankRepairReceiptPreservation`
  quantifies over every reference state, including states with OLD
  grants, where no-FIRE and the projected W/R/D steps fail.  The finish
  only uses it at states reached from `BankPreparedAtSomeRoot`, all in
  the closed `BankPostInheritedGrantDrain`.  The drain-guarded five
  closures are proved here from the BANK pieces (the BANK twin of
  `smallRepairReceiptPreservationOnGuardProved`).
* Debt stage (repair.tex 5367-5374).  On the drain, every DBarred state
  has QReader and QDigit, so every OLD pair runs the quiet DCC row: both
  endpoints leave with EU = ED = false and no other site changes.  Each
  debt site is cleared by its two incident edges.  A concave potential
  in the number d of debt sites, with increments n/(2k)+1, has drift one
  and total at most n²/2: the stage holds at its 1 half-unit budget.
* Stop stage: `bankRepairStopStageProved`.

Left open: the AcceptedWord completion premise (W monitor), the digit
half-stage (R10c) and the request half-stage, each on its drain class.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-! ## Drain-guarded receipt preservation -/

/-- Core closure on the drain.  Consumer: `bankFinishCleanPreservation`. -/
theorem bankFinishCleanCoreStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hD : BankPostInheritedGrantDrain ring hbank z)
    (hc : BankRepairCore ring hbank z) (e : Fin n) :
    BankRepairCore ring hbank (bankRepairNext ring hbank z e) := by
  have hnative := bankAfterGrantDrainNativeStep ring hn hbank z hD.1 e
  change nativeProjection
      ((bankValidRootedReferenceData ring hbank).referenceNext z e).val.1 =
    nativeE ring (nativeProjection z.val.1) e at hnative
  have hsector := nativeE_preserves_singleton_C_native
    hn ring (nativeProjection z.val.1) e ⟨hc.1.1, hc.1.2.2⟩
  constructor
  · change OneNativeLeader (nativeProjection
        ((bankValidRootedReferenceData ring hbank).referenceNext z e).val.1) ∧
      Protected ring (nativeProjection
        ((bankValidRootedReferenceData ring hbank).referenceNext z e).val.1) ∧
      C_native ring (nativeProjection
        ((bankValidRootedReferenceData ring hbank).referenceNext z e).val.1)
    rw [hnative]
    exact ⟨hsector.1, hsector.2.1.1, hsector.2⟩
  · change H_cand ring (bankValidCandidateView ring hbank
      ((bankValidRootedReferenceData ring hbank).referenceNext z e))
    rw [bankPostInheritedCandidateStep ring hn hbank z hD e]
    exact H_cand_birthFree_step ring (bankValidCandidateView ring hbank z) e hc.2

/-- Reader-factor closure on the drain.  Consumer: `bankFinishCleanPreservation`. -/
theorem bankFinishCleanReaderStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hD : BankPostInheritedGrantDrain ring hbank z)
    (hr : BankRepairReader ring hbank z) (e : Fin n) :
    BankRepairReader ring hbank (bankRepairNext ring hbank z e) := by
  have hphi := bankRepairReaderPhiStepOfNoFire ring (by omega) hbank z e
    (bankRepairCloseNoFireOfDrain ring hbank z hD e)
  change AcceptedReceipts.AcceptedReader ring
    (AcceptedReceipts.AcceptedWord ring
      (BlockA.wordT ring) (BlockA.wordValidated ring))
    (Closure.readerFoldValid (ceilLogTwo n) n)
    (piR z.val.1) at hr
  change AcceptedReceipts.AcceptedReader ring
    (AcceptedReceipts.AcceptedWord ring
      (BlockA.wordT ring) (BlockA.wordValidated ring))
    (Closure.readerFoldValid (ceilLogTwo n) n)
    (piR (bankRepairNext ring hbank z e).val.1)
  rw [hphi]
  exact Closure.readerGeneratedPhiStep (by omega)
    (ClosureFull.adviceWidthPositive (ceilLogTwo n)) ring
    (AcceptedReceipts.AcceptedWord ring
      (BlockA.wordT ring) (BlockA.wordValidated ring))
    (piR z.val.1) e hr

/-- Digit-factor closure on the drain.  Consumer: `bankFinishCleanPreservation`. -/
theorem bankFinishCleanDigitStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hD : BankPostInheritedGrantDrain ring hbank z)
    (hd : BankRepairDigit ring hbank z) (e : Fin n) :
    BankRepairDigit ring hbank (bankRepairNext ring hbank z e) := by
  have hphi := bankRepairDigitMaskedProjectionOfNoFire ring hbank z e
    (bankRepairCloseNoFireOfDrain ring hbank z hD e)
  change AcceptedReceipts.BarredDigitClass ring
    (AcceptedReceipts.AcceptedWordAtRoot ring
      (BlockA.wordT ring) (BlockA.wordValidated ring))
    (piD z.val.1) at hd
  change AcceptedReceipts.BarredDigitClass ring
    (AcceptedReceipts.AcceptedWordAtRoot ring
      (BlockA.wordT ring) (BlockA.wordValidated ring))
    (piD (bankRepairNext ring hbank z e).val.1)
  rw [hphi]
  exact Closure.digitGeneratedPhiStep (by omega) ring (piD z.val.1) e hd

/-- Under the quiet DCC event both selected endpoints leave with no
debt.  Consumer: `bankFinishCleanDebtEndpoints`. -/
theorem bankFinishCleanQuietDcc {c : Compiled} (x y : Agent c) :
    (dccStep x y Closure.readerDigitQuietEvent).xEU = false ∧
      (dccStep x y Closure.readerDigitQuietEvent).xED = false ∧
      (dccStep x y Closure.readerDigitQuietEvent).yEU = false ∧
      (dccStep x y Closure.readerDigitQuietEvent).yED = false := by
  cases h1 : x.EU <;> cases h2 : x.ED <;> cases h3 : y.EU <;> cases h4 : y.ED <;>
    simp [dccStep, Closure.readerDigitQuietEvent, h1, h2, h3, h4]

/-- One masked BANK edge from a Reader ∧ Digit state: both endpoints
leave with EU = ED = false, every other site is unchanged.
Consumer: `bankFinishCleanDebtStep`, `bankFinishCleanDebtBitStep`. -/
theorem bankFinishCleanDebtEndpoints {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hreader : BankRepairReader ring hbank z)
    (hdigit : BankRepairDigit ring hbank z) (e : Fin n) :
    ((bankRepairNext ring hbank z e).val.1 e).EU = false ∧
      ((bankRepairNext ring hbank z e).val.1 e).ED = false ∧
      ((bankRepairNext ring hbank z e).val.1 (ring.rightNeighbor e)).EU = false ∧
      ((bankRepairNext ring hbank z e).val.1 (ring.rightNeighbor e)).ED = false ∧
      (∀ i : Fin n, i ≠ e → i ≠ ring.rightNeighbor e →
        (bankRepairNext ring hbank z e).val.1 i = z.val.1 i) := by
  have hne := clockNeighborDifferent ring (by omega) e
  have hQReader : AcceptedReceipts.QReader ring (piR z.val.1) :=
    AcceptedReceipts.accepted_reader_qreader ring
      (AcceptedReceipts.AcceptedWord ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      (Closure.readerFoldValid (ceilLogTwo n) n)
      (piR z.val.1) hreader
  have hQDigit : AcceptedReceipts.QDigit ring (piD z.val.1) :=
    AcceptedReceipts.barred_digit_qdigit ring
      (AcceptedReceipts.AcceptedWordAtRoot ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      (piD z.val.1) hdigit
  have hev := Closure.certificateEventQuietFromSafe
    (by omega) ring z.val.1 e hQReader hQDigit
  have hq := bankFinishCleanQuietDcc (z.val.1 e) (z.val.1 (ring.rightNeighbor e))
  have hx := Closure.transitionDebtSourceFormula
    (compileAdvice (ceilLogTwo n))
    (z.val.1 e) (z.val.1 (ring.rightNeighbor e))
  have hy := Closure.transitionDebtDestinationFormula
    (compileAdvice (ceilLogTwo n))
    (z.val.1 e) (z.val.1 (ring.rightNeighbor e))
  rw [hev] at hx hy
  rw [hq.1, hq.2.1] at hx
  rw [hq.2.2.1, hq.2.2.2] at hy
  have hmaskX :
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring z.val.1 z.val.2 e)
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).1.EU = false ∧
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring z.val.1 z.val.2 e)
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).1.ED = false := by
    cases hm : renewalBankCut ring z.val.1 z.val.2 e with
    | false => simpa [renewalMaskedPair, hm] using hx
    | true => simpa [renewalMaskedPair, hm] using hx
  have hmaskY :
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring z.val.1 z.val.2 e)
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).2.EU = false ∧
      (renewalMaskedPair (compileAdvice (ceilLogTwo n))
        (renewalBankCut ring z.val.1 z.val.2 e)
        (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).2.ED = false := by
    cases hm : renewalBankCut ring z.val.1 z.val.2 e with
    | false => simpa [renewalMaskedPair, hm] using hy
    | true => simpa [renewalMaskedPair, hm] using hy
  have hstep : ∀ i : Fin n, (bankRepairNext ring hbank z e).val.1 i =
      (if i = e then
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalBankCut ring z.val.1 z.val.2 e)
          (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).1
       else if i = ring.rightNeighbor e then
        (renewalMaskedPair (compileAdvice (ceilLogTwo n))
          (renewalBankCut ring z.val.1 z.val.2 e)
          (z.val.1 e) (z.val.1 (ring.rightNeighbor e))).2
       else z.val.1 i) := fun i => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [hstep, ↓reduceIte]; exact hmaskX.1
  · simp only [hstep, ↓reduceIte]; exact hmaskX.2
  · simp only [hstep, if_neg hne, ↓reduceIte]; exact hmaskY.1
  · simp only [hstep, if_neg hne, ↓reduceIte]; exact hmaskY.2
  · intro i hi hj
    simp only [hstep, if_neg hi]
    exact if_neg hj

/-- DebtZero closure from Reader ∧ Digit.  Consumer: `bankFinishCleanPreservation`. -/
theorem bankFinishCleanDebtStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hreader : BankRepairReader ring hbank z)
    (hdigit : BankRepairDigit ring hbank z)
    (hdebt : BankRepairDebtZero ring hbank z) (e : Fin n) :
    BankRepairDebtZero ring hbank (bankRepairNext ring hbank z e) := by
  obtain ⟨h1, h2, h3, h4, hother⟩ :=
    bankFinishCleanDebtEndpoints ring hn hbank z hreader hdigit e
  intro i
  by_cases hi : i = e
  · subst hi; exact ⟨h1, h2⟩
  · by_cases hj : i = ring.rightNeighbor e
    · subst hj; exact ⟨h3, h4⟩
    · rw [hother i hi hj]; exact hdebt i

/-- The five receipt closures, each guarded by the drain.
Consumer: `bankFinishMaskedRepairBoundClean`. -/
def BankRepairReceiptPreservationOnDrain {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  (∀ z, BankPostInheritedGrantDrain ring hbank z → BankRepairCore ring hbank z →
    ∀ e, BankRepairCore ring hbank (bankRepairNext ring hbank z e)) ∧
  (∀ z, BankPostInheritedGrantDrain ring hbank z →
    BankRepairWAccepted ring hbank z →
    ∀ e, BankRepairWAccepted ring hbank (bankRepairNext ring hbank z e)) ∧
  (∀ z, BankPostInheritedGrantDrain ring hbank z →
    BankRepairRFoldEstablished ring hbank z →
    ∀ e, BankRepairRFoldEstablished ring hbank (bankRepairNext ring hbank z e)) ∧
  (∀ z, BankPostInheritedGrantDrain ring hbank z →
    BankRepairDBarred ring hbank z →
    ∀ e, BankRepairDBarred ring hbank (bankRepairNext ring hbank z e)) ∧
  (∀ z, BankPostInheritedGrantDrain ring hbank z →
    BankRepairDebtCleared ring hbank z →
    ∀ e, BankRepairDebtCleared ring hbank (bankRepairNext ring hbank z e))

/-- The drain-guarded receipt preservation, from the earlier pieces only.
Consumer: `bankFinishMaskedRepairBoundClean`. -/
theorem bankFinishCleanPreservation {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankRepairReceiptPreservationOnDrain ring hbank := by
  have hW : ∀ z, BankPostInheritedGrantDrain ring hbank z →
      BankRepairWAccepted ring hbank z →
      ∀ e, BankRepairWAccepted ring hbank (bankRepairNext ring hbank z e) :=
    fun z hD hz e => ⟨bankFinishCleanCoreStep ring hn hbank z hD hz.1 e,
      bankWordAcceptedReferenceStep ring hn hbank z hD hz.2 e⟩
  have hR : ∀ z, BankPostInheritedGrantDrain ring hbank z →
      BankRepairRFoldEstablished ring hbank z →
      ∀ e, BankRepairRFoldEstablished ring hbank (bankRepairNext ring hbank z e) :=
    fun z hD hz e => ⟨hW z hD hz.1 e,
      bankFinishCleanReaderStep ring hn hbank z hD hz.2 e⟩
  have hDb : ∀ z, BankPostInheritedGrantDrain ring hbank z →
      BankRepairDBarred ring hbank z →
      ∀ e, BankRepairDBarred ring hbank (bankRepairNext ring hbank z e) :=
    fun z hD hz e => ⟨hR z hD hz.1 e,
      bankFinishCleanDigitStep ring hn hbank z hD hz.2 e⟩
  refine ⟨fun z hD hz e => bankFinishCleanCoreStep ring hn hbank z hD hz e,
    hW, hR, hDb, ?_⟩
  intro z hD hz e
  exact ⟨hDb z hD hz.1 e,
    bankFinishCleanDebtStep ring hn hbank z hz.1.1.2 hz.1.2 hz.2 e⟩

/-! ## The debt stage on the drain -/

/-- One debt bit per site.  Consumer: `bankFinishCleanDebtCount`. -/
def bankFinishCleanDebtBit {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) (i : Fin n) : Nat :=
  if ((z.val.1 i).EU || (z.val.1 i).ED) = true then 1 else 0

/-- Number of debt sites.  Consumer: `bankFinishCleanDebtStage`. -/
def bankFinishCleanDebtCount {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Nat :=
  (List.ofFn (bankFinishCleanDebtBit ring hbank z)).sum

/-- Concave potential in the number of debt sites: increments
n/(2k)+1.  Consumer: `bankFinishCleanDebtStage`. -/
def bankFinishCleanDebtPotential (n : Nat) : Nat → Nat
  | 0 => 0
  | d + 1 => bankFinishCleanDebtPotential n d + (n / (2 * (d + 1)) + 1)

/-- Concavity: removing δ ≤ d debt sites lowers the potential by at
least δ copies of the top increment.  Consumer: `bankFinishCleanDebtDrift`. -/
theorem bankFinishCleanPotentialConcave (n d : Nat) :
    ∀ δ : Nat, δ ≤ d →
      bankFinishCleanDebtPotential n (d - δ) + δ * (n / (2 * d) + 1) ≤
        bankFinishCleanDebtPotential n d := by
  intro δ
  induction δ with
  | zero => intro _; simp
  | succ δ ih =>
      intro hδ
      have hprev := ih (by omega)
      have hd : d - δ = (d - (δ + 1)) + 1 := by omega
      have hstep : bankFinishCleanDebtPotential n (d - δ) =
          bankFinishCleanDebtPotential n (d - (δ + 1)) +
            (n / (2 * (d - δ)) + 1) := by
        rw [hd]; rfl
      have hmono : n / (2 * d) ≤ n / (2 * (d - δ)) :=
        Nat.div_le_div_left (by omega) (by omega)
      rw [Nat.succ_mul]
      omega

/-- The potential is monotone.  Consumer: `bankFinishCleanDebtStage`. -/
theorem bankFinishCleanPotentialMono (n : Nat) :
    ∀ a b : Nat, a ≤ b →
      bankFinishCleanDebtPotential n a ≤ bankFinishCleanDebtPotential n b := by
  intro a b hab
  have h := bankFinishCleanPotentialConcave n b (b - a) (by omega)
  rw [show b - (b - a) = a by omega] at h
  omega

/-- Linear-growth bound after the first two increments.
Consumer: `bankFinishCleanPotentialHalf`. -/
theorem bankFinishCleanPotentialLinear (n : Nat) :
    ∀ d : Nat, 6 * bankFinishCleanDebtPotential n (d + 2) ≤
      5 * n + 12 + d * (n + 6) := by
  intro d
  induction d with
  | zero =>
      show 6 * (0 + (n / (2 * (0 + 1)) + 1) + (n / (2 * (1 + 1)) + 1)) ≤
        5 * n + 12 + 0 * (n + 6)
      have h1 := Nat.div_add_mod n 2
      have h2 := Nat.div_add_mod n 4
      have h1' : n / (2 * (0 + 1)) = n / 2 := rfl
      have h2' : n / (2 * (1 + 1)) = n / 4 := rfl
      rw [h1', h2']
      omega
  | succ d ih =>
      have hs : bankFinishCleanDebtPotential n (d + 1 + 2) =
          bankFinishCleanDebtPotential n (d + 2) +
            (n / (2 * (d + 2 + 1)) + 1) := rfl
      have hle : n / (2 * (d + 2 + 1)) ≤ n / 6 :=
        Nat.div_le_div_left (by omega) (by omega)
      have h6 := Nat.div_add_mod n 6
      have hg : (d + 1) * (n + 6) = d * (n + 6) + (n + 6) := Nat.succ_mul d (n + 6)
      rw [hs, hg]
      omega

/-- The potential never exceeds n²/2 on at most n debt sites (n ≥ 5).
Consumer: `bankFinishCleanDebtStage`. -/
theorem bankFinishCleanPotentialHalf (n : Nat) (hn : 5 ≤ n) (d : Nat)
    (hd : d ≤ n) :
    2 * bankFinishCleanDebtPotential n d ≤ n ^ 2 := by
  have hmono := bankFinishCleanPotentialMono n d n hd
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hlin := bankFinishCleanPotentialLinear (m + 2) m
  have hsq : (m + 2) ^ 2 = m * m + 4 * m + 4 := by
    rw [Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.mul_add]
    omega
  have hmm : m * (m + 2 + 6) = m * m + 8 * m := by
    rw [Nat.mul_add, Nat.mul_add]
    omega
  have h3 : 3 * m ≤ m * m := Nat.mul_le_mul_right m (by omega)
  rw [hsq]
  rw [hmm] at hlin
  omega

/-- Swapping a finite double sum.  Consumer: `bankFinishCleanDebtCountStep`. -/
theorem bankFinishCleanSumSwap : ∀ {m k : Nat} (F : Fin m → Fin k → Nat),
    (List.ofFn (fun e : Fin m => (List.ofFn (fun i : Fin k => F e i)).sum)).sum =
      (List.ofFn (fun i : Fin k => (List.ofFn (fun e : Fin m => F e i)).sum)).sum
  | 0, k, F => by
      simp only [List.ofFn_zero, List.sum_nil]
      rw [ofFn_sum_const]
      simp
  | m + 1, k, F => by
      rw [List.ofFn_succ, List.sum_cons, bankFinishCleanSumSwap
        (fun e : Fin m => fun i : Fin k => F e.succ i), ← ofFn_sum_add]
      have hfun : (fun i : Fin k => F 0 i +
          (List.ofFn (fun e : Fin m => F e.succ i)).sum) =
          (fun i : Fin k => (List.ofFn (fun e : Fin (m + 1) => F e i)).sum) := by
        funext i
        rw [List.ofFn_succ, List.sum_cons]
      rw [hfun]

/-- The left neighbour's outgoing edge reaches the site.
Consumer: `bankFinishCleanDebtCountStep`. -/
theorem bankFinishCleanRightOfLeft {n : Nat} (ring : DirectedRing n)
    (i : Fin n) : ring.rightNeighbor (ring.leftNeighbor i) = i := by
  apply Fin.ext
  show ((i.val + n - 1) % n + 1) % n = i.val
  have hn := ring.hn
  have hi := i.isLt
  rw [Nat.mod_add_mod, show i.val + n - 1 + 1 = i.val + n by omega,
    Nat.add_mod_right]
  exact Nat.mod_eq_of_lt hi

/-- Each debt site is cleared by its two incident edges and no site
gains debt: summed over all n edges, the next debt counts are at most
(n-2) times the current one.  Consumer: `bankFinishCleanDebtDrift`. -/
theorem bankFinishCleanDebtCountStep {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hreader : BankRepairReader ring hbank z)
    (hdigit : BankRepairDigit ring hbank z) :
    (List.ofFn (fun e : Fin n =>
        bankFinishCleanDebtCount ring hbank (bankRepairNext ring hbank z e))).sum +
      2 * bankFinishCleanDebtCount ring hbank z ≤
      n * bankFinishCleanDebtCount ring hbank z := by
  have hsite : ∀ i : Fin n,
      (List.ofFn (fun e : Fin n =>
          bankFinishCleanDebtBit ring hbank (bankRepairNext ring hbank z e) i)).sum +
        2 * bankFinishCleanDebtBit ring hbank z i ≤
        n * bankFinishCleanDebtBit ring hbank z i := by
    intro i
    have hcell : ∀ e : Fin n,
        bankFinishCleanDebtBit ring hbank (bankRepairNext ring hbank z e) i ≤
          (if e = i then 0 else if e = ring.leftNeighbor i then 0
            else bankFinishCleanDebtBit ring hbank z i) := by
      intro e
      obtain ⟨h1, h2, h3, h4, hother⟩ :=
        bankFinishCleanDebtEndpoints ring hn hbank z hreader hdigit e
      by_cases hei : e = i
      · subst hei
        simp [bankFinishCleanDebtBit, h1, h2]
      · rw [if_neg hei]
        by_cases hel : e = ring.leftNeighbor i
        · rw [if_pos hel]
          have hj : ring.rightNeighbor e = i := by
            rw [hel]; exact bankFinishCleanRightOfLeft ring i
          rw [← hj]
          simp [bankFinishCleanDebtBit, h3, h4]
        · rw [if_neg hel]
          have hij : i ≠ ring.rightNeighbor e := by
            intro h
            apply hel
            have hl : ring.leftNeighbor (ring.rightNeighbor e) = e := by
              apply Fin.ext
              show ((((e.val + 1) % n) + n - 1) % n) = e.val
              have hn' := ring.hn
              have he := e.isLt
              by_cases hlast : e.val + 1 < n
              · rw [Nat.mod_eq_of_lt hlast,
                  show e.val + 1 + n - 1 = e.val + n by omega,
                  Nat.add_mod_right]
                exact Nat.mod_eq_of_lt he
              · have hev : e.val + 1 = n := by omega
                rw [hev, Nat.mod_self, show 0 + n - 1 = e.val by omega]
                exact Nat.mod_eq_of_lt he
            rw [h, hl]
          unfold bankFinishCleanDebtBit
          rw [hother i (Ne.symm hei) hij]
          exact Nat.le_refl _
    have hsum := ofFn_sum_le _ _ hcell
    have hli : ring.leftNeighbor i ≠ i := by
      intro h
      have := clockNeighborDifferent ring (by omega) (ring.leftNeighbor i)
      rw [bankFinishCleanRightOfLeft ring i] at this
      exact this h.symm
    have htwo := bankRepairCloseSumTwoCells
      (fun _ : Fin n => bankFinishCleanDebtBit ring hbank z i)
      (fun e : Fin n => if e = i then 0 else if e = ring.leftNeighbor i then 0
        else bankFinishCleanDebtBit ring hbank z i)
      i (ring.leftNeighbor i) hli
      (fun e he hel => by simp [he, hel])
    simp only [↓reduceIte, if_neg hli] at htwo
    rw [ofFn_sum_const] at htwo
    have hcomm := Nat.mul_comm (bankFinishCleanDebtBit ring hbank z i) n
    omega
  have hall := ofFn_sum_le _ _ hsite
  rw [ofFn_sum_add] at hall
  have hswap := bankFinishCleanSumSwap
    (fun e i => bankFinishCleanDebtBit ring hbank (bankRepairNext ring hbank z e) i)
  unfold bankFinishCleanDebtCount
  rw [hswap]
  rw [ofFn_sum_mul_left, ofFn_sum_mul_left] at hall
  exact hall

/-- Debt count zero is exactly the debt-free target.
Consumer: `bankFinishCleanDebtStage`. -/
theorem bankFinishCleanDebtZeroOfCount {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (h : ¬ BankRepairDebtZero ring hbank z) :
    1 ≤ bankFinishCleanDebtCount ring hbank z := by
  have hex : ∃ i : Fin n, bankFinishCleanDebtBit ring hbank z i = 1 := by
    apply Classical.byContradiction
    intro hno
    apply h
    intro i
    have hb : bankFinishCleanDebtBit ring hbank z i ≠ 1 := fun hb => hno ⟨i, hb⟩
    unfold bankFinishCleanDebtBit at hb
    cases hu : (z.val.1 i).EU <;> cases hd : (z.val.1 i).ED <;> simp_all
  obtain ⟨i, hi⟩ := hex
  have hcell := bankRepairCloseSumExchange
    (bankFinishCleanDebtBit ring hbank z)
    (fun j => if j = i then 0 else bankFinishCleanDebtBit ring hbank z j) i
    (fun j hj => by simp [hj])
  simp only [↓reduceIte] at hcell
  unfold bankFinishCleanDebtCount
  omega

/-- At most n debt sites.  Consumer: `bankFinishCleanDebtStage`. -/
theorem bankFinishCleanDebtCountLe {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) :
    bankFinishCleanDebtCount ring hbank z ≤ n := by
  have h := ofFn_sum_le (bankFinishCleanDebtBit ring hbank z) (fun _ => 1)
    (fun i => by unfold bankFinishCleanDebtBit; split <;> omega)
  rw [ofFn_sum_const] at h
  unfold bankFinishCleanDebtCount
  omega

/-- The Bellman drift of the debt potential on the drain-DBarred class.
Consumer: `bankFinishCleanDebtStage`. -/
theorem bankFinishCleanDebtDrift {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hreader : BankRepairReader ring hbank z)
    (hdigit : BankRepairDigit ring hbank z)
    (hnot : ¬ BankRepairDebtZero ring hbank z) :
    n + (List.ofFn (fun e : Fin n => bankFinishCleanDebtPotential n
        (bankFinishCleanDebtCount ring hbank (bankRepairNext ring hbank z e)))).sum ≤
      n * bankFinishCleanDebtPotential n (bankFinishCleanDebtCount ring hbank z) := by
  let d := bankFinishCleanDebtCount ring hbank z
  let de := fun e : Fin n =>
    bankFinishCleanDebtCount ring hbank (bankRepairNext ring hbank z e)
  let a := n / (2 * d) + 1
  have hd1 : 1 ≤ d := bankFinishCleanDebtZeroOfCount ring hbank z hnot
  have hcount := bankFinishCleanDebtCountStep ring hn hbank z hreader hdigit
  have hle : ∀ e, de e ≤ d := by
    intro e
    have hstep := bankFinishCleanDebtCountStep ring hn hbank z hreader hdigit
    -- pointwise: every site's bit does not increase
    have hbit : ∀ i, bankFinishCleanDebtBit ring hbank (bankRepairNext ring hbank z e) i ≤
        bankFinishCleanDebtBit ring hbank z i := by
      intro i
      obtain ⟨h1, h2, h3, h4, hother⟩ :=
        bankFinishCleanDebtEndpoints ring hn hbank z hreader hdigit e
      by_cases hie : i = e
      · subst hie; simp [bankFinishCleanDebtBit, h1, h2]
      · by_cases hij : i = ring.rightNeighbor e
        · subst hij; simp [bankFinishCleanDebtBit, h3, h4]
        · unfold bankFinishCleanDebtBit; rw [hother i hie hij]; exact Nat.le_refl _
    exact ofFn_sum_le _ _ hbit
  have hper : ∀ e, bankFinishCleanDebtPotential n (de e) + (d - de e) * a ≤
      bankFinishCleanDebtPotential n d := by
    intro e
    have h := bankFinishCleanPotentialConcave n d (d - de e) (by omega)
    rw [show d - (d - de e) = de e by have := hle e; omega] at h
    exact h
  have hsum := ofFn_sum_le _ _ hper
  rw [ofFn_sum_add, ofFn_sum_const] at hsum
  have hdrop : (List.ofFn (fun e => (d - de e) * a)).sum =
      (List.ofFn (fun e => d - de e)).sum * a := by
    have hfun : (fun e => (d - de e) * a) = (fun e => a * (d - de e)) :=
      funext (fun e => Nat.mul_comm _ _)
    rw [hfun, ofFn_sum_mul_left, Nat.mul_comm]
  have hsplit : (List.ofFn (fun e => d - de e)).sum + (List.ofFn de).sum = n * d := by
    rw [← ofFn_sum_add]
    have : (fun e => d - de e + de e) = fun _ => d := by
      funext e; have := hle e; omega
    rw [this, ofFn_sum_const]
  have htwo : 2 * d ≤ (List.ofFn (fun e => d - de e)).sum := by
    have := hcount
    change (List.ofFn de).sum + 2 * d ≤ n * d at this
    omega
  have hka : n ≤ (2 * d) * a := by
    have h := Nat.div_add_mod n (2 * d)
    have h2 := Nat.mod_lt n (show 0 < 2 * d by omega)
    show n ≤ (2 * d) * (n / (2 * d) + 1)
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hmul : (2 * d) * a ≤ (List.ofFn (fun e => d - de e)).sum * a :=
    Nat.mul_le_mul_right a htwo
  rw [hdrop] at hsum
  change n + (List.ofFn (fun e => bankFinishCleanDebtPotential n (de e))).sum ≤
    n * bankFinishCleanDebtPotential n d
  omega

/-- The drain-guarded debt-bearing class.  Consumer: `bankFinishCleanDebtStage`. -/
def BankRepairDBarredOnDrain {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  BankPostInheritedGrantDrain ring hbank z ∧ BankRepairDBarred ring hbank z

/-- repair.tex 5367-5374 on the drain: old EU/ED debt clears within
n²/2 (one half-unit).  Consumer: `bankFinishMaskedRepairBoundClean`. -/
theorem bankFinishCleanDebtStage {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankRepairDBarredOnDrain ring hbank)
      (BankRepairDebtZero ring hbank) 1 := by
  have hpres := bankFinishCleanPreservation ring hn hbank
  have hclosed : ∀ (z : BankReferenceState ring hbank),
      BankRepairDBarredOnDrain ring hbank z → ∀ e : Fin n,
      BankRepairDBarredOnDrain ring hbank (bankRepairNext ring hbank z e) :=
    fun z hz e => ⟨bankPostInheritedGrantDrainClosed ring hn hbank z hz.1 e,
      hpres.2.2.2.1 z hz.1 hz.2 e⟩
  let S := {z : BankReferenceState ring hbank // BankRepairDBarredOnDrain ring hbank z}
  let nextS : S → Fin n → S := fun x e =>
    ⟨bankRepairNext ring hbank x.1 e, hclosed x.1 x.2 e⟩
  intro z hz T
  have hpot := Prob.costNumerator_le_of_potential nextS
    (fun x : S => BankRepairDebtZero ring hbank x.1)
    (fun x : S => bankFinishCleanDebtPotential n
      (bankFinishCleanDebtCount ring hbank x.1))
    (fun x hx => bankFinishCleanDebtDrift ring hn hbank x.1
      x.2.2.1.2 x.2.2.2 hx)
    ⟨z, hz⟩ T
  have hmap := costNumerator_map_eq nextS (bankRepairNext ring hbank)
    (fun x : S => x.1) (fun _ _ => rfl) (BankRepairDebtZero ring hbank) T ⟨z, hz⟩
  rw [hmap] at hpot
  have hhalf := bankFinishCleanPotentialHalf n hn
    (bankFinishCleanDebtCount ring hbank z)
    (bankFinishCleanDebtCountLe ring hbank z)
  have h2 := Nat.mul_le_mul_left 2 hpot
  calc
    2 * costNumerator (bankRepairNext ring hbank)
        (BankRepairDebtZero ring hbank) z T ≤
      2 * (n ^ T * bankFinishCleanDebtPotential n
        (bankFinishCleanDebtCount ring hbank z)) := h2
    _ = n ^ T * (2 * bankFinishCleanDebtPotential n
        (bankFinishCleanDebtCount ring hbank z)) := by ac_rfl
    _ ≤ n ^ T * (n ^ 2) := Nat.mul_le_mul_left _ hhalf
    _ = n ^ T * (1 * n ^ 2) := by rw [Nat.one_mul]

/-! ## The six-stage finish with only the open premises -/

/-- The digit half-stage on the drain (R10c).  Consumer:
`bankFinishMaskedRepairBoundClean`. -/
def BankRepairDigitHalfOnDrain {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  BankRepairHalfStage (bankRepairNext ring hbank)
    (fun z => BankPostInheritedGrantDrain ring hbank z ∧
      BankRepairRFoldEstablished ring hbank z)
    (BankRepairDigit ring hbank) 203

/-- The installed digit stage gives the drain one.
Consumer: callers holding `BankRepairDigitStage`. -/
theorem bankRepairDigitHalfOnDrainOfStage {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (h : BankRepairDigitStage ring hbank) :
    BankRepairDigitHalfOnDrain ring hbank :=
  fun z hz T => h.2 z hz.2 T

/-- The request half-stage on the drain.  Consumer:
`bankFinishMaskedRepairBoundClean`. -/
def BankRepairRequestHalfOnDrain {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  BankRepairHalfStage (bankRepairNext ring hbank)
    (fun z => BankPostInheritedGrantDrain ring hbank z ∧
      BankRepairDebtCleared ring hbank z)
    (BankRepairRequestZero ring hbank) 2

/-- The installed request stage gives the drain one.
Consumer: callers holding `BankRepairRequestStage`. -/
theorem bankRepairRequestHalfOnDrainOfStage {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (h : BankRepairRequestStage ring hbank) :
    BankRepairRequestHalfOnDrain ring hbank :=
  fun z hz T => h.2 z hz.2 T

/-- Replaces `bankFinishMaskedRepairBoundOfCleanWord`: receipt
preservation (drain-guarded), the R stage, the debt stage and the stop
stage are discharged; the W clean stage, the digit half-stage and the
request half-stage remain, each on its drain class.
Consumer: `bankFinishReferenceFinishClean`. -/
theorem bankFinishMaskedRepairBoundClean {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hword : BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankPreparedAtSomeRoot ring hbank)
      (BankRepairWordClean ring hbank)
      (2 * (440 * ceilLogTwo (ceilLogTwo n) + 275)))
    (hdigit : BankRepairDigitHalfOnDrain ring hbank)
    (hrequest : BankRepairRequestHalfOnDrain ring hbank) :
    BankFinishMaskedRepairBound ring hbank := by
  have hpres := bankFinishCleanPreservation ring hn hbank
  have hDC := bankPostInheritedGrantDrainClosed ring hn hbank
  have hW0 := bankRepairCloseHalfStrengthen (bankRepairNext ring hbank)
    (BankPreparedAtSomeRoot ring hbank)
    (fun z => BankPostInheritedGrantDrain ring hbank z ∧
      BankRepairCore ring hbank z)
    (BankRepairWordClean ring hbank)
    (2 * (440 * ceilLogTwo (ceilLogTwo n) + 275))
    (fun z hz => ⟨bankWordPreparedPostInherited ring hbank z hz,
      bankRepairPreparedCore ring hn hbank z hz⟩)
    (fun z hz e => ⟨hDC z hz.1 e, hpres.1 z hz.1 hz.2 e⟩) hword
  have hW : BankRepairHalfStage (bankRepairNext ring hbank)
      (BankPreparedAtSomeRoot ring hbank)
      (BankRepairWAcceptedClean ring hbank)
      (2 * (440 * ceilLogTwo (ceilLogTwo n) + 275)) :=
    bankRepairCloseHalfWeaken (bankRepairNext ring hbank) _ _ _ _
      (fun z hz => ⟨⟨hz.1.1, hz.1.2, hz.2.1⟩, hz.2.2⟩) hW0
  have hR0 := bankRepairCloseHalfStrengthen (bankRepairNext ring hbank)
    (BankRepairWAcceptedClean ring hbank)
    (BankRepairWAcceptedOnDrain ring hbank)
    (BankRepairReader ring hbank) (2 * ceilLogTwo (ceilLogTwo n))
    (fun z hz => hz.1)
    (fun z hz e => ⟨hDC z hz.1 e, hpres.2.1 z hz.1 hz.2 e⟩)
    (bankRepairReaderStageClean ring hn hbank)
  have hR : BankRepairHalfStage (bankRepairNext ring hbank)
      (BankRepairWAcceptedClean ring hbank)
      (fun z => BankPostInheritedGrantDrain ring hbank z ∧
        BankRepairRFoldEstablished ring hbank z)
      (2 * ceilLogTwo (ceilLogTwo n)) :=
    bankRepairCloseHalfWeaken (bankRepairNext ring hbank) _ _ _ _
      (fun z hz => ⟨hz.1.1, hz.1.2, hz.2⟩) hR0
  have hD0 := bankRepairCloseHalfStrengthen (bankRepairNext ring hbank)
    (fun z => BankPostInheritedGrantDrain ring hbank z ∧
      BankRepairRFoldEstablished ring hbank z)
    (fun z => BankPostInheritedGrantDrain ring hbank z ∧
      BankRepairRFoldEstablished ring hbank z)
    (BankRepairDigit ring hbank) 203 (fun z hz => hz)
    (fun z hz e => ⟨hDC z hz.1 e, hpres.2.2.1 z hz.1 hz.2 e⟩) hdigit
  have hD : BankRepairHalfStage (bankRepairNext ring hbank)
      (fun z => BankPostInheritedGrantDrain ring hbank z ∧
        BankRepairRFoldEstablished ring hbank z)
      (BankRepairDBarredOnDrain ring hbank) 203 :=
    bankRepairCloseHalfWeaken (bankRepairNext ring hbank) _ _ _ _
      (fun z hz => ⟨hz.1.1, hz.1.2, hz.2⟩) hD0
  have hDebt0 := bankRepairCloseHalfStrengthen (bankRepairNext ring hbank)
    (BankRepairDBarredOnDrain ring hbank)
    (BankRepairDBarredOnDrain ring hbank)
    (BankRepairDebtZero ring hbank) 1 (fun z hz => hz)
    (fun z hz e => ⟨hDC z hz.1 e, hpres.2.2.2.1 z hz.1 hz.2 e⟩)
    (bankFinishCleanDebtStage ring hn hbank)
  have hDebt : BankRepairHalfStage (bankRepairNext ring hbank)
      (BankRepairDBarredOnDrain ring hbank)
      (fun z => BankPostInheritedGrantDrain ring hbank z ∧
        BankRepairDebtCleared ring hbank z) 1 :=
    bankRepairCloseHalfWeaken (bankRepairNext ring hbank) _ _ _ _
      (fun z hz => ⟨hz.1.1, hz.1.2, hz.2⟩) hDebt0
  have hReq0 := bankRepairCloseHalfStrengthen (bankRepairNext ring hbank)
    (fun z => BankPostInheritedGrantDrain ring hbank z ∧
      BankRepairDebtCleared ring hbank z)
    (fun z => BankPostInheritedGrantDrain ring hbank z ∧
      BankRepairDebtCleared ring hbank z)
    (BankRepairRequestZero ring hbank) 2 (fun z hz => hz)
    (fun z hz e => ⟨hDC z hz.1 e, hpres.2.2.2.2 z hz.1 hz.2 e⟩) hrequest
  have hReq : BankRepairHalfStage (bankRepairNext ring hbank)
      (fun z => BankPostInheritedGrantDrain ring hbank z ∧
        BankRepairDebtCleared ring hbank z)
      (BankRepairRequestsQuiet ring hbank) 2 :=
    bankRepairCloseHalfWeaken (bankRepairNext ring hbank) _ _ _ _
      (fun z hz => ⟨hz.1.2, hz.2⟩) hReq0
  have hFromDebt := bankRepairCloseHalfCompose (bankRepairNext ring hbank)
    _ (BankRepairRequestsQuiet ring hbank) (bankRepairStop ring hbank) 2 0
    hReq (bankRepairStopStageProved ring hn hbank).2
  have hFromDigit := bankRepairCloseHalfCompose (bankRepairNext ring hbank)
    _ _ (bankRepairStop ring hbank) 1 (2 + 0) hDebt hFromDebt
  have hFromReader := bankRepairCloseHalfCompose (bankRepairNext ring hbank)
    _ _ (bankRepairStop ring hbank) 203 (1 + (2 + 0)) hD hFromDigit
  have hFromWord := bankRepairCloseHalfCompose (bankRepairNext ring hbank)
    _ _ (bankRepairStop ring hbank)
    (2 * ceilLogTwo (ceilLogTwo n)) (203 + (1 + (2 + 0))) hR hFromReader
  have hFromPrepared := bankRepairCloseHalfCompose (bankRepairNext ring hbank)
    _ _ (bankRepairStop ring hbank)
    (2 * (440 * ceilLogTwo (ceilLogTwo n) + 275))
    (2 * ceilLogTwo (ceilLogTwo n) + (203 + (1 + (2 + 0)))) hW hFromWord
  intro z hz T
  change costNumerator (bankRepairNext ring hbank)
    (bankRepairStop ring hbank) z T ≤
      n ^ T * ((441 * ceilLogTwo (ceilLogTwo n) + 378) * n ^ 2)
  have hcost := hFromPrepared z hz T
  have hcoefficient :
      2 * (440 * ceilLogTwo (ceilLogTwo n) + 275) +
        (2 * ceilLogTwo (ceilLogTwo n) + (203 + (1 + (2 + 0)))) =
        2 * (441 * ceilLogTwo (ceilLogTwo n) + 378) := by
    omega
  rw [hcoefficient] at hcost
  have hscale :
      n ^ T * (2 * (441 * ceilLogTwo (ceilLogTwo n) + 378) * n ^ 2) =
        2 * (n ^ T * ((441 * ceilLogTwo (ceilLogTwo n) + 378) * n ^ 2)) := by
    ac_rfl
  rw [hscale] at hcost
  omega

/-- The BANK reference finish allowance with only the open premises:
AcceptedWord at every reachable causal W completion (W monitor), the
digit half-stage on the drain (R10c) and the request half-stage on the
drain.  Replaces `bankFinishReferenceFinishOfCleanCompletion`.
Consumer: the BANK reference finish (`BankReferenceClock`, R12). -/
theorem bankFinishReferenceFinishClean {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hcompletion : ∀ root : Fin n,
      ∀ s : Fin n → ProjW (compileAdvice (ceilLogTwo n)),
        BankWordSerializerRootClass ring hbank root s →
        ∀ z : BankWordEpochState n,
          BankWordEpochReachable ring root s z →
          BankWordRenewalCompleted z →
          BankWordProjectedTarget ring z.2.1)
    (hdigit : BankRepairDigitHalfOnDrain ring hbank)
    (hrequest : BankRepairRequestHalfOnDrain ring hbank) :
    StageReferenceGeneratedFinish
      (bankRepairNext ring hbank)
      (BankPreparedAtSomeRoot ring hbank)
      (bankRepairStop ring hbank)
      (headlineReferenceFinishRate (ceilLogTwo n)) :=
  bankFinishRepairBoundToReferenceFinish ring hn hbank
    (bankFinishMaskedRepairBoundClean ring hn hbank
      (bankRepairWordCleanHalfStageOfClock ring hn hbank
        (bankWordCleanClockOfCompletion ring hn hbank hcompletion))
      hdigit hrequest)

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankFinishCleanPreservation
#print axioms L3.RenewalReferenceClock.bankFinishCleanDebtStage
#print axioms L3.RenewalReferenceClock.bankFinishMaskedRepairBoundClean
#print axioms L3.RenewalReferenceClock.bankFinishReferenceFinishClean
