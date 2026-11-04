import Leader.L3.Small.CandidatePreparation
import Leader.L3.Bank.FinishRepair

/-!
SMALL finish repair.
Generic G-factor classes use only the original physical word.
The masked successors and numerical stage obligations remain distinct.
BANK's 203-half-unit D budget is not transferred to finite SMALL.
-/

namespace L3.SmallFinishRepair

open L3
open L3.HeadlineRenewal
open L3.SmallRenewal
open L3.SmallCandidatePreparation
open L3.RenewalReferenceClock
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree
open Classical

set_option autoImplicit false
set_option Elab.async false

/-! All eleven static classes are pullbacks along a physical view. -/

def RepairCore {n : Nat} {S : Type} (ring : DirectedRing n)
    (view : S → HeadlineConfiguration n) (z : S) : Prop :=
  Closure.NativeFactor ring (view z) ∧
    Closure.CandidateFactor ring (view z)

def RepairWord {n : Nat} {S : Type} (ring : DirectedRing n)
    (view : S → HeadlineConfiguration n) (z : S) : Prop :=
  Closure.WordFactor ring (view z)

def RepairReader {n : Nat} {S : Type} (ring : DirectedRing n)
    (view : S → HeadlineConfiguration n) (z : S) : Prop :=
  Closure.ReaderFactor ring
    (Closure.readerFoldValid (ceilLogTwo n) n) (view z)

def RepairDigit {n : Nat} {S : Type} (ring : DirectedRing n)
    (view : S → HeadlineConfiguration n) (z : S) : Prop :=
  Closure.DigitFactor ring (view z)

def RepairDebtZero {n : Nat} {S : Type}
    (view : S → HeadlineConfiguration n) (z : S) : Prop :=
  ∀ i : Fin n, (view z i).EU = false ∧ (view z i).ED = false

def RepairRequestZero {n : Nat} {S : Type}
    (view : S → HeadlineConfiguration n) (z : S) : Prop :=
  ∀ i : Fin n, (view z i).req = false

def RepairWAccepted {n : Nat} {S : Type} (ring : DirectedRing n)
    (view : S → HeadlineConfiguration n) (z : S) : Prop :=
  RepairCore ring view z ∧ RepairWord ring view z

def RepairRFoldEstablished {n : Nat} {S : Type} (ring : DirectedRing n)
    (view : S → HeadlineConfiguration n) (z : S) : Prop :=
  RepairWAccepted ring view z ∧ RepairReader ring view z

def RepairDBarred {n : Nat} {S : Type} (ring : DirectedRing n)
    (view : S → HeadlineConfiguration n) (z : S) : Prop :=
  RepairRFoldEstablished ring view z ∧ RepairDigit ring view z

def RepairDebtCleared {n : Nat} {S : Type} (ring : DirectedRing n)
    (view : S → HeadlineConfiguration n) (z : S) : Prop :=
  RepairDBarred ring view z ∧ RepairDebtZero view z

def RepairRequestsQuiet {n : Nat} {S : Type} (ring : DirectedRing n)
    (view : S → HeadlineConfiguration n) (z : S) : Prop :=
  RepairDebtCleared ring view z ∧ RepairRequestZero view z

/-- The FIVE suffix-closure obligations, not a free theorem from
static definitional equivalence of the physical classes. -/
def RepairReceiptPreservation {n : Nat} {S : Type}
    (next : S → Fin n → S) (ring : DirectedRing n)
    (view : S → HeadlineConfiguration n) : Prop :=
  (∀ z, RepairCore ring view z →
    ∀ e, RepairCore ring view (next z e)) ∧
  (∀ z, RepairWAccepted ring view z →
    ∀ e, RepairWAccepted ring view (next z e)) ∧
  (∀ z, RepairRFoldEstablished ring view z →
    ∀ e, RepairRFoldEstablished ring view (next z e)) ∧
  (∀ z, RepairDBarred ring view z →
    ∀ e, RepairDBarred ring view (next z e)) ∧
  (∀ z, RepairDebtCleared ring view z →
    ∀ e, RepairDebtCleared ring view (next z e))

def bankRepairPhysicalView {n : Nat} (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankReferenceState ring hbank → HeadlineConfiguration n :=
  fun z => z.val.1

theorem bankRepairCoreGeneric {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) :
    BankRepairCore ring hbank z ↔
      RepairCore ring (bankRepairPhysicalView ring hbank) z := by
  rfl

theorem bankRepairWordGeneric {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) :
    BankRepairWord ring hbank z ↔
      RepairWord ring (bankRepairPhysicalView ring hbank) z := by
  rfl

theorem bankRepairReaderGeneric {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) :
    BankRepairReader ring hbank z ↔
      RepairReader ring (bankRepairPhysicalView ring hbank) z := by
  rfl

theorem bankRepairDigitGeneric {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) :
    BankRepairDigit ring hbank z ↔
      RepairDigit ring (bankRepairPhysicalView ring hbank) z := by
  rfl

theorem bankRepairDebtZeroGeneric {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) :
    BankRepairDebtZero ring hbank z ↔
      RepairDebtZero (bankRepairPhysicalView ring hbank) z := by
  rfl

theorem bankRepairRequestZeroGeneric {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) :
    BankRepairRequestZero ring hbank z ↔
      RepairRequestZero (bankRepairPhysicalView ring hbank) z := by
  rfl

theorem bankRepairWAcceptedGeneric {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) :
    BankRepairWAccepted ring hbank z ↔
      RepairWAccepted ring (bankRepairPhysicalView ring hbank) z := by
  rfl

theorem bankRepairRFoldEstablishedGeneric {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) :
    BankRepairRFoldEstablished ring hbank z ↔
      RepairRFoldEstablished ring (bankRepairPhysicalView ring hbank) z := by
  rfl

theorem bankRepairDBarredGeneric {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) :
    BankRepairDBarred ring hbank z ↔
      RepairDBarred ring (bankRepairPhysicalView ring hbank) z := by
  rfl

theorem bankRepairDebtClearedGeneric {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) :
    BankRepairDebtCleared ring hbank z ↔
      RepairDebtCleared ring (bankRepairPhysicalView ring hbank) z := by
  rfl

theorem bankRepairRequestsQuietGeneric {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) :
    BankRepairRequestsQuiet ring hbank z ↔
      RepairRequestsQuiet ring (bankRepairPhysicalView ring hbank) z := by
  rfl

theorem bankRepairPreservationGeneric {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankRepairReceiptPreservation ring hbank ↔
      RepairReceiptPreservation (bankRepairNext ring hbank)
        ring (bankRepairPhysicalView ring hbank) := by
  rfl

/-! Counter-independent stage interfaces with variable D budget.
The whole and half rates remain distinct, just as in BANK. -/

def RepairWordStage {n : Nat} {S : Type}
    (next : S → Fin n → S) (ring : DirectedRing n)
    (view : S → HeadlineConfiguration n)
    (prepared : S → Prop) (t : Nat) : Prop :=
  StageReferenceGeneratedFinish next prepared
    (RepairWord ring view) (440 * t + 275) ∧
  BankRepairHalfStage next prepared
    (RepairWord ring view) (2 * (440 * t + 275))

def RepairReaderStage {n : Nat} {S : Type}
    (next : S → Fin n → S) (ring : DirectedRing n)
    (view : S → HeadlineConfiguration n)
    (t : Nat) : Prop :=
  StageReferenceGeneratedFinish next
    (RepairWAccepted ring view) (RepairReader ring view) t ∧
  BankRepairHalfStage next
    (RepairWAccepted ring view) (RepairReader ring view) (2 * t)

def RepairDigitStage {n : Nat} {S : Type}
    (next : S → Fin n → S) (ring : DirectedRing n)
    (view : S → HeadlineConfiguration n)
    (wholeUnits halfUnits : Nat) : Prop :=
  StageReferenceGeneratedFinish next
    (RepairRFoldEstablished ring view)
    (RepairDigit ring view) wholeUnits ∧
  BankRepairHalfStage next
    (RepairRFoldEstablished ring view)
    (RepairDigit ring view) halfUnits

def RepairDebtStage {n : Nat} {S : Type}
    (next : S → Fin n → S) (ring : DirectedRing n)
    (view : S → HeadlineConfiguration n) : Prop :=
  StageReferenceGeneratedFinish next
    (RepairDBarred ring view) (RepairDebtZero view) 1 ∧
  BankRepairHalfStage next
    (RepairDBarred ring view) (RepairDebtZero view) 1

def RepairRequestStage {n : Nat} {S : Type}
    (next : S → Fin n → S) (ring : DirectedRing n)
    (view : S → HeadlineConfiguration n) : Prop :=
  StageReferenceGeneratedFinish next
    (RepairDebtCleared ring view) (RepairRequestZero view) 1 ∧
  BankRepairHalfStage next
    (RepairDebtCleared ring view) (RepairRequestZero view) 2

def RepairStopStage {n : Nat} {S : Type}
    (next : S → Fin n → S) (ring : DirectedRing n)
    (view : S → HeadlineConfiguration n)
    (stop : S → Prop) : Prop :=
  StageReferenceGeneratedFinish next
    (RepairRequestsQuiet ring view) stop 0 ∧
  BankRepairHalfStage next
    (RepairRequestsQuiet ring view) stop 0

theorem bankRepairWordStageGeneric {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankRepairWordStage ring hbank ↔
      RepairWordStage (bankRepairNext ring hbank) ring
        (bankRepairPhysicalView ring hbank)
        (BankPreparedAtSomeRoot ring hbank)
        (ceilLogTwo (ceilLogTwo n)) := by
  rfl

theorem bankRepairReaderStageGeneric {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankRepairReaderStage ring hbank ↔
      RepairReaderStage (bankRepairNext ring hbank) ring
        (bankRepairPhysicalView ring hbank)
        (ceilLogTwo (ceilLogTwo n)) := by
  rfl

theorem bankRepairDigitStageGeneric {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankRepairDigitStage ring hbank ↔
      RepairDigitStage (bankRepairNext ring hbank) ring
        (bankRepairPhysicalView ring hbank) 102 203 := by
  rfl

theorem bankRepairDebtStageGeneric {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankRepairDebtStage ring hbank ↔
      RepairDebtStage (bankRepairNext ring hbank) ring
        (bankRepairPhysicalView ring hbank) := by
  rfl

theorem bankRepairRequestStageGeneric {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankRepairRequestStage ring hbank ↔
      RepairRequestStage (bankRepairNext ring hbank) ring
        (bankRepairPhysicalView ring hbank) := by
  rfl

theorem bankRepairStopStageGeneric {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankRepairStopStage ring hbank ↔
      RepairStopStage (bankRepairNext ring hbank) ring
        (bankRepairPhysicalView ring hbank)
        (bankRepairStop ring hbank) := by
  rfl

theorem bankRepairStopStageRecovered {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    RepairStopStage (bankRepairNext ring hbank) ring
      (bankRepairPhysicalView ring hbank)
      (bankRepairStop ring hbank) := by
  exact (bankRepairStopStageGeneric ring hbank).mp
    (bankRepairStopStageProved ring hn hbank)


/-! SMALL classes on the original proof-decorated reference. -/

def smallRepairView {n : Nat} :
    RenewalSmallReference n → HeadlineConfiguration n :=
  fun r => r.1

abbrev SmallRepairCore {n : Nat}
    (ring : DirectedRing n) : RenewalSmallReference n → Prop :=
  RepairCore ring smallRepairView

abbrev SmallRepairWord {n : Nat}
    (ring : DirectedRing n) : RenewalSmallReference n → Prop :=
  RepairWord ring smallRepairView

abbrev SmallRepairReader {n : Nat}
    (ring : DirectedRing n) : RenewalSmallReference n → Prop :=
  RepairReader ring smallRepairView

abbrev SmallRepairDigit {n : Nat}
    (ring : DirectedRing n) : RenewalSmallReference n → Prop :=
  RepairDigit ring smallRepairView

abbrev SmallRepairWAccepted {n : Nat}
    (ring : DirectedRing n) : RenewalSmallReference n → Prop :=
  RepairWAccepted ring smallRepairView

abbrev SmallRepairRFoldEstablished {n : Nat}
    (ring : DirectedRing n) : RenewalSmallReference n → Prop :=
  RepairRFoldEstablished ring smallRepairView

abbrev SmallRepairDBarred {n : Nat}
    (ring : DirectedRing n) : RenewalSmallReference n → Prop :=
  RepairDBarred ring smallRepairView

abbrev SmallRepairDebtCleared {n : Nat}
    (ring : DirectedRing n) : RenewalSmallReference n → Prop :=
  RepairDebtCleared ring smallRepairView

abbrev SmallRepairRequestsQuiet {n : Nat}
    (ring : DirectedRing n) : RenewalSmallReference n → Prop :=
  RepairRequestsQuiet ring smallRepairView

/-- The earlier physical prepared-core theorem implies the same
generated native/candidate pair as on the BANK side. -/
theorem smallRepairPreparedCore {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (r : RenewalSmallReference n)
    (hr : SmallPreparedAtSomeRoot ring r) :
    SmallRepairCore ring r := by
  have hp := smallPreparedAtSomeRootCore ring hn r hr
  rcases hp with ⟨hprotected, _, hone, hclean, _, _⟩
  constructor
  · change OneNativeLeader (nativeProjection r.1) ∧
      Protected ring (nativeProjection r.1) ∧
      C_native ring (nativeProjection r.1)
    exact ⟨hone, hprotected, hclean⟩
  · change H_cand ring (smallCandidateView r)
    exact smallPreparedAtSomeRootCandidateHistory ring hn r hr

/-- The final conjunction is the exact fixed Closure.targetSet
and has no extra physical counter coordinate. -/
theorem repairRequestsQuietTarget {n : Nat} {S : Type}
    (ring : DirectedRing n)
    (view : S → HeadlineConfiguration n)
    (z : S)
    (hz : RepairRequestsQuiet ring view z) :
    headlineGeneratedTarget ring (view z) := by
  rcases hz with
    ⟨⟨⟨⟨⟨hcore, hword⟩, hreader⟩, hdigit⟩, hdebt⟩, hrequest⟩
  rcases hcore with ⟨hnative, hcand⟩
  change Closure.G ring
    (Closure.readerFoldValid (ceilLogTwo n) n) (view z)
  exact ⟨hnative, hcand, hword, hreader, hdigit,
    fun i => ⟨(hdebt i).1, (hdebt i).2, hrequest i⟩⟩

theorem smallRepairRequestsQuietStop {n : Nat}
    (ring : DirectedRing n)
    (r : RenewalSmallReference n)
    (hr : SmallRepairRequestsQuiet ring r) :
    renewalSmallStop ring r := by
  exact repairRequestsQuietTarget ring smallRepairView r hr

/-- STOP is the only no-hypothesis BANK repair clock producer
currently in BankFinishRepair, and it transfers verbatim. -/
theorem smallRepairStopStageProved {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n) :
    RepairStopStage (renewalSmallNext ring) ring smallRepairView
      (renewalSmallStop ring) := by
  constructor
  · intro r hr
    apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      (renewalSmallNext ring) (renewalSmallStop ring)
      (by omega : 0 < n) r (0 * n ^ 2)).2
    intro T
    rw [costNumerator_terminal (renewalSmallNext ring)
      (renewalSmallStop ring) r
      (smallRepairRequestsQuietStop ring r hr) T]
    exact Nat.zero_le _
  · intro r hr T
    rw [costNumerator_terminal (renewalSmallNext ring)
      (renewalSmallStop ring) r
      (smallRepairRequestsQuietStop ring r hr) T]
    exact Nat.zero_le _

/-- Short counter's actual no-birth repair guard, established
after the grant drain and joint candidate preparation.
It is distinct from the finite counter's origin-success clock. -/
def SmallRepairShortCounterGuard {n : Nat}
    (ring : DirectedRing n) : Prop :=
  ∀ r : RenewalSmallReference n,
    SmallPreparedAtSomeRoot ring r →
    ∀ e : Fin n,
      (r.1 e).grant = false ∧
      NativeLiftNoFireOn ring r.1 e ∧
      NativeLiftGrantFree (renewalSmallNext ring r e).1

theorem smallRepairShortCounterGuardProved {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    SmallRepairShortCounterGuard ring := by
  intro r hr e
  obtain ⟨root, hfixed, _⟩ := hr
  have hnext := smallReferenceGrantFreeClosed ring hn hsmall
    r hfixed.1 e
  exact ⟨hfixed.1.2.2 e,
    smallCandidateNoFireOn ring r hfixed.1 e,
    hnext.2.2⟩

/-! Source-specific width and finite-slice D clock allowance.
The BANK 203-half-unit D ledger is not reused. -/

def smallRepairWidth (n : Nat) : Nat :=
  (compileAdvice (ceilLogTwo n)).t

def smallRepairDigitHalf (n : Nat) : Nat :=
  2 * (headlineReferenceFinishRate (ceilLogTwo n) -
    (441 * smallRepairWidth n + 275)) - 3

def smallRepairDigitWhole (n : Nat) : Nat :=
  (smallRepairDigitHalf n + 1) / 2

theorem smallRepairFiniteMargin (q : Nat)
    (hq : 3 ≤ q)
    (hsmall : (compileAdvice q).useSmall = true) :
    441 * (compileAdvice q).t + 277 ≤
      headlineReferenceFinishRate q := by
  have hqstar : q ≤ qStar := by
    have he :
        (compileAdvice q).useSmall = decide (q ≤ qStar) := rfl
    rw [he] at hsmall
    exact of_decide_eq_true hsmall
  have hlt : q < 80 := by
    have hstar : qStar = 79 := rfl
    omega
  have hcheck :
      ∀ i : Fin 80, 3 ≤ i.val →
        441 * (compileAdvice i.val).t + 277 ≤
          headlineReferenceFinishRate i.val := by
    decide +kernel
  exact hcheck ⟨q, hlt⟩ hq

private theorem smallRepairAdviceAtLeastThree (n : Nat)
    (hn : 5 ≤ n) : 3 ≤ ceilLogTwo n := by
  have hupper := (ceilLogTwo_spec n (by omega : 2 ≤ n)).2
  by_cases hlow : ceilLogTwo n ≤ 2
  · have hp : 2 ^ ceilLogTwo n ≤ 2 ^ 2 :=
      Nat.pow_le_pow_right (by omega) hlow
    have hfour : (2 : Nat) ^ 2 = 4 := by decide
    rw [hfour] at hp
    omega
  · omega

private theorem repairHalfRateArithmetic (F t : Nat)
    (h : 441 * t + 277 ≤ F) :
    2 * (440 * t + 275) +
      (2 * t + ((2 * (F - (441 * t + 275)) - 3) +
        (1 + (2 + 0)))) = 2 * F := by
  omega

theorem smallRepairHalfRate {n : Nat}
    (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true) :
    2 * (440 * smallRepairWidth n + 275) +
      (2 * smallRepairWidth n +
        (smallRepairDigitHalf n + (1 + (2 + 0)))) =
      2 * headlineReferenceFinishRate (ceilLogTwo n) := by
  have hmargin := smallRepairFiniteMargin (ceilLogTwo n)
    (smallRepairAdviceAtLeastThree n hn) hsmall
  unfold smallRepairDigitHalf smallRepairWidth
  exact repairHalfRateArithmetic
    (headlineReferenceFinishRate (ceilLogTwo n))
    (compileAdvice (ceilLogTwo n)).t hmargin

abbrev SmallRepairReceiptPreservation {n : Nat}
    (ring : DirectedRing n) : Prop :=
  RepairReceiptPreservation (renewalSmallNext ring)
    ring smallRepairView

abbrev SmallRepairWordStage {n : Nat}
    (ring : DirectedRing n) : Prop :=
  RepairWordStage (renewalSmallNext ring) ring smallRepairView
    (SmallPreparedAtSomeRoot ring) (smallRepairWidth n)

abbrev SmallRepairReaderStage {n : Nat}
    (ring : DirectedRing n) : Prop :=
  RepairReaderStage (renewalSmallNext ring) ring smallRepairView
    (smallRepairWidth n)

/-- F.6/F.7 and F.34 supply the finite SMALL reference envelope.
The actual masked SMALL D clock is still an OPEN stage. -/
abbrev SmallRepairDigitStage {n : Nat}
    (ring : DirectedRing n) : Prop :=
  RepairDigitStage (renewalSmallNext ring) ring smallRepairView
    (smallRepairDigitWhole n) (smallRepairDigitHalf n)

abbrev SmallRepairDebtStage {n : Nat}
    (ring : DirectedRing n) : Prop :=
  RepairDebtStage (renewalSmallNext ring) ring smallRepairView

abbrev SmallRepairRequestStage {n : Nat}
    (ring : DirectedRing n) : Prop :=
  RepairRequestStage (renewalSmallNext ring) ring smallRepairView


/-! Independent generic half-cost composition, preserving the
half-n² debt credit. No inaccessible private BANK lemma is used. -/

private theorem repairHalfReserve {S : Type} {n : Nat}
    (next : S → Fin n → S) (A P : S → Prop) (allowance : Nat)
    (hsecond : ∀ y, A y → ∀ T,
      2 * costNumerator next P y T ≤ n ^ T * allowance) :
    ∀ y T,
      2 * costNumerator next P y T ≤
        2 * costNumerator next (fun z => A z ∨ P z) y T +
          n ^ T * allowance := by
  classical
  intro y T
  induction T generalizing y with
  | zero =>
      simp only [costNumerator_zero, Nat.mul_zero, Nat.zero_add]
      exact Nat.zero_le _
  | succ T ih =>
      by_cases hp : P y
      · have hu : A y ∨ P y := Or.inr hp
        rw [costNumerator_terminal next P y hp (T + 1),
          costNumerator_terminal next (fun z => A z ∨ P z)
            y hu (T + 1)]
        simp only [Nat.mul_zero, Nat.zero_add]
        exact Nat.zero_le _
      · by_cases ha : A y
        · have hu : A y ∨ P y := Or.inl ha
          rw [costNumerator_terminal next (fun z => A z ∨ P z)
            y hu (T + 1)]
          simpa only [Nat.mul_zero, Nat.zero_add] using
            hsecond y ha (T + 1)
        · have hu : ¬ (A y ∨ P y) := by
            intro h
            rcases h with hA | hP
            · exact ha hA
            · exact hp hP
          have hs :
              2 * (List.ofFn (fun e : Fin n =>
                costNumerator next P (next y e) T)).sum ≤
              2 * (List.ofFn (fun e : Fin n =>
                costNumerator next (fun z => A z ∨ P z)
                  (next y e) T)).sum +
                n ^ (T + 1) * allowance := by
            calc
              2 * (List.ofFn (fun e : Fin n =>
                costNumerator next P (next y e) T)).sum =
                  (List.ofFn (fun e : Fin n =>
                    2 * costNumerator next P (next y e) T)).sum := by
                    rw [ofFn_sum_mul_left]
              _ ≤ (List.ofFn (fun e : Fin n =>
                    2 * costNumerator next (fun z => A z ∨ P z)
                      (next y e) T + n ^ T * allowance)).sum :=
                    ofFn_sum_le _ _ (fun e => ih (next y e))
              _ = 2 * (List.ofFn (fun e : Fin n =>
                    costNumerator next (fun z => A z ∨ P z)
                      (next y e) T)).sum +
                      n ^ (T + 1) * allowance := by
                    rw [ofFn_sum_add, ofFn_sum_const,
                      ofFn_sum_mul_left, Nat.pow_succ]
                    simp only [Nat.mul_assoc, Nat.mul_left_comm,
                      Nat.mul_comm]
          rw [costNumerator_succ next P y hp T,
            costNumerator_succ next (fun z => A z ∨ P z) y hu T]
          omega

private theorem repairHalfCompose {S : Type} {n : Nat}
    (next : S → Fin n → S) (A B Target : S → Prop)
    (a b : Nat)
    (hfirst : BankRepairHalfStage next A B a)
    (hsecond : BankRepairHalfStage next B Target b) :
    BankRepairHalfStage next A Target (a + b) := by
  intro x hx T
  have hfirstUnion :
      2 * costNumerator next (fun z => B z ∨ Target z) x T ≤
        n ^ T * (a * n ^ 2) := by
    have hmono := Prob.costNumerator_target_mono next B
      (fun z => B z ∨ Target z)
      (fun z hz => Or.inl hz) x T
    exact Nat.le_trans (Nat.mul_le_mul_left 2 hmono)
      (hfirst x hx T)
  have hreserve := repairHalfReserve next B Target
    (b * n ^ 2) (fun y hy T => hsecond y hy T) x T
  calc
    2 * costNumerator next Target x T ≤
        2 * costNumerator next (fun z => B z ∨ Target z) x T +
          n ^ T * (b * n ^ 2) := hreserve
    _ ≤ n ^ T * (a * n ^ 2) + n ^ T * (b * n ^ 2) :=
      Nat.add_le_add_right hfirstUnion _
    _ = n ^ T * ((a + b) * n ^ 2) := by
      rw [Nat.add_mul, Nat.mul_add]

private theorem repairHalfStrengthen {S : Type} {n : Nat}
    (next : S → Fin n → S) (Start I Q : S → Prop)
    (a : Nat)
    (hstart : ∀ z, Start z → I z)
    (hclosed : ∀ z, I z → ∀ e : Fin n, I (next z e))
    (hraw : BankRepairHalfStage next Start Q a) :
    BankRepairHalfStage next Start (fun z => I z ∧ Q z) a := by
  intro z hz T
  have hstrength := costNumeratorTargetOnClosed next I
    (fun y => I y ∧ Q y) Q hclosed
    (fun y hi hq => ⟨hi, hq⟩) T z (hstart z hz)
  exact Nat.le_trans (Nat.mul_le_mul_left 2 hstrength)
    (hraw z hz T)

/-- A same-scheduler, masked SMALL finish decomposition with the
complete physical-reader fold and actual Closure.targetSet.
Only W/R/D/debt/request clocks and five preservation statements
remain conditional; the zero-unit STOP is proved. -/
theorem smallFinishFromCandidateOfStages {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (hpres : SmallRepairReceiptPreservation ring)
    (hword : SmallRepairWordStage ring)
    (hreader : SmallRepairReaderStage ring)
    (hdigit : SmallRepairDigitStage ring)
    (hdebt : SmallRepairDebtStage ring)
    (hrequest : SmallRepairRequestStage ring) :
    SmallFinishFromCandidate ring := by
  rcases hpres with
    ⟨hCoreClosed, hWordClosed, hReaderClosed,
      hDigitClosed, hDebtClosed⟩
  have hW : BankRepairHalfStage
      (renewalSmallNext ring)
      (SmallPreparedAtSomeRoot ring)
      (SmallRepairWAccepted ring)
      (2 * (440 * smallRepairWidth n + 275)) :=
    repairHalfStrengthen (renewalSmallNext ring)
      (SmallPreparedAtSomeRoot ring)
      (SmallRepairCore ring) (SmallRepairWord ring)
      (2 * (440 * smallRepairWidth n + 275))
      (fun r hr => smallRepairPreparedCore ring hn r hr)
      hCoreClosed hword.2
  have hR : BankRepairHalfStage
      (renewalSmallNext ring)
      (SmallRepairWAccepted ring)
      (SmallRepairRFoldEstablished ring)
      (2 * smallRepairWidth n) :=
    repairHalfStrengthen (renewalSmallNext ring)
      (SmallRepairWAccepted ring)
      (SmallRepairWAccepted ring) (SmallRepairReader ring)
      (2 * smallRepairWidth n)
      (fun r hr => hr) hWordClosed hreader.2
  have hD : BankRepairHalfStage
      (renewalSmallNext ring)
      (SmallRepairRFoldEstablished ring)
      (SmallRepairDBarred ring)
      (smallRepairDigitHalf n) :=
    repairHalfStrengthen (renewalSmallNext ring)
      (SmallRepairRFoldEstablished ring)
      (SmallRepairRFoldEstablished ring) (SmallRepairDigit ring)
      (smallRepairDigitHalf n)
      (fun r hr => hr) hReaderClosed hdigit.2
  have hDebt : BankRepairHalfStage
      (renewalSmallNext ring)
      (SmallRepairDBarred ring)
      (SmallRepairDebtCleared ring) 1 :=
    repairHalfStrengthen (renewalSmallNext ring)
      (SmallRepairDBarred ring)
      (SmallRepairDBarred ring)
      (RepairDebtZero smallRepairView) 1
      (fun r hr => hr) hDigitClosed hdebt.2
  have hRequest : BankRepairHalfStage
      (renewalSmallNext ring)
      (SmallRepairDebtCleared ring)
      (SmallRepairRequestsQuiet ring) 2 :=
    repairHalfStrengthen (renewalSmallNext ring)
      (SmallRepairDebtCleared ring)
      (SmallRepairDebtCleared ring)
      (RepairRequestZero smallRepairView) 2
      (fun r hr => hr) hDebtClosed hrequest.2
  have hStop : BankRepairHalfStage
      (renewalSmallNext ring)
      (SmallRepairRequestsQuiet ring)
      (renewalSmallStop ring) 0 :=
    (smallRepairStopStageProved ring hn).2
  have hAfterDebt : BankRepairHalfStage
      (renewalSmallNext ring)
      (SmallRepairDebtCleared ring)
      (renewalSmallStop ring) (2 + 0) :=
    repairHalfCompose (renewalSmallNext ring)
      (SmallRepairDebtCleared ring)
      (SmallRepairRequestsQuiet ring)
      (renewalSmallStop ring) 2 0 hRequest hStop
  have hAfterDigit : BankRepairHalfStage
      (renewalSmallNext ring)
      (SmallRepairDBarred ring)
      (renewalSmallStop ring) (1 + (2 + 0)) :=
    repairHalfCompose (renewalSmallNext ring)
      (SmallRepairDBarred ring)
      (SmallRepairDebtCleared ring)
      (renewalSmallStop ring) 1 (2 + 0) hDebt hAfterDebt
  have hAfterReader : BankRepairHalfStage
      (renewalSmallNext ring)
      (SmallRepairRFoldEstablished ring)
      (renewalSmallStop ring)
      (smallRepairDigitHalf n + (1 + (2 + 0))) :=
    repairHalfCompose (renewalSmallNext ring)
      (SmallRepairRFoldEstablished ring)
      (SmallRepairDBarred ring)
      (renewalSmallStop ring)
      (smallRepairDigitHalf n) (1 + (2 + 0))
      hD hAfterDigit
  have hAfterWord : BankRepairHalfStage
      (renewalSmallNext ring)
      (SmallRepairWAccepted ring)
      (renewalSmallStop ring)
      (2 * smallRepairWidth n +
        (smallRepairDigitHalf n + (1 + (2 + 0)))) :=
    repairHalfCompose (renewalSmallNext ring)
      (SmallRepairWAccepted ring)
      (SmallRepairRFoldEstablished ring)
      (renewalSmallStop ring)
      (2 * smallRepairWidth n)
      (smallRepairDigitHalf n + (1 + (2 + 0)))
      hR hAfterReader
  have hAll : BankRepairHalfStage
      (renewalSmallNext ring)
      (SmallPreparedAtSomeRoot ring)
      (renewalSmallStop ring)
      (2 * (440 * smallRepairWidth n + 275) +
        (2 * smallRepairWidth n +
          (smallRepairDigitHalf n + (1 + (2 + 0))))) :=
    repairHalfCompose (renewalSmallNext ring)
      (SmallPreparedAtSomeRoot ring)
      (SmallRepairWAccepted ring)
      (renewalSmallStop ring)
      (2 * (440 * smallRepairWidth n + 275))
      (2 * smallRepairWidth n +
        (smallRepairDigitHalf n + (1 + (2 + 0))))
      hW hAfterWord
  intro r hr
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (renewalSmallNext ring) (renewalSmallStop ring)
    (by omega : 0 < n) r
    (headlineReferenceFinishRate (ceilLogTwo n) * n ^ 2)).2
  intro T
  have hcost := hAll r hr T
  rw [smallRepairHalfRate hn hsmall] at hcost
  have hscale :
      n ^ T *
        (2 * headlineReferenceFinishRate (ceilLogTwo n) * n ^ 2) =
      2 * (n ^ T *
        (headlineReferenceFinishRate (ceilLogTwo n) * n ^ 2)) := by
    simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  rw [hscale] at hcost
  omega

/-- Conditional full SMALL reference-clock consumption. The
previously 6n² joint candidate preparation is unchanged. -/
theorem smallReferenceClockOfRepairStages {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = true)
    (hpres : SmallRepairReceiptPreservation ring)
    (hword : SmallRepairWordStage ring)
    (hreader : SmallRepairReaderStage ring)
    (hdigit : SmallRepairDigitStage ring)
    (hdebt : SmallRepairDebtStage ring)
    (hrequest : SmallRepairRequestStage ring) :
    ReferenceClock ring (smallRootedReferenceData ring hsmall)
      (headlineReferenceRate (ceilLogTwo n)) := by
  exact smallReferenceClockOfCandidateFinish ring hn hsmall
    (smallFinishFromCandidateOfStages ring hn hsmall
      hpres hword hreader hdigit hdebt hrequest)

end L3.SmallFinishRepair

#print axioms L3.SmallFinishRepair.bankRepairCoreGeneric
#print axioms L3.SmallFinishRepair.bankRepairWordGeneric
#print axioms L3.SmallFinishRepair.bankRepairReaderGeneric
#print axioms L3.SmallFinishRepair.bankRepairDigitGeneric
#print axioms L3.SmallFinishRepair.bankRepairDebtZeroGeneric
#print axioms L3.SmallFinishRepair.bankRepairRequestZeroGeneric
#print axioms L3.SmallFinishRepair.bankRepairWAcceptedGeneric
#print axioms L3.SmallFinishRepair.bankRepairRFoldEstablishedGeneric
#print axioms L3.SmallFinishRepair.bankRepairDBarredGeneric
#print axioms L3.SmallFinishRepair.bankRepairDebtClearedGeneric
#print axioms L3.SmallFinishRepair.bankRepairRequestsQuietGeneric
#print axioms L3.SmallFinishRepair.bankRepairPreservationGeneric
#print axioms L3.SmallFinishRepair.bankRepairWordStageGeneric
#print axioms L3.SmallFinishRepair.bankRepairReaderStageGeneric
#print axioms L3.SmallFinishRepair.bankRepairDigitStageGeneric
#print axioms L3.SmallFinishRepair.bankRepairDebtStageGeneric
#print axioms L3.SmallFinishRepair.bankRepairRequestStageGeneric
#print axioms L3.SmallFinishRepair.bankRepairStopStageGeneric
#print axioms L3.SmallFinishRepair.bankRepairStopStageRecovered
#print axioms L3.SmallFinishRepair.smallRepairPreparedCore
#print axioms L3.SmallFinishRepair.repairRequestsQuietTarget
#print axioms L3.SmallFinishRepair.smallRepairRequestsQuietStop
#print axioms L3.SmallFinishRepair.smallRepairStopStageProved
#print axioms L3.SmallFinishRepair.smallRepairShortCounterGuardProved
#print axioms L3.SmallFinishRepair.smallRepairFiniteMargin
#print axioms L3.SmallFinishRepair.smallRepairHalfRate
#print axioms L3.SmallFinishRepair.smallFinishFromCandidateOfStages
#print axioms L3.SmallFinishRepair.smallReferenceClockOfRepairStages
