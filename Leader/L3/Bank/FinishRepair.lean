import Leader.L3.Bank.FinishPhysical

/-!
Six masked BANK finish clocks and their half-unit composition.

This file adds CONDITIONAL clock/closure interfaces, not clock producers.
The reference successor is the original valid, masked BANK successor.

The whole-n² ceilings of the six paper stages sum to
(441*s+379)*n², NOT (441*s+378)*n². The sharper doubled-cost
clauses retain the half-n² debt credit and compose to the required
(882*s+756)*n² = 2*(441*s+378)*n².

Unproved producers: five nontrivial clocks and the preservation
clauses. In particular no frozen-root or unmasked-physical clock is
substituted for a masked BANK clock.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

private def bankRepairWidth (n : Nat) : Nat :=
  ceilLogTwo (ceilLogTwo n)

/-- A definitional abbreviation, not a new or replacement Markov chain. -/
abbrev bankRepairNext {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankReferenceState ring hbank → Fin n → BankReferenceState ring hbank :=
  (bankValidRootedReferenceData ring hbank).referenceNext

/-- Exactly the installed valid BANK reference stop, with no new flag. -/
abbrev bankRepairStop {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankReferenceState ring hbank → Prop :=
  (bankValidRootedReferenceData ring hbank).referenceStop

/-! The physical W, R and D membership tests use the audited,
accepted E.G17/E.G23/E.G36 classes, not the older legacy WZero/R/Ddel. -/

def BankRepairCore {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  Closure.NativeFactor ring z.val.1 ∧
    Closure.CandidateFactor ring z.val.1

def BankRepairWord {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  Closure.WordFactor ring z.val.1

def BankRepairReader {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  Closure.ReaderFactor ring
    (Closure.readerFoldValid (ceilLogTwo n) n) z.val.1

def BankRepairDigit {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  Closure.DigitFactor ring z.val.1

def BankRepairDebtZero {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  ∀ i : Fin n, (z.val.1 i).EU = false ∧ (z.val.1 i).ED = false

def BankRepairRequestZero {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  ∀ i : Fin n, (z.val.1 i).req = false

/-- The later classes explicitly carry all previously earned receipts. -/
def BankRepairWAccepted {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  BankRepairCore ring hbank z ∧ BankRepairWord ring hbank z

def BankRepairRFoldEstablished {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  BankRepairWAccepted ring hbank z ∧ BankRepairReader ring hbank z

def BankRepairDBarred {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  BankRepairRFoldEstablished ring hbank z ∧ BankRepairDigit ring hbank z

def BankRepairDebtCleared {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  BankRepairDBarred ring hbank z ∧ BankRepairDebtZero ring hbank z

def BankRepairRequestsQuiet {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  BankRepairDebtCleared ring hbank z ∧ BankRepairRequestZero ring hbank z

/-- E.G5/E.G37 on the actual masked chain. Its five components
give the suffix closure needed to strengthen each raw first hit
to a cut retaining all earlier factors. This is a producer Prop. -/
def BankRepairReceiptPreservation {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  (∀ z : BankReferenceState ring hbank, BankRepairCore ring hbank z →
    ∀ e : Fin n,
      BankRepairCore ring hbank (bankRepairNext ring hbank z e)) ∧
  (∀ z : BankReferenceState ring hbank,
    BankRepairWAccepted ring hbank z → ∀ e : Fin n,
      BankRepairWAccepted ring hbank (bankRepairNext ring hbank z e)) ∧
  (∀ z : BankReferenceState ring hbank,
    BankRepairRFoldEstablished ring hbank z → ∀ e : Fin n,
      BankRepairRFoldEstablished ring hbank
        (bankRepairNext ring hbank z e)) ∧
  (∀ z : BankReferenceState ring hbank,
    BankRepairDBarred ring hbank z → ∀ e : Fin n,
      BankRepairDBarred ring hbank (bankRepairNext ring hbank z e)) ∧
  (∀ z : BankReferenceState ring hbank,
    BankRepairDebtCleared ring hbank z → ∀ e : Fin n,
      BankRepairDebtCleared ring hbank (bankRepairNext ring hbank z e))

/-- Twice the finite-horizon numerator, so a Nat rate means
rate*(n²/2) interactions. This is the cost form of a rational
ExpectedHittingTimeAtMost contract; it retains fractional credits
which whole-n² ceilings would lose. -/
def BankRepairHalfStage {S : Type} {n : Nat}
    (next : S → Fin n → S) (start finish : S → Prop)
    (halfUnits : Nat) : Prop :=
  ∀ x, start x → ∀ T,
    2 * costNumerator next finish x T ≤
      n ^ T * (halfUnits * n ^ 2)

/-! Each stage contains the ordinary StageReferenceGeneratedFinish
at the separately rounded-up whole-n² rate, AND the sharper
half-unit paper ledger obligation needed for the desired sum. -/

/-- repair.tex:2755-2767, 3296-3434, 5296-5323.
Prepared singleton -> actual accepted recurrence W. -/
def BankRepairWordStage {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  StageReferenceGeneratedFinish
    (bankRepairNext ring hbank)
    (BankPreparedAtSomeRoot ring hbank)
    (BankRepairWord ring hbank) (440 * bankRepairWidth n + 275) ∧
  BankRepairHalfStage
    (bankRepairNext ring hbank)
    (BankPreparedAtSomeRoot ring hbank)
    (BankRepairWord ring hbank) (2 * (440 * bankRepairWidth n + 275))

/-- repair.tex:3439-3450 and 5325-5329.
Accepted W -> retirement of resident readers and actual accepted fold. -/
def BankRepairReaderStage {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  StageReferenceGeneratedFinish
    (bankRepairNext ring hbank)
    (BankRepairWAccepted ring hbank)
    (BankRepairReader ring hbank) (bankRepairWidth n) ∧
  BankRepairHalfStage
    (bankRepairNext ring hbank)
    (BankRepairWAccepted ring hbank)
    (BankRepairReader ring hbank) (2 * bankRepairWidth n)

/-- repair.tex:4195-4239, 4552-4566, 4708-4748,
4994-5086, 5330-5361.
R -> barred D, including the dirty drain: e+g+P_pair+1 < 101.5
on the BANK band. Thus 102 whole units or 203 half units. -/
def BankRepairDigitStage {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  StageReferenceGeneratedFinish
    (bankRepairNext ring hbank)
    (BankRepairRFoldEstablished ring hbank)
    (BankRepairDigit ring hbank) 102 ∧
  BankRepairHalfStage
    (bankRepairNext ring hbank)
    (BankRepairRFoldEstablished ring hbank)
    (BankRepairDigit ring hbank) 203

/-- repair.tex:5367-5374: old EU/ED debt clears within n²/2. -/
def BankRepairDebtStage {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  StageReferenceGeneratedFinish
    (bankRepairNext ring hbank)
    (BankRepairDBarred ring hbank)
    (BankRepairDebtZero ring hbank) 1 ∧
  BankRepairHalfStage
    (bankRepairNext ring hbank)
    (BankRepairDBarred ring hbank)
    (BankRepairDebtZero ring hbank) 1

/-- repair.tex:5374-5380: requests coalesce to the protected root
in strictly less than n²; no new request is generated after debt. -/
def BankRepairRequestStage {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  StageReferenceGeneratedFinish
    (bankRepairNext ring hbank)
    (BankRepairDebtCleared ring hbank)
    (BankRepairRequestZero ring hbank) 1 ∧
  BankRepairHalfStage
    (bankRepairNext ring hbank)
    (BankRepairDebtCleared ring hbank)
    (BankRepairRequestZero ring hbank) 2

/-- repair.tex:5381-5389: the conjunction is the existing
referenceStop at zero extra scheduled services. -/
def BankRepairStopStage {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  StageReferenceGeneratedFinish
    (bankRepairNext ring hbank)
    (BankRepairRequestsQuiet ring hbank)
    (bankRepairStop ring hbank) 0 ∧
  BankRepairHalfStage
    (bankRepairNext ring hbank)
    (BankRepairRequestsQuiet ring hbank)
    (bankRepairStop ring hbank) 0

/-! Green preparation handoff supplies the two core factors
on the actual reference, with no extra entrance hypothesis. -/

theorem bankRepairPreparedCore {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankPreparedAtSomeRoot ring hbank z) :
    BankRepairCore ring hbank z := by
  have h := bankPreparedAtSomeRootCore ring hn hbank z hz
  rcases h with ⟨hprepared, _, hcand⟩
  rcases hprepared with ⟨hprotected, _, hone, hclean, _, _⟩
  constructor
  · change OneNativeLeader (nativeProjection z.val.1) ∧
      Protected ring (nativeProjection z.val.1) ∧
      C_native ring (nativeProjection z.val.1)
    exact ⟨hone, hprotected, hclean⟩
  · change H_cand ring (bankValidCandidateView ring hbank z)
    exact hcand

/-- All five physical target factors and the debt/request factor
are exactly the installed target, not a new strengthened target. -/
theorem bankRepairRequestsQuietStop {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank)
    (hz : BankRepairRequestsQuiet ring hbank z) :
    bankRepairStop ring hbank z := by
  rcases hz with
    ⟨⟨⟨⟨⟨hcore, hword⟩, hreader⟩, hdigit⟩, hdebt⟩, hrequest⟩
  rcases hcore with ⟨hnative, hcand⟩
  change Closure.G ring
    (Closure.readerFoldValid (ceilLogTwo n) n) z.val.1
  exact ⟨hnative, hcand, hword, hreader, hdigit,
    fun i => ⟨(hdebt i).1, (hdebt i).2, hrequest i⟩⟩

theorem bankRepairStopStageProved {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    BankRepairStopStage ring hbank := by
  constructor
  · intro z hz
    apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
      (bankRepairNext ring hbank) (bankRepairStop ring hbank)
      (by omega : 0 < n) z (0 * n ^ 2)).2
    intro T
    rw [costNumerator_terminal (bankRepairNext ring hbank)
      (bankRepairStop ring hbank) z
      (bankRepairRequestsQuietStop ring hbank z hz) T]
    exact Nat.zero_le _
  · intro z hz T
    rw [costNumerator_terminal (bankRepairNext ring hbank)
      (bankRepairStop ring hbank) z
      (bankRepairRequestsQuietStop ring hbank z hz) T]
    exact Nat.zero_le _

/-! Doubled-cost same-scheduler composition, proved directly from
the existing finite-horizon cost recursion. No independence of
stage clocks, and no integer rounding after each stop. -/

private theorem bankRepairHalfReserve {S : Type} {n : Nat}
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
                    ac_rfl
          rw [costNumerator_succ next P y hp T,
            costNumerator_succ next (fun z => A z ∨ P z) y hu T]
          omega

private theorem bankRepairHalfCompose {S : Type} {n : Nat}
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
  have hreserve := bankRepairHalfReserve next B Target
    (b * n ^ 2) (fun y hy T => hsecond y hy T) x T
  calc
    2 * costNumerator next Target x T ≤
        2 * costNumerator next (fun z => B z ∨ Target z) x T +
          n ^ T * (b * n ^ 2) := hreserve
    _ ≤ n ^ T * (a * n ^ 2) + n ^ T * (b * n ^ 2) :=
      Nat.add_le_add_right hfirstUnion _
    _ = n ^ T * ((a + b) * n ^ 2) := by
      rw [Nat.add_mul, Nat.mul_add]

/-- Zero-cost strengthening using a suffix-closed already earned
receipt class. This is where E.G37 is used in the six-stage chain. -/
private theorem bankRepairHalfStrengthen {S : Type} {n : Nat}
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

/-- The six genuine masked-reference clock propositions plus
the E.G5/E.G37 receipt closures give the fixed masked repair bound.
All five earlier receipts are retained by first-hit strengthening;
no unproved physical/unmasked cost domination is used. -/
theorem bankFinishMaskedRepairBoundOfStages {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hpres : BankRepairReceiptPreservation ring hbank)
    (hword : BankRepairWordStage ring hbank)
    (hreader : BankRepairReaderStage ring hbank)
    (hdigit : BankRepairDigitStage ring hbank)
    (hdebt : BankRepairDebtStage ring hbank)
    (hrequest : BankRepairRequestStage ring hbank)
    (hstop : BankRepairStopStage ring hbank) :
    BankFinishMaskedRepairBound ring hbank := by
  rcases hpres with
    ⟨hCoreClosed, hWordClosed, hReaderClosed,
      hDigitClosed, hDebtClosed⟩
  have hW : BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankPreparedAtSomeRoot ring hbank)
      (BankRepairWAccepted ring hbank)
      (2 * (440 * bankRepairWidth n + 275)) :=
    bankRepairHalfStrengthen (bankRepairNext ring hbank)
      (BankPreparedAtSomeRoot ring hbank)
      (BankRepairCore ring hbank) (BankRepairWord ring hbank)
      (2 * (440 * bankRepairWidth n + 275))
      (fun z hz => bankRepairPreparedCore ring hn hbank z hz)
      hCoreClosed hword.2
  have hR : BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankRepairWAccepted ring hbank)
      (BankRepairRFoldEstablished ring hbank)
      (2 * bankRepairWidth n) :=
    bankRepairHalfStrengthen (bankRepairNext ring hbank)
      (BankRepairWAccepted ring hbank)
      (BankRepairWAccepted ring hbank)
      (BankRepairReader ring hbank) (2 * bankRepairWidth n)
      (fun z hz => hz) hWordClosed hreader.2
  have hD : BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankRepairRFoldEstablished ring hbank)
      (BankRepairDBarred ring hbank) 203 :=
    bankRepairHalfStrengthen (bankRepairNext ring hbank)
      (BankRepairRFoldEstablished ring hbank)
      (BankRepairRFoldEstablished ring hbank)
      (BankRepairDigit ring hbank) 203
      (fun z hz => hz) hReaderClosed hdigit.2
  have hDebt : BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankRepairDBarred ring hbank)
      (BankRepairDebtCleared ring hbank) 1 :=
    bankRepairHalfStrengthen (bankRepairNext ring hbank)
      (BankRepairDBarred ring hbank)
      (BankRepairDBarred ring hbank)
      (BankRepairDebtZero ring hbank) 1
      (fun z hz => hz) hDigitClosed hdebt.2
  have hRequest : BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankRepairDebtCleared ring hbank)
      (BankRepairRequestsQuiet ring hbank) 2 :=
    bankRepairHalfStrengthen (bankRepairNext ring hbank)
      (BankRepairDebtCleared ring hbank)
      (BankRepairDebtCleared ring hbank)
      (BankRepairRequestZero ring hbank) 2
      (fun z hz => hz) hDebtClosed hrequest.2
  have hFromRequest : BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankRepairRequestsQuiet ring hbank)
      (bankRepairStop ring hbank) 0 := hstop.2
  have hFromDebt : BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankRepairDebtCleared ring hbank)
      (bankRepairStop ring hbank) (2 + 0) :=
    bankRepairHalfCompose (bankRepairNext ring hbank)
      (BankRepairDebtCleared ring hbank)
      (BankRepairRequestsQuiet ring hbank)
      (bankRepairStop ring hbank) 2 0 hRequest hFromRequest
  have hFromDigit : BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankRepairDBarred ring hbank)
      (bankRepairStop ring hbank) (1 + (2 + 0)) :=
    bankRepairHalfCompose (bankRepairNext ring hbank)
      (BankRepairDBarred ring hbank)
      (BankRepairDebtCleared ring hbank)
      (bankRepairStop ring hbank) 1 (2 + 0)
      hDebt hFromDebt
  have hFromReader : BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankRepairRFoldEstablished ring hbank)
      (bankRepairStop ring hbank) (203 + (1 + (2 + 0))) :=
    bankRepairHalfCompose (bankRepairNext ring hbank)
      (BankRepairRFoldEstablished ring hbank)
      (BankRepairDBarred ring hbank)
      (bankRepairStop ring hbank) 203 (1 + (2 + 0))
      hD hFromDigit
  have hFromWord : BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankRepairWAccepted ring hbank)
      (bankRepairStop ring hbank)
      (2 * bankRepairWidth n + (203 + (1 + (2 + 0)))) :=
    bankRepairHalfCompose (bankRepairNext ring hbank)
      (BankRepairWAccepted ring hbank)
      (BankRepairRFoldEstablished ring hbank)
      (bankRepairStop ring hbank)
      (2 * bankRepairWidth n) (203 + (1 + (2 + 0)))
      hR hFromReader
  have hFromPrepared : BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankPreparedAtSomeRoot ring hbank)
      (bankRepairStop ring hbank)
      (2 * (440 * bankRepairWidth n + 275) +
        (2 * bankRepairWidth n + (203 + (1 + (2 + 0))))) :=
    bankRepairHalfCompose (bankRepairNext ring hbank)
      (BankPreparedAtSomeRoot ring hbank)
      (BankRepairWAccepted ring hbank)
      (bankRepairStop ring hbank)
      (2 * (440 * bankRepairWidth n + 275))
      (2 * bankRepairWidth n + (203 + (1 + (2 + 0))))
      hW hFromWord
  intro z hz T
  change costNumerator (bankRepairNext ring hbank)
    (bankRepairStop ring hbank) z T ≤
      n ^ T * ((441 * bankRepairWidth n + 378) * n ^ 2)
  have hcost := hFromPrepared z hz T
  have hcoefficient :
      2 * (440 * bankRepairWidth n + 275) +
        (2 * bankRepairWidth n + (203 + (1 + (2 + 0)))) =
        2 * (441 * bankRepairWidth n + 378) := by
    omega
  rw [hcoefficient] at hcost
  have hscale :
      n ^ T * (2 * (441 * bankRepairWidth n + 378) * n ^ 2) =
        2 * (n ^ T * ((441 * bankRepairWidth n + 378) * n ^ 2)) := by
    ac_rfl
  rw [hscale] at hcost
  omega

/-- The SMALL/BANK selector itself entails q >= 80. -/
theorem bankRepairBankBand {n : Nat}
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) :
    80 ≤ ceilLogTwo n := by
  have hnot : ¬ ceilLogTwo n ≤ 79 := by
    intro hle
    have hsmall :
        (compileAdvice (ceilLogTwo n)).useSmall = true := by
      simp [Compiled.useSmall, compileAdvice, qStar, hle]
    rw [hbank] at hsmall
    cases hsmall
  omega

/-- The paper-sized cost converts to the precise installed
reference finish allowance, using the 113135*n² gap. -/
theorem bankFinishRepairBoundToReferenceFinish {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hrepair : BankFinishMaskedRepairBound ring hbank) :
    StageReferenceGeneratedFinish
      (bankRepairNext ring hbank)
      (BankPreparedAtSomeRoot ring hbank)
      (bankRepairStop ring hbank)
      (headlineReferenceFinishRate (ceilLogTwo n)) := by
  have hgap := bankFinishSpatialCoefficientGap
    (ceilLogTwo n) (bankRepairBankBand hbank)
  have hrate :
      441 * bankRepairWidth n + 378 ≤
        headlineReferenceFinishRate (ceilLogTwo n) := by
    unfold bankRepairWidth
    omega
  intro z hz
  apply (UniformFirstHit.expectedHittingTimeAtMost_iff_cost
    (bankRepairNext ring hbank) (bankRepairStop ring hbank)
    (by omega : 0 < n) z
    (headlineReferenceFinishRate (ceilLogTwo n) * n ^ 2)).2
  intro T
  exact Nat.le_trans (hrepair z hz T)
    (Nat.mul_le_mul_left (n ^ T)
      (Nat.mul_le_mul_right (n ^ 2) hrate))

/-- Conditional final interface, with no change to the source files. -/
theorem bankFinishReferenceFinishOfStages {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hpres : BankRepairReceiptPreservation ring hbank)
    (hword : BankRepairWordStage ring hbank)
    (hreader : BankRepairReaderStage ring hbank)
    (hdigit : BankRepairDigitStage ring hbank)
    (hdebt : BankRepairDebtStage ring hbank)
    (hrequest : BankRepairRequestStage ring hbank)
    (hstop : BankRepairStopStage ring hbank) :
    StageReferenceGeneratedFinish
      (bankRepairNext ring hbank)
      (BankPreparedAtSomeRoot ring hbank)
      (bankRepairStop ring hbank)
      (headlineReferenceFinishRate (ceilLogTwo n)) := by
  exact bankFinishRepairBoundToReferenceFinish ring hn hbank
    (bankFinishMaskedRepairBoundOfStages ring hn hbank
      hpres hword hreader hdigit hdebt hrequest hstop)

end L3.RenewalReferenceClock
