import Leader.L3.Bank.RepairReaderClose
import Leader.L3.Bank.RepairDigit

/-!
R10b consumer side of the grant-free retirement clock.

The installed reader interface `BankRepairReaderStage` (and its
producer `bankRepairReaderStageOfRetirementAndFold`) quantifies over
every `BankRepairWAccepted` start, a class with no grant field.  Its
only consumer, `bankFinishMaskedRepairBoundOfStages` (and through it
`bankFinishReferenceFinishOfStages`), starts at
`BankPreparedAtSomeRoot`, whose root singleton already contains
`BankPostInheritedGrantDrain`, and the drain is closed under
`bankRepairNext` (`bankPostInheritedGrantDrainClosed`).  So every state
at which the six-stage chain uses the reader clock is grant-free.

This module restates the R stage on `BankPostInheritedGrantDrain ∧
BankRepairWAccepted`, produces it from
`bankRepairResidentRetirementClockOnDrain` plus a fold-soundness input
restricted to the same class, and re-proves the six-stage masked
repair bound with that stage in place of `BankRepairReaderStage`.
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-! ## Half-unit stage algebra (public copies of the private
BankFinishRepair helpers, same statements) -/

/-- Reserve: hitting P costs at most hitting A ∨ P plus A's allowance.
Consumer: `bankRepairCloseHalfCompose`. -/
theorem bankRepairCloseHalfReserve {S : Type} {n : Nat}
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

/-- Sequential composition of half-unit stages.
Consumer: `bankFinishMaskedRepairBoundOfStagesOnDrain`. -/
theorem bankRepairCloseHalfCompose {S : Type} {n : Nat}
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
  have hreserve := bankRepairCloseHalfReserve next B Target
    (b * n ^ 2) (fun y hy T => hsecond y hy T) x T
  calc
    2 * costNumerator next Target x T ≤
        2 * costNumerator next (fun z => B z ∨ Target z) x T +
          n ^ T * (b * n ^ 2) := hreserve
    _ ≤ n ^ T * (a * n ^ 2) + n ^ T * (b * n ^ 2) :=
      Nat.add_le_add_right hfirstUnion _
    _ = n ^ T * ((a + b) * n ^ 2) := by
      rw [Nat.add_mul, Nat.mul_add]

/-- Zero-cost strengthening by a suffix-closed class.
Consumer: `bankFinishMaskedRepairBoundOfStagesOnDrain`. -/
theorem bankRepairCloseHalfStrengthen {S : Type} {n : Nat}
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

/-- Weakening the target of a half-unit stage.
Consumer: `bankFinishMaskedRepairBoundOfStagesOnDrain`. -/
theorem bankRepairCloseHalfWeaken {S : Type} {n : Nat}
    (next : S → Fin n → S) (Start P Q : S → Prop) (a : Nat)
    (hPQ : ∀ z, P z → Q z)
    (h : BankRepairHalfStage next Start P a) :
    BankRepairHalfStage next Start Q a := by
  intro z hz T
  exact Nat.le_trans
    (Nat.mul_le_mul_left 2
      (Prob.costNumerator_target_mono next P Q hPQ z T))
    (h z hz T)

/-! ## The R stage on the grant-free class -/

/-- The W-accepted grant-free class in which the R stage runs.
Consumer: `BankRepairReaderStageOnDrain`. -/
def BankRepairWAcceptedOnDrain {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (z : BankReferenceState ring hbank) : Prop :=
  BankPostInheritedGrantDrain ring hbank z ∧
    BankRepairWAccepted ring hbank z

/-- `BankRepairReaderFoldSound` restricted to grant-free W starts:
the same E.G22 acceptance at a done cut, demanded only where the
repair runs.  Consumer: `bankRepairReaderStageOnDrainOfFold`. -/
def BankRepairReaderFoldSoundOnDrain {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  ∀ (start finish : BankReferenceState ring hbank)
    (word : List (Fin n))
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))))
    (control : BlockA.ReaderControl n
      (compileAdvice (ceilLogTwo n))),
    BankRepairWAcceptedOnDrain ring hbank start →
    finish = word.foldl (bankRepairNext ring hbank) start →
    BlockA.initializesReader
      (AcceptedReceipts.AcceptedWord ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      (piR start.val.1) initial →
    BlockA.Run ring (phiR ring)
      (BlockA.readerControlNext ring)
      (piR start.val.1) initial word
      (piR finish.val.1)
      (.live (piR finish.val.1) control) →
    control.phase = .done →
    (∀ name : Fin n, control.inheritedNames name = false) →
    BlockA.acceptsReader
      (Closure.readerFoldValid (ceilLogTwo n) n)
      (AcceptedReceipts.QReader ring)
      (piR finish.val.1)
      (.live (piR finish.val.1) control)

/-- The installed fold soundness implies the restricted one.
Consumer: callers holding `BankRepairReaderFoldSound`. -/
theorem bankRepairReaderFoldSoundOnDrainOfFoldSound {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hfold : BankRepairReaderFoldSound ring hbank) :
    BankRepairReaderFoldSoundOnDrain ring hbank := by
  intro start finish word initial control hW
  exact hfold start finish word initial control hW.2

/-- The R half-stage of `BankRepairReaderStage`, on the grant-free
class.  Consumer: `bankFinishMaskedRepairBoundOfStagesOnDrain`. -/
def BankRepairReaderStageOnDrain {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false) : Prop :=
  BankRepairHalfStage
    (bankRepairNext ring hbank)
    (BankRepairWAcceptedOnDrain ring hbank)
    (BankRepairReader ring hbank)
    (2 * ceilLogTwo (ceilLogTwo n))

/-- Replaces `bankRepairReaderStageOfRetirementAndFold` (half-unit
part) on the grant-free class: the clock premise is now the proved
`bankRepairResidentRetirementClockOnDrain`; the remaining input is
fold soundness on the same class.
Consumer: `bankFinishMaskedRepairBoundOfStagesOnDrain`. -/
theorem bankRepairReaderStageOnDrainOfFold {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hfold : BankRepairReaderFoldSoundOnDrain ring hbank) :
    BankRepairReaderStageOnDrain ring hbank := by
  intro start hS T
  have hmono :
      costNumerator (bankRepairNext ring hbank)
          (BankRepairReader ring hbank) start T ≤
        costNumerator (bankRepairNext ring hbank)
          (BankRepairReaderRetiredFrom ring hbank start)
          start T :=
    Prob.costNumerator_target_mono
      (bankRepairNext ring hbank)
      (BankRepairReaderRetiredFrom ring hbank start)
      (BankRepairReader ring hbank)
      (fun finish hret => by
        rcases hret with
          ⟨word, initial, control, hactual, hinit,
            hrun, hdone, hnames⟩
        have hacc := hfold start finish word initial control
          hS hactual hinit hrun hdone hnames
        change AcceptedReceipts.AcceptedReader ring
          (AcceptedReceipts.AcceptedWord ring
            (BlockA.wordT ring) (BlockA.wordValidated ring))
          (Closure.readerFoldValid (ceilLogTwo n) n)
          (piR finish.val.1)
        exact ⟨piR start.val.1, initial, word,
          .live (piR finish.val.1) control,
          hinit, hrun, hacc⟩) start T
  exact Nat.le_trans (Nat.mul_le_mul_left 2 hmono)
    (bankRepairResidentRetirementClockOnDrain ring hn hbank
      start hS.1 hS.2 T)

/-! ## The six-stage masked repair bound with the grant-free R stage -/

/-- Replaces `bankFinishMaskedRepairBoundOfStages`: the same masked
repair bound from `BankPreparedAtSomeRoot`, with the R stage taken on
the grant-free class.  Every other premise is the installed one.
Consumer: `bankFinishReferenceFinishOfStagesOnDrain`. -/
theorem bankFinishMaskedRepairBoundOfStagesOnDrain {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hpres : BankRepairReceiptPreservation ring hbank)
    (hword : BankRepairWordStage ring hbank)
    (hreader : BankRepairReaderStageOnDrain ring hbank)
    (hdigit : BankRepairDigitStage ring hbank)
    (hdebt : BankRepairDebtStage ring hbank)
    (hrequest : BankRepairRequestStage ring hbank)
    (hstop : BankRepairStopStage ring hbank) :
    BankFinishMaskedRepairBound ring hbank := by
  rcases hpres with
    ⟨hCoreClosed, hWordClosed, hReaderClosed,
      hDigitClosed, hDebtClosed⟩
  have hDrainClosed := bankPostInheritedGrantDrainClosed ring hn hbank
  have hPrepDrain : ∀ z, BankPreparedAtSomeRoot ring hbank z →
      BankPostInheritedGrantDrain ring hbank z := by
    intro z hz
    obtain ⟨_, hs, _⟩ := hz
    exact hs.1
  have hW0 : BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankPreparedAtSomeRoot ring hbank)
      (fun z => (BankPostInheritedGrantDrain ring hbank z ∧
          BankRepairCore ring hbank z) ∧ BankRepairWord ring hbank z)
      (2 * (440 * ceilLogTwo (ceilLogTwo n) + 275)) :=
    bankRepairCloseHalfStrengthen (bankRepairNext ring hbank)
      (BankPreparedAtSomeRoot ring hbank)
      (fun z => BankPostInheritedGrantDrain ring hbank z ∧
        BankRepairCore ring hbank z)
      (BankRepairWord ring hbank)
      (2 * (440 * ceilLogTwo (ceilLogTwo n) + 275))
      (fun z hz => ⟨hPrepDrain z hz,
        bankRepairPreparedCore ring hn hbank z hz⟩)
      (fun z hz e => ⟨hDrainClosed z hz.1 e, hCoreClosed z hz.2 e⟩)
      hword.2
  have hW : BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankPreparedAtSomeRoot ring hbank)
      (BankRepairWAcceptedOnDrain ring hbank)
      (2 * (440 * ceilLogTwo (ceilLogTwo n) + 275)) :=
    bankRepairCloseHalfWeaken (bankRepairNext ring hbank) _ _ _ _
      (fun z hz => ⟨hz.1.1, hz.1.2, hz.2⟩) hW0
  have hR0 : BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankRepairWAcceptedOnDrain ring hbank)
      (fun z => BankRepairWAcceptedOnDrain ring hbank z ∧
        BankRepairReader ring hbank z)
      (2 * ceilLogTwo (ceilLogTwo n)) :=
    bankRepairCloseHalfStrengthen (bankRepairNext ring hbank)
      (BankRepairWAcceptedOnDrain ring hbank)
      (BankRepairWAcceptedOnDrain ring hbank)
      (BankRepairReader ring hbank) (2 * ceilLogTwo (ceilLogTwo n))
      (fun z hz => hz)
      (fun z hz e => ⟨hDrainClosed z hz.1 e, hWordClosed z hz.2 e⟩)
      hreader
  have hR : BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankRepairWAcceptedOnDrain ring hbank)
      (BankRepairRFoldEstablished ring hbank)
      (2 * ceilLogTwo (ceilLogTwo n)) :=
    bankRepairCloseHalfWeaken (bankRepairNext ring hbank) _ _ _ _
      (fun z hz => ⟨hz.1.2, hz.2⟩) hR0
  have hD : BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankRepairRFoldEstablished ring hbank)
      (BankRepairDBarred ring hbank) 203 :=
    bankRepairCloseHalfStrengthen (bankRepairNext ring hbank)
      (BankRepairRFoldEstablished ring hbank)
      (BankRepairRFoldEstablished ring hbank)
      (BankRepairDigit ring hbank) 203
      (fun z hz => hz) hReaderClosed hdigit.2
  have hDebt : BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankRepairDBarred ring hbank)
      (BankRepairDebtCleared ring hbank) 1 :=
    bankRepairCloseHalfStrengthen (bankRepairNext ring hbank)
      (BankRepairDBarred ring hbank)
      (BankRepairDBarred ring hbank)
      (BankRepairDebtZero ring hbank) 1
      (fun z hz => hz) hDigitClosed hdebt.2
  have hRequest : BankRepairHalfStage
      (bankRepairNext ring hbank)
      (BankRepairDebtCleared ring hbank)
      (BankRepairRequestsQuiet ring hbank) 2 :=
    bankRepairCloseHalfStrengthen (bankRepairNext ring hbank)
      (BankRepairDebtCleared ring hbank)
      (BankRepairDebtCleared ring hbank)
      (BankRepairRequestZero ring hbank) 2
      (fun z hz => hz) hDebtClosed hrequest.2
  have hFromDebt := bankRepairCloseHalfCompose (bankRepairNext ring hbank)
    (BankRepairDebtCleared ring hbank)
    (BankRepairRequestsQuiet ring hbank)
    (bankRepairStop ring hbank) 2 0 hRequest hstop.2
  have hFromDigit := bankRepairCloseHalfCompose (bankRepairNext ring hbank)
    (BankRepairDBarred ring hbank)
    (BankRepairDebtCleared ring hbank)
    (bankRepairStop ring hbank) 1 (2 + 0) hDebt hFromDebt
  have hFromReader := bankRepairCloseHalfCompose (bankRepairNext ring hbank)
    (BankRepairRFoldEstablished ring hbank)
    (BankRepairDBarred ring hbank)
    (bankRepairStop ring hbank) 203 (1 + (2 + 0)) hD hFromDigit
  have hFromWord := bankRepairCloseHalfCompose (bankRepairNext ring hbank)
    (BankRepairWAcceptedOnDrain ring hbank)
    (BankRepairRFoldEstablished ring hbank)
    (bankRepairStop ring hbank)
    (2 * ceilLogTwo (ceilLogTwo n)) (203 + (1 + (2 + 0))) hR hFromReader
  have hFromPrepared := bankRepairCloseHalfCompose (bankRepairNext ring hbank)
    (BankPreparedAtSomeRoot ring hbank)
    (BankRepairWAcceptedOnDrain ring hbank)
    (bankRepairStop ring hbank)
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

/-- Replaces `bankFinishReferenceFinishOfStages`: the installed
reference finish allowance from the six stages, with the R stage on
the grant-free class supplied by the proved retirement clock and
grant-free fold soundness.  Consumer: the BANK reference finish
(`BankReferenceClock` finish field) once fold soundness is closed. -/
theorem bankFinishReferenceFinishOfStagesOnDrain {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hpres : BankRepairReceiptPreservation ring hbank)
    (hword : BankRepairWordStage ring hbank)
    (hfold : BankRepairReaderFoldSoundOnDrain ring hbank)
    (hdigit : BankRepairDigitStage ring hbank)
    (hdebt : BankRepairDebtStage ring hbank)
    (hrequest : BankRepairRequestStage ring hbank)
    (hstop : BankRepairStopStage ring hbank) :
    StageReferenceGeneratedFinish
      (bankRepairNext ring hbank)
      (BankPreparedAtSomeRoot ring hbank)
      (bankRepairStop ring hbank)
      (headlineReferenceFinishRate (ceilLogTwo n)) :=
  bankFinishRepairBoundToReferenceFinish ring hn hbank
    (bankFinishMaskedRepairBoundOfStagesOnDrain ring hn hbank
      hpres hword (bankRepairReaderStageOnDrainOfFold ring hn hbank hfold)
      hdigit hdebt hrequest hstop)

/-! ## E.G22 (iv): clockwise sample-site geometry of fresh reader windows

A fresh R1c/R0b ledger at site `s` with index `L` records its OLD
samples at the L consecutive clockwise sites ending at `s`: the entry
at position `pos` was read at the site `L-1-pos` steps counterclockwise
of `s`.  Each recorded OLD bit and marker is the W-origin visible value
at that source site, and a sample read at the fixed root records
`postLeader = true`.  This geometry is carried by the genuine phiR
reader Run from the accepted W cut (where no fresh ledger exists). -/

/-- One recorded sample read `d` steps counterclockwise of `site`.
Consumer: `BankRepairCloseReaderWindow`. -/
def BankRepairCloseSampleFacts {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (origin : Fin n → ProjR c) (site : Fin n) (d : Nat)
    (r : BlockA.ReaderSample n) : Prop :=
  PPL.shiftRight ring r.source d = site ∧
    r.oldBit = (origin r.source).word.u ∧
    r.oldMarker = (origin r.source).word.beta ∧
    (r.source = root → r.postLeader = true)

/-- The sample-window geometry of every fresh ledger.
Consumer: `bankRepairCloseNoRootGuard` via `bankRepairCloseRowsAtOfValues`. -/
def BankRepairCloseReaderWindow {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (root : Fin n)
    (origin : Fin n → ProjR c) (h : BlockA.ReaderControl n c) : Prop :=
  ∀ (site name : Fin n) (index : Fin (c.t + 1))
    (samples : BlockA.FiniteLedger (BlockA.ReaderSample n) c.t),
    h.tags site = .fresh name index samples →
    ∀ pos : Fin c.t, pos.val < index.val →
      ∃ r : BlockA.ReaderSample n, samples.entries pos = some r ∧
        BankRepairCloseSampleFacts ring root origin site
          (index.val - 1 - pos.val) r

/-- Zero clockwise steps.  Consumer: `bankRepairCloseWindowStep`. -/
theorem bankRepairCloseShiftZero {n : Nat} (ring : DirectedRing n)
    (i : Fin n) : PPL.shiftRight ring i 0 = i := by
  apply Fin.ext
  show (i.val + 0) % n = i.val
  rw [Nat.add_zero]
  exact Nat.mod_eq_of_lt i.isLt

/-- Clockwise steps compose.  Consumer: `bankRepairCloseNoRootGuard`. -/
theorem bankRepairCloseShiftAdd {n : Nat} (ring : DirectedRing n)
    (i : Fin n) (a b : Nat) :
    PPL.shiftRight ring (PPL.shiftRight ring i a) b =
      PPL.shiftRight ring i (a + b) := by
  apply Fin.ext
  show ((i.val + a) % n + b) % n = (i.val + (a + b)) % n
  rw [Nat.mod_add_mod, Nat.add_assoc]

/-- n clockwise steps return.  Consumer: `bankRepairCloseNoRootGuard`. -/
theorem bankRepairCloseShiftFull {n : Nat} (ring : DirectedRing n)
    (i : Fin n) : PPL.shiftRight ring i n = i := by
  apply Fin.ext
  show (i.val + n) % n = i.val
  rw [Nat.add_mod_right]
  exact Nat.mod_eq_of_lt i.isLt

/-- A fixed number of clockwise steps is injective.
Consumer: `bankRepairCloseNoRootGuard`. -/
theorem bankRepairCloseShiftCancel {n : Nat} (ring : DirectedRing n)
    (i i' : Fin n) (d : Nat)
    (h : PPL.shiftRight ring i d = PPL.shiftRight ring i' d) :
    i = i' := by
  have key : ∀ x : Fin n,
      PPL.shiftRight ring (PPL.shiftRight ring x d) (n - d % n) = x := by
    intro x
    rw [bankRepairCloseShiftAdd]
    apply Fin.ext
    show (x.val + (d + (n - d % n))) % n = x.val
    have hdm := Nat.div_add_mod d n
    have hlt := Nat.mod_lt d ring.hn
    have harith : x.val + (d + (n - d % n)) = x.val + n * (d / n + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    rw [harith, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt x.isLt
  have h1 := key i
  rw [h, key i'] at h1
  exact h1.symm

/-- Every site sits at some clockwise offset below n from the root.
Consumer: `bankRepairCloseNoRootGuard`. -/
theorem bankRepairCloseOffset {n : Nat} (ring : DirectedRing n)
    (root site : Fin n) :
    ∃ k : Nat, k < n ∧ PPL.shiftRight ring root k = site := by
  refine ⟨(site.val + n - root.val) % n, Nat.mod_lt _ ring.hn, ?_⟩
  apply Fin.ext
  show (root.val + (site.val + n - root.val) % n) % n = site.val
  rw [Nat.add_mod_mod]
  have hr := root.isLt
  rw [show root.val + (site.val + n - root.val) = site.val + n by omega,
    Nat.add_mod_right]
  exact Nat.mod_eq_of_lt site.isLt

/-- The source tag of the selected pair is erased or kept.
Consumer: `bankRepairCloseWindowStep`. -/
theorem bankRepairCloseTagsSourceCases {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.ReaderControl n c)
    (p p' : Fin n → ProjR c) (e : Fin n) :
    (BlockA.readerControlNext ring h p e p').tags e = .empty ∨
      (BlockA.readerControlNext ring h p e p').tags e = h.tags e := by
  rcases bankRepairCloseRowCases (p e) (p (ring.rightNeighbor e)) with
    ⟨_, _, _, _, hc, _, _⟩ | ⟨_, _, _, _, _, hc, _, _, _⟩ |
    ⟨_, _, _, _, hc, _, _⟩ | ⟨_, _, _, hc, _, _⟩ |
    ⟨_, _, hc, _, _⟩ | ⟨_, _, hc, _⟩
  · exact Or.inl (bankRepairCloseTagsSourceErased ring h p p' e (Or.inl hc))
  · exact Or.inl (bankRepairCloseTagsSourceErased ring h p p' e
      (Or.inr (Or.inl hc)))
  · exact Or.inl (bankRepairCloseTagsSourceErased ring h p p' e
      (Or.inr (Or.inr hc)))
  · exact Or.inr (bankRepairCloseTagsSourceKept ring h p p' e (Or.inl hc))
  · exact Or.inr (bankRepairCloseTagsSourceKept ring h p p' e
      (Or.inr (Or.inl hc)))
  · exact Or.inr (bankRepairCloseTagsSourceKept ring h p p' e
      (Or.inr (Or.inr hc)))

/-- R1c launch shape: the new fresh ledger has index one and its
single entry is the selected OLD sample.
Consumer: `bankRepairCloseWindowStep`. -/
theorem bankRepairCloseLaunchShape {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (h : BlockA.ReaderControl n c)
    (p p' : Fin n → ProjR c) (e : Fin n)
    (hne : ring.rightNeighbor e ≠ e)
    (hc : BlockA.readerCase (p e) (p (ring.rightNeighbor e)) = .kickLaunch)
    (name : Fin n) (index : Fin (c.t + 1))
    (samples : BlockA.FiniteLedger (BlockA.ReaderSample n) c.t)
    (htag : (BlockA.readerControlNext ring h p e p').tags
      (ring.rightNeighbor e) = .fresh name index samples) :
    index.val = 1 ∧ ∀ pos : Fin c.t, pos.val < index.val →
      samples.entries pos = some (BlockA.readerSelectedSample
        (ring.rightNeighbor e) (p e) (p (ring.rightNeighbor e))) := by
  simp [BlockA.readerControlNext, hc, hne] at htag
  split at htag
  · cases htag
  · split at htag
    · rename_i ht
      cases htag
      refine ⟨rfl, ?_⟩
      intro pos hpos
      have hpos0 : pos.val = 0 := by
        change pos.val < 1 at hpos
        omega
      simp [BlockA.FiniteLedger.push, ht, hpos0]
    · cases htag

/-- E.G22 (iv) one-edge step: the sample-window geometry survives
every OLD reader row on the phiR successor.  Inputs are the numerical
count/cursor of the moving ledger, the visible value of the sampled
responder, and the root's POST leader bit.
Consumer: `bankRepairCloseWindowAlongRun`. -/
theorem bankRepairCloseWindowStep {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (hn2 : 2 ≤ n) (root : Fin n)
    (origin : Fin n → ProjR c) (h : BlockA.ReaderControl n c)
    (p p' : Fin n → ProjR c) (e : Fin n)
    (hW : BankRepairCloseReaderWindow ring root origin h)
    (hsrc : ∀ (name : Fin n) (index : Fin (c.t + 1))
      (samples : BlockA.FiniteLedger (BlockA.ReaderSample n) c.t),
      h.tags e = .fresh name index samples →
      samples.count = index ∧
        ∀ raw : RawTok c.t, (p e).rawTok = some raw → raw.j = index.val)
    (hread : (BlockA.readerSelectedSample (ring.rightNeighbor e)
        (p e) (p (ring.rightNeighbor e))).oldBit =
        (origin (ring.rightNeighbor e)).word.u ∧
      (BlockA.readerSelectedSample (ring.rightNeighbor e)
        (p e) (p (ring.rightNeighbor e))).oldMarker =
        (origin (ring.rightNeighbor e)).word.beta)
    (hroot : ring.rightNeighbor e = root →
      (postW (p e).word (p (ring.rightNeighbor e)).word).eY.l = true) :
    BankRepairCloseReaderWindow ring root origin
      (BlockA.readerControlNext ring h p e p') := by
  have hne := clockNeighborDifferent ring hn2 e
  have hfresh : BankRepairCloseSampleFacts ring root origin
      (ring.rightNeighbor e) 0
      (BlockA.readerSelectedSample (ring.rightNeighbor e)
        (p e) (p (ring.rightNeighbor e))) := by
    refine ⟨bankRepairCloseShiftZero ring _, hread.1, hread.2, ?_⟩
    intro hr
    exact hroot hr
  intro site name index samples htag pos hpos
  by_cases hse : site = e
  · subst hse
    rcases bankRepairCloseTagsSourceCases ring h p p' site with hE | hK
    · rw [hE] at htag
      cases htag
    · rw [hK] at htag
      exact hW site name index samples htag pos hpos
  · by_cases hsj : site = ring.rightNeighbor e
    · subst hsj
      rcases bankRepairCloseRowCases (p e) (p (ring.rightNeighbor e)) with
        ⟨_, _, _, _, hc, _, _⟩ | ⟨src, _, hx, _, hm, hc, _, _, _⟩ |
        ⟨_, _, _, _, hc, _, _⟩ | ⟨_, _, _, hc, _, _⟩ |
        ⟨_, _, hc, _, _⟩ | ⟨_, _, hc, _⟩
      · rw [bankRepairCloseTagsTargetKept ring h p p' e hne (Or.inl hc)] at htag
        exact hW _ name index samples htag pos hpos
      · rw [bankRepairCloseTagsTargetMove ring h p p' e hne hc] at htag
        cases hte : h.tags e with
        | empty =>
            rw [hte] at htag
            cases htag
        | inherited m =>
            rw [hte] at htag
            cases htag
        | fresh name0 idx0 smp0 =>
            rw [hte] at htag
            obtain ⟨hcount, hcur⟩ := hsrc name0 idx0 smp0 hte
            have hj := hcur src hx
            have hlt0 : idx0.val < c.t := by
              have : src.j < c.t := hm
              omega
            have hT : BlockA.readerTransfer (.fresh name0 idx0 smp0)
                (BlockA.readerSelectedSample (ring.rightNeighbor e)
                  (p e) (p (ring.rightNeighbor e))) =
                .fresh name0 ⟨idx0.val + 1, Nat.succ_lt_succ hlt0⟩
                  (smp0.push (BlockA.readerSelectedSample
                    (ring.rightNeighbor e) (p e)
                    (p (ring.rightNeighbor e)))) := by
              simp [BlockA.readerTransfer, hlt0]
            rw [hT] at htag
            injection htag with hnm hidx hsmp
            subst hidx
            subst hsmp
            have hclt : smp0.count.val < c.t := by
              rw [hcount]
              exact hlt0
            have hentries : (smp0.push (BlockA.readerSelectedSample
                (ring.rightNeighbor e) (p e)
                (p (ring.rightNeighbor e)))).entries pos =
                if pos.val = smp0.count.val then
                  some (BlockA.readerSelectedSample
                    (ring.rightNeighbor e) (p e)
                    (p (ring.rightNeighbor e)))
                else smp0.entries pos := by
              unfold BlockA.FiniteLedger.push
              rw [dif_pos hclt]
            rw [hentries]
            have hcv : smp0.count.val = idx0.val := by rw [hcount]
            rw [hcv]
            change pos.val < idx0.val + 1 at hpos
            by_cases hpe : pos.val = idx0.val
            · rw [if_pos hpe]
              refine ⟨_, rfl, ?_⟩
              have hd : idx0.val + 1 - 1 - pos.val = 0 := by omega
              rw [hd]
              exact hfresh
            · rw [if_neg hpe]
              obtain ⟨r, hr, hfacts⟩ :=
                hW e name0 idx0 smp0 hte pos (by omega)
              refine ⟨r, hr, ?_⟩
              obtain ⟨hshift, hb, hmk, hrt⟩ := hfacts
              refine ⟨?_, hb, hmk, hrt⟩
              have hd : idx0.val + 1 - 1 - pos.val =
                  (idx0.val - 1 - pos.val) + 1 := by omega
              rw [hd, WordPhase.wordPhaseShiftSucc, hshift]
      · rw [bankRepairCloseTagsTargetTerminal ring h p p' e hne hc] at htag
        cases htag
      · rw [bankRepairCloseTagsTargetKept ring h p p' e hne
          (Or.inr (Or.inl hc))] at htag
        exact hW _ name index samples htag pos hpos
      · rw [bankRepairCloseTagsTargetKept ring h p p' e hne
          (Or.inr (Or.inr hc))] at htag
        exact hW _ name index samples htag pos hpos
      · obtain ⟨hone, hent⟩ := bankRepairCloseLaunchShape ring h p p' e hne hc
          name index samples htag
        refine ⟨_, hent pos hpos, ?_⟩
        have hd : index.val - 1 - pos.val = 0 := by omega
        rw [hd]
        exact hfresh
    · rw [bankRepairCloseTagsOther ring h p p' e site hse hsj] at htag
      exact hW site name index samples htag pos hpos

/-- The fixed W root survives along the genuine phiR reader Run.
Consumer: `bankRepairCloseWindowAlongRun`, `bankRepairCloseRowsAtOfValues`. -/
theorem bankRepairCloseFixedRootAlongRun {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (hn3 : 3 ≤ n) (root : Fin n)
    (origin : Fin n → ProjR c)
    (initial : BlockA.Decoration (Fin n → ProjR c)
      (BlockA.ReaderControl n c))
    (hfix : WFixedRoot ring root
      (AcceptedReceipts.wordProjectionR origin))
    (word : List (Fin n)) (p : Fin n → ProjR c)
    (γ : BlockA.Decoration (Fin n → ProjR c) (BlockA.ReaderControl n c))
    (hrun : BlockA.Run ring (phiR ring) (BlockA.readerControlNext ring)
      origin initial word p γ) :
    WFixedRoot ring root (AcceptedReceipts.wordProjectionR p) := by
  induction hrun with
  | empty => exact hfix
  | @next w q γ' _ e ih =>
      rw [AcceptedReceipts.wordProjectionR_phiR]
      exact bankRepairDigitWFixedRootPhiW hn3 ring root _ e ih

/-- The root's POST-E leader bit is set on every edge into the root.
Consumer: `bankRepairCloseWindowAlongRun`. -/
theorem bankRepairCloseRootPostLeader {n : Nat} {c : Compiled}
    (ring : DirectedRing n) (hn3 : 3 ≤ n) (root : Fin n)
    (p : Fin n → ProjR c)
    (hfix : WFixedRoot ring root (AcceptedReceipts.wordProjectionR p))
    (e : Fin n) (hj : ring.rightNeighbor e = root) :
    (postW (p e).word (p (ring.rightNeighbor e)).word).eY.l = true := by
  have hne := clockNeighborDifferent ring (by omega) e
  cases hl : (postW (p e).word (p (ring.rightNeighbor e)).word).eY.l with
  | true => rfl
  | false =>
      exact absurd hj (bankRepairDigitEYFalse ring root
        (AcceptedReceipts.wordProjectionR p) e hne
        (bankRepairDigitWFixedRootPhiW hn3 ring root _ e hfix) hl)

/-- E.G22 (iv): along the genuine phiR reader Run from an accepted W
cut with fixed root, every fresh ledger satisfies the sample-window
geometry.  Consumer: `bankRepairCloseRowsAtOfValues` (E22 row
preservation, hence `BankRepairReaderFoldSound`). -/
theorem bankRepairCloseWindowAlongRun {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (origin : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))))
    (hinit : BlockA.initializesReader
      (AcceptedReceipts.AcceptedWord ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      origin initial)
    (hfix : WFixedRoot ring root
      (AcceptedReceipts.wordProjectionR origin))
    (word : List (Fin n))
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (γ : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))))
    (hrun : BlockA.Run ring (phiR ring) (BlockA.readerControlNext ring)
      origin initial word p γ) :
    ∃ h : BlockA.ReaderControl n (compileAdvice (ceilLogTwo n)),
      γ = .live p h ∧ BankRepairCloseReaderWindow ring root origin h := by
  have hn3 : 3 ≤ n := by omega
  induction hrun with
  | empty =>
      obtain ⟨_hword, h, heq, _hphase, hslots⟩ := hinit
      refine ⟨h, heq, ?_⟩
      intro site name index samples htag
      exact False.elim
        ((bankRepairReaderE22InitialNoFresh origin h hslots)
          site name index samples htag)
  | @next w q γ' hrunPrefix e ih =>
      obtain ⟨h, hγ, hwin⟩ := ih
      have hprefix : BlockA.Run ring (phiR ring)
          (BlockA.readerControlNext ring)
          origin initial w q (.live q h) := by
        simpa [hγ] using hrunPrefix
      have hnumeric := bankRepairReaderE22NumericalRunLive
        ring hbank origin initial hinit w q h hprefix
      have hread := bankRepairReaderE22SelectedReadFixedOnRun
        ring origin initial hinit w q h hprefix e
      have hfixq := bankRepairCloseFixedRootAlongRun ring hn3 root origin
        initial hfix w q _ hprefix
      have hstep := bankRepairCloseWindowStep ring (by omega) root origin h q
        (phiR ring q e) e hwin
        (fun name index samples htag => by
          obtain ⟨hcount, hvalid⟩ := hnumeric.2 e name index samples htag
          refine ⟨hcount, ?_⟩
          intro raw hraw
          rw [hraw] at hvalid
          dsimp [Closure.readerFoldValid] at hvalid
          exact hvalid.2.1)
        hread
        (bankRepairCloseRootPostLeader ring hn3 root q hfixq e)
      refine ⟨_, ?_, hstep⟩
      rw [hγ]
      classical
      simp [BlockA.update]

/-! ## Finite fold identities for the published window -/

/-- mapM over a range with only `some` results.
Consumer: `bankRepairCloseNoRootGuard`. -/
theorem bankRepairCloseMapMRange {α : Type} (f : Nat → Option α)
    (F : Nat → α) :
    ∀ (m s : Nat), (∀ pos, s ≤ pos → pos < s + m → f pos = some (F pos)) →
      (List.range' s m).mapM f = some ((List.range' s m).map F) := by
  intro m
  induction m with
  | zero => intro s _; rfl
  | succ m ih =>
      intro s hf
      rw [List.range'_succ, List.mapM_cons, List.map_cons,
        hf s (Nat.le_refl s) (by omega),
        ih (s + 1) (fun pos h1 h2 => hf pos (by omega) (by omega))]
      rfl

/-- Pointwise agreement below m gives equal range folds.
Consumer: `bankRepairCloseNoRootGuard`. -/
theorem bankRepairCloseFoldRangeCongr {α : Type} (f g : α → Nat → α)
    (init : α) :
    ∀ m : Nat, (∀ a j, j < m → f a j = g a j) →
      (List.range m).foldl f init = (List.range m).foldl g init := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
      intro hfg
      rw [List.range_succ, List.foldl_append, List.foldl_append,
        ih (fun a j hj => hfg a j (by omega))]
      simp only [List.foldl_cons, List.foldl_nil]
      exact hfg _ m (by omega)

/-- The counter-carrying parity fold is the indexed parity fold.
Consumer: `bankRepairCloseNoRootGuard`. -/
theorem bankRepairCloseParityCounter (taps : Nat → Bool) (B : Nat → Bool) :
    ∀ m : Nat,
      (List.range m).foldl
        (fun (acc : Nat × Bool) j => (acc.1 + 1, Bool.xor acc.2 (taps acc.1 && B j)))
        (0, false) =
      (m, (List.range m).foldl
        (fun par j => Bool.xor par (taps j && B j)) false) := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_append, ih]
      rfl

/-- The trailing-window AND of `CleanWorkerWordValues.markers`, with
the last bit appended, is the AND of the whole window.
Consumer: `bankRepairCloseNoRootGuard`. -/
theorem bankRepairCloseTrailingAnd (H : Nat → Bool) :
    ∀ m : Nat,
      ((List.range (m + 1)).foldl
        (fun a j => if j = 0 then a else a && H j) true && H (m + 1)) =
      (List.range (m + 1)).foldl (fun a j => a && H (j + 1)) true := by
  intro m
  induction m with
  | zero => simp [List.range_succ]
  | succ m ih =>
      rw [List.range_succ (n := m + 1), List.foldl_append, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [if_neg (by omega : m + 1 ≠ 0), ih]

/-- An OR fold that ends false had every input false.
Consumer: `bankRepairCloseNoRootGuard`. -/
theorem bankRepairCloseOrFoldFalse {β : Type} (g : β → Bool) :
    ∀ (xs : List β) (a : Bool),
      xs.foldl (fun h s => h || g s) a = false →
        a = false ∧ ∀ s ∈ xs, g s = false := by
  intro xs
  induction xs with
  | nil => intro a h; exact ⟨h, fun s hs => by cases hs⟩
  | cons x xs ih =>
      intro a h
      rw [List.foldl_cons] at h
      obtain ⟨h1, h2⟩ := ih _ h
      have ha : a = false := by
        cases a <;> simp_all
      have hx : g x = false := by
        cases hg : g x <;> simp_all
      refine ⟨ha, ?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs'
      · exact hx
      · exact h2 s hs'

/-! ## The no-root R0c guard from the published W equations -/

/-- E.G22 R0c with no sampled root: a valid full terminal ledger whose
samples obey the window geometry passes the literal R0c guard, given
the static `CleanWorkerWordValues` of the W origin at its fixed root.
Consumer: `bankRepairCloseRowsAtOfValues`. -/
theorem bankRepairCloseNoRootGuard {n : Nat}
    (ring : DirectedRing n) (hn3 : 3 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (root : Fin n)
    (origin : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (hvals : AcceptedReceipts.WordEntrance.CleanWorker.CleanWorkerWordValues
      ring root (AcceptedReceipts.wordProjectionR origin))
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (hfix : WFixedRoot ring root (AcceptedReceipts.wordProjectionR p))
    (hvis : ∀ i : Fin n, (p i).word.u = (origin i).word.u)
    (site : Fin n)
    (old : RawTok (compileAdvice (ceilLogTwo n)).t)
    (index : Fin ((compileAdvice (ceilLogTwo n)).t + 1))
    (samples : BlockA.FiniteLedger (BlockA.ReaderSample n)
      (compileAdvice (ceilLogTwo n)).t)
    (hvalid : Closure.readerFoldValid (ceilLogTwo n) n
      site (some old) index samples)
    (hterm : ¬ old.j < (compileAdvice (ceilLogTwo n)).t)
    (hno : old.h = false)
    (hwin : ∀ pos : Fin (compileAdvice (ceilLogTwo n)).t,
      pos.val < index.val →
      ∃ r : BlockA.ReaderSample n, samples.entries pos = some r ∧
        BankRepairCloseSampleFacts ring root origin site
          (index.val - 1 - pos.val) r) :
    (old.m ||
      (!(old.h ||
        (postW (p site).word
          (p (ring.rightNeighbor site)).word).eY.l) &&
        (!old.z ||
          ((p (ring.rightNeighbor site)).word.u != old.p)))) = false := by
  have ht0 := bankRepairReaderCompiledWidthPos hbank
  have hvalidCopy := hvalid
  dsimp [Closure.readerFoldValid] at hvalidCopy
  obtain ⟨_hcount, hj, reads, hreads, _hlen, ⟨last, hlast, hlastsrc⟩,
    hz, hp, _ha, hh, _hm⟩ := hvalidCopy
  have hidx : index.val = (compileAdvice (ceilLogTwo n)).t := by
    have := index.isLt
    omega
  -- the ledger as a function of position
  let dflt : BlockA.ReaderSample n :=
    { source := site, oldBit := false, oldMarker := false,
      postLeader := false }
  let F : Nat → BlockA.ReaderSample n := fun pos =>
    if hpt : pos < (compileAdvice (ceilLogTwo n)).t then
      (samples.entries ⟨pos, hpt⟩).getD dflt
    else dflt
  have hF : ∀ pos (hpt : pos < (compileAdvice (ceilLogTwo n)).t),
      samples.entries ⟨pos, hpt⟩ = some (F pos) ∧
        BankRepairCloseSampleFacts ring root origin site
          ((compileAdvice (ceilLogTwo n)).t - 1 - pos) (F pos) := by
    intro pos hpt
    obtain ⟨r, hr, hfacts⟩ := hwin ⟨pos, hpt⟩ (by omega)
    have hFr : F pos = r := by
      simp only [F, dif_pos hpt, hr, Option.getD_some]
    rw [hFr]
    rw [hidx] at hfacts
    exact ⟨hr, hfacts⟩
  have hreadsEq : reads =
      (List.range (compileAdvice (ceilLogTwo n)).t).map F := by
    have hm := bankRepairCloseMapMRange
      (fun pos => if hpt : pos < (compileAdvice (ceilLogTwo n)).t then
        samples.entries ⟨pos, hpt⟩ else none) F
      (compileAdvice (ceilLogTwo n)).t 0
      (fun pos _ h2 => by
        have hpt : pos < (compileAdvice (ceilLogTwo n)).t := by omega
        rw [dif_pos hpt]
        exact (hF pos hpt).1)
    have hl : Closure.readerSampleList (compileAdvice (ceilLogTwo n))
        samples index =
        some ((List.range (compileAdvice (ceilLogTwo n)).t).map F) := by
      unfold Closure.readerSampleList
      rw [hidx, List.range_eq_range']
      exact hm
    rw [hl] at hreads
    exact (Option.some.inj hreads).symm
  have hmemF : ∀ r ∈ reads, ∃ pos, pos < (compileAdvice (ceilLogTwo n)).t ∧
      r = F pos := by
    intro r hr
    rw [hreadsEq] at hr
    obtain ⟨pos, hpos, hrp⟩ := List.mem_map.mp hr
    exact ⟨pos, List.mem_range.mp hpos, hrp.symm⟩
  have hfree : ∀ r ∈ reads, r.postLeader = false := by
    have hroot : Closure.readerSampleRootTouch reads = false := by
      rw [← hh]; exact hno
    unfold Closure.readerSampleRootTouch at hroot
    exact (bankRepairCloseOrFoldFalse (fun s => s.postLeader) reads false
      hroot).2
  obtain ⟨k, hk, hsite⟩ := bankRepairCloseOffset ring root site
  -- the window does not reach the root, so it ends at offset k ≥ t
  have hkt : (compileAdvice (ceilLogTwo n)).t ≤ k := by
    by_cases hkt : (compileAdvice (ceilLogTwo n)).t ≤ k
    · exact hkt
    · exfalso
      have hpt : (compileAdvice (ceilLogTwo n)).t - 1 - k <
          (compileAdvice (ceilLogTwo n)).t := by omega
      obtain ⟨_, hshift, _, _, hrt⟩ := hF _ hpt
      have hd : (compileAdvice (ceilLogTwo n)).t - 1 -
          ((compileAdvice (ceilLogTwo n)).t - 1 - k) = k := by omega
      rw [hd, ← hsite] at hshift
      have hsr := bankRepairCloseShiftCancel ring _ _ k hshift
      have hpl := hrt hsr
      have hmem : F ((compileAdvice (ceilLogTwo n)).t - 1 - k) ∈ reads := by
        rw [hreadsEq]
        exact List.mem_map.mpr ⟨_, List.mem_range.mpr hpt, rfl⟩
      rw [hfree _ hmem] at hpl
      cases hpl
  let G : Nat → Bool := fun j =>
    AcceptedReceipts.WordEntrance.CleanWorker.cwBit ring root (AcceptedReceipts.wordProjectionR origin)
      (k - (compileAdvice (ceilLogTwo n)).t + 1 + j)
  have hsrcpos : ∀ pos (hpt : pos < (compileAdvice (ceilLogTwo n)).t),
      (F pos).source = PPL.shiftRight ring root
        (k - (compileAdvice (ceilLogTwo n)).t + 1 + pos) := by
    intro pos hpt
    obtain ⟨_, hshift, _, _, _⟩ := hF pos hpt
    apply bankRepairCloseShiftCancel ring _ _
      ((compileAdvice (ceilLogTwo n)).t - 1 - pos)
    rw [hshift, bankRepairCloseShiftAdd, ← hsite]
    congr 1
    omega
  have hbits : ∀ j, j < (compileAdvice (ceilLogTwo n)).t →
      (F j).oldBit = G j := by
    intro j hjt
    obtain ⟨_, _, hb, _, _⟩ := hF j hjt
    rw [hb, hsrcpos j hjt]
    rfl
  -- the three folds in window form
  have hor : Closure.readerSampleOr reads =
      (List.range (compileAdvice (ceilLogTwo n)).t).foldl
        (fun z j => z || G j) false := by
    unfold Closure.readerSampleOr
    rw [hreadsEq, List.foldl_map]
    exact bankRepairCloseFoldRangeCongr _ _ false _
      (fun a j hjt => by rw [hbits j hjt])
  have hand : Closure.readerSampleAnd reads =
      (List.range (compileAdvice (ceilLogTwo n)).t).foldl
        (fun a j => a && G j) true := by
    unfold Closure.readerSampleAnd
    rw [hreadsEq, List.foldl_map]
    exact bankRepairCloseFoldRangeCongr _ _ true _
      (fun a j hjt => by rw [hbits j hjt])
  have hpar : Closure.readerSampleParity (compileAdvice (ceilLogTwo n)) reads =
      (List.range (compileAdvice (ceilLogTwo n)).t).foldl
        (fun par j => Bool.xor par
          ((compileAdvice (ceilLogTwo n)).taps j && G j)) false := by
    unfold Closure.readerSampleParity
    rw [hreadsEq, List.foldl_map]
    have hc := bankRepairCloseParityCounter
      (compileAdvice (ceilLogTwo n)).taps (fun j => (F j).oldBit)
      (compileAdvice (ceilLogTwo n)).t
    rw [hc]
    exact bankRepairCloseFoldRangeCongr _ _ false _
      (fun a j hjt => by rw [hbits j hjt])
  -- marker: the last sample's marker is the window AND
  have hlastMem : last ∈ reads := by
    cases hr : reads.reverse with
    | nil =>
        rw [hr] at hlast
        cases hlast
    | cons a l =>
        rw [hr] at hlast
        have hal : a = last := Option.some.inj hlast
        have : last ∈ reads.reverse := by
          rw [hr, ← hal]
          exact List.mem_cons_self
        exact List.mem_reverse.mp this
  have hlastMarker : last.oldMarker =
      AcceptedReceipts.WordEntrance.CleanWorker.cwMarker ring root (AcceptedReceipts.wordProjectionR origin) k := by
    obtain ⟨pos, hpt, hrp⟩ := hmemF last hlastMem
    obtain ⟨_, _, _, hmk, _⟩ := hF pos hpt
    rw [hrp, hmk]
    rw [hrp] at hlastsrc
    rw [hlastsrc, ← hsite]
    rfl
  have hmarkerWord :
      AcceptedReceipts.WordEntrance.CleanWorker.cwMarker ring root (AcceptedReceipts.wordProjectionR origin) k =
        Closure.readerSampleAnd reads := by
    rw [hvals.markers ⟨k, hk⟩ hkt, hand]
    unfold AcceptedReceipts.WordEntrance.CleanWorker.cwSumTrailing
    obtain ⟨m, hm⟩ : ∃ m, (compileAdvice (ceilLogTwo n)).t = m + 1 :=
      ⟨(compileAdvice (ceilLogTwo n)).t - 1, by omega⟩
    have htr := bankRepairCloseTrailingAnd
      (fun j => AcceptedReceipts.WordEntrance.CleanWorker.cwBit ring root (AcceptedReceipts.wordProjectionR origin)
        (k - (compileAdvice (ceilLogTwo n)).t + j)) m
    have hk' : AcceptedReceipts.WordEntrance.CleanWorker.cwBit ring root (AcceptedReceipts.wordProjectionR origin) k =
        AcceptedReceipts.WordEntrance.CleanWorker.cwBit ring root (AcceptedReceipts.wordProjectionR origin)
          (k - (compileAdvice (ceilLogTwo n)).t + (m + 1)) := by
      congr 1
      omega
    simp only [AcceptedReceipts.WordEntrance.CleanWorker.cwSourceBit]
    rw [← hm] at htr
    rw [hk', ← hm, htr]
    exact bankRepairCloseFoldRangeCongr _ _ true _
      (fun a j _ => by
        show (a && AcceptedReceipts.WordEntrance.CleanWorker.cwBit ring root (AcceptedReceipts.wordProjectionR origin)
          (k - (compileAdvice (ceilLogTwo n)).t + (j + 1))) = (a && G j)
        congr 2
        omega)
  have hmarker : ∀ reads' : List (BlockA.ReaderSample n),
      Closure.readerSampleList (compileAdvice (ceilLogTwo n)) samples index =
        some reads' →
      ∀ last' : BlockA.ReaderSample n,
        reads'.reverse.head? = some last' →
          last'.oldMarker = Closure.readerSampleAnd reads' := by
    intro reads' hr' last' hl'
    rw [hreads] at hr'
    have hrr : reads' = reads := (Option.some.inj hr').symm
    subst hrr
    rw [hl'] at hlast
    have hll : last' = last := Option.some.inj hlast
    subst hll
    rw [hlastMarker, hmarkerWord]
  have hm := bankRepairReaderE22MarkerOfPublishedSamples
    site old index samples hvalid hmarker
  cases hg : (postW (p site).word (p (ring.rightNeighbor site)).word).eY.l with
  | true => simp [hm]
  | false =>
      -- the next responder is not the root, so offset k+1 < n
      have hnext : ring.rightNeighbor site =
          PPL.shiftRight ring root (k + 1) := by
        rw [WordPhase.wordPhaseShiftSucc, hsite]
      have hnr : ring.rightNeighbor site ≠ root :=
        bankRepairDigitEYFalse ring root
          (AcceptedReceipts.wordProjectionR p) site
          (clockNeighborDifferent ring (by omega) site)
          (bankRepairDigitWFixedRootPhiW hn3 ring root _ site hfix) hg
      have hk1 : k + 1 < n := by
        by_cases hk1 : k + 1 < n
        · exact hk1
        · exfalso
          have : k + 1 = n := by omega
          rw [this, bankRepairCloseShiftFull] at hnext
          exact hnr hnext
      have hwin' : ∀ j : Nat,
          AcceptedReceipts.WordEntrance.CleanWorker.cwSourceBit ring root (AcceptedReceipts.wordProjectionR origin)
            (k + 1) j = G j := by
        intro j
        show AcceptedReceipts.WordEntrance.CleanWorker.cwBit ring root (AcceptedReceipts.wordProjectionR origin)
            (k + 1 - (compileAdvice (ceilLogTwo n)).t + j) = G j
        show _ = AcceptedReceipts.WordEntrance.CleanWorker.cwBit ring root (AcceptedReceipts.wordProjectionR origin)
            (k - (compileAdvice (ceilLogTwo n)).t + 1 + j)
        congr 1
        omega
      have hnonzero : ∀ reads' : List (BlockA.ReaderSample n),
          Closure.readerSampleList (compileAdvice (ceilLogTwo n))
            samples index = some reads' →
          Closure.readerSampleOr reads' = true := by
        intro reads' hr'
        rw [hreads] at hr'
        have hrr : reads' = reads := (Option.some.inj hr').symm
        subst hrr
        rw [hor]
        have hlater := hvals.laterNonzero ⟨k + 1, hk1⟩ (by
          show (compileAdvice (ceilLogTwo n)).t < k + 1
          omega)
        unfold AcceptedReceipts.WordEntrance.CleanWorker.cwSumOr at hlater
        have hcg : (List.range (compileAdvice (ceilLogTwo n)).t).foldl
            (fun z j => z || G j) false =
            (List.range (compileAdvice (ceilLogTwo n)).t).foldl
            (fun z j => z ||
              AcceptedReceipts.WordEntrance.CleanWorker.cwSourceBit ring root (AcceptedReceipts.wordProjectionR origin)
                (k + 1) j) false :=
          bankRepairCloseFoldRangeCongr _ _ false _
            (fun a j _ => by rw [hwin' j])
        rw [hcg]
        exact hlater
      have hrecurrence : ∀ reads' : List (BlockA.ReaderSample n),
          Closure.readerSampleList (compileAdvice (ceilLogTwo n))
            samples index = some reads' →
          (p (ring.rightNeighbor site)).word.u =
            Closure.readerSampleParity (compileAdvice (ceilLogTwo n)) reads' := by
        intro reads' hr'
        rw [hreads] at hr'
        have hrr : reads' = reads := (Option.some.inj hr').symm
        subst hrr
        rw [hpar, hvis]
        have hrec := hvals.recurrence ⟨k + 1, hk1⟩ (by
          show (compileAdvice (ceilLogTwo n)).t < k + 1
          omega)
        unfold AcceptedReceipts.WordEntrance.CleanWorker.cwSumParity at hrec
        have hcg : (List.range (compileAdvice (ceilLogTwo n)).t).foldl
            (fun par j => Bool.xor par
              ((compileAdvice (ceilLogTwo n)).taps j && G j)) false =
            (List.range (compileAdvice (ceilLogTwo n)).t).foldl
            (fun par j => Bool.xor par
              ((compileAdvice (ceilLogTwo n)).taps j &&
                AcceptedReceipts.WordEntrance.CleanWorker.cwSourceBit ring root (AcceptedReceipts.wordProjectionR origin)
                  (k + 1) j)) false :=
          bankRepairCloseFoldRangeCongr _ _ false _
            (fun a j _ => by rw [hwin' j])
        rw [hcg, hnext]
        exact hrec
      have hfinal := bankRepairReaderE22GuardOfPublishedSamples ring p site old
        index samples hvalid hmarker hnonzero hrecurrence
      rw [hg] at hfinal
      exact hfinal

/-! ## E22 row preservation at one W start, and the FoldSound assembly -/

/-- `BankRepairReaderE22RowPreservation` at one fixed W start.
Consumer: `bankRepairCloseFoldAt`, `bankRepairReaderE22RowPreservationOfWordValues`. -/
def BankRepairCloseRowsAt {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank) : Prop :=
  ∀ (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))))
    (word : List (Fin n))
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (h : BlockA.ReaderControl n (compileAdvice (ceilLogTwo n)))
    (e : Fin n),
    BlockA.initializesReader
      (AcceptedReceipts.AcceptedWord ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      (piR start.val.1) initial →
    BlockA.Run ring (phiR ring) (BlockA.readerControlNext ring)
      (piR start.val.1) initial word p (.live p h) →
    BankRepairReaderE22Invariant ring hbank p h →
    BankRepairReaderE22Invariant ring hbank
      (phiR ring p e)
      (BlockA.readerControlNext ring h p e (phiR ring p e))

/-- E22 row preservation at a W start whose words have a fixed root
and the static clean-worker values there: the R0c guard is closed by
root touch (installed) or by the window geometry plus the published
marker/OR/recurrence equations (`bankRepairCloseNoRootGuard`).
Consumer: `bankRepairReaderE22RowPreservationOfWordValues`,
`bankRepairReaderFoldSoundOnDrainOfWordValues`. -/
theorem bankRepairCloseRowsAtOfValues {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank) (root : Fin n)
    (hfix : WFixedRoot ring root (piW start.val.1))
    (hvals : AcceptedReceipts.WordEntrance.CleanWorker.CleanWorkerWordValues
      ring root (piW start.val.1)) :
    BankRepairCloseRowsAt ring hbank start := by
  have hn3 : 3 ≤ n := by omega
  intro initial word p h e hinit hrun hI
  have hword :
      AcceptedReceipts.AcceptedWord ring
        (BlockA.wordT ring) (BlockA.wordValidated ring)
        (fun i => ((phiR ring p e) i).word) := by
    change AcceptedReceipts.AcceptedWord ring
      (BlockA.wordT ring) (BlockA.wordValidated ring)
      (AcceptedReceipts.wordProjectionR (phiR ring p e))
    rw [AcceptedReceipts.wordProjectionR_phiR]
    exact AcceptedReceipts.accepted_word_phi_step
      ring (AcceptedReceipts.wordProjectionR p) e hI.1
  have hghost := Closure.readerGhostWellFormedStep
    (bankRepairReaderE22BankSize hbank)
    (bankRepairReaderCompiledWidthPos hbank)
    ring p h e hI.2.1
  have hnumeric := bankRepairReaderE22FreshStep
    ring hbank p h e hI.2.1 hI.2.2
  refine ⟨hword, hghost, ⟨?_, ?_⟩⟩
  · intro i name index samples htag
    exact hnumeric i name index samples htag
  · intro site old name index samples hx hy hterminal htag
    have hguard :
        (old.m ||
          (!(old.h ||
            (postW ((phiR ring p e) site).word
              ((phiR ring p e) (ring.rightNeighbor site)).word).eY.l) &&
            (!old.z ||
              (((phiR ring p e) (ring.rightNeighbor site)).word.u !=
                old.p)))) = false := by
      by_cases htouch : old.h = true
      · exact bankRepairReaderE22NextFreshRootTouchSafe
          ring hbank p h e site old name index samples hI hx htag htouch
      · have hno : old.h = false := by
          cases hh : old.h with
          | false => rfl
          | true => exact absurd hh htouch
        have hrun' : BlockA.Run ring (phiR ring)
            (BlockA.readerControlNext ring)
            (piR start.val.1) initial (word ++ [e])
            (phiR ring p e)
            (.live (phiR ring p e)
              (BlockA.readerControlNext ring h p e (phiR ring p e))) := by
          have hs := BlockA.Run.next hrun e
          simpa [BlockA.update] using hs
        have hfix0 : WFixedRoot ring root
            (AcceptedReceipts.wordProjectionR (piR start.val.1)) := hfix
        obtain ⟨h', heq, hwin⟩ := bankRepairCloseWindowAlongRun ring hn hbank
          root (piR start.val.1) initial hinit hfix0 (word ++ [e])
          (phiR ring p e) _ hrun'
        have hh' : BlockA.readerControlNext ring h p e (phiR ring p e) = h' := by
          cases heq
          rfl
        rw [hh'] at htag
        have hfresh := hnumeric site name index samples (by rw [hh']; exact htag)
        have hvalid : Closure.readerFoldValid (ceilLogTwo n) n
            site (some old) index samples := by
          have hv := hfresh.2
          rw [hx] at hv
          exact hv
        have hfix' := bankRepairCloseFixedRootAlongRun ring hn3 root
          (piR start.val.1) initial hfix0 (word ++ [e]) (phiR ring p e) _ hrun'
        have hvis : ∀ i : Fin n,
            ((phiR ring p e) i).word.u = ((piR start.val.1) i).word.u := by
          intro i
          have hv := (bankRepairReaderE22AdmittedVisibleFixed ring
            (piR start.val.1) initial hinit (word ++ [e]) (phiR ring p e) _
            hrun').2 i
          simpa [AcceptedReceipts.wordProjectionR,
            AcceptedReceipts.wordVisible] using congrArg Prod.fst hv
        exact bankRepairCloseNoRootGuard ring hn3 hbank root (piR start.val.1)
          hvals (phiR ring p e) hfix' hvis site old index samples hvalid
          hterminal hno (hwin site name index samples htag)
    simpa [rawR, rawD1Step, ProjR.lift, ProjW.lift,
      hx, hy, hterminal] using hguard

/-- A W-accepted state's native leader is a fixed W root of its words.
Consumer: `bankRepairReaderE22RowPreservationOfWordValues`. -/
theorem bankRepairCloseFixedRootOfAccepted {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (hW : BankRepairWAccepted ring hbank start) (root : Fin n)
    (hroot : (nativeProjection start.val.1 root).l = true) :
    WFixedRoot ring root (piW start.val.1) := by
  obtain ⟨⟨⟨⟨leader, _, huniq⟩, hprot, _⟩, _⟩, _⟩ := hW
  have hr : root = leader := huniq root hroot
  refine ⟨hroot, ?_, hprot⟩
  intro i hi
  rw [hr]
  exact huniq i hi

/-- The static clean-worker word values at the native leader of a
W-accepted start: the input another worker produces at the accepted W
endpoint (lem:e-word).  Consumer:
`bankRepairReaderE22RowPreservationOfWordValues`,
`bankRepairReaderFoldSoundOnDrainOfWordValues`. -/
def BankRepairCloseWordValuesAt {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank) : Prop :=
  ∃ root : Fin n, (nativeProjection start.val.1 root).l = true ∧
    AcceptedReceipts.WordEntrance.CleanWorker.CleanWorkerWordValues
      ring root (piW start.val.1)

/-- E.G22 row preservation (the installed open Prop), from the static
clean-worker word values at every W-accepted start.
Consumer: `bankRepairReaderFoldSoundOfWordValues`. -/
theorem bankRepairReaderE22RowPreservationOfWordValues {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hvalues : ∀ start : BankReferenceState ring hbank,
      BankRepairWAccepted ring hbank start →
      BankRepairCloseWordValuesAt ring hbank start) :
    BankRepairReaderE22RowPreservation ring hbank := by
  intro start initial word p h e hW hinit hrun hI
  obtain ⟨root, hroot, hvals⟩ := hvalues start hW
  exact bankRepairCloseRowsAtOfValues ring hn hbank start root
    (bankRepairCloseFixedRootOfAccepted ring hbank start hW root hroot)
    hvals initial word p h e hinit hrun hI

/-- The installed `BankRepairReaderFoldSound`, from the static
clean-worker word values at every W-accepted start.
Consumer: `bankRepairReaderStageOfRetirementAndFold` /
`bankRepairReaderFoldSoundOnDrainOfFoldSound`. -/
theorem bankRepairReaderFoldSoundOfWordValues {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hvalues : ∀ start : BankReferenceState ring hbank,
      BankRepairWAccepted ring hbank start →
      BankRepairCloseWordValuesAt ring hbank start) :
    BankRepairReaderFoldSound ring hbank :=
  bankRepairReaderFoldSoundOfE22Rows ring hbank
    (bankRepairReaderE22RowPreservationOfWordValues ring hn hbank hvalues)

/-- Per-start copy of `bankRepairReaderE22RunInvariant`.
Consumer: `bankRepairCloseFoldAt`. -/
theorem bankRepairCloseRunInvariantAt {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (hrows : BankRepairCloseRowsAt ring hbank start)
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))))
    (hinit : BlockA.initializesReader
      (AcceptedReceipts.AcceptedWord ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      (piR start.val.1) initial)
    (word : List (Fin n))
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (γ : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))))
    (hrun : BlockA.Run ring (phiR ring) (BlockA.readerControlNext ring)
      (piR start.val.1) initial word p γ) :
    ∃ control : BlockA.ReaderControl n (compileAdvice (ceilLogTwo n)),
      γ = .live p control ∧
      BankRepairReaderE22Invariant ring hbank p control := by
  induction hrun with
  | empty =>
      exact bankRepairReaderE22InvariantOrigin ring hbank
        (piR start.val.1) initial hinit
  | @next w q γ' h e ih =>
      obtain ⟨control, hγ, hI⟩ := ih
      have hprefix : BlockA.Run ring (phiR ring)
          (BlockA.readerControlNext ring)
          (piR start.val.1) initial w q (.live q control) := by
        simpa [hγ] using h
      have hstep := hrows initial w q control e hinit hprefix hI
      refine ⟨_, ?_, hstep⟩
      rw [hγ]
      classical
      simp [BlockA.update]

/-- Per-start copy of `bankRepairReaderE22SafeFromRows`.
Consumer: `bankRepairCloseFoldAt`. -/
theorem bankRepairCloseSafeAt {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start : BankReferenceState ring hbank)
    (hrows : BankRepairCloseRowsAt ring hbank start)
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))))
    (hinit : BlockA.initializesReader
      (AcceptedReceipts.AcceptedWord ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      (piR start.val.1) initial)
    (word : List (Fin n))
    (p : Fin n → ProjR (compileAdvice (ceilLogTwo n)))
    (control : BlockA.ReaderControl n (compileAdvice (ceilLogTwo n)))
    (hrun : BlockA.Run ring (phiR ring) (BlockA.readerControlNext ring)
      (piR start.val.1) initial word p (.live p control))
    (hI : BankRepairReaderE22Invariant ring hbank p control)
    (hdone : control.phase = .done) :
    AcceptedReceipts.QReader ring p := by
  apply AcceptedReceipts.safe_inclusion_image
    (phiR ring) (AcceptedReceipts.badReader ring)
    (BankRepairReaderE22PostDoneWitness ring hbank start initial)
  · intro cursor state hc e
    rcases cursor with ⟨pfx, h⟩
    obtain ⟨hprefix, hInv, hphase⟩ := hc
    have hno := bankRepairReaderE22NoRejectAtDone
      ring hbank state h hInv hphase e
    have hstep := hrows initial pfx state h e hinit hprefix hInv
    have hdoneNext :=
      Closure.readerDoneSticky ring h state e hphase
    have hrunNext : BlockA.Run ring (phiR ring)
        (BlockA.readerControlNext ring)
        (piR start.val.1) initial (pfx ++ [e])
        (phiR ring state e)
        (.live (phiR ring state e)
          (BlockA.readerControlNext ring h state e
            (phiR ring state e))) := by
      have hs := BlockA.Run.next hprefix e
      simpa [BlockA.update] using hs
    exact ⟨hno, ⟨(pfx ++ [e],
      BlockA.readerControlNext ring h state e
        (phiR ring state e)), hrunNext, hstep, hdoneNext⟩⟩
  · exact ⟨(word, control), hrun, hI, hdone⟩

/-- Per-start copy of `bankRepairReaderFoldSoundOfE22Rows`: E.G22
acceptance at a done cut of a run from one W start.
Consumer: `bankRepairReaderFoldSoundOnDrainOfWordValues`. -/
theorem bankRepairCloseFoldAt {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (start finish : BankReferenceState ring hbank)
    (hrows : BankRepairCloseRowsAt ring hbank start)
    (word : List (Fin n))
    (initial : BlockA.Decoration
      (Fin n → ProjR (compileAdvice (ceilLogTwo n)))
      (BlockA.ReaderControl n (compileAdvice (ceilLogTwo n))))
    (control : BlockA.ReaderControl n (compileAdvice (ceilLogTwo n)))
    (hinit : BlockA.initializesReader
      (AcceptedReceipts.AcceptedWord ring
        (BlockA.wordT ring) (BlockA.wordValidated ring))
      (piR start.val.1) initial)
    (hrun : BlockA.Run ring (phiR ring) (BlockA.readerControlNext ring)
      (piR start.val.1) initial word
      (piR finish.val.1) (.live (piR finish.val.1) control))
    (hdone : control.phase = .done)
    (hnames : ∀ name : Fin n, control.inheritedNames name = false) :
    BlockA.acceptsReader
      (Closure.readerFoldValid (ceilLogTwo n) n)
      (AcceptedReceipts.QReader ring)
      (piR finish.val.1)
      (.live (piR finish.val.1) control) := by
  obtain ⟨observed, hEq, hInv⟩ :=
    bankRepairCloseRunInvariantAt ring hbank start hrows
      initial hinit word (piR finish.val.1)
      (.live (piR finish.val.1) control) hrun
  have hControl : control = observed := by
    cases hEq
    rfl
  subst observed
  have hsafe : AcceptedReceipts.QReader ring (piR finish.val.1) :=
    bankRepairCloseSafeAt ring hbank start hrows initial hinit word
      (piR finish.val.1) control hrun hInv hdone
  dsimp [BlockA.acceptsReader]
  refine ⟨rfl, hdone, hnames, ?_, hsafe⟩
  intro i htok
  obtain ⟨name, index, samples, htag⟩ :=
    bankRepairReaderDoneTagFresh (piR finish.val.1)
      control hInv.2.1 hdone i htok
  have hn := hInv.2.2.1 i name index samples htag
  exact ⟨name, index, samples, htag, hn.1, hn.2⟩

/-- Grant-free fold soundness from the static clean-worker word values
at every grant-free W-accepted start.  With
`bankRepairReaderStageOnDrainOfFold` this closes the R stage of
`bankFinishReferenceFinishOfStagesOnDrain` once those values are
produced.  Consumer: `bankFinishReferenceFinishOfStagesOnDrain`. -/
theorem bankRepairReaderFoldSoundOnDrainOfWordValues {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hvalues : ∀ start : BankReferenceState ring hbank,
      BankRepairWAcceptedOnDrain ring hbank start →
      BankRepairCloseWordValuesAt ring hbank start) :
    BankRepairReaderFoldSoundOnDrain ring hbank := by
  intro start finish word initial control hS _hactual hinit hrun hdone hnames
  obtain ⟨root, hroot, hvals⟩ := hvalues start hS
  exact bankRepairCloseFoldAt ring hbank start finish
    (bankRepairCloseRowsAtOfValues ring hn hbank start root
      (bankRepairCloseFixedRootOfAccepted ring hbank start hS.2 root hroot)
      hvals)
    word initial control hinit hrun hdone hnames

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.bankRepairReaderStageOnDrainOfFold
#print axioms L3.RenewalReferenceClock.bankFinishMaskedRepairBoundOfStagesOnDrain
#print axioms L3.RenewalReferenceClock.bankFinishReferenceFinishOfStagesOnDrain
#print axioms L3.RenewalReferenceClock.bankRepairCloseWindowAlongRun
#print axioms L3.RenewalReferenceClock.bankRepairCloseNoRootGuard
#print axioms L3.RenewalReferenceClock.bankRepairCloseRowsAtOfValues
#print axioms L3.RenewalReferenceClock.bankRepairReaderE22RowPreservationOfWordValues
#print axioms L3.RenewalReferenceClock.bankRepairReaderFoldSoundOfWordValues
#print axioms L3.RenewalReferenceClock.bankRepairReaderFoldSoundOnDrainOfWordValues
