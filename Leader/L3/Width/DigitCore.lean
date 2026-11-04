import Leader.L3.Bank.RepairDigitClean

/-!
# The R10c digit half from a causal core, on any successor

`bankDigitHalfOfCausalCore` (BankRepairDigitClean) composes four charged
first-hit stages, a forward-closed pre-drain and a nominated-edge dirty rank
into the 201 + 2 half-unit digit stage.  None of that composition uses the
BANK band: the stages are `BankRepairDigitChargedStage` on an arbitrary
successor, the composition is the strong-Markov reserve, the dirty drain is
`Prob.costNumerator_le_of_nominated_edge`.  The band enters only through
the numeric fit `bankRepairDigitMicroChargesFit` (four micro-charges
≤ 201 n², from 2ν_s < n, which needs s = ψ ≥ 7) and through the BANK
reference type of the cuts.

Here the composition is stated once for any state type `S`, successor
`next`, any four charges and any budget `H` with the charges ≤ H n²; the
result is the half-stage at H + 2.  BANK instantiates it at H = 201
(`widthDigitHalfOfBankCore`), SMALL at H = smallRepairDigitHalf n - 2
(SmallDigitClean).
-/

namespace L3.RenewalReferenceClock

open L3.HeadlineRenewal
open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-- Copy of the private `bankRepairDigitHalfReserve` (strong-Markov reserve on any
successor).  Consumer: `widthDigitChargedCompose`. -/
theorem widthDigitHalfReserve {S : Type} {n : Nat}
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
                    2 * costNumerator next
                      (fun z => A z ∨ P z) (next y e) T +
                        n ^ T * allowance)).sum :=
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

/-- Reuse the existing half-unit strong-Markov reserve, but
with exact Nat charges rather than k*n^2. No independence
of stage durations or scheduler samples is used.  Copy of the private
`bankRepairDigitChargedCompose`.  Consumer: `widthDigitPreDrainOfCharges`. -/
theorem widthDigitChargedCompose
    {S : Type} {n : Nat}
    (next : S → Fin n → S)
    (A B Target : S → Prop) (a b : Nat)
    (hfirst : BankRepairDigitChargedStage next A B a)
    (hsecond : BankRepairDigitChargedStage next B Target b) :
    BankRepairDigitChargedStage next A Target (a + b) := by
  intro x hx T
  have hfirstUnion :
      2 * costNumerator next (fun z => B z ∨ Target z) x T ≤
        n ^ T * a := by
    have hmono := L3.Prob.costNumerator_target_mono next B
      (fun z => B z ∨ Target z)
      (fun z hz => Or.inl hz) x T
    exact Nat.le_trans (Nat.mul_le_mul_left 2 hmono)
      (hfirst x hx T)
  have hreserve := widthDigitHalfReserve next B Target b
    (fun y hy U => hsecond y hy U) x T
  calc
    2 * costNumerator next Target x T ≤
        2 * costNumerator next (fun z => B z ∨ Target z) x T +
          n ^ T * b := hreserve
    _ ≤ n ^ T * a + n ^ T * b :=
      Nat.add_le_add_right hfirstUnion _
    _ = n ^ T * (a + b) := by rw [Nat.mul_add]

/-- A forward-closed pre-drain class cannot be escaped along
any scheduler word.  Hence adjoining its complement to the
terminal does not change first-hit cost at entry.  Copy of the private `bankDigitCostOnForwardClosed`.  Consumer:
`widthDigitDirtyHalfOfRank`. -/
theorem widthDigitCostOnForwardClosed {S : Type} {n : Nat}
    (next : S → Fin n → S) (A terminal : S → Prop)
    (hclosed : ∀ z, A z → ∀ e : Fin n, A (next z e)) :
    ∀ z, A z → ∀ T,
      costNumerator next terminal z T =
        costNumerator next (fun y => ¬ A y ∨ terminal y) z T := by
  classical
  intro z hz T
  induction T generalizing z with
  | zero =>
      simp only [costNumerator_zero]
  | succ T ih =>
      by_cases ht : terminal z
      · rw [costNumerator_terminal next terminal z ht (T + 1),
          costNumerator_terminal next (fun y => ¬ A y ∨ terminal y)
            z (Or.inr ht) (T + 1)]
      · have hu : ¬ (¬ A z ∨ terminal z) := by
          intro h
          rcases h with hna | ht'
          · exact hna hz
          · exact ht ht'
        rw [costNumerator_succ next terminal z ht T,
          costNumerator_succ next (fun y => ¬ A y ∨ terminal y)
            z hu T]
        have hsum := ofFn_sum_eq
          (fun e : Fin n => costNumerator next terminal (next z e) T)
          (fun e : Fin n =>
            costNumerator next (fun y => ¬ A y ∨ terminal y)
              (next z e) T)
          (fun e => ih (next z e) (hclosed z hz e))
        rw [hsum]


/-- The three intermediate cuts of the R10c digit wave, on any state
type (the analogue of `BankRepairDigitPreDrainCuts`).  Consumer:
`WidthDigitCausalCore`. -/
structure WidthDigitCuts (S : Type) where
  boundaryRetired : S → Prop
  firstBlockZero : S → Prop
  successorValuesStable : S → Prop

/-- The R10c causal core on any successor: four charged first-hit stages
(boundary, first zero, value wave, comparison) with explicit charges, a
forward-closed pre-drain, and a nominated-edge dirty rank to the terminal.
Consumer: `widthDigitHalfOfCausalCore`. -/
def WidthDigitCausalCore {S : Type} {n : Nat}
    (next : S → Fin n → S)
    (entrance preDrain terminal : S → Prop)
    (cuts : WidthDigitCuts S)
    (boundaryCharge zeroCharge waveCharge comparisonCharge : Nat) : Prop :=
  BankRepairDigitChargedStage next entrance cuts.boundaryRetired boundaryCharge ∧
  BankRepairDigitChargedStage next cuts.boundaryRetired cuts.firstBlockZero
    zeroCharge ∧
  BankRepairDigitChargedStage next cuts.firstBlockZero
    cuts.successorValuesStable waveCharge ∧
  BankRepairDigitChargedStage next cuts.successorValuesStable preDrain
    comparisonCharge ∧
  (∀ z, preDrain z → ∀ e : Fin n, preDrain (next z e)) ∧
  ∃ (rank : S → Nat) (chosen : S → Fin n),
    (∀ z, preDrain z → rank z ≤ n) ∧
    (∀ z, preDrain z → rank z = 0 → terminal z) ∧
    (∀ z, preDrain z → ¬ terminal z →
      rank (next z (chosen z)) + 1 ≤ rank z) ∧
    (∀ z, preDrain z → ¬ terminal z →
      ∀ e : Fin n, rank (next z e) ≤ rank z)

/-- Four charged stages whose charges fit in H n² give the pre-drain
half-stage H.  Consumer: `widthDigitHalfOfCausalCore`. -/
theorem widthDigitPreDrainOfCharges {S : Type} {n : Nat}
    (next : S → Fin n → S) (entrance preDrain : S → Prop)
    (cuts : WidthDigitCuts S)
    (cb cz cw cc H : Nat)
    (hfit : cb + cz + cw + cc ≤ H * n ^ 2)
    (hboundary : BankRepairDigitChargedStage next entrance cuts.boundaryRetired cb)
    (hzero : BankRepairDigitChargedStage next cuts.boundaryRetired
      cuts.firstBlockZero cz)
    (hwave : BankRepairDigitChargedStage next cuts.firstBlockZero
      cuts.successorValuesStable cw)
    (hpair : BankRepairDigitChargedStage next cuts.successorValuesStable
      preDrain cc) :
    BankRepairHalfStage next entrance preDrain H := by
  have h1 := widthDigitChargedCompose next entrance cuts.boundaryRetired
    cuts.firstBlockZero cb cz hboundary hzero
  have h2 := widthDigitChargedCompose next entrance cuts.firstBlockZero
    cuts.successorValuesStable (cb + cz) cw h1 hwave
  have h3 := widthDigitChargedCompose next entrance cuts.successorValuesStable
    preDrain (cb + cz + cw) cc h2 hpair
  intro z hz T
  exact Nat.le_trans (h3 z hz T) (Nat.mul_le_mul_left (n ^ T) hfit)

/-- The two-half-unit dirty drain on any successor, from a forward-closed
pre-drain and a nominated-edge rank bounded by n (the argument of
`bankDigitDirtyHalfOfCausalRank`).  Consumer: `widthDigitHalfOfCausalCore`. -/
theorem widthDigitDirtyHalfOfRank {S : Type} {n : Nat}
    (next : S → Fin n → S) (preDrain terminal : S → Prop)
    (hclosed : ∀ z, preDrain z → ∀ e : Fin n, preDrain (next z e))
    (rank : S → Nat) (chosen : S → Fin n)
    (hcap : ∀ z, preDrain z → rank z ≤ n)
    (hdrop : ∀ z, preDrain z → ¬ terminal z →
      rank (next z (chosen z)) + 1 ≤ rank z)
    (hnoninc : ∀ z, preDrain z → ¬ terminal z →
      ∀ e : Fin n, rank (next z e) ≤ rank z) :
    BankRepairHalfStage next preDrain terminal 2 := by
  classical
  have hglobal :
      ∀ z T,
        costNumerator next (fun y => ¬ preDrain y ∨ terminal y) z T ≤
          n ^ T * (n * (if preDrain z then rank z else 0)) :=
    Prob.costNumerator_le_of_nominated_edge next
      (fun y => ¬ preDrain y ∨ terminal y)
      (fun y => if preDrain y then rank y else 0)
      chosen
      (fun y hnot => by
        have hy : preDrain y := by
          by_cases hp : preDrain y
          · exact hp
          · exact False.elim (hnot (Or.inl hp))
        have hnotTerminal : ¬ terminal y := fun ht => hnot (Or.inr ht)
        have hnext := hclosed y hy (chosen y)
        simpa only [if_pos hy, if_pos hnext] using hdrop y hy hnotTerminal)
      (fun y hnot e => by
        have hy : preDrain y := by
          by_cases hp : preDrain y
          · exact hp
          · exact False.elim (hnot (Or.inl hp))
        have hnotTerminal : ¬ terminal y := fun ht => hnot (Or.inr ht)
        have hnext := hclosed y hy e
        simpa only [if_pos hy, if_pos hnext] using hnoninc y hy hnotTerminal e)
  intro z hz T
  have heq := widthDigitCostOnForwardClosed next preDrain terminal
    (fun y hy e => hclosed y hy e) z hz T
  have hle := hglobal z T
  rw [← heq] at hle
  simp only [if_pos hz] at hle
  have hcapz : n * rank z ≤ n * n := Nat.mul_le_mul_left n (hcap z hz)
  calc
    2 * costNumerator next terminal z T ≤ 2 * (n ^ T * (n * rank z)) :=
      Nat.mul_le_mul_left 2 hle
    _ ≤ 2 * (n ^ T * (n * n)) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left (n ^ T) hcapz)
    _ = n ^ T * (2 * n ^ 2) := by
      simp only [Nat.pow_two]
      ac_rfl

/-- The R10c digit half on any successor: a causal core whose four charges
fit in H n² gives the half-stage H + 2.  Consumer:
`widthDigitHalfOfBankCore` (BANK, H = 201) and
`smallCleanDigitHalfOfCausalCore` (SMALL). -/
theorem widthDigitHalfOfCausalCore {S : Type} {n : Nat}
    (next : S → Fin n → S)
    (entrance preDrain terminal : S → Prop)
    (cuts : WidthDigitCuts S)
    (cb cz cw cc H : Nat)
    (hfit : cb + cz + cw + cc ≤ H * n ^ 2)
    (hcore : WidthDigitCausalCore next entrance preDrain terminal cuts
      cb cz cw cc) :
    BankRepairHalfStage next entrance terminal (H + 2) := by
  obtain ⟨hboundary, hzero, hwave, hpair, hclosed,
    rank, chosen, hcap, _hrankzero, hdrop, hnoninc⟩ := hcore
  exact bankRepairCloseHalfCompose next entrance preDrain terminal H 2
    (widthDigitPreDrainOfCharges next entrance preDrain cuts cb cz cw cc H
      hfit hboundary hzero hwave hpair)
    (widthDigitDirtyHalfOfRank next preDrain terminal hclosed rank chosen
      hcap hdrop hnoninc)

/-- A half-stage at a budget a is a half-stage at any larger budget b.
Consumer: `smallCleanDigitHalfOfSplitCore` (SMALL pays the BANK 201 + 2
split inside its larger digit budget). -/
theorem widthDigitHalfBudgetMono {S : Type} {n : Nat}
    (next : S → Fin n → S) (start finish : S → Prop) (a b : Nat)
    (hab : a ≤ b)
    (h : BankRepairHalfStage next start finish a) :
    BankRepairHalfStage next start finish b := by
  intro z hz T
  exact Nat.le_trans (h z hz T)
    (Nat.mul_le_mul_left (n ^ T) (Nat.mul_le_mul_right (n ^ 2) hab))

/-- The BANK causal core is the generic core at the BANK successor, the
BANK cuts and the four BANK micro-charges.  Consumer:
`widthDigitHalfOfBankCore`. -/
theorem widthDigitCoreOfBank {n : Nat}
    (ring : DirectedRing n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (entrance preDrain terminal : BankReferenceState ring hbank → Prop)
    (cuts : BankRepairDigitPreDrainCuts ring hbank)
    (hcore : BankDigitCausalCore ring hbank entrance preDrain terminal cuts) :
    WidthDigitCausalCore (bankRepairNext ring hbank) entrance preDrain terminal
      ⟨cuts.boundaryRetired, cuts.firstBlockZero, cuts.successorValuesStable⟩
      (bankRepairDigitBoundaryMicroCharge n)
      (bankRepairDigitFirstZeroMicroCharge n)
      (bankRepairDigitValueWaveMicroCharge n)
      (bankRepairDigitComparisonMicroCharge n) :=
  hcore

/-- BANK instance of the generic digit half (H = 201 by
`bankRepairDigitMicroChargesFit`): the same 203 half-units as
`bankDigitHalfOfCausalCore`.  Consumer: the BANK clean digit half,
showing that BANK and SMALL share `widthDigitHalfOfCausalCore`. -/
theorem widthDigitHalfOfBankCore {n : Nat}
    (ring : DirectedRing n) (hn : 5 ≤ n)
    (hbank : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (entrance preDrain terminal : BankReferenceState ring hbank → Prop)
    (cuts : BankRepairDigitPreDrainCuts ring hbank)
    (hcore : BankDigitCausalCore ring hbank entrance preDrain terminal cuts) :
    BankRepairHalfStage (bankRepairNext ring hbank) entrance terminal 203 :=
  widthDigitHalfOfCausalCore (bankRepairNext ring hbank) entrance preDrain
    terminal _ _ _ _ _ 201 (bankRepairDigitMicroChargesFit hn hbank)
    (widthDigitCoreOfBank ring hbank entrance preDrain terminal cuts hcore)

end L3.RenewalReferenceClock

#print axioms L3.RenewalReferenceClock.widthDigitHalfReserve
#print axioms L3.RenewalReferenceClock.widthDigitChargedCompose
#print axioms L3.RenewalReferenceClock.widthDigitCostOnForwardClosed
#print axioms L3.RenewalReferenceClock.widthDigitPreDrainOfCharges
#print axioms L3.RenewalReferenceClock.widthDigitDirtyHalfOfRank
#print axioms L3.RenewalReferenceClock.widthDigitHalfOfCausalCore
#print axioms L3.RenewalReferenceClock.widthDigitHalfBudgetMono
#print axioms L3.RenewalReferenceClock.widthDigitCoreOfBank
#print axioms L3.RenewalReferenceClock.widthDigitHalfOfBankCore
