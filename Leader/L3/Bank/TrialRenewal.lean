import Leader.L3.Bank.TrialSuccess
import Leader.L3.Headline.GrantProducer

/-!
G13-INDEX-RENEWAL, trial cutoff lemmas for one Clean BANK start.

All masses and costs are finite sums over original n-edge words.
ACTIVE words pay their entire censored length in costNumerator.
No assertion of almost-sure termination is used.
-/

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- (c1) The C.6 censored first-hit cost bounds unfinished mass.
The existing Markov lemma proves the exact ACTIVE-word length
identity underneath this inequality. -/
theorem bankTrialRenewalActiveCutoff {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (L : Nat) :
    L * bankTrialDurationActiveMass ring root S L ≤
      n ^ L * ((8 * (compileAdvice q).b + 12) * n) := by
  exact Nat.le_trans
    (bankTrialSuccessMarkovFromCost ring root S L)
    (bankTrialDurationC6Holds ring root hn hsmall hw
      hpositive hK S hclean L)

/-- The state-level absorbing-WON mass is nondecreasing under one
additional original scheduler letter. The state parameter is needed
to induct through the first-letter scheduleSum recursion. -/
private theorem bankTrialRenewalStateWonStep {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (L : Nat) (z : BankTrialLocalState q),
      n * bankTrialProbabilityStateWinMass ring root z L ≤
        bankTrialProbabilityStateWinMass ring root z (L + 1) := by
  intro L
  induction L with
  | zero =>
      intro z
      by_cases hw : z.phase = .won
      · have hterminal : bankTrialLocalTerminal z := Or.inl hw
        have hconstant (T : Nat) :
            bankTrialProbabilityStateWinMass ring root z T =
              n ^ T := by
          unfold bankTrialProbabilityStateWinMass
          have hfun :
              (fun w : List (Fin n) =>
                if (bankTrialLocalRun ring root w z).phase = .won
                then 1 else 0) =
              (fun _ : List (Fin n) => 1) := by
            funext w
            rw [bankTrialLocalRunTerminalAbsorbs
              ring root w z hterminal]
            simp [hw]
          rw [hfun, bankTrialProbabilityScheduleSumConst]
          simp
        rw [hconstant 0, hconstant 1]
        simp
      · have hzero :
            bankTrialProbabilityStateWinMass ring root z 0 = 0 := by
          unfold bankTrialProbabilityStateWinMass
          rw [bankTrialProbabilityScheduleSumZero]
          simp [bankTrialLocalRun, hw]
        rw [hzero, Nat.mul_zero]
        exact Nat.zero_le _
  | succ L ih =>
      intro z
      have hchild (e : Fin n) :
          n * bankTrialProbabilityStateWinMass ring root
              (bankTrialLocalNext ring root z e) L ≤
            bankTrialProbabilityStateWinMass ring root
              (bankTrialLocalNext ring root z e) (L + 1) :=
        ih (bankTrialLocalNext ring root z e)
      have hsum :
          (List.ofFn (fun e : Fin n =>
            n * bankTrialProbabilityStateWinMass ring root
              (bankTrialLocalNext ring root z e) L)).sum ≤
          (List.ofFn (fun e : Fin n =>
            bankTrialProbabilityStateWinMass ring root
              (bankTrialLocalNext ring root z e) (L + 1))).sum :=
        ofFn_sum_le _ _ hchild
      calc
        n * bankTrialProbabilityStateWinMass ring root z (L + 1) =
            (List.ofFn (fun e : Fin n =>
              n * bankTrialProbabilityStateWinMass ring root
                (bankTrialLocalNext ring root z e) L)).sum := by
          rw [bankTrialProbabilityStateWinMassFirst ring root z L]
          exact (ofFn_sum_mul_left n
            (fun e : Fin n =>
              bankTrialProbabilityStateWinMass ring root
                (bankTrialLocalNext ring root z e) L)).symm
        _ ≤ (List.ofFn (fun e : Fin n =>
              bankTrialProbabilityStateWinMass ring root
                (bankTrialLocalNext ring root z e) (L + 1))).sum :=
          hsum
        _ = bankTrialProbabilityStateWinMass ring root z
              ((L + 1) + 1) :=
          (bankTrialProbabilityStateWinMassFirst
            ring root z (L + 1)).symm

/-- (c2), one-step formulation on bankTrialProbabilityWinMass. -/
theorem bankTrialRenewalWonStep {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (L : Nat) :
    n * bankTrialProbabilityWinMass ring root S L ≤
      bankTrialProbabilityWinMass ring root S (L + 1) := by
  change n * bankTrialProbabilityStateWinMass
      ring root (bankTrialLocalStart S) L ≤
    bankTrialProbabilityStateWinMass
      ring root (bankTrialLocalStart S) (L + 1)
  exact bankTrialRenewalStateWonStep
    ring root L (bankTrialLocalStart S)

/-- (c2), arbitrary finite padding by m scheduler letters. -/
theorem bankTrialRenewalWonMonotone {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (L m : Nat) :
    n ^ m * bankTrialProbabilityWinMass ring root S L ≤
      bankTrialProbabilityWinMass ring root S (L + m) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      have hstep :=
        bankTrialRenewalWonStep ring root S (L + m)
      calc
        n ^ (m + 1) * bankTrialProbabilityWinMass ring root S L =
            n * (n ^ m *
              bankTrialProbabilityWinMass ring root S L) := by
          rw [Nat.pow_succ, Nat.mul_comm (n ^ m) n, Nat.mul_assoc]
        _ ≤ n * bankTrialProbabilityWinMass ring root S (L + m) :=
          Nat.mul_le_mul_left n ih
        _ ≤ bankTrialProbabilityWinMass ring root S ((L + m) + 1) :=
          hstep
        _ = bankTrialProbabilityWinMass ring root S (L + (m + 1)) := by
          rw [Nat.add_assoc]

/-- (c3) C.8 with ACTIVE absorbed into WON by the cutoff
hypothesis. The hypothesis is the denominator-cleared
d*n*n^L <= L*WON(L) inequality; no division is used. -/
theorem bankTrialRenewalCompletedSuccessCost {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (L : Nat)
    (hcut : ((8 * (compileAdvice q).b + 12) * n) * n ^ L ≤
      L * bankTrialProbabilityWinMass ring root S L) :
    bankTrialDurationSuccessCostMass ring root S L ≤
      (2 * ((8 * (compileAdvice q).b + 12) *
        ((compileAdvice q).K + 1) * n)) *
          bankTrialProbabilityWinMass ring root S L := by
  have hpositiveBudget :
      0 < ((8 * (compileAdvice q).b + 12) * n) * n ^ L :=
    Nat.mul_pos
      (Nat.mul_pos (by omega) (by omega))
      (Nat.pow_pos (by omega))
  have hlen : 0 < L := by
    cases L with
    | zero =>
        have hz :
            ((8 * (compileAdvice q).b + 12) * n) *
              n ^ 0 = 0 := by
          apply Nat.le_zero.mp
          simpa only [Nat.zero_mul] using hcut
        exact False.elim ((Nat.ne_of_gt hpositiveBudget) hz)
    | succ k =>
        exact Nat.zero_lt_succ k
  have hactiveCost :=
    bankTrialRenewalActiveCutoff ring root hn hsmall hw
      hpositive hK S hclean L
  have hscaled :
      L * bankTrialDurationActiveMass ring root S L ≤
        L * bankTrialProbabilityWinMass ring root S L := by
    calc
      L * bankTrialDurationActiveMass ring root S L ≤
          n ^ L * ((8 * (compileAdvice q).b + 12) * n) :=
        hactiveCost
      _ = ((8 * (compileAdvice q).b + 12) * n) * n ^ L :=
        Nat.mul_comm _ _
      _ ≤ L * bankTrialProbabilityWinMass ring root S L :=
        hcut
  have hactiveLe :
      bankTrialDurationActiveMass ring root S L ≤
        bankTrialProbabilityWinMass ring root S L :=
    Nat.le_of_mul_le_mul_left hscaled hlen
  have hsum :
      bankTrialProbabilityWinMass ring root S L +
          bankTrialDurationActiveMass ring root S L ≤
        bankTrialProbabilityWinMass ring root S L +
          bankTrialProbabilityWinMass ring root S L :=
    Nat.add_le_add_left hactiveLe _
  have hC8 :=
    (bankTrialDurationSuccessConditionalTargetHolds
      ring root hw hsmall hlarge hpositive hK) S hclean L
  calc
    bankTrialDurationSuccessCostMass ring root S L ≤
        (bankTrialProbabilityWinMass ring root S L +
          bankTrialDurationActiveMass ring root S L) *
          ((8 * (compileAdvice q).b + 12) *
            ((compileAdvice q).K + 1) * n) :=
      hC8
    _ ≤ (bankTrialProbabilityWinMass ring root S L +
          bankTrialProbabilityWinMass ring root S L) *
          ((8 * (compileAdvice q).b + 12) *
            ((compileAdvice q).K + 1) * n) :=
      Nat.mul_le_mul_right _ hsum
    _ = (2 * ((8 * (compileAdvice q).b + 12) *
          ((compileAdvice q).K + 1) * n)) *
          bankTrialProbabilityWinMass ring root S L := by
      rw [← Nat.two_mul (bankTrialProbabilityWinMass ring root S L),
        Nat.mul_assoc,
        Nat.mul_comm (bankTrialProbabilityWinMass ring root S L),
        ← Nat.mul_assoc]

/-- A completed LOST word carries no greater stopped-cost
charge than the entire original-scheduler word. -/
private theorem bankTrialRenewalFailureCostLeTotal {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (L : Nat) :
    bankTrialDurationFailureCostMass ring root S L ≤
      costNumerator (bankTrialLocalNext ring root)
        bankTrialLocalTerminal (bankTrialLocalStart S) L := by
  unfold bankTrialDurationFailureCostMass
  change Prob.scheduleSum n L (fun w =>
      if (bankTrialLocalRun ring root w
        (bankTrialLocalStart S)).phase = .lost then
        costWord (bankTrialLocalNext ring root)
          bankTrialLocalTerminal (bankTrialLocalStart S) w
      else 0) ≤
    Prob.scheduleSum n L
      (costWord (bankTrialLocalNext ring root)
        bankTrialLocalTerminal (bankTrialLocalStart S))
  apply bankTrialProbabilityScheduleSumMono n L
  intro w
  split
  · exact Nat.le_refl _
  · exact Nat.zero_le _

/-- (c4) The unconditional C.6 charge gives the completed LOST
cost, and the denominator-cleared LOST-mass hypothesis converts
the d*n^L budget into the sharper (d+1)*LOST budget. -/
theorem bankTrialRenewalCompletedFailureCost {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (L : Nat)
    (hLost : (8 * (compileAdvice q).b + 12) * n ^ L ≤
      (8 * (compileAdvice q).b + 13) *
        bankTrialDurationFailureMass ring root S L) :
    bankTrialDurationFailureCostMass ring root S L ≤
      bankTrialDurationFailureMass ring root S L *
        ((8 * (compileAdvice q).b + 13) * n) := by
  have hscaled := Nat.mul_le_mul_left n hLost
  calc
    bankTrialDurationFailureCostMass ring root S L ≤
        costNumerator (bankTrialLocalNext ring root)
          bankTrialLocalTerminal (bankTrialLocalStart S) L :=
      bankTrialRenewalFailureCostLeTotal ring root S L
    _ ≤ n ^ L * ((8 * (compileAdvice q).b + 12) * n) :=
      bankTrialDurationC6Holds ring root hn hsmall hw
        hpositive hK S hclean L
    _ = n * ((8 * (compileAdvice q).b + 12) * n ^ L) := by
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    _ ≤ n * ((8 * (compileAdvice q).b + 13) *
          bankTrialDurationFailureMass ring root S L) :=
      hscaled
    _ = bankTrialDurationFailureMass ring root S L *
          ((8 * (compileAdvice q).b + 13) * n) := by
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

end L3


namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
G13-INDEX-RENEWAL: finite-word regenerative scanner.
The LOSS cut already contains the postservice Clean bank. The next
letter starts a new bankTrialLocalStart using that stored bank; the
LOSS-producing letter belongs to the old trial, not to both trials.
All trial indices below are zero based: index j means j completed
LOST trials followed by the (j+1)-st trial ending WON.
-/

structure BankTrialRenewalState (q : Nat) where
  observer : BankTrialLocalState q
  failures : List Nat
  age : Nat
  elapsed : Nat

def bankTrialRenewalStart {q : Nat}
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) : BankTrialRenewalState q :=
  { observer := bankTrialLocalStart S
    failures := []
    age := 0
    elapsed := 0 }

/-- Advance exactly one local trial, recording its completed LOST
duration. The input age counts the letters already in this trial. -/
noncomputable def bankTrialRenewalAdvance {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankTrialRenewalState q)
    (trial : BankTrialLocalState q)
    (age : Nat) (e : Fin n) : BankTrialRenewalState q :=
  if (bankTrialLocalNext ring root trial e).phase = .lost then
    { observer := bankTrialLocalNext ring root trial e
      failures := z.failures ++ [age + 1]
      age := age + 1
      elapsed := z.elapsed + 1 }
  else
    { observer := bankTrialLocalNext ring root trial e
      failures := z.failures
      age := age + 1
      elapsed := z.elapsed + 1 }

/-- A pending LOST state restarts from its stored postservice bank
BEFORE processing the next letter. A WON state is absorbing. -/
noncomputable def bankTrialRenewalNext {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankTrialRenewalState q) (e : Fin n) :
    BankTrialRenewalState q :=
  match z.observer.phase with
  | .won => z
  | .lost =>
      bankTrialRenewalAdvance ring root z
        (bankTrialLocalStart z.observer.bank) 0 e
  | .recovery =>
      bankTrialRenewalAdvance ring root z z.observer z.age e
  | .live _ =>
      bankTrialRenewalAdvance ring root z z.observer z.age e

/-- A finite run from any renewal scanner state. -/
noncomputable def bankTrialRenewalRunFrom {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    List (Fin n) → BankTrialRenewalState q → BankTrialRenewalState q
  | [], z => z
  | e :: tail, z =>
      bankTrialRenewalRunFrom ring root tail
        (bankTrialRenewalNext ring root z e)

/-- The requested one-Clean-start regenerative run on the original
Fin n word, including trial index (failures.length), current trial
age, and total elapsed scheduler letters up to the first WON. -/
noncomputable def bankTrialRenewalRun {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (word : List (Fin n)) : BankTrialRenewalState q :=
  bankTrialRenewalRunFrom ring root word (bankTrialRenewalStart S)

theorem bankTrialRenewalAdvanceElapsed {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankTrialRenewalState q)
    (trial : BankTrialLocalState q)
    (age : Nat) (e : Fin n) :
    (bankTrialRenewalAdvance ring root z trial age e).elapsed =
      z.elapsed + 1 := by
  unfold bankTrialRenewalAdvance
  split <;> rfl

theorem bankTrialRenewalNextWon {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankTrialRenewalState q)
    (hwon : z.observer.phase = .won) :
    bankTrialRenewalNext ring root z e = z := by
  unfold bankTrialRenewalNext
  rw [hwon]

theorem bankTrialRenewalNextElapsed {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankTrialRenewalState q)
    (hnot : z.observer.phase ≠ .won) :
    (bankTrialRenewalNext ring root z e).elapsed =
      z.elapsed + 1 := by
  cases hphase : z.observer.phase with
  | won =>
      exact False.elim (hnot hphase)
  | lost =>
      simp only [bankTrialRenewalNext, hphase]
      exact bankTrialRenewalAdvanceElapsed ring root z
        (bankTrialLocalStart z.observer.bank) 0 e
  | recovery =>
      simp only [bankTrialRenewalNext, hphase]
      exact bankTrialRenewalAdvanceElapsed ring root z z.observer z.age e
  | live begun =>
      simp only [bankTrialRenewalNext, hphase]
      exact bankTrialRenewalAdvanceElapsed ring root z z.observer z.age e

theorem bankTrialRenewalRunFromAppend {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (u v : List (Fin n)) (z : BankTrialRenewalState q),
      bankTrialRenewalRunFrom ring root (u ++ v) z =
        bankTrialRenewalRunFrom ring root v
          (bankTrialRenewalRunFrom ring root u z) := by
  intro u
  induction u with
  | nil =>
      intro v z
      rfl
  | cons e rest ih =>
      intro v z
      change bankTrialRenewalRunFrom ring root (rest ++ v)
          (bankTrialRenewalNext ring root z e) =
        bankTrialRenewalRunFrom ring root v
          (bankTrialRenewalRunFrom ring root rest
            (bankTrialRenewalNext ring root z e))
      exact ih v _

theorem bankTrialRenewalRunFromWon {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (word : List (Fin n)) (z : BankTrialRenewalState q),
      z.observer.phase = .won →
      bankTrialRenewalRunFrom ring root word z = z := by
  intro word
  induction word with
  | nil =>
      intro z _
      rfl
  | cons e rest ih =>
      intro z hw
      change bankTrialRenewalRunFrom ring root rest
          (bankTrialRenewalNext ring root z e) = z
      rw [bankTrialRenewalNextWon ring root e z hw]
      exact ih z hw

theorem bankTrialRenewalRunFromElapsedMono {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (word : List (Fin n)) (z : BankTrialRenewalState q),
      z.elapsed ≤ (bankTrialRenewalRunFrom ring root word z).elapsed := by
  intro word
  induction word with
  | nil =>
      intro z
      exact Nat.le_refl _
  | cons e rest ih =>
      intro z
      have hstep :
          z.elapsed ≤ (bankTrialRenewalNext ring root z e).elapsed := by
        by_cases hw : z.observer.phase = .won
        · rw [bankTrialRenewalNextWon ring root e z hw]
          exact Nat.le_refl _
        · rw [bankTrialRenewalNextElapsed ring root e z hw]
          omega
      change z.elapsed ≤
        (bankTrialRenewalRunFrom ring root rest
          (bankTrialRenewalNext ring root z e)).elapsed
      exact Nat.le_trans hstep (ih (bankTrialRenewalNext ring root z e))

/-- If the completed run has won by elapsed time <= initial time
plus W, the actual prefix of W letters has already won. -/
theorem bankTrialRenewalWonWithinCutoff {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (W : Nat) (word : List (Fin n))
      (z : BankTrialRenewalState q),
      (bankTrialRenewalRunFrom ring root word z).observer.phase = .won →
      (bankTrialRenewalRunFrom ring root word z).elapsed ≤ z.elapsed + W →
      (bankTrialRenewalRunFrom ring root (word.take W) z).observer.phase =
        .won := by
  intro W
  induction W with
  | zero =>
      intro word z hwon htime
      by_cases hz : z.observer.phase = .won
      · rw [bankTrialRenewalRunFromWon ring root (word.take 0) z hz]
        exact hz
      · cases word with
        | nil =>
            exact False.elim (hz hwon)
        | cons e rest =>
            have hstep := bankTrialRenewalNextElapsed ring root e z hz
            have hmono := bankTrialRenewalRunFromElapsedMono
              ring root rest (bankTrialRenewalNext ring root z e)
            change
              (bankTrialRenewalRunFrom ring root rest
                (bankTrialRenewalNext ring root z e)).elapsed ≤
                  z.elapsed + 0 at htime
            omega
  | succ W ih =>
      intro word z hwon htime
      by_cases hz : z.observer.phase = .won
      · rw [bankTrialRenewalRunFromWon
          ring root (word.take (W + 1)) z hz]
        exact hz
      · cases word with
        | nil =>
            exact False.elim (hz hwon)
        | cons e rest =>
            have hstep := bankTrialRenewalNextElapsed ring root e z hz
            have htimeRest :
                (bankTrialRenewalRunFrom ring root rest
                  (bankTrialRenewalNext ring root z e)).elapsed ≤
                (bankTrialRenewalNext ring root z e).elapsed + W := by
              change
                (bankTrialRenewalRunFrom ring root rest
                  (bankTrialRenewalNext ring root z e)).elapsed ≤
                    z.elapsed + (W + 1) at htime
              omega
            have hrest := ih rest (bankTrialRenewalNext ring root z e)
              (by simpa only [bankTrialRenewalRunFrom] using hwon)
              htimeRest
            change
              (bankTrialRenewalRunFrom ring root (rest.take W)
                (bankTrialRenewalNext ring root z e)).observer.phase =
                .won
            exact hrest

/-- Pattern E_j: j complete losing trials, then a successful
trial. Every previous loss duration and the final success duration
must be at most L. All durations are measured from their *own*
regenerated Clean start. -/
noncomputable def bankTrialRenewalPattern {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (L j : Nat) (word : List (Fin n)) : Bool :=
  decide
    ((bankTrialRenewalRun ring root S word).observer.phase = .won ∧
     (bankTrialRenewalRun ring root S word).failures.length = j ∧
     (bankTrialRenewalRun ring root S word).failures.all
       (fun age => decide (age ≤ L)) = true ∧
     (bankTrialRenewalRun ring root S word).age ≤ L)

/-- The elapsed charge is masked by its exact E_j event. -/
noncomputable def bankTrialRenewalTau {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (L j : Nat) (word : List (Fin n)) : Nat :=
  if bankTrialRenewalPattern ring root S L j word then
    (bankTrialRenewalRun ring root S word).elapsed
  else 0

/-- The frozen first-private-success indicator, measured on the
prefix of W letters in the same physical scheduler word. -/
noncomputable def bankTrialRenewalHitWord {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (W : Nat) (word : List (Fin n)) : Bool :=
  decide ((bankTrialRenewalRun ring root S (word.take W)).observer.phase =
    .won)

theorem bankTrialRenewalPatternDisjoint {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (L i j : Nat) (word : List (Fin n))
    (hi : bankTrialRenewalPattern ring root S L i word = true)
    (hj : bankTrialRenewalPattern ring root S L j word = true) :
    i = j := by
  have hfirst :
      (bankTrialRenewalRun ring root S word).observer.phase = .won ∧
      (bankTrialRenewalRun ring root S word).failures.length = i ∧
      (bankTrialRenewalRun ring root S word).failures.all
        (fun age => decide (age ≤ L)) = true ∧
      (bankTrialRenewalRun ring root S word).age ≤ L := by
    simpa only [bankTrialRenewalPattern, decide_eq_true_eq] using hi
  have hsecond :
      (bankTrialRenewalRun ring root S word).observer.phase = .won ∧
      (bankTrialRenewalRun ring root S word).failures.length = j ∧
      (bankTrialRenewalRun ring root S word).failures.all
        (fun age => decide (age ≤ L)) = true ∧
      (bankTrialRenewalRun ring root S word).age ≤ L := by
    simpa only [bankTrialRenewalPattern, decide_eq_true_eq] using hj
  exact hfirst.2.1.symm.trans hsecond.2.1

theorem bankTrialRenewalPatternSound {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (L j W : Nat) (word : List (Fin n))
    (hpattern : bankTrialRenewalPattern ring root S L j word = true)
    (htime : bankTrialRenewalTau ring root S L j word ≤ W) :
    bankTrialRenewalHitWord ring root S W word = true := by
  have hp :
      (bankTrialRenewalRun ring root S word).observer.phase = .won ∧
      (bankTrialRenewalRun ring root S word).failures.length = j ∧
      (bankTrialRenewalRun ring root S word).failures.all
        (fun age => decide (age ≤ L)) = true ∧
      (bankTrialRenewalRun ring root S word).age ≤ L := by
    simpa only [bankTrialRenewalPattern, decide_eq_true_eq] using hpattern
  have hclock :
      (bankTrialRenewalRun ring root S word).elapsed ≤ W := by
    simpa [bankTrialRenewalTau, hpattern] using htime
  have hhit :
      (bankTrialRenewalRunFrom ring root (word.take W)
        (bankTrialRenewalStart S)).observer.phase = .won :=
    bankTrialRenewalWonWithinCutoff ring root W word
      (bankTrialRenewalStart S) hp.1
      (by simpa only [bankTrialRenewalRun, bankTrialRenewalStart,
          Nat.zero_add] using hclock)
  unfold bankTrialRenewalHitWord bankTrialRenewalRun
  simp [hhit]

private theorem bankTrialRenewalPatternOneHot {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (L H : Nat) (word : List (Fin n)) :
    bankTrialSuccessStageIndexSum (fun j =>
      Prob.indicator (bankTrialRenewalPattern ring root S L j word)) H ≤
      1 := by
  have hstage (j : Nat)
      (hj : bankTrialRenewalPattern ring root S L j word = true) :
      true = true ∧
        j = (bankTrialRenewalRun ring root S word).failures.length := by
    have hp :
        (bankTrialRenewalRun ring root S word).observer.phase = .won ∧
        (bankTrialRenewalRun ring root S word).failures.length = j ∧
        (bankTrialRenewalRun ring root S word).failures.all
          (fun age => decide (age ≤ L)) = true ∧
        (bankTrialRenewalRun ring root S word).age ≤ L := by
      simpa only [bankTrialRenewalPattern, decide_eq_true_eq] using hj
    exact ⟨rfl, hp.2.1.symm⟩
  have hbound := bankTrialSuccessStageIndexSumIndicatorBound true
    (bankTrialRenewalRun ring root S word).failures.length H
    (fun j => bankTrialRenewalPattern ring root S L j word) hstage
  change bankTrialSuccessStageIndexSum (fun j =>
    Prob.indicator (bankTrialRenewalPattern ring root S L j word)) H ≤
    1 at hbound
  exact hbound

private theorem bankTrialRenewalStageScale
    (a H : Nat) (f : Nat → Nat) :
    bankTrialSuccessStageIndexSum (fun j => a * f j) H =
      a * bankTrialSuccessStageIndexSum f H := by
  induction H with
  | zero =>
      rfl
  | succ H ih =>
      change bankTrialSuccessStageIndexSum (fun j => a * f j) H +
          a * f H =
        a * (bankTrialSuccessStageIndexSum f H + f H)
      rw [ih, Nat.mul_add]

/-- Per-word finite window inequality. If a pattern occurs late,
its cost covers W; if one occurs early, the single hit indicator
covers W. Different E_j cannot both contribute. -/
theorem bankTrialRenewalWordWindow {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (L W H : Nat) (word : List (Fin n)) :
    W * bankTrialSuccessStageIndexSum (fun j =>
      Prob.indicator (bankTrialRenewalPattern ring root S L j word)) H ≤
    W * Prob.indicator (bankTrialRenewalHitWord ring root S W word) +
      bankTrialSuccessStageIndexSum (fun j =>
        bankTrialRenewalTau ring root S L j word) H := by
  cases hh : bankTrialRenewalHitWord ring root S W word with
  | true =>
      have hone := bankTrialRenewalPatternOneHot
        ring root S L H word
      have hscaled := Nat.mul_le_mul_left W hone
      have hbound :
          W * bankTrialSuccessStageIndexSum (fun j =>
            Prob.indicator
              (bankTrialRenewalPattern ring root S L j word)) H ≤
          W + bankTrialSuccessStageIndexSum (fun j =>
            bankTrialRenewalTau ring root S L j word) H := by
        omega
      simpa [Prob.indicator, hh] using hbound
  | false =>
      have hpoint (j : Nat) :
          W * Prob.indicator
              (bankTrialRenewalPattern ring root S L j word) ≤
            bankTrialRenewalTau ring root S L j word := by
        cases hp : bankTrialRenewalPattern ring root S L j word with
        | false =>
            simp [Prob.indicator, bankTrialRenewalTau, hp]
        | true =>
            have hlate : W <
                bankTrialRenewalTau ring root S L j word := by
              by_cases hle :
                  bankTrialRenewalTau ring root S L j word ≤ W
              · have hhit := bankTrialRenewalPatternSound
                  ring root S L j W word hp hle
                rw [hh] at hhit
                cases hhit
              · omega
            simpa [Prob.indicator, bankTrialRenewalTau, hp]
              using (Nat.le_of_lt hlate)
      have hsum := bankTrialSuccessStageIndexSumMono
        (fun j => W * Prob.indicator
          (bankTrialRenewalPattern ring root S L j word))
        (fun j => bankTrialRenewalTau ring root S L j word)
        hpoint H
      rw [bankTrialRenewalStageScale] at hsum
      simpa [Prob.indicator, hh] using hsum

noncomputable def bankTrialRenewalPatternMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (T L j : Nat) : Nat :=
  Prob.scheduleSum n T (fun word =>
    Prob.indicator (bankTrialRenewalPattern ring root S L j word))

noncomputable def bankTrialRenewalPatternCost {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (T L j : Nat) : Nat :=
  Prob.scheduleSum n T (bankTrialRenewalTau ring root S L j)

noncomputable def bankTrialRenewalHitMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (T W : Nat) : Nat :=
  Prob.scheduleSum n T (fun word =>
    Prob.indicator (bankTrialRenewalHitWord ring root S W word))

/-- (e3) The exact sum-over-indices window inequality on one
length-T scheduler ensemble; the two horizon hypotheses are those
used by the subsequent finite-cutoff mass argument. -/
theorem bankTrialRenewalWindowInequality {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (T L W H : Nat)
    (_hwindow : W ≤ T)
    (_hpattern : H * L ≤ T) :
    W * bankTrialSuccessStageIndexSum (fun j =>
      bankTrialRenewalPatternMass ring root S T L j) H ≤
    W * bankTrialRenewalHitMass ring root S T W +
      bankTrialSuccessStageIndexSum (fun j =>
        bankTrialRenewalPatternCost ring root S T L j) H := by
  calc
    W * bankTrialSuccessStageIndexSum (fun j =>
        bankTrialRenewalPatternMass ring root S T L j) H =
      W * Prob.scheduleSum n T (fun word =>
        bankTrialSuccessStageIndexSum (fun j =>
          Prob.indicator
            (bankTrialRenewalPattern ring root S L j word)) H) := by
      unfold bankTrialRenewalPatternMass
      rw [bankTrialSuccessStageIndexSumSchedule]
    _ = Prob.scheduleSum n T (fun word =>
          W * bankTrialSuccessStageIndexSum (fun j =>
            Prob.indicator
              (bankTrialRenewalPattern ring root S L j word)) H) :=
      (bankTrialSuccessScheduleSumScale n T W _).symm
    _ ≤ Prob.scheduleSum n T (fun word =>
          W * Prob.indicator
              (bankTrialRenewalHitWord ring root S W word) +
          bankTrialSuccessStageIndexSum (fun j =>
            bankTrialRenewalTau ring root S L j word) H) :=
      bankTrialProbabilityScheduleSumMono n T _ _
        (fun word => bankTrialRenewalWordWindow
          ring root S L W H word)
    _ = W * bankTrialRenewalHitMass ring root S T W +
          bankTrialSuccessStageIndexSum (fun j =>
            bankTrialRenewalPatternCost ring root S T L j) H := by
      rw [bankTrialC5ScheduleSumAdd, bankTrialSuccessScheduleSumScale]
      rw [← bankTrialSuccessStageIndexSumSchedule]
      rfl

/-- A stop exactly when the current single-trial observer enters
LOST. The first-stop machinery chooses the earliest LOST prefix. -/
noncomputable def bankTrialRenewalFirstLostStop {n q : Nat}
    (_pre : List (Fin n)) (z : BankTrialLocalState q) : Bool :=
  decide (z.phase = .lost)

/-- (e4) Exact first-LOST word factorization. F may inspect both
the unique first LOST cut and the restarted suffix, including the
stored Clean bank at that cut. Nothing is conditioned on a
hypothetical infinite-horizon exit. -/
theorem bankTrialRenewalFirstLostFactor {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (F : List (Fin n) → BankTrialLocalState q →
      List (Fin n) → Nat) (T : Nat) :
    Prob.scheduleSum n T (fun word =>
      bankTrialSuccessNatStoppedWord
        (bankTrialLocalNext ring root)
        bankTrialRenewalFirstLostStop
        (fun cut z _ suffix => F cut z suffix)
        T [] (bankTrialLocalStart S) word) =
      ((Prob.firstStoppedPrefixes
        (bankTrialLocalNext ring root)
        bankTrialRenewalFirstLostStop T [] (bankTrialLocalStart S)).map
        (fun cut =>
          Prob.scheduleSum n (T - cut.length)
            (fun suffix =>
              F cut
                (bankTrialLocalRun ring root cut
                  (bankTrialLocalStart S)) suffix))).sum := by
  exact bankTrialSuccessNatStoppedFactorizationLocal ring root
    bankTrialRenewalFirstLostStop
    (fun cut z _ suffix => F cut z suffix)
    (bankTrialLocalStart S) T

/-- Every first-LOST cut c contributes n^(T-|c|) continuations
when the suffix weight is constant. This is the unnormalized
first-LOST cylinder count; suffix-dependent weights instead use
the exact restarted scheduleSum in bankTrialRenewalFirstLostFactor. -/
theorem bankTrialRenewalFirstLostExtensionCount {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (F : List (Fin n) → BankTrialLocalState q → Nat)
    (T : Nat) :
    Prob.scheduleSum n T (fun word =>
      bankTrialSuccessNatStoppedWord
        (bankTrialLocalNext ring root)
        bankTrialRenewalFirstLostStop
        (fun cut z _ _ => F cut z)
        T [] (bankTrialLocalStart S) word) =
      ((Prob.firstStoppedPrefixes
        (bankTrialLocalNext ring root)
        bankTrialRenewalFirstLostStop T [] (bankTrialLocalStart S)).map
        (fun cut =>
          n ^ (T - cut.length) *
            F cut (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)))).sum := by
  rw [bankTrialRenewalFirstLostFactor ring root S
    (fun cut z _ => F cut z) T]
  apply congrArg List.sum
  apply List.map_congr_left
  intro cut _
  exact bankTrialProbabilityScheduleSumConst n
    (T - cut.length)
    (F cut (bankTrialLocalRun ring root cut
      (bankTrialLocalStart S)))

end L3


namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
G13-INDEX-RENEWAL: independent bridge.
The two full j-index sandwiches remain UNPROVED and are deliberately
declared below as target Props, not theorems.

With rational lower probabilities lo/den and win/den the correct
Nat-cleared mass claim is
  lo^j * win * n^T <= den^(j+1) * m_j(T).
The additional denominator power is essential.
-/

/-- Uniform completed trial masses, with one positive denominator. -/
def BankTrialRenewalUniformMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (L lo win den : Nat) : Prop :=
  0 < den ∧
  ∀ (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b),
    BankTrialLocalClean q B →
      lo * n ^ L ≤
        den * bankTrialDurationFailureMass ring root B L ∧
      win * n ^ L ≤
        den * bankTrialProbabilityWinMass ring root B L

/-- Uniform C.4 upper mass and completed C.7/C.8 cost bounds. -/
def BankTrialRenewalUniformCost {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (L f g : Nat) : Prop :=
  ∀ (B : GrantBankReference.BankLocalReference
      (compileAdvice q).b),
    BankTrialLocalClean q B →
      2 ^ (compileAdvice q).K *
          bankTrialProbabilityWinMass ring root B L ≤ n ^ L ∧
      bankTrialDurationFailureCostMass ring root B L ≤
        (f * n) * bankTrialDurationFailureMass ring root B L ∧
      bankTrialDurationSuccessCostMass ring root B L ≤
        (g * n) * bankTrialProbabilityWinMass ring root B L

/-- Exact requested mass endpoint, UNPROVED: a named Prop. -/
def BankTrialRenewalMassSandwichTarget {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (L lo win den : Nat) : Prop :=
  ∀ (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b),
    BankTrialLocalClean q S →
      ∀ (j T : Nat), (j + 1) * L ≤ T →
        lo ^ j * win * n ^ T ≤
          den ^ (j + 1) *
            bankTrialRenewalPatternMass ring root S T L j

/-- Exact requested absolute-cost endpoint, UNPROVED: a named Prop. -/
def BankTrialRenewalCostSandwichTarget {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (L f g : Nat) : Prop :=
  ∀ (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b),
    BankTrialLocalClean q S →
      ∀ (j T : Nat), (j + 1) * L ≤ T →
        2 ^ (compileAdvice q).K *
          bankTrialRenewalPatternCost ring root S T L j ≤
        n ^ T * (n * (g + j * f))

/-- Pure cleared-integer induction step, on opaque coefficients.
It is NOT the missing physical first-LOST pattern recurrence. -/
private theorem bankTrialRenewalMassOpaqueStep
    (den lo win N j old next : Nat)
    (hprev :
      lo ^ j * win * N ≤ den ^ (j + 1) * old)
    (hrenew : lo * old ≤ den * next) :
    lo ^ (j + 1) * win * N ≤ den ^ (j + 2) * next := by
  have hscaled := Nat.mul_le_mul_left (den ^ (j + 1)) hrenew
  calc
    lo ^ (j + 1) * win * N =
        lo * (lo ^ j * win * N) := by
      rw [Nat.pow_succ]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ lo * (den ^ (j + 1) * old) :=
      Nat.mul_le_mul_left lo hprev
    _ = den ^ (j + 1) * (lo * old) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ den ^ (j + 1) * (den * next) :=
      hscaled
    _ = den ^ (j + 2) * next := by
      have hexp : j + 2 = (j + 1) + 1 := by omega
      rw [hexp, Nat.pow_succ den (j + 1), Nat.pow_succ den j]
      simp only [Nat.mul_assoc]

/-- Add a history of completed losses and elapsed scheduler letters,
without changing the current trial state or its age. -/
def bankTrialRenewalShift {q : Nat}
    (pfx : List Nat) (offset : Nat)
    (z : BankTrialRenewalState q) : BankTrialRenewalState q :=
  { z with failures := pfx ++ z.failures
           elapsed := offset + z.elapsed }

/-- One-letter advance commutes with history shift. -/
theorem bankTrialRenewalAdvanceShift {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (pfx : List Nat) (offset : Nat)
    (z : BankTrialRenewalState q)
    (trial : BankTrialLocalState q) (age : Nat) (e : Fin n) :
    bankTrialRenewalAdvance ring root
        (bankTrialRenewalShift pfx offset z) trial age e =
      bankTrialRenewalShift pfx offset
        (bankTrialRenewalAdvance ring root z trial age e) := by
  by_cases hlost :
      (bankTrialLocalNext ring root trial e).phase = .lost
  · simp [bankTrialRenewalAdvance, bankTrialRenewalShift,
      hlost, List.append_assoc, Nat.add_assoc]
  · simp [bankTrialRenewalAdvance, bankTrialRenewalShift,
      hlost, List.append_assoc, Nat.add_assoc]

/-- The actual next-letter regeneration step commutes with shift,
including the pending-LOST and terminal-WON cases. -/
theorem bankTrialRenewalNextShift {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (pfx : List Nat) (offset : Nat)
    (z : BankTrialRenewalState q) (e : Fin n) :
    bankTrialRenewalNext ring root
        (bankTrialRenewalShift pfx offset z) e =
      bankTrialRenewalShift pfx offset
        (bankTrialRenewalNext ring root z e) := by
  cases hphase : z.observer.phase with
  | won =>
      simp [bankTrialRenewalNext, bankTrialRenewalShift, hphase]
  | lost =>
      simpa only [bankTrialRenewalNext,
        bankTrialRenewalShift, hphase] using
        (bankTrialRenewalAdvanceShift ring root
          pfx offset z
          (bankTrialLocalStart z.observer.bank) 0 e)
  | recovery =>
      simpa only [bankTrialRenewalNext,
        bankTrialRenewalShift, hphase] using
        (bankTrialRenewalAdvanceShift ring root
          pfx offset z z.observer z.age e)
  | live begun =>
      simpa only [bankTrialRenewalNext,
        bankTrialRenewalShift, hphase] using
        (bankTrialRenewalAdvanceShift ring root
          pfx offset z z.observer z.age e)

/-- Shift covariance along any finite original-scheduler word. -/
theorem bankTrialRenewalRunShift {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (pfx : List Nat) (offset : Nat) :
    ∀ (word : List (Fin n)) (z : BankTrialRenewalState q),
      bankTrialRenewalRunFrom ring root word
          (bankTrialRenewalShift pfx offset z) =
        bankTrialRenewalShift pfx offset
          (bankTrialRenewalRunFrom ring root word z) := by
  intro word
  induction word with
  | nil =>
      intro z
      rfl
  | cons e rest ih =>
      intro z
      change
        bankTrialRenewalRunFrom ring root rest
          (bankTrialRenewalNext ring root
            (bankTrialRenewalShift pfx offset z) e) =
        bankTrialRenewalShift pfx offset
          (bankTrialRenewalRunFrom ring root rest
            (bankTrialRenewalNext ring root z e))
      rw [bankTrialRenewalNextShift ring root pfx offset z e]
      exact ih (bankTrialRenewalNext ring root z e)

/-- If the prior observer is LOST, the next scheduler letter
belongs exclusively to the new trial from the stored bank. -/
theorem bankTrialRenewalLostRestartLetter {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankTrialRenewalState q)
    (hlost : z.observer.phase = .lost) :
    bankTrialRenewalNext ring root z e =
      bankTrialRenewalShift z.failures z.elapsed
        (bankTrialRenewalNext ring root
          (bankTrialRenewalStart z.observer.bank) e) := by
  by_cases hnew :
      (bankTrialLocalNext ring root
        (bankTrialLocalStart z.observer.bank) e).phase = .lost
  · simp only [bankTrialLocalStart] at hnew
    simp [bankTrialRenewalNext, bankTrialRenewalAdvance,
      bankTrialRenewalStart, bankTrialRenewalShift, bankTrialLocalStart,
      hlost, hnew, List.append_assoc, Nat.add_assoc]
  · simp only [bankTrialLocalStart] at hnew
    simp [bankTrialRenewalNext, bankTrialRenewalAdvance,
      bankTrialRenewalStart, bankTrialRenewalShift, bankTrialLocalStart,
      hlost, hnew, List.append_assoc, Nat.add_assoc]

/-- Exact suffix restart, for a nonempty suffix. -/
theorem bankTrialRenewalLostRestartSuffix {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (rest : List (Fin n)) (z : BankTrialRenewalState q)
    (hlost : z.observer.phase = .lost) :
    bankTrialRenewalRunFrom ring root (e :: rest) z =
      bankTrialRenewalShift z.failures z.elapsed
        (bankTrialRenewalRun ring root z.observer.bank
          (e :: rest)) := by
  change bankTrialRenewalRunFrom ring root rest
      (bankTrialRenewalNext ring root z e) =
    bankTrialRenewalShift z.failures z.elapsed
      (bankTrialRenewalRunFrom ring root rest
        (bankTrialRenewalNext ring root
          (bankTrialRenewalStart z.observer.bank) e))
  rw [bankTrialRenewalLostRestartLetter ring root e z hlost]
  exact bankTrialRenewalRunShift ring root z.failures
    z.elapsed rest
    (bankTrialRenewalNext ring root
      (bankTrialRenewalStart z.observer.bank) e)

/-- Completed E_j patterns are unchanged by subsequent letters. -/
theorem bankTrialRenewalPatternAppend {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (L j : Nat) (word suffix : List (Fin n))
    (hpattern : bankTrialRenewalPattern ring root S L j word = true) :
    bankTrialRenewalPattern ring root S L j
      (word ++ suffix) = true := by
  have hdec :
      decide
        ((bankTrialRenewalRun ring root S word).observer.phase = .won ∧
         (bankTrialRenewalRun ring root S word).failures.length = j ∧
         (bankTrialRenewalRun ring root S word).failures.all
           (fun age => decide (age ≤ L)) = true ∧
         (bankTrialRenewalRun ring root S word).age ≤ L) = true := by
    simpa only [bankTrialRenewalPattern] using hpattern
  have hp :
      (bankTrialRenewalRun ring root S word).observer.phase = .won :=
    (of_decide_eq_true hdec).1
  have hrun :
      bankTrialRenewalRun ring root S (word ++ suffix) =
        bankTrialRenewalRun ring root S word := by
    unfold bankTrialRenewalRun
    rw [bankTrialRenewalRunFromAppend]
    exact bankTrialRenewalRunFromWon ring root suffix
      (bankTrialRenewalRunFrom ring root word
        (bankTrialRenewalStart S)) hp
  simpa only [bankTrialRenewalPattern, hrun] using hpattern

/-- Every enumerated first-LOST pfx is an actual LOST state. -/
theorem bankTrialRenewalFirstLostCutSound {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (T : Nat) (cut : List (Fin n))
    (hcut : cut ∈ Prob.firstStoppedPrefixes
      (bankTrialLocalNext ring root)
      bankTrialRenewalFirstLostStop T [] (bankTrialLocalStart S)) :
    (bankTrialLocalRun ring root cut
      (bankTrialLocalStart S)).phase = .lost := by
  have hs := bankTrialSuccessStoppedPrefixesSound
    (bankTrialLocalNext ring root) bankTrialRenewalFirstLostStop
    T [] (bankTrialLocalStart S) cut hcut
  change decide
    ((Prob.stoppedTapeRun (bankTrialLocalNext ring root)
      cut (bankTrialLocalStart S)).phase = .lost) = true at hs
  have hphase := of_decide_eq_true hs
  rw [bankTrialSuccessStoppedRunEqLocal ring root cut
    (bankTrialLocalStart S)] at hphase
  exact hphase

/-- Finite first-LOST cutoff kernel, with the next-trial weight
depending on the bank stored at the first LOST cut. -/
theorem bankTrialRenewalFirstLostCutoffKernel {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (F : GrantBankReference.BankLocalReference
      (compileAdvice q).b → List (Fin n) → Nat)
    (T L : Nat) :
    Prob.scheduleSum n T (fun word =>
      bankTrialSuccessNatStoppedWord
        (bankTrialLocalNext ring root)
        bankTrialRenewalFirstLostStop
        (fun cut z _ suffix =>
          if cut.length ≤ L then F z.bank suffix else 0)
        T [] (bankTrialLocalStart S) word) =
      ((Prob.firstStoppedPrefixes
        (bankTrialLocalNext ring root)
        bankTrialRenewalFirstLostStop T [] (bankTrialLocalStart S)).map
        (fun cut =>
          Prob.scheduleSum n (T - cut.length) (fun suffix =>
            if cut.length ≤ L then
              F (bankTrialLocalRun ring root cut
                (bankTrialLocalStart S)).bank suffix
            else 0))).sum := by
  exact bankTrialRenewalFirstLostFactor ring root S
    (fun cut z suffix =>
      if cut.length ≤ L then F z.bank suffix else 0) T

end L3


namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
G13-INDEX-RENEWAL: first-LOST scanner bridge.

At the first LOST cut the scanner has *not yet restarted*.
Its age equals cut.length, rather than zero. The following letter
starts a new trial with age zero, as prescribed by bankTrialRenewalNext.

All words use the original Fin n scheduler. No totality theorem or
hypothetical terminal-time conditioning is invoked.
-/

/-- Before a single trial ends, the regenerative and single-trial
steps agree. At its very first LOST letter the scanner appends exactly
the elapsed trial length. -/
private theorem bankTrialRenewalBeforeLossStep {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (k : Nat) (x : BankTrialLocalState q) (e : Fin n)
    (hwon : x.phase ≠ .won) (hlost : x.phase ≠ .lost) :
    bankTrialRenewalNext ring root
        ({ observer := x, failures := [], age := k, elapsed := k } :
          BankTrialRenewalState q) e =
      if (bankTrialLocalNext ring root x e).phase = .lost then
        { observer := bankTrialLocalNext ring root x e
          failures := [k + 1]
          age := k + 1
          elapsed := k + 1 }
      else
        { observer := bankTrialLocalNext ring root x e
          failures := []
          age := k + 1
          elapsed := k + 1 } := by
  cases hp : x.phase with
  | won => exact False.elim (hwon hp)
  | lost => exact False.elim (hlost hp)
  | recovery =>
      simp [bankTrialRenewalNext, bankTrialRenewalAdvance, hp]
  | live begun =>
      simp [bankTrialRenewalNext, bankTrialRenewalAdvance, hp]

/-- Coupling from an arbitrary already-exposed pfx. The scanner
is initialized with its spent-clock length, but no previous failure.
Membership in firstStoppedPrefixes supplies exactly the *first*
LOST cut, excluding an earlier WON or LOST along the selected cut. -/
private theorem bankTrialRenewalFirstLostPrefixCouple {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (T : Nat) (pre : List (Fin n))
      (x : BankTrialLocalState q) (cut : List (Fin n)),
      x.phase ≠ .won →
      x.phase ≠ .lost →
      cut ∈ Prob.firstStoppedPrefixes
        (bankTrialLocalNext ring root)
        bankTrialRenewalFirstLostStop T pre x →
      bankTrialRenewalRunFrom ring root cut
          ({ observer := x, failures := [], age := pre.length,
             elapsed := pre.length } : BankTrialRenewalState q) =
        { observer := bankTrialLocalRun ring root cut x
          failures := [(pre ++ cut).length]
          age := (pre ++ cut).length
          elapsed := (pre ++ cut).length } := by
  intro T
  induction T with
  | zero =>
      intro pre x cut hwon hlost hcut
      have hs : bankTrialRenewalFirstLostStop pre x = false := by
        simp [bankTrialRenewalFirstLostStop, hlost]
      simp [Prob.firstStoppedPrefixes, hs] at hcut
  | succ t ih =>
      intro pre x cut hwon hlost hcut
      have hs : bankTrialRenewalFirstLostStop pre x = false := by
        simp [bankTrialRenewalFirstLostStop, hlost]
      have hm :
          cut ∈ (List.ofFn (fun e : Fin n => e)).flatMap
            (fun e =>
              (Prob.firstStoppedPrefixes
                (bankTrialLocalNext ring root)
                bankTrialRenewalFirstLostStop t
                (pre ++ [e]) (bankTrialLocalNext ring root x e)).map
                (List.cons e)) := by
        simpa only [Prob.firstStoppedPrefixes, hs,
          Bool.false_eq_true, if_false] using hcut
      obtain ⟨e, _, he⟩ := List.mem_flatMap.mp hm
      obtain ⟨tail, htail, hcutEq⟩ := List.mem_map.mp he
      subst cut
      have hstep := bankTrialRenewalBeforeLossStep
        ring root pre.length x e hwon hlost
      by_cases hnewLost :
          (bankTrialLocalNext ring root x e).phase = .lost
      · have hnextStop :
            bankTrialRenewalFirstLostStop (pre ++ [e])
              (bankTrialLocalNext ring root x e) = true := by
          simp [bankTrialRenewalFirstLostStop, hnewLost]
        have hnil : tail = [] := by
          cases t <;> simpa [Prob.firstStoppedPrefixes, hnextStop] using htail
        subst tail
        change bankTrialRenewalNext ring root
            ({ observer := x, failures := [], age := pre.length,
               elapsed := pre.length } : BankTrialRenewalState q) e =
          ({ observer := bankTrialLocalNext ring root x e
             failures := [(pre ++ [e]).length]
             age := (pre ++ [e]).length
             elapsed := (pre ++ [e]).length } :
            BankTrialRenewalState q)
        rw [hstep, if_pos hnewLost]
        simp
      · by_cases hnewWon :
            (bankTrialLocalNext ring root x e).phase = .won
        · have hsound := bankTrialSuccessStoppedPrefixesSound
            (bankTrialLocalNext ring root)
            bankTrialRenewalFirstLostStop t (pre ++ [e])
            (bankTrialLocalNext ring root x e) tail htail
          change decide
            ((Prob.stoppedTapeRun (bankTrialLocalNext ring root) tail
              (bankTrialLocalNext ring root x e)).phase = .lost) = true
            at hsound
          have hterminal : bankTrialLocalTerminal
              (bankTrialLocalNext ring root x e) := Or.inl hnewWon
          rw [bankTrialSuccessStoppedRunEqLocal
            ring root tail (bankTrialLocalNext ring root x e),
            bankTrialLocalRunTerminalAbsorbs
              ring root tail (bankTrialLocalNext ring root x e)
              hterminal] at hsound
          have hbad := of_decide_eq_true hsound
          rw [hnewWon] at hbad
          cases hbad
        · have hchild := ih (pre ++ [e])
            (bankTrialLocalNext ring root x e) tail
            hnewWon hnewLost htail
          change bankTrialRenewalRunFrom ring root tail
              (bankTrialRenewalNext ring root
                ({ observer := x, failures := [], age := pre.length,
                   elapsed := pre.length } : BankTrialRenewalState q) e) =
            ({ observer := bankTrialLocalRun ring root (e :: tail) x
               failures := [(pre ++ (e :: tail)).length]
               age := (pre ++ (e :: tail)).length
               elapsed := (pre ++ (e :: tail)).length } :
              BankTrialRenewalState q)
          rw [hstep, if_neg hnewLost]
          simpa only [bankTrialLocalRun, List.append_assoc,
            List.singleton_append, List.length_append,
            List.length_singleton, Nat.add_zero] using hchild

/-- (s1) The actual first-LOST stopped pfx is one and only one
completed failure. Under the earlier precise state representation, its
age is the first-hit length (not zero); restart is pending. -/
theorem bankTrialRenewalFirstLostScanner {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (T : Nat) (cut : List (Fin n))
    (hcut : cut ∈ Prob.firstStoppedPrefixes
      (bankTrialLocalNext ring root)
      bankTrialRenewalFirstLostStop T [] (bankTrialLocalStart S)) :
    bankTrialRenewalRun ring root S cut =
      { observer := bankTrialLocalRun ring root cut
          (bankTrialLocalStart S)
        failures := [cut.length]
        age := cut.length
        elapsed := cut.length } := by
  have hnowon : (bankTrialLocalStart S).phase ≠ .won := by
    intro h
    cases h
  have hnolost : (bankTrialLocalStart S).phase ≠ .lost := by
    intro h
    cases h
  have hmain := bankTrialRenewalFirstLostPrefixCouple
    ring root T [] (bankTrialLocalStart S) cut
    hnowon hnolost hcut
  simpa only [bankTrialRenewalRun, bankTrialRenewalStart,
    List.nil_append, List.length_nil] using hmain

/-- The LOST suffix shift, now specialized to an enumerated
first-LOST cut. The suffix must be nonempty, since its first letter
is the first service of the regenerated trial. -/
theorem bankTrialRenewalFirstLostScannerSuffix {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (T : Nat) (cut : List (Fin n))
    (hcut : cut ∈ Prob.firstStoppedPrefixes
      (bankTrialLocalNext ring root)
      bankTrialRenewalFirstLostStop T [] (bankTrialLocalStart S))
    (e : Fin n) (rest : List (Fin n)) :
    bankTrialRenewalRun ring root S (cut ++ (e :: rest)) =
      bankTrialRenewalShift [cut.length] cut.length
        (bankTrialRenewalRun ring root
          (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)).bank (e :: rest)) := by
  have hfirst :=
    bankTrialRenewalFirstLostScanner ring root S T cut hcut
  have hlost :=
    bankTrialRenewalFirstLostCutSound ring root S T cut hcut
  unfold bankTrialRenewalRun
  rw [bankTrialRenewalRunFromAppend]
  change bankTrialRenewalRunFrom ring root (e :: rest)
      (bankTrialRenewalRun ring root S cut) =
    bankTrialRenewalShift [cut.length] cut.length
      (bankTrialRenewalRun ring root
        (bankTrialLocalRun ring root cut
          (bankTrialLocalStart S)).bank (e :: rest))
  rw [hfirst]
  exact bankTrialRenewalLostRestartSuffix ring root e rest
    ({ observer := bankTrialLocalRun ring root cut
        (bankTrialLocalStart S)
       failures := [cut.length]
       age := cut.length
       elapsed := cut.length } : BankTrialRenewalState q) hlost

/-- If a non-LOST local state takes a transition to LOST, the
resulting stored bank is Clean. This is exactly the LIVE or
RECOVERY loss row; terminal states do not forge new losses. -/
private theorem bankTrialRenewalNextLostBankClean {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankTrialLocalState q) (e : Fin n)
    (hnot : z.phase ≠ .lost)
    (hlost : (bankTrialLocalNext ring root z e).phase = .lost) :
    BankTrialLocalClean q (bankTrialLocalNext ring root z e).bank := by
  cases z with
  | mk B phase =>
      cases phase with
      | lost =>
          exact False.elim (hnot rfl)
      | won =>
          have hterm : bankTrialLocalTerminal
              (⟨B, .won⟩ : BankTrialLocalState q) := Or.inl rfl
          have heq := bankTrialLocalTerminalAbsorbs ring root e
            (⟨B, .won⟩ : BankTrialLocalState q) hterm
          rw [heq] at hlost
          cases hlost
      | live begun =>
          have hwit := bankTrialLocalLiveLossWitness
            ring root e B begun hlost
          have hguard :
              BankTrialLocalClean q
                  (GrantBankReference.bankLocalReferenceStepClamped
                    ring root B e) ∧
                (begun = true ∨ e = root ∨
                  ring.rightNeighbor e = root) :=
            ⟨hwit.2.1, hwit.2.2⟩
          have heq :
              bankTrialLocalNext ring root
                  (⟨B, .live begun⟩ : BankTrialLocalState q) e =
                ⟨GrantBankReference.bankLocalReferenceStepClamped
                  ring root B e, .lost⟩ := by
            simp [bankTrialLocalNext, hwit.1, hguard]
          rw [heq]
          exact hwit.2.1
      | recovery =>
          by_cases hc : BankTrialLocalClean q
              (GrantBankReference.bankLocalReferenceStepClamped
                ring root B e)
          · have heq := bankTrialLocalRecoveryCleanLoss
              ring root e B hc
            rw [heq]
            exact hc
          · by_cases hs :
                (GrantBankReference.bankLocalReferenceStepClamped
                  ring root B e).success = true
            · have hwin :
                (bankTrialLocalNext ring root
                  (⟨B, .recovery⟩ : BankTrialLocalState q) e).phase =
                    .won := by
                simp [bankTrialLocalNext, hs]
              rw [hwin] at hlost
              cases hlost
            · have hstay :
                (bankTrialLocalNext ring root
                  (⟨B, .recovery⟩ : BankTrialLocalState q) e).phase =
                    .recovery := by
                simp [bankTrialLocalNext, hs, hc]
              rw [hstay] at hlost
              cases hlost

/-- Cleanliness of the bank at an arbitrary LOST terminal endpoint.
This is a finite-word induction; absorption covers later padding. -/
private theorem bankTrialRenewalLocalRunLostClean {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (word : List (Fin n)) (z : BankTrialLocalState q),
      z.phase ≠ .lost →
      (bankTrialLocalRun ring root word z).phase = .lost →
      BankTrialLocalClean q
        (bankTrialLocalRun ring root word z).bank := by
  intro word
  induction word with
  | nil =>
      intro z hnot hlost
      exact False.elim (hnot hlost)
  | cons e rest ih =>
      intro z hnot hlost
      by_cases he :
          (bankTrialLocalNext ring root z e).phase = .lost
      · have hc := bankTrialRenewalNextLostBankClean
          ring root z e hnot he
        have hterminal : bankTrialLocalTerminal
            (bankTrialLocalNext ring root z e) := Or.inr he
        have hfreeze := bankTrialLocalRunTerminalAbsorbs
          ring root rest (bankTrialLocalNext ring root z e) hterminal
        change BankTrialLocalClean q
          (bankTrialLocalRun ring root rest
            (bankTrialLocalNext ring root z e)).bank
        rw [hfreeze]
        exact hc
      · change (bankTrialLocalRun ring root rest
          (bankTrialLocalNext ring root z e)).phase = .lost at hlost
        change BankTrialLocalClean q
          (bankTrialLocalRun ring root rest
            (bankTrialLocalNext ring root z e)).bank
        exact ih (bankTrialLocalNext ring root z e) he hlost

/-- The postservice bank at each authenticated first-LOST cut is
Clean, so the uniform completed-mass/cost hypotheses apply
to it without adding a new statistical assumption. -/
theorem bankTrialRenewalFirstLostCutClean {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (T : Nat) (cut : List (Fin n))
    (hcut : cut ∈ Prob.firstStoppedPrefixes
      (bankTrialLocalNext ring root)
      bankTrialRenewalFirstLostStop T [] (bankTrialLocalStart S)) :
    BankTrialLocalClean q
      (bankTrialLocalRun ring root cut
        (bankTrialLocalStart S)).bank := by
  have hnot : (bankTrialLocalStart S).phase ≠ .lost := by
    intro h
    cases h
  exact bankTrialRenewalLocalRunLostClean ring root cut
    (bankTrialLocalStart S) hnot
    (bankTrialRenewalFirstLostCutSound ring root S T cut hcut)

/-- A bounded first LOST contributes exactly one failure to the
full pattern. After its first following scheduler letter, the
remaining index is j, and the new local bank is the stored Clean
bank. This is the crucial wordwise Markov bridge. -/
theorem bankTrialRenewalPatternFirstLostSuffix {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (T L j : Nat) (cut : List (Fin n))
    (hcut : cut ∈ Prob.firstStoppedPrefixes
      (bankTrialLocalNext ring root)
      bankTrialRenewalFirstLostStop T [] (bankTrialLocalStart S))
    (hbound : cut.length ≤ L)
    (e : Fin n) (rest : List (Fin n)) :
    bankTrialRenewalPattern ring root S L (j + 1)
        (cut ++ (e :: rest)) =
      bankTrialRenewalPattern ring root
        (bankTrialLocalRun ring root cut
          (bankTrialLocalStart S)).bank L j (e :: rest) := by
  have hrun := bankTrialRenewalFirstLostScannerSuffix
    ring root S T cut hcut e rest
  have hbool : decide (cut.length ≤ L) = true :=
    decide_eq_true hbound
  unfold bankTrialRenewalPattern
  rw [hrun]
  simp [bankTrialRenewalShift, hbool, List.all_cons,
]

/-- Absolute elapsed-time charge at a bounded first LOST:
initial cost cut.length plus the successful suffix charge. -/
theorem bankTrialRenewalTauFirstLostSuffix {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (T L j : Nat) (cut : List (Fin n))
    (hcut : cut ∈ Prob.firstStoppedPrefixes
      (bankTrialLocalNext ring root)
      bankTrialRenewalFirstLostStop T [] (bankTrialLocalStart S))
    (hbound : cut.length ≤ L)
    (e : Fin n) (rest : List (Fin n)) :
    bankTrialRenewalTau ring root S L (j + 1)
        (cut ++ (e :: rest)) =
      if bankTrialRenewalPattern ring root
          (bankTrialLocalRun ring root cut
            (bankTrialLocalStart S)).bank L j (e :: rest) then
        cut.length +
          bankTrialRenewalTau ring root
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)).bank L j (e :: rest)
      else 0 := by
  have hpat := bankTrialRenewalPatternFirstLostSuffix
    ring root S T L j cut hcut hbound e rest
  have hrun := bankTrialRenewalFirstLostScannerSuffix
    ring root S T cut hcut e rest
  unfold bankTrialRenewalTau
  rw [hpat]
  cases hp : bankTrialRenewalPattern ring root
      (bankTrialLocalRun ring root cut
        (bankTrialLocalStart S)).bank L j (e :: rest) with
  | false =>
      simp [hp]
  | true =>
      simp [hp, hrun, bankTrialRenewalShift]

end L3


namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
G13-INDEX-RENEWAL: first-LOST *whole-word* indicator.
The auxiliary scanner adds an already-consumed pfx length to
the currently running trial; if the single-trial observer has just
reached LOST, it carries one recorded failure.  This matches the
scanner until and at the first LOST cut.  No new probabilistic
or terminal-time assumption is made.
-/

/-- The finite first-LOST coupling carrier. -/
def bankTrialRenewalCoupled {n q : Nat}
    (pre : List (Fin n)) (x : BankTrialLocalState q) :
    BankTrialRenewalState q :=
  if x.phase = .lost then
    { observer := x
      failures := [pre.length]
      age := pre.length
      elapsed := pre.length }
  else
    { observer := x
      failures := []
      age := pre.length
      elapsed := pre.length }

/-- A pattern evaluated from an arbitrary regenerative scanner state
rather than from a new Clean start. -/
noncomputable def bankTrialRenewalPatternFrom {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : BankTrialRenewalState q)
    (L j : Nat) (word : List (Fin n)) : Bool :=
  decide
    ((bankTrialRenewalRunFrom ring root word z).observer.phase = .won ∧
     (bankTrialRenewalRunFrom ring root word z).failures.length = j ∧
     (bankTrialRenewalRunFrom ring root word z).failures.all
       (fun age => decide (age ≤ L)) = true ∧
     (bankTrialRenewalRunFrom ring root word z).age ≤ L)

/-- The auxiliary pattern is exactly the earlier pattern at an ordinary
Clean start. -/
theorem bankTrialRenewalPatternFromStart {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (L j : Nat) (word : List (Fin n)) :
    bankTrialRenewalPatternFrom ring root
      (bankTrialRenewalStart S) L j word =
        bankTrialRenewalPattern ring root S L j word := by
  rfl

/-- A nonterminal letter advances the coupled scanner exactly
once, and transports the consumed pfx to pre ++ [e]. -/
private theorem bankTrialRenewalCoupledNext {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (pre : List (Fin n)) (x : BankTrialLocalState q)
    (hwon : x.phase ≠ .won) (hlost : x.phase ≠ .lost) :
    bankTrialRenewalNext ring root (bankTrialRenewalCoupled pre x) e =
      bankTrialRenewalCoupled (pre ++ [e])
        (bankTrialLocalNext ring root x e) := by
  cases hp : x.phase with
  | won =>
      exact False.elim (hwon hp)
  | lost =>
      exact False.elim (hlost hp)
  | recovery =>
      by_cases hnew :
          (bankTrialLocalNext ring root x e).phase = .lost
      · simp [bankTrialRenewalCoupled, bankTrialRenewalNext,
          bankTrialRenewalAdvance, hp, hnew, List.length_append]
      · simp [bankTrialRenewalCoupled, bankTrialRenewalNext,
          bankTrialRenewalAdvance, hp, hnew, List.length_append]
  | live begun =>
      by_cases hnew :
          (bankTrialLocalNext ring root x e).phase = .lost
      · simp [bankTrialRenewalCoupled, bankTrialRenewalNext,
          bankTrialRenewalAdvance, hp, hnew, List.length_append]
      · simp [bankTrialRenewalCoupled, bankTrialRenewalNext,
          bankTrialRenewalAdvance, hp, hnew, List.length_append]

/-- At zero remaining letters the coupled scanner cannot already
satisfy a pattern with at least one completed failure *and* WON:
LOST is not WON and a non-LOST carrier has an empty failure list. -/
private theorem bankTrialRenewalCoupledNil {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (pre : List (Fin n)) (x : BankTrialLocalState q)
    (L j : Nat) :
    bankTrialRenewalPatternFrom ring root
      (bankTrialRenewalCoupled pre x) L (j + 1) [] = false := by
  cases hp : x.phase with
  | won =>
      simp [bankTrialRenewalPatternFrom, bankTrialRenewalCoupled,
        bankTrialRenewalRunFrom, hp]
  | lost =>
      simp [bankTrialRenewalPatternFrom, bankTrialRenewalCoupled,
        bankTrialRenewalRunFrom, hp]
  | recovery =>
      simp [bankTrialRenewalPatternFrom, bankTrialRenewalCoupled,
        bankTrialRenewalRunFrom, hp]
  | live begun =>
      simp [bankTrialRenewalPatternFrom, bankTrialRenewalCoupled,
        bankTrialRenewalRunFrom, hp]

/-- A coupled observer already at WON cannot acquire a prior LOST
record, even after an arbitrary continuation. -/
private theorem bankTrialRenewalCoupledWonZero {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (pre : List (Fin n)) (x : BankTrialLocalState q)
    (L j : Nat) (word : List (Fin n))
    (hwon : x.phase = .won) :
    Prob.indicator (bankTrialRenewalPatternFrom ring root
      (bankTrialRenewalCoupled pre x) L (j + 1) word) = 0 := by
  have hphase :
      (bankTrialRenewalCoupled pre x).observer.phase = .won := by
    simp [bankTrialRenewalCoupled, hwon]
  have hrun := bankTrialRenewalRunFromWon ring root word
    (bankTrialRenewalCoupled pre x) hphase
  unfold bankTrialRenewalPatternFrom
  rw [hrun]
  simp [bankTrialRenewalCoupled, hwon, Prob.indicator]

/-- The observation at the first LOST cut is precisely the pattern
of the fresh Clean bank on the untouched suffix, unless the first
LOST duration exceeds L.  The empty suffix is handled separately
because the first trial has not yet restarted. -/
private theorem bankTrialRenewalCoupledLostEvent {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (pre : List (Fin n)) (x : BankTrialLocalState q)
    (L j : Nat) (word : List (Fin n))
    (hlost : x.phase = .lost) :
    Prob.indicator (bankTrialRenewalPatternFrom ring root
        (bankTrialRenewalCoupled pre x) L (j + 1) word) =
      if pre.length ≤ L then
        Prob.indicator (bankTrialRenewalPattern
          ring root x.bank L j word)
      else 0 := by
  cases word with
  | nil =>
      simp [bankTrialRenewalPatternFrom, bankTrialRenewalCoupled,
        bankTrialRenewalPattern, bankTrialRenewalRun,
        bankTrialRenewalRunFrom, bankTrialRenewalStart,
        hlost, bankTrialLocalStart, Prob.indicator]
  | cons e tail =>
      have hcoupled :
          bankTrialRenewalCoupled pre x =
            { observer := x
              failures := [pre.length]
              age := pre.length
              elapsed := pre.length } := by
        simp [bankTrialRenewalCoupled, hlost]
      have hrun :
          bankTrialRenewalRunFrom ring root (e :: tail)
            (bankTrialRenewalCoupled pre x) =
          bankTrialRenewalShift [pre.length] pre.length
            (bankTrialRenewalRun ring root x.bank (e :: tail)) := by
        rw [hcoupled]
        exact bankTrialRenewalLostRestartSuffix ring root e tail
          { observer := x
            failures := [pre.length]
            age := pre.length
            elapsed := pre.length } hlost
      unfold bankTrialRenewalPatternFrom
      rw [hrun]
      unfold bankTrialRenewalPattern
      by_cases hcut : pre.length ≤ L
      · simp [bankTrialRenewalShift, hcut,
          List.all_cons, Prob.indicator]
      · simp [bankTrialRenewalShift, hcut,
          List.all_cons, Prob.indicator]

/-- The generic original-word recursion: an index-(j+1) pattern
from a coupled current state is sampled exactly at the *first*
LOST stopping cut, then tested as index j on the remaining word.
Every intermediate pfx and all untouched letters are retained. -/
private theorem bankTrialRenewalWholeEventCoupled {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (L j : Nat) :
    ∀ (word pre : List (Fin n)) (x : BankTrialLocalState q)
      (T : Nat),
      Prob.indicator
          (bankTrialRenewalPatternFrom ring root
            (bankTrialRenewalCoupled pre x) L (j + 1) word) =
        bankTrialSuccessNatStoppedWord
          (bankTrialLocalNext ring root)
          bankTrialRenewalFirstLostStop
          (fun cut z _ suffix =>
            if cut.length ≤ L then
              Prob.indicator (bankTrialRenewalPattern
                ring root z.bank L j suffix)
            else 0)
          T pre x word := by
  intro word
  induction word with
  | nil =>
      intro pre x T
      have hleft := bankTrialRenewalCoupledNil
        ring root pre x L j
      by_cases hlost : x.phase = .lost
      · have hright :
            bankTrialRenewalPattern ring root x.bank L j [] =
              false := by
          simp [bankTrialRenewalPattern, bankTrialRenewalRun,
            bankTrialRenewalStart, bankTrialRenewalRunFrom, bankTrialLocalStart]
        simp [bankTrialSuccessNatStoppedWord,
          bankTrialRenewalFirstLostStop, hlost,
          hleft, hright, Prob.indicator]
      · simp [bankTrialSuccessNatStoppedWord,
          bankTrialRenewalFirstLostStop, hlost,
          hleft, Prob.indicator]
  | cons e tail ih =>
      intro pre x T
      by_cases hlost : x.phase = .lost
      · have hl := bankTrialRenewalCoupledLostEvent
          ring root pre x L j (e :: tail) hlost
        simpa [bankTrialSuccessNatStoppedWord,
          bankTrialRenewalFirstLostStop, hlost] using hl
      · by_cases hwon : x.phase = .won
        · have hterm : bankTrialLocalTerminal x := Or.inl hwon
          have heq := bankTrialLocalTerminalAbsorbs
            ring root e x hterm
          have hleft := bankTrialRenewalCoupledWonZero
            ring root pre x L j (e :: tail) hwon
          have hright := bankTrialRenewalCoupledWonZero
            ring root (pre ++ [e]) x L j tail hwon
          have hchild := ih (pre ++ [e]) x (T - 1)
          calc
            Prob.indicator
                (bankTrialRenewalPatternFrom ring root
                  (bankTrialRenewalCoupled pre x) L (j + 1)
                  (e :: tail)) = 0 := hleft
            _ = Prob.indicator
                (bankTrialRenewalPatternFrom ring root
                  (bankTrialRenewalCoupled (pre ++ [e]) x)
                  L (j + 1) tail) := hright.symm
            _ = bankTrialSuccessNatStoppedWord
                  (bankTrialLocalNext ring root)
                  bankTrialRenewalFirstLostStop
                  (fun cut z _ suffix =>
                    if cut.length ≤ L then
                      Prob.indicator (bankTrialRenewalPattern
                        ring root z.bank L j suffix)
                    else 0)
                  (T - 1) (pre ++ [e]) x tail := hchild
            _ = bankTrialSuccessNatStoppedWord
                  (bankTrialLocalNext ring root)
                  bankTrialRenewalFirstLostStop
                  (fun cut z _ suffix =>
                    if cut.length ≤ L then
                      Prob.indicator (bankTrialRenewalPattern
                        ring root z.bank L j suffix)
                    else 0)
                  T pre x (e :: tail) := by
                    simp [bankTrialSuccessNatStoppedWord,
                      bankTrialRenewalFirstLostStop, hlost, heq]
        · have hstep := bankTrialRenewalCoupledNext
            ring root e pre x hwon hlost
          have hchild := ih (pre ++ [e])
            (bankTrialLocalNext ring root x e) (T - 1)
          calc
            Prob.indicator
                (bankTrialRenewalPatternFrom ring root
                  (bankTrialRenewalCoupled pre x) L (j + 1)
                  (e :: tail)) =
              Prob.indicator
                (bankTrialRenewalPatternFrom ring root
                  (bankTrialRenewalNext ring root
                    (bankTrialRenewalCoupled pre x) e)
                  L (j + 1) tail) := by
                    rfl
            _ = Prob.indicator
                (bankTrialRenewalPatternFrom ring root
                  (bankTrialRenewalCoupled (pre ++ [e])
                    (bankTrialLocalNext ring root x e))
                  L (j + 1) tail) := by
                    rw [hstep]
            _ = bankTrialSuccessNatStoppedWord
                  (bankTrialLocalNext ring root)
                  bankTrialRenewalFirstLostStop
                  (fun cut z _ suffix =>
                    if cut.length ≤ L then
                      Prob.indicator (bankTrialRenewalPattern
                        ring root z.bank L j suffix)
                    else 0)
                  (T - 1) (pre ++ [e])
                    (bankTrialLocalNext ring root x e) tail := hchild
            _ = bankTrialSuccessNatStoppedWord
                  (bankTrialLocalNext ring root)
                  bankTrialRenewalFirstLostStop
                  (fun cut z _ suffix =>
                    if cut.length ≤ L then
                      Prob.indicator (bankTrialRenewalPattern
                        ring root z.bank L j suffix)
                    else 0)
                  T pre x (e :: tail) := by
                    simp [bankTrialSuccessNatStoppedWord,
                      bankTrialRenewalFirstLostStop, hlost]

/-- The index-(j+1) E-pattern is exactly the first-LOST stopped
Nat observer on one common length-T original scheduler word.
This is a whole-event statement, not merely a cut-level suffix
equation. -/
theorem bankTrialRenewalWholeEvent {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (T L j : Nat) (word : List (Fin n)) :
    Prob.indicator (bankTrialRenewalPattern
      ring root S L (j + 1) word) =
      bankTrialSuccessNatStoppedWord
        (bankTrialLocalNext ring root)
        bankTrialRenewalFirstLostStop
        (fun cut z _ suffix =>
          if cut.length ≤ L then
            Prob.indicator
              (bankTrialRenewalPattern ring root z.bank L j suffix)
          else 0)
        T [] (bankTrialLocalStart S) word := by
  have h := bankTrialRenewalWholeEventCoupled
    ring root L j word [] (bankTrialLocalStart S) T
  simpa [bankTrialRenewalCoupled,
    bankTrialRenewalPatternFrom,
    bankTrialRenewalPattern, bankTrialRenewalRun,
    bankTrialRenewalStart, bankTrialLocalStart] using h

/-- Finite first-LOST identity for the actual index-(j+1)
mass, obtained from the whole-word indicator and the established
Nat first-stop factorization. -/
theorem bankTrialRenewalMassFirstLostExact {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T L j : Nat) :
    bankTrialRenewalPatternMass ring root S T L (j + 1) =
      ((Prob.firstStoppedPrefixes
        (bankTrialLocalNext ring root)
        bankTrialRenewalFirstLostStop T [] (bankTrialLocalStart S)).map
        (fun cut =>
          Prob.scheduleSum n (T - cut.length) (fun suffix =>
            if cut.length ≤ L then
              Prob.indicator (bankTrialRenewalPattern
                ring root (bankTrialLocalRun ring root cut
                  (bankTrialLocalStart S)).bank L j suffix)
            else 0))).sum := by
  have hfun :
      (fun word : List (Fin n) =>
        Prob.indicator
          (bankTrialRenewalPattern ring root S L (j + 1) word)) =
      (fun word : List (Fin n) =>
        bankTrialSuccessNatStoppedWord
          (bankTrialLocalNext ring root)
          bankTrialRenewalFirstLostStop
          (fun cut z _ suffix =>
            if cut.length ≤ L then
              Prob.indicator (bankTrialRenewalPattern
                ring root z.bank L j suffix)
            else 0)
          T [] (bankTrialLocalStart S) word) := by
    funext word
    exact bankTrialRenewalWholeEvent ring root S T L j word
  unfold bankTrialRenewalPatternMass
  rw [hfun]
  exact bankTrialRenewalFirstLostFactor ring root S
    (fun cut z suffix =>
      if cut.length ≤ L then
        Prob.indicator (bankTrialRenewalPattern
          ring root z.bank L j suffix)
      else 0) T

end L3


namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- The denominator-free first-LOST cylinder count restricted to
cuts of length at most L.  The if-filter uses exactly the cut list
and cutoff predicate in bankTrialRenewalMassFirstLostExact. -/
noncomputable def bankTrialRenewalLostBoundedExtensionMass
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T L : Nat) : Nat :=
  ((Prob.firstStoppedPrefixes
      (bankTrialLocalNext ring root)
      bankTrialRenewalFirstLostStop T []
      (bankTrialLocalStart S)).map
    (fun cut =>
      if cut.length ≤ L then n ^ (T - cut.length) else 0)).sum

/-- (W) Uniform one-trial WON-by-L lower bound, measured on
the length-T original scheduler and the index-zero pattern. -/
def BankTrialRenewalWonWithinBound {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (L win den : Nat) : Prop :=
  ∀ (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b),
    BankTrialLocalClean q S →
    ∀ (T : Nat), L ≤ T →
      win * n ^ T ≤
        den * bankTrialRenewalPatternMass ring root S T L 0

/-- (F) Uniform one-trial first-LOST-by-L lower bound.  The
cutoff is inside the finite mapped sum, matching the if branch
of bankTrialRenewalMassFirstLostExact exactly. -/
def BankTrialRenewalLostWithinBound {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (L lo den : Nat) : Prop :=
  ∀ (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b),
    BankTrialLocalClean q S →
    ∀ (T : Nat), L ≤ T →
      lo * n ^ T ≤
        den * bankTrialRenewalLostBoundedExtensionMass
          ring root S T L

/-- Multiply pointwise cleared inequalities over a finite list.
No Finset or auxiliary probability assumption is involved. -/
private theorem bankTrialRenewalMapSumScale
    {A : Type} (a b : Nat) (xs : List A)
    (f g : A → Nat) :
    (∀ x, x ∈ xs → a * f x ≤ b * g x) →
      a * (xs.map f).sum ≤ b * (xs.map g).sum := by
  induction xs with
  | nil =>
      intro _
      simp
  | cons x xs ih =>
      intro h
      have hx : a * f x ≤ b * g x := h x (by simp)
      have ht : a * (xs.map f).sum ≤
          b * (xs.map g).sum := by
        apply ih
        intro y hy
        exact h y (by simp [hy])
      simpa only [List.map_cons, List.sum_cons, Nat.mul_add] using
        (Nat.add_le_add hx ht)

/-- Compose the first-LOST extension bound with the sum of all
restarted suffix bounds.  The opaque arithmetic step is reused
with exponent index zero and the suffix coefficient as its lo. -/
private theorem bankTrialRenewalMassCutCompose
    (den lo win N j cutMass nextMass : Nat)
    (hcut : lo * N ≤ den * cutMass)
    (hnext : lo ^ j * win * cutMass ≤
      den ^ (j + 1) * nextMass) :
    lo ^ (j + 1) * win * N ≤
      den ^ (j + 2) * nextMass := by
  have hprev :
      (lo ^ j * win) ^ 0 * lo * N ≤
        den ^ (0 + 1) * cutMass := by
    simpa only [Nat.pow_zero, Nat.pow_one,
      Nat.one_mul, Nat.zero_add] using hcut
  have hrenew :
      (lo ^ j * win) * cutMass ≤
        den * (den ^ j * nextMass) := by
    calc
      _ ≤ den ^ (j + 1) * nextMass := hnext
      _ = den * (den ^ j * nextMass) := by
        rw [Nat.pow_succ den j]
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hstage :
      (lo ^ j * win) * lo * N ≤
        den ^ 2 * (den ^ j * nextMass) := by
    have hh := bankTrialRenewalMassOpaqueStep
      den (lo ^ j * win) lo N 0 cutMass
      (den ^ j * nextMass) hprev hrenew
    simpa only [Nat.zero_add, Nat.pow_one] using hh
  calc
    lo ^ (j + 1) * win * N =
        (lo ^ j * win) * lo * N := by
      rw [Nat.pow_succ lo j]
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ den ^ 2 * (den ^ j * nextMass) := hstage
    _ = den ^ (j + 2) * nextMass := by
      calc
        den ^ 2 * (den ^ j * nextMass) =
            (den ^ 2 * den ^ j) * nextMass :=
          (Nat.mul_assoc _ _ _).symm
        _ = den ^ (j + 2) * nextMass := by
          rw [← Nat.pow_add, Nat.add_comm 2 j]

/-- The G13 index-renewal mass sandwich, conditional only on
the named one-trial W and F bounds, uniformly over Clean starts. -/
theorem bankTrialRenewalMassSandwichOfTrialBounds
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (L lo win den : Nat)
    (hW : BankTrialRenewalWonWithinBound (q := q) ring root L win den)
    (hF : BankTrialRenewalLostWithinBound (q := q) ring root L lo den) :
    BankTrialRenewalMassSandwichTarget (q := q) ring root L lo win den := by
  intro S hclean j T hT
  have hmain :
      ∀ (k : Nat)
        (B : GrantBankReference.BankLocalReference
          (compileAdvice q).b),
        BankTrialLocalClean q B →
        ∀ (H : Nat), (k + 1) * L ≤ H →
          lo ^ k * win * n ^ H ≤
            den ^ (k + 1) *
              bankTrialRenewalPatternMass ring root B H L k := by
    intro k
    induction k with
    | zero =>
        intro B hB H hbudget
        have hlength : L ≤ H := by
          simpa only [Nat.zero_add, Nat.one_mul] using hbudget
        have hw := hW B hB H hlength
        simpa only [Nat.pow_zero, Nat.pow_one,
          Nat.one_mul, Nat.zero_add] using hw
    | succ k ih =>
        intro B hB H hbudget
        have hdecomp :
            (Nat.succ k + 1) * L = (k + 1) * L + L := by
          change ((k + 1) + 1) * L = (k + 1) * L + L
          rw [Nat.add_mul, Nat.one_mul]
        have ht : (k + 1) * L + L ≤ H := by
          simpa only [hdecomp] using hbudget
        have hlength : L ≤ H := by omega
        have hsum :
            lo ^ k * win *
                bankTrialRenewalLostBoundedExtensionMass
                  ring root B H L ≤
              den ^ (k + 1) *
                bankTrialRenewalPatternMass
                  ring root B H L (k + 1) := by
          unfold bankTrialRenewalLostBoundedExtensionMass
          rw [bankTrialRenewalMassFirstLostExact ring root B H L k]
          apply bankTrialRenewalMapSumScale
          intro cut hcut
          by_cases hb : cut.length ≤ L
          · have hcutClean :=
              bankTrialRenewalFirstLostCutClean
                ring root B H cut hcut
            have hremaining :
                (k + 1) * L ≤ H - cut.length := by omega
            have hinner := ih
              (bankTrialLocalRun ring root cut
                (bankTrialLocalStart B)).bank
              hcutClean (H - cut.length) hremaining
            simpa only [if_pos hb, bankTrialRenewalPatternMass]
              using hinner
          · simp only [if_neg hb, Nat.mul_zero]
            exact Nat.zero_le _
        have hloss := hF B hB H hlength
        change lo ^ (k + 1) * win * n ^ H ≤
          den ^ (k + 2) *
            bankTrialRenewalPatternMass ring root B H L (k + 1)
        exact bankTrialRenewalMassCutCompose den lo win (n ^ H)
          k (bankTrialRenewalLostBoundedExtensionMass ring root B H L)
          (bankTrialRenewalPatternMass ring root B H L (k + 1))
          hloss hsum
  exact hmain j S hclean T hT

end L3


namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
G13-INDEX-RENEWAL. All sums remain on the original
length-T scheduler tape. Rarity is assumed only at index zero.
-/

/-- Pull a full-word weight inside the first-stop observer. -/
private theorem bankTrialRenewalStoppedWordWeight
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (A : List (Fin n) → X → Nat → List (Fin n) → Nat)
    (weight : List (Fin n) → Nat) :
    ∀ (word : List (Fin n)) (T : Nat)
      (pre : List (Fin n)) (x : X),
      bankTrialSuccessNatStoppedWord next stop
        (fun cut z t suffix =>
          A cut z t suffix * weight (cut ++ suffix))
        T pre x word =
      bankTrialSuccessNatStoppedWord next stop A T pre x word *
        weight (pre ++ word) := by
  intro word
  induction word with
  | nil =>
      intro T pre x
      cases hs : stop pre x with
      | false => simp [bankTrialSuccessNatStoppedWord, hs]
      | true => simp [bankTrialSuccessNatStoppedWord, hs]
  | cons e rest ih =>
      intro T pre x
      cases hs : stop pre x with
      | true => simp [bankTrialSuccessNatStoppedWord, hs]
      | false =>
          simpa only [bankTrialSuccessNatStoppedWord, hs,
            Bool.false_eq_true, if_false,
            List.append_assoc, List.singleton_append] using
              ih (T - 1) (pre ++ [e]) (next x e)

/-- The masked absolute cost is indicator times elapsed time. -/
private theorem bankTrialRenewalTauIndicator
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (L j : Nat) (word : List (Fin n)) :
    bankTrialRenewalTau ring root S L j word =
      Prob.indicator (bankTrialRenewalPattern ring root S L j word) *
        (bankTrialRenewalRun ring root S word).elapsed := by
  cases hp : bankTrialRenewalPattern ring root S L j word with
  | false => simp [bankTrialRenewalTau, Prob.indicator, hp]
  | true => simp [bankTrialRenewalTau, Prob.indicator, hp]

/-- At an actual first-LOST cut, the weighted suffix indicator
is cut.length times suffix mass plus suffix absolute cost.
The empty suffix has neither a restarted WON nor a cost. -/
private theorem bankTrialRenewalCostCutSuffixWeight
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (T L j : Nat) (cut : List (Fin n))
    (hcut : cut ∈ Prob.firstStoppedPrefixes
      (bankTrialLocalNext ring root)
      bankTrialRenewalFirstLostStop T [] (bankTrialLocalStart S))
    (suffix : List (Fin n)) :
    (if cut.length ≤ L then
      Prob.indicator (bankTrialRenewalPattern ring root
        (bankTrialLocalRun ring root cut
          (bankTrialLocalStart S)).bank L j suffix)
     else 0) *
       (bankTrialRenewalRun ring root S (cut ++ suffix)).elapsed =
    if cut.length ≤ L then
      cut.length * Prob.indicator (bankTrialRenewalPattern ring root
        (bankTrialLocalRun ring root cut
          (bankTrialLocalStart S)).bank L j suffix) +
      bankTrialRenewalTau ring root
        (bankTrialLocalRun ring root cut
          (bankTrialLocalStart S)).bank L j suffix
    else 0 := by
  by_cases hb : cut.length ≤ L
  · cases suffix with
    | nil =>
        have hz :
            bankTrialRenewalPattern ring root
              (bankTrialLocalRun ring root cut
                (bankTrialLocalStart S)).bank L j [] = false := by
          simp [bankTrialRenewalPattern, bankTrialRenewalRun,
            bankTrialRenewalStart, bankTrialRenewalRunFrom,
            bankTrialLocalStart]
        simp [hb, hz, Prob.indicator, bankTrialRenewalTau]
    | cons e rest =>
        have hrun := bankTrialRenewalFirstLostScannerSuffix
          ring root S T cut hcut e rest
        cases hp : bankTrialRenewalPattern ring root
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)).bank L j (e :: rest) with
        | false =>
            simp [hb, hp, Prob.indicator, bankTrialRenewalTau]
        | true =>
            simp [hb, hp, Prob.indicator, bankTrialRenewalTau,
              hrun, bankTrialRenewalShift]
  · simp [hb]

/-- Exact cost counterpart of bankTrialRenewalMassFirstLostExact.
There is no second independent scheduler word. -/
theorem bankTrialRenewalCostFirstLostExact
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T L j : Nat) :
    bankTrialRenewalPatternCost ring root S T L (j + 1) =
      ((Prob.firstStoppedPrefixes
        (bankTrialLocalNext ring root)
        bankTrialRenewalFirstLostStop T [] (bankTrialLocalStart S)).map
        (fun cut =>
          if cut.length ≤ L then
            cut.length * bankTrialRenewalPatternMass ring root
              (bankTrialLocalRun ring root cut
                (bankTrialLocalStart S)).bank
              (T - cut.length) L j +
            bankTrialRenewalPatternCost ring root
              (bankTrialLocalRun ring root cut
                (bankTrialLocalStart S)).bank
              (T - cut.length) L j
          else 0)).sum := by
  have hfun :
      (fun word : List (Fin n) =>
        bankTrialRenewalTau ring root S L (j + 1) word) =
      (fun word : List (Fin n) =>
        bankTrialSuccessNatStoppedWord
          (bankTrialLocalNext ring root)
          bankTrialRenewalFirstLostStop
          (fun cut z _ suffix =>
            (if cut.length ≤ L then
              Prob.indicator (bankTrialRenewalPattern
                ring root z.bank L j suffix)
             else 0) *
              (bankTrialRenewalRun ring root S
                (cut ++ suffix)).elapsed)
          T [] (bankTrialLocalStart S) word) := by
    funext word
    calc
      bankTrialRenewalTau ring root S L (j + 1) word =
          Prob.indicator (bankTrialRenewalPattern ring root
            S L (j + 1) word) *
            (bankTrialRenewalRun ring root S word).elapsed :=
        bankTrialRenewalTauIndicator ring root S L (j + 1) word
      _ = bankTrialSuccessNatStoppedWord
            (bankTrialLocalNext ring root)
            bankTrialRenewalFirstLostStop
            (fun cut z _ suffix =>
              if cut.length ≤ L then
                Prob.indicator (bankTrialRenewalPattern
                  ring root z.bank L j suffix)
              else 0)
            T [] (bankTrialLocalStart S) word *
          (bankTrialRenewalRun ring root S word).elapsed := by
            rw [bankTrialRenewalWholeEvent ring root S T L j word]
      _ = bankTrialSuccessNatStoppedWord
            (bankTrialLocalNext ring root)
            bankTrialRenewalFirstLostStop
            (fun cut z _ suffix =>
              (if cut.length ≤ L then
                Prob.indicator (bankTrialRenewalPattern
                  ring root z.bank L j suffix)
               else 0) *
                (bankTrialRenewalRun ring root S
                  (cut ++ suffix)).elapsed)
            T [] (bankTrialLocalStart S) word := by
              simpa only [List.nil_append] using
                (bankTrialRenewalStoppedWordWeight
                  (bankTrialLocalNext ring root)
                  bankTrialRenewalFirstLostStop
                  (fun cut z _ suffix =>
                    if cut.length ≤ L then
                      Prob.indicator (bankTrialRenewalPattern
                        ring root z.bank L j suffix)
                    else 0)
                  (fun w => (bankTrialRenewalRun ring root S w).elapsed)
                  word T [] (bankTrialLocalStart S)).symm
  unfold bankTrialRenewalPatternCost
  rw [show bankTrialRenewalTau ring root S L (j + 1) = _ from hfun, bankTrialRenewalFirstLostFactor ring root S
    (fun cut z suffix =>
      (if cut.length ≤ L then
        Prob.indicator (bankTrialRenewalPattern
          ring root z.bank L j suffix)
       else 0) *
        (bankTrialRenewalRun ring root S
          (cut ++ suffix)).elapsed) T]
  apply congrArg List.sum
  apply List.map_congr_left
  intro cut hcut
  calc
    Prob.scheduleSum n (T - cut.length) (fun suffix =>
        (if cut.length ≤ L then
          Prob.indicator (bankTrialRenewalPattern ring root
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)).bank L j suffix)
         else 0) *
          (bankTrialRenewalRun ring root S
            (cut ++ suffix)).elapsed) =
      Prob.scheduleSum n (T - cut.length) (fun suffix =>
        if cut.length ≤ L then
          cut.length * Prob.indicator (bankTrialRenewalPattern ring root
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)).bank L j suffix) +
          bankTrialRenewalTau ring root
            (bankTrialLocalRun ring root cut
              (bankTrialLocalStart S)).bank L j suffix
        else 0) := by
          apply congrArg (Prob.scheduleSum n (T - cut.length))
          funext suffix
          exact bankTrialRenewalCostCutSuffixWeight
            ring root S T L j cut hcut suffix
    _ = if cut.length ≤ L then
          cut.length * Prob.scheduleSum n (T - cut.length)
            (fun suffix =>
              Prob.indicator (bankTrialRenewalPattern ring root
                (bankTrialLocalRun ring root cut
                  (bankTrialLocalStart S)).bank L j suffix)) +
          Prob.scheduleSum n (T - cut.length)
            (bankTrialRenewalTau ring root
              (bankTrialLocalRun ring root cut
                (bankTrialLocalStart S)).bank L j)
        else 0 := by
          by_cases hb : cut.length ≤ L
          · simp only [if_pos hb]
            rw [bankTrialC5ScheduleSumAdd,
              bankTrialSuccessScheduleSumScale]
          · simp only [if_neg hb]
            rw [bankTrialProbabilityScheduleSumConst]
            simp
    _ = _ := rfl

/-- A constant-one first-stop observer is pointwise at most one. -/
private theorem bankTrialRenewalStoppedUnitLe
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool) :
    ∀ (word : List (Fin n)) (T : Nat)
      (pre : List (Fin n)) (x : X),
      bankTrialSuccessNatStoppedWord next stop
        (fun _ _ _ _ => 1) T pre x word ≤ 1 := by
  intro word
  induction word with
  | nil =>
      intro T pre x
      cases hs : stop pre x with
      | false => simp [bankTrialSuccessNatStoppedWord, hs]
      | true => simp [bankTrialSuccessNatStoppedWord, hs]
  | cons e rest ih =>
      intro T pre x
      cases hs : stop pre x with
      | true => simp [bankTrialSuccessNatStoppedWord, hs]
      | false =>
          simpa [bankTrialSuccessNatStoppedWord, hs] using
            ih (T - 1) (pre ++ [e]) (next x e)

/-- Prefix-free first-LOST cylinders occupy at most n^T words. -/
theorem bankTrialRenewalFirstLostCylinderLe
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T : Nat) :
    ((Prob.firstStoppedPrefixes
      (bankTrialLocalNext ring root)
      bankTrialRenewalFirstLostStop T [] (bankTrialLocalStart S)).map
      (fun cut => n ^ (T - cut.length))).sum ≤ n ^ T := by
  calc
    ((Prob.firstStoppedPrefixes
        (bankTrialLocalNext ring root)
        bankTrialRenewalFirstLostStop T [] (bankTrialLocalStart S)).map
        (fun cut => n ^ (T - cut.length))).sum =
      Prob.scheduleSum n T (fun word =>
        bankTrialSuccessNatStoppedWord
          (bankTrialLocalNext ring root)
          bankTrialRenewalFirstLostStop
          (fun _ _ _ _ => 1) T [] (bankTrialLocalStart S) word) := by
            simpa only [Nat.mul_one] using
              (bankTrialRenewalFirstLostExtensionCount
                ring root S (fun _ _ => 1) T).symm
    _ ≤ Prob.scheduleSum n T (fun _ => 1) := by
          apply bankTrialProbabilityScheduleSumMono n T
          intro word
          exact bankTrialRenewalStoppedUnitLe
            (bankTrialLocalNext ring root)
            bankTrialRenewalFirstLostStop
            word T [] (bankTrialLocalStart S)
    _ = n ^ T := by
          simpa only [Nat.mul_one] using
            (bankTrialProbabilityScheduleSumConst n T 1)

/-- Distribute addition across a mapped finite Nat sum. -/
private theorem bankTrialRenewalNatMapSumAdd
    {A : Type} (xs : List A) (f g : A → Nat) :
    (xs.map (fun x => f x + g x)).sum =
      (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      omega

/-- Distribute multiplication across a mapped finite Nat sum. -/
private theorem bankTrialRenewalNatMapSumScale
    {A : Type} (xs : List A) (c : Nat) (f : A → Nat) :
    (xs.map (fun x => c * f x)).sum =
      c * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

/-- Filtering to cuts with length at most L cannot increase mass. -/
theorem bankTrialRenewalLostBoundedExtensionLe
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T L : Nat) :
    bankTrialRenewalLostBoundedExtensionMass
      ring root S T L ≤ n ^ T := by
  unfold bankTrialRenewalLostBoundedExtensionMass
  have hmap := bankTrialRenewalMapSumScale 1 1
    (Prob.firstStoppedPrefixes
      (bankTrialLocalNext ring root)
      bankTrialRenewalFirstLostStop T [] (bankTrialLocalStart S))
    (fun cut => if cut.length ≤ L then n ^ (T - cut.length) else 0)
    (fun cut => n ^ (T - cut.length))
    (by
      intro cut _
      by_cases hb : cut.length ≤ L
      · simp only [if_pos hb]
        exact Nat.le_refl _
      · simp only [if_neg hb]
        exact Nat.zero_le _)
  have hfilter :
      ((Prob.firstStoppedPrefixes
        (bankTrialLocalNext ring root)
        bankTrialRenewalFirstLostStop T [] (bankTrialLocalStart S)).map
        (fun cut =>
          if cut.length ≤ L then n ^ (T - cut.length) else 0)).sum ≤
      ((Prob.firstStoppedPrefixes
        (bankTrialLocalNext ring root)
        bankTrialRenewalFirstLostStop T [] (bankTrialLocalStart S)).map
        (fun cut => n ^ (T - cut.length))).sum := by
          simpa only [Nat.one_mul] using hmap
  exact Nat.le_trans hfilter
    (bankTrialRenewalFirstLostCylinderLe ring root S T)

/-- (G0) Index-zero cost bound, uniformly over Clean starts. -/
def BankTrialRenewalZeroCostWithinBound
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (L g : Nat) : Prop :=
  ∀ (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b),
    BankTrialLocalClean q S →
      ∀ (T : Nat), L ≤ T →
        2 ^ (compileAdvice q).K *
          bankTrialRenewalPatternCost ring root S T L 0 ≤
        n ^ T * (n * g)

/-- (Fc) Bounded first-LOST length moment, on the same cut set. -/
def BankTrialRenewalLostCostWithinBound
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (L f : Nat) : Prop :=
  ∀ (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b),
    BankTrialLocalClean q S →
      ∀ (T : Nat), L ≤ T →
        ((Prob.firstStoppedPrefixes
          (bankTrialLocalNext ring root)
          bankTrialRenewalFirstLostStop T []
          (bankTrialLocalStart S)).map
          (fun cut =>
            if cut.length ≤ L then
              cut.length * n ^ (T - cut.length)
            else 0)).sum ≤
          n ^ T * (n * f)

/-- (R0) Index-zero rarity. This is a one-trial premise because
the current head mass bound applies to a *local head event*, not
directly to the E_0 regenerative pattern indicator. -/
def BankTrialRenewalZeroRareWithinBound
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (L : Nat) : Prop :=
  ∀ (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b),
    BankTrialLocalClean q S →
      ∀ (T : Nat), L ≤ T →
        2 ^ (compileAdvice q).K *
          bankTrialRenewalPatternMass ring root S T L 0 ≤ n ^ T

/-- R0 propagates to every index by the exact first-LOST mass
recursion and the pfx-free cylinder estimate. -/
private theorem bankTrialRenewalRareAllOfZero
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (L : Nat)
    (hR : BankTrialRenewalZeroRareWithinBound (q := q) ring root L) :
    ∀ (j : Nat)
      (S : GrantBankReference.BankLocalReference
        (compileAdvice q).b),
      BankTrialLocalClean q S →
        ∀ (T : Nat), (j + 1) * L ≤ T →
          2 ^ (compileAdvice q).K *
            bankTrialRenewalPatternMass ring root S T L j ≤
          n ^ T := by
  intro j
  induction j with
  | zero =>
      intro S hS T hbudget
      have hlength : L ≤ T := by
        simpa only [Nat.zero_add, Nat.one_mul] using hbudget
      exact hR S hS T hlength
  | succ j ih =>
      intro S hS T hbudget
      have hdecomp :
          (Nat.succ j + 1) * L = (j + 1) * L + L := by
        change ((j + 1) + 1) * L = (j + 1) * L + L
        rw [Nat.add_mul, Nat.one_mul]
      have ht : (j + 1) * L + L ≤ T := by
        simpa only [hdecomp] using hbudget
      have hsum :
          2 ^ (compileAdvice q).K *
            bankTrialRenewalPatternMass ring root S T L (j + 1) ≤
          bankTrialRenewalLostBoundedExtensionMass
            ring root S T L := by
        unfold bankTrialRenewalLostBoundedExtensionMass
        rw [bankTrialRenewalMassFirstLostExact ring root S T L j]
        have hlist := bankTrialRenewalMapSumScale
          (2 ^ (compileAdvice q).K) 1
          (Prob.firstStoppedPrefixes
            (bankTrialLocalNext ring root)
            bankTrialRenewalFirstLostStop T []
            (bankTrialLocalStart S))
          (fun cut =>
            Prob.scheduleSum n (T - cut.length) (fun suffix =>
              if cut.length ≤ L then
                Prob.indicator (bankTrialRenewalPattern ring root
                  (bankTrialLocalRun ring root cut
                    (bankTrialLocalStart S)).bank L j suffix)
              else 0))
          (fun cut =>
            if cut.length ≤ L then n ^ (T - cut.length) else 0)
          (by
            intro cut hcut
            by_cases hb : cut.length ≤ L
            · have hc := bankTrialRenewalFirstLostCutClean
                ring root S T cut hcut
              have hremaining :
                  (j + 1) * L ≤ T - cut.length := by omega
              have hr := ih
                (bankTrialLocalRun ring root cut
                  (bankTrialLocalStart S)).bank
                hc (T - cut.length) hremaining
              simpa only [if_pos hb, bankTrialRenewalPatternMass,
                Nat.one_mul] using hr
            · simp [hb, bankTrialProbabilityScheduleSumConst])
        simpa only [Nat.one_mul] using hlist
      exact Nat.le_trans hsum
        (bankTrialRenewalLostBoundedExtensionLe ring root S T L)

/-- Opaque arithmetic: multiplication is distributed before any
instantiation with large scheduler powers. -/
private theorem bankTrialRenewalCutCostBound
    (a mass cost N ell C : Nat)
    (hm : a * mass ≤ N)
    (hc : a * cost ≤ N * C) :
    a * (ell * mass + cost) ≤ N * (ell + C) := by
  calc
    a * (ell * mass + cost) =
      ell * (a * mass) + a * cost := by
        simp only [Nat.mul_add, Nat.mul_assoc,
          Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ ell * N + N * C :=
      Nat.add_le_add (Nat.mul_le_mul_left ell hm) hc
    _ = N * (ell + C) := by
      rw [Nat.mul_add, Nat.mul_comm N ell]

/-- Split a stopped-pfx weight into its first-length moment
and a constant times its extension mass. All arithmetic is over
opaque functions; the later application may contain n^T. -/
private theorem bankTrialRenewalMomentSplit
    {A : Type} (test : A → Prop) [DecidablePred test]
    (xs : List A) (ell ext : A → Nat) (C : Nat) :
    (xs.map (fun x =>
      if test x then ext x * (ell x + C) else 0)).sum =
    (xs.map (fun x =>
      if test x then ell x * ext x else 0)).sum +
    C * (xs.map (fun x =>
      if test x then ext x else 0)).sum := by
  calc
    (xs.map (fun x =>
        if test x then ext x * (ell x + C) else 0)).sum =
      (xs.map (fun x =>
        (if test x then ell x * ext x else 0) +
        C * (if test x then ext x else 0))).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro x _
          by_cases ht : test x
          · simp only [if_pos ht, Nat.mul_add]
            rw [Nat.mul_comm (ext x) (ell x),
              Nat.mul_comm (ext x) C]
          · simp only [if_neg ht, Nat.mul_zero, Nat.zero_add]
    _ = (xs.map (fun x =>
          if test x then ell x * ext x else 0)).sum +
        (xs.map (fun x =>
          C * (if test x then ext x else 0))).sum :=
      bankTrialRenewalNatMapSumAdd _ _ _
    _ = (xs.map (fun x =>
          if test x then ell x * ext x else 0)).sum +
        C * (xs.map (fun x =>
          if test x then ext x else 0)).sum := by
            rw [bankTrialRenewalNatMapSumScale]

/-- Only opaque Nat variables appear in the final coefficient
rearrangement (N may later be instantiated with n^H). -/
private theorem bankTrialRenewalCostOpaqueStep
    (N n f g j : Nat) :
    N * (n * f) + (n * (g + j * f)) * N =
      N * (n * (g + (j + 1) * f)) := by
  have hcoefficient :
      f + (g + j * f) = g + (j + 1) * f := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  calc
    N * (n * f) + (n * (g + j * f)) * N =
      N * (n * f) + N * (n * (g + j * f)) := by
        rw [Nat.mul_comm (n * (g + j * f)) N]
    _ = N * (n * f + n * (g + j * f)) :=
      (Nat.mul_add N (n * f) (n * (g + j * f))).symm
    _ = N * (n * (f + (g + j * f))) := by
      rw [Nat.mul_add n f (g + j * f)]
    _ = N * (n * (g + (j + 1) * f)) := by
      rw [hcoefficient]

/-- The cost sandwich under exactly three one-trial premises:
G0, Fc, R0. Rarity at every later index is derived above. -/
theorem bankTrialRenewalCostSandwichOfTrialBounds
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (L f g : Nat)
    (hG : BankTrialRenewalZeroCostWithinBound (q := q) ring root L g)
    (hFc : BankTrialRenewalLostCostWithinBound (q := q) ring root L f)
    (hR : BankTrialRenewalZeroRareWithinBound (q := q) ring root L) :
    BankTrialRenewalCostSandwichTarget (q := q) ring root L f g := by
  intro S hS j T hT
  have hrare := bankTrialRenewalRareAllOfZero ring root L hR
  have hmain :
      ∀ (k : Nat)
        (B : GrantBankReference.BankLocalReference
          (compileAdvice q).b),
        BankTrialLocalClean q B →
          ∀ (H : Nat), (k + 1) * L ≤ H →
            2 ^ (compileAdvice q).K *
              bankTrialRenewalPatternCost ring root B H L k ≤
            n ^ H * (n * (g + k * f)) := by
    intro k
    induction k with
    | zero =>
        intro B hB H hbudget
        have hlength : L ≤ H := by
          simpa only [Nat.zero_add, Nat.one_mul] using hbudget
        have hbase := hG B hB H hlength
        simpa only [Nat.zero_mul, Nat.add_zero] using hbase
    | succ k ih =>
        intro B hB H hbudget
        have hdecomp :
            (Nat.succ k + 1) * L = (k + 1) * L + L := by
          change ((k + 1) + 1) * L = (k + 1) * L + L
          rw [Nat.add_mul, Nat.one_mul]
        have ht : (k + 1) * L + L ≤ H := by
          simpa only [hdecomp] using hbudget
        have hlength : L ≤ H := by omega
        have hcut :
            2 ^ (compileAdvice q).K *
              bankTrialRenewalPatternCost ring root B H L (k + 1) ≤
            ((Prob.firstStoppedPrefixes
              (bankTrialLocalNext ring root)
              bankTrialRenewalFirstLostStop H []
              (bankTrialLocalStart B)).map
              (fun cut =>
                if cut.length ≤ L then
                  n ^ (H - cut.length) *
                    (cut.length + n * (g + k * f))
                else 0)).sum := by
          rw [bankTrialRenewalCostFirstLostExact ring root B H L k]
          have hlist := bankTrialRenewalMapSumScale
            (2 ^ (compileAdvice q).K) 1
            (Prob.firstStoppedPrefixes
              (bankTrialLocalNext ring root)
              bankTrialRenewalFirstLostStop H []
              (bankTrialLocalStart B))
            (fun cut =>
              if cut.length ≤ L then
                cut.length * bankTrialRenewalPatternMass ring root
                  (bankTrialLocalRun ring root cut
                    (bankTrialLocalStart B)).bank
                  (H - cut.length) L k +
                bankTrialRenewalPatternCost ring root
                  (bankTrialLocalRun ring root cut
                    (bankTrialLocalStart B)).bank
                  (H - cut.length) L k
              else 0)
            (fun cut =>
              if cut.length ≤ L then
                n ^ (H - cut.length) *
                  (cut.length + n * (g + k * f))
              else 0)
            (by
              intro cut hmem
              by_cases hb : cut.length ≤ L
              · have hc := bankTrialRenewalFirstLostCutClean
                  ring root B H cut hmem
                have hremaining :
                    (k + 1) * L ≤ H - cut.length := by omega
                have hr := hrare k
                  (bankTrialLocalRun ring root cut
                    (bankTrialLocalStart B)).bank
                  hc (H - cut.length) hremaining
                have hcost := ih
                  (bankTrialLocalRun ring root cut
                    (bankTrialLocalStart B)).bank
                  hc (H - cut.length) hremaining
                simp only [if_pos hb, Nat.one_mul]
                exact bankTrialRenewalCutCostBound
                  (2 ^ (compileAdvice q).K)
                  (bankTrialRenewalPatternMass ring root
                    (bankTrialLocalRun ring root cut
                      (bankTrialLocalStart B)).bank
                    (H - cut.length) L k)
                  (bankTrialRenewalPatternCost ring root
                    (bankTrialLocalRun ring root cut
                      (bankTrialLocalStart B)).bank
                    (H - cut.length) L k)
                  (n ^ (H - cut.length)) cut.length
                  (n * (g + k * f)) hr hcost
              · simp only [if_neg hb, Nat.mul_zero]
                exact Nat.zero_le _)
          simpa only [Nat.one_mul] using hlist
        have hsplit :
            ((Prob.firstStoppedPrefixes
              (bankTrialLocalNext ring root)
              bankTrialRenewalFirstLostStop H []
              (bankTrialLocalStart B)).map
              (fun cut =>
                if cut.length ≤ L then
                  n ^ (H - cut.length) *
                    (cut.length + n * (g + k * f))
                else 0)).sum =
            ((Prob.firstStoppedPrefixes
              (bankTrialLocalNext ring root)
              bankTrialRenewalFirstLostStop H []
              (bankTrialLocalStart B)).map
              (fun cut =>
                if cut.length ≤ L then
                  cut.length * n ^ (H - cut.length)
                else 0)).sum +
            (n * (g + k * f)) *
              bankTrialRenewalLostBoundedExtensionMass
                ring root B H L := by
          simpa only [bankTrialRenewalLostBoundedExtensionMass] using
            (bankTrialRenewalMomentSplit
              (fun cut : List (Fin n) => cut.length ≤ L)
              (Prob.firstStoppedPrefixes
                (bankTrialLocalNext ring root)
                bankTrialRenewalFirstLostStop H []
                (bankTrialLocalStart B))
              (fun cut => cut.length)
              (fun cut => n ^ (H - cut.length))
              (n * (g + k * f)))
        have hfirst := hFc B hB H hlength
        have hsecond :=
          bankTrialRenewalLostBoundedExtensionLe ring root B H L
        calc
          2 ^ (compileAdvice q).K *
              bankTrialRenewalPatternCost ring root B H L (k + 1) ≤
            ((Prob.firstStoppedPrefixes
              (bankTrialLocalNext ring root)
              bankTrialRenewalFirstLostStop H []
              (bankTrialLocalStart B)).map
              (fun cut =>
                if cut.length ≤ L then
                  n ^ (H - cut.length) *
                    (cut.length + n * (g + k * f))
                else 0)).sum := hcut
          _ = ((Prob.firstStoppedPrefixes
                (bankTrialLocalNext ring root)
                bankTrialRenewalFirstLostStop H []
                (bankTrialLocalStart B)).map
                (fun cut =>
                  if cut.length ≤ L then
                    cut.length * n ^ (H - cut.length)
                  else 0)).sum +
              (n * (g + k * f)) *
                bankTrialRenewalLostBoundedExtensionMass
                  ring root B H L := hsplit
          _ ≤ n ^ H * (n * f) +
              (n * (g + k * f)) * n ^ H := by
                exact Nat.add_le_add hfirst
                  (Nat.mul_le_mul_left (n * (g + k * f)) hsecond)
          _ = n ^ H * (n * (g + (k + 1) * f)) :=
            bankTrialRenewalCostOpaqueStep (n ^ H) n f g k
  exact hmain j S hS T hT

end L3


namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
G13-INDEX-RENEWAL: one-trial upper inputs.

R0 uses the already-proved authentication lemma
bankTrialDurationWinHasAllHeads. The missing bridge is not the
local WON/head lemma, but the zero-failure renewal/local coupling
below. G0 uses the TWO-fold coefficient from the actual finite
C.8 + cutoff, rather than silently dropping ACTIVE. Fc is proved
by the stronger unconditional C.6 bound at every T, so a
separate first-LOST horizon-padding lemma is unnecessary.
-/

/-- A renewal step cannot delete a recorded failure. -/
private theorem bankTrialRenewalNextFailureLengthMono
    {n q : Nat} (ring : DirectedRing n) (root e : Fin n)
    (z : BankTrialRenewalState q) :
    z.failures.length ≤
      (bankTrialRenewalNext ring root z e).failures.length := by
  cases hp : z.observer.phase with
  | won =>
      rw [bankTrialRenewalNextWon ring root e z hp]
      exact Nat.le_refl _
  | lost =>
      simp only [bankTrialRenewalNext, hp]
      unfold bankTrialRenewalAdvance
      split
      · simp only [List.length_append, List.length_singleton]
        omega
      · exact Nat.le_refl _
  | recovery =>
      simp only [bankTrialRenewalNext, hp]
      unfold bankTrialRenewalAdvance
      split
      · simp only [List.length_append, List.length_singleton]
        omega
      · exact Nat.le_refl _
  | live begun =>
      simp only [bankTrialRenewalNext, hp]
      unfold bankTrialRenewalAdvance
      split
      · simp only [List.length_append, List.length_singleton]
        omega
      · exact Nat.le_refl _

/-- Failure-list length is nondecreasing along an entire run. -/
private theorem bankTrialRenewalRunFailureLengthMono
    {n q : Nat} (ring : DirectedRing n) (root : Fin n) :
    ∀ (word : List (Fin n)) (z : BankTrialRenewalState q),
      z.failures.length ≤
        (bankTrialRenewalRunFrom ring root word z).failures.length := by
  intro word
  induction word with
  | nil =>
      intro z
      exact Nat.le_refl _
  | cons e tail ih =>
      intro z
      change z.failures.length ≤
        (bankTrialRenewalRunFrom ring root tail
          (bankTrialRenewalNext ring root z e)).failures.length
      exact Nat.le_trans
        (bankTrialRenewalNextFailureLengthMono ring root e z)
        (ih (bankTrialRenewalNext ring root z e))

/-- Before a LOST state, the renewal observer makes the very same
one-letter transition as the local trial observer. -/
private theorem bankTrialRenewalNextObserverBeforeLost
    {n q : Nat} (ring : DirectedRing n) (root e : Fin n)
    (z : BankTrialRenewalState q)
    (hnot : z.observer.phase ≠ .lost) :
    (bankTrialRenewalNext ring root z e).observer =
      bankTrialLocalNext ring root z.observer e := by
  cases hp : z.observer.phase with
  | won =>
      rw [bankTrialRenewalNextWon ring root e z hp]
      exact (bankTrialLocalTerminalAbsorbs ring root e
        z.observer (Or.inl hp)).symm
  | lost =>
      exact False.elim (hnot hp)
  | recovery =>
      simp only [bankTrialRenewalNext, hp]
      unfold bankTrialRenewalAdvance
      split <;> rfl
  | live begun =>
      simp only [bankTrialRenewalNext, hp]
      unfold bankTrialRenewalAdvance
      split <;> rfl

/-- If no new failure was recorded on a step, the next observer
cannot be LOST (provided the old observer was not LOST). -/
private theorem bankTrialRenewalNextNotLostWithoutFailure
    {n q : Nat} (ring : DirectedRing n) (root e : Fin n)
    (z : BankTrialRenewalState q)
    (hnot : z.observer.phase ≠ .lost)
    (hcount : (bankTrialRenewalNext ring root z e).failures.length =
      z.failures.length) :
    (bankTrialRenewalNext ring root z e).observer.phase ≠ .lost := by
  intro hlost
  have hobs := bankTrialRenewalNextObserverBeforeLost
    ring root e z hnot
  rw [hobs] at hlost
  cases hp : z.observer.phase with
  | won =>
      have ht : bankTrialLocalTerminal z.observer := Or.inl hp
      rw [bankTrialLocalTerminalAbsorbs ring root e z.observer ht] at hlost
      rw [hp] at hlost
      cases hlost
  | lost =>
      exact False.elim (hnot hp)
  | recovery =>
      have hincrease :
          (bankTrialRenewalNext ring root z e).failures.length =
            z.failures.length + 1 := by
        simp [bankTrialRenewalNext, hp,
          bankTrialRenewalAdvance, hlost, List.length_append]
      omega
  | live begun =>
      have hincrease :
          (bankTrialRenewalNext ring root z e).failures.length =
            z.failures.length + 1 := by
        simp [bankTrialRenewalNext, hp,
          bankTrialRenewalAdvance, hlost, List.length_append]
      omega

/-- With no new failure in the whole word, the scanner agrees
with the single-trial observer AND its stopped-cost clock. -/
private theorem bankTrialRenewalNoFailureLocalAndCost
    {n q : Nat} (ring : DirectedRing n) (root : Fin n) :
    ∀ (word : List (Fin n)) (z : BankTrialRenewalState q),
      z.observer.phase ≠ .lost →
      (bankTrialRenewalRunFrom ring root word z).failures.length =
        z.failures.length →
      (bankTrialRenewalRunFrom ring root word z).observer =
        bankTrialLocalRun ring root word z.observer ∧
      (bankTrialRenewalRunFrom ring root word z).elapsed =
        z.elapsed +
          costWord (bankTrialLocalNext ring root)
            bankTrialLocalTerminal z.observer word := by
  intro word
  induction word with
  | nil =>
      intro z _ _
      constructor
      · rfl
      · simp [bankTrialRenewalRunFrom, costWord,
          K2FiniteSafeEliminationExpected.rawCost]
  | cons e tail ih =>
      intro z hnot hcount
      have hstep := bankTrialRenewalNextFailureLengthMono
        ring root e z
      have htail := bankTrialRenewalRunFailureLengthMono
        ring root tail (bankTrialRenewalNext ring root z e)
      have hsame :
          (bankTrialRenewalNext ring root z e).failures.length =
            z.failures.length := by
        change
          (bankTrialRenewalRunFrom ring root tail
            (bankTrialRenewalNext ring root z e)).failures.length =
            z.failures.length at hcount
        omega
      have hnotnext := bankTrialRenewalNextNotLostWithoutFailure
        ring root e z hnot hsame
      have hremain :
          (bankTrialRenewalRunFrom ring root tail
            (bankTrialRenewalNext ring root z e)).failures.length =
          (bankTrialRenewalNext ring root z e).failures.length := by
        change
          (bankTrialRenewalRunFrom ring root tail
            (bankTrialRenewalNext ring root z e)).failures.length =
              z.failures.length at hcount
        omega
      obtain ⟨hobserver, helapsed⟩ :=
        ih (bankTrialRenewalNext ring root z e) hnotnext hremain
      have hnext := bankTrialRenewalNextObserverBeforeLost
        ring root e z hnot
      constructor
      · change
          (bankTrialRenewalRunFrom ring root tail
            (bankTrialRenewalNext ring root z e)).observer =
          bankTrialLocalRun ring root tail
            (bankTrialLocalNext ring root z.observer e)
        rw [hobserver, hnext]
      · by_cases hw : z.observer.phase = .won
        · have ht : bankTrialLocalTerminal z.observer := Or.inl hw
          have hrun := bankTrialRenewalRunFromWon
            ring root (e :: tail) z hw
          have hcost :
              costWord (bankTrialLocalNext ring root)
                bankTrialLocalTerminal z.observer (e :: tail) = 0 := by
            simp only [costWord,
              K2FiniteSafeEliminationExpected.rawCost,
              if_pos ht]
          change (bankTrialRenewalRunFrom ring root
            (e :: tail) z).elapsed =
            z.elapsed + costWord (bankTrialLocalNext ring root)
              bankTrialLocalTerminal z.observer (e :: tail)
          rw [hrun, hcost, Nat.add_zero]
        · have hnotterm :
              ¬ bankTrialLocalTerminal z.observer := by
            intro ht
            cases ht with
            | inl h => exact hw h
            | inr h => exact hnot h
          have hcost :
              costWord (bankTrialLocalNext ring root)
                  bankTrialLocalTerminal z.observer (e :: tail) =
                1 + costWord (bankTrialLocalNext ring root)
                  bankTrialLocalTerminal
                  (bankTrialLocalNext ring root z.observer e) tail := by
            simp only [costWord,
              K2FiniteSafeEliminationExpected.rawCost,
              if_neg hnotterm]
          have hclock := bankTrialRenewalNextElapsed
            ring root e z hw
          change (bankTrialRenewalRunFrom ring root tail
            (bankTrialRenewalNext ring root z e)).elapsed =
            z.elapsed + costWord (bankTrialLocalNext ring root)
              bankTrialLocalTerminal z.observer (e :: tail)
          calc
            (bankTrialRenewalRunFrom ring root tail
                (bankTrialRenewalNext ring root z e)).elapsed =
              (bankTrialRenewalNext ring root z e).elapsed +
                costWord (bankTrialLocalNext ring root)
                  bankTrialLocalTerminal
                  (bankTrialRenewalNext ring root z e).observer tail :=
              helapsed
            _ = (z.elapsed + 1) +
                costWord (bankTrialLocalNext ring root)
                  bankTrialLocalTerminal
                  (bankTrialLocalNext ring root z.observer e) tail := by
              rw [hclock, hnext]
            _ = z.elapsed +
                costWord (bankTrialLocalNext ring root)
                  bankTrialLocalTerminal z.observer (e :: tail) := by
              rw [hcost]
              omega

/-- A zero-failure successful renewal word is a genuine local
single-trial WON word, with exactly the same stopped cost. -/
private theorem bankTrialRenewalZeroPatternLocalWitness
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (L : Nat) (word : List (Fin n))
    (hpat : bankTrialRenewalPattern ring root S L 0 word = true) :
    (bankTrialLocalRun ring root word
      (bankTrialLocalStart S)).phase = .won ∧
    (bankTrialRenewalRun ring root S word).elapsed =
      costWord (bankTrialLocalNext ring root)
        bankTrialLocalTerminal (bankTrialLocalStart S) word := by
  have hp :
      (bankTrialRenewalRun ring root S word).observer.phase = .won ∧
      (bankTrialRenewalRun ring root S word).failures.length = 0 ∧
      (bankTrialRenewalRun ring root S word).failures.all
        (fun age => decide (age ≤ L)) = true ∧
      (bankTrialRenewalRun ring root S word).age ≤ L := by
    simpa only [bankTrialRenewalPattern, decide_eq_true_eq] using hpat
  have hzero :
      (bankTrialRenewalRunFrom ring root word
        (bankTrialRenewalStart S)).failures.length =
      (bankTrialRenewalStart S).failures.length := by
    simpa only [bankTrialRenewalRun, bankTrialRenewalStart,
      List.length_nil] using hp.2.1
  have hnot :
      (bankTrialRenewalStart S).observer.phase ≠ .lost := by
    intro h
    cases h
  obtain ⟨hobserver, helapsed⟩ :=
    bankTrialRenewalNoFailureLocalAndCost ring root
      word (bankTrialRenewalStart S) hnot hzero
  constructor
  · have hw := hp.1
    change (bankTrialRenewalRunFrom ring root word
      (bankTrialRenewalStart S)).observer.phase = .won at hw
    rw [hobserver] at hw
    exact hw
  · change (bankTrialRenewalRunFrom ring root word
        (bankTrialRenewalStart S)).elapsed =
      costWord (bankTrialLocalNext ring root)
        bankTrialLocalTerminal (bankTrialLocalStart S) word
    simpa only [bankTrialRenewalStart, Nat.zero_add] using helapsed

/-- R0: the zero-failure pattern is contained in the authenticated
local WON event, which is contained in the K-head event. -/
theorem bankTrialRenewalZeroRareWithinBoundHolds
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (hsmall : (compileAdvice q).useSmall = false)
    (_hw : BankTrialLiveWindowNonalias n q)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (_hpositive : 0 < (compileAdvice q).K)
    (_hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (L : Nat) :
    BankTrialRenewalZeroRareWithinBound (q := q) ring root L := by
  intro S hclean T _
  have hcontain :
      bankTrialRenewalPatternMass ring root S T L 0 ≤
        bankTrialProbabilityHeadMass ring root
          (bankTrialLocalStart S) (compileAdvice q).K T := by
    unfold bankTrialRenewalPatternMass bankTrialProbabilityHeadMass
    apply bankTrialProbabilityScheduleSumMono n T
    intro word
    cases hp : bankTrialRenewalPattern ring root S L 0 word with
    | false =>
        simp [Prob.indicator, hp]
    | true =>
        have hwin :=
          (bankTrialRenewalZeroPatternLocalWitness
            ring root S L word hp).1
        have hh := bankTrialDurationWinHasAllHeads
          ring root S hclean hsmall hlarge word hwin
        simp [Prob.indicator, hp, hh]
  exact Nat.le_trans
    (Nat.mul_le_mul_left (2 ^ (compileAdvice q).K) hcontain)
    (bankTrialProbabilityHeadMassBound ring hn root
      T (compileAdvice q).K (bankTrialLocalStart S))

/-- The index-zero cost is a subcharge of the physical local WON
stopped cost, word by word, on the same scheduler tape. -/
private theorem bankTrialRenewalZeroCostLeLocalSuccessCost
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T L : Nat) :
    bankTrialRenewalPatternCost ring root S T L 0 ≤
      bankTrialDurationSuccessCostMass ring root S T := by
  unfold bankTrialRenewalPatternCost
    bankTrialDurationSuccessCostMass
  apply bankTrialProbabilityScheduleSumMono n T
  intro word
  cases hp : bankTrialRenewalPattern ring root S L 0 word with
  | false =>
      simp [bankTrialRenewalTau, hp]
  | true =>
      obtain ⟨hwin, hclock⟩ :=
        bankTrialRenewalZeroPatternLocalWitness
          ring root S L word hp
      simp only [bankTrialRenewalTau, hp, if_true, if_pos hwin]
      rw [hclock]
      exact Nat.le_refl _

/-- An opaque monotonicity calculation for transporting a
finite-horizon cutoff through extra scheduler letters. -/
private theorem bankTrialRenewalCutoffPadArithmetic
    (B N pad L T oldMass newMass : Nat)
    (hLT : L ≤ T)
    (hcut : B * N ≤ L * oldMass)
    (hmono : pad * oldMass ≤ newMass) :
    B * (N * pad) ≤ T * newMass := by
  calc
    B * (N * pad) = pad * (B * N) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ pad * (L * oldMass) :=
      Nat.mul_le_mul_left pad hcut
    _ = L * (pad * oldMass) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ L * newMass := Nat.mul_le_mul_left L hmono
    _ ≤ T * newMass := Nat.mul_le_mul_right newMass hLT

/-- Extend a denominator-cleared ACTIVE cutoff from L to T.
The only arithmetic on n^T is via an opaque factor lemma. -/
private theorem bankTrialRenewalCutoffPad
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (B L T : Nat) (hLT : L ≤ T)
    (hcut : B * n ^ L ≤
      L * bankTrialProbabilityWinMass ring root S L) :
    B * n ^ T ≤
      T * bankTrialProbabilityWinMass ring root S T := by
  have hsum : L + (T - L) = T := by omega
  have hpow : n ^ T = n ^ L * n ^ (T - L) := by
    calc
      n ^ T = n ^ (L + (T - L)) := by rw [hsum]
      _ = n ^ L * n ^ (T - L) := Nat.pow_add n L (T - L)
  have hmon :
      n ^ (T - L) * bankTrialProbabilityWinMass ring root S L ≤
        bankTrialProbabilityWinMass ring root S T := by
    have h := bankTrialRenewalWonMonotone ring root S L (T - L)
    simpa only [hsum] using h
  rw [hpow]
  exact bankTrialRenewalCutoffPadArithmetic
    B (n ^ L) (n ^ (T - L)) L T
    (bankTrialProbabilityWinMass ring root S L)
    (bankTrialProbabilityWinMass ring root S T)
    hLT hcut hmon

/-- The C.8 + cutoff + K-head rarity calculation is twofold,
not onefold, in the presence of ACTIVE mass. -/
private theorem bankTrialRenewalZeroCostArithmetic
    (Q M N C W a n : Nat)
    (hsub : M ≤ C)
    (hcost : C ≤ (2 * (a * n)) * W)
    (hrare : Q * W ≤ N) :
    Q * M ≤ N * (n * (2 * a)) := by
  calc
    Q * M ≤ Q * C := Nat.mul_le_mul_left Q hsub
    _ ≤ Q * ((2 * (a * n)) * W) :=
      Nat.mul_le_mul_left Q hcost
    _ = (n * (2 * a)) * (Q * W) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ (n * (2 * a)) * N :=
      Nat.mul_le_mul_left _ hrare
    _ = N * (n * (2 * a)) := Nat.mul_comm _ _

/-- G0 at the exact coefficient available from C.8 and the
given cutoff: g = 2 * (8b+12) * (K+1).
A onefold coefficient would require the stronger inequality
2^K*(WON+ACTIVE) <= n^T, which is not among the source results. -/
theorem bankTrialRenewalZeroCostWithinBoundHolds
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (L : Nat)
    (hcut : ∀ S : GrantBankReference.BankLocalReference
        (compileAdvice q).b,
      BankTrialLocalClean q S →
      ((8 * (compileAdvice q).b + 12) * n) * n ^ L ≤
        L * bankTrialProbabilityWinMass ring root S L) :
    BankTrialRenewalZeroCostWithinBound (q := q) ring root L
      (2 * ((8 * (compileAdvice q).b + 12) *
        ((compileAdvice q).K + 1))) := by
  intro S hclean T hLT
  have hcutT :
      ((8 * (compileAdvice q).b + 12) * n) * n ^ T ≤
      T * bankTrialProbabilityWinMass ring root S T :=
    bankTrialRenewalCutoffPad ring root S
      ((8 * (compileAdvice q).b + 12) * n)
      L T hLT (hcut S hclean)
  have hcost := bankTrialRenewalCompletedSuccessCost
    ring root hn hsmall hw hlarge hpositive hK
    S hclean T hcutT
  have hsub := bankTrialRenewalZeroCostLeLocalSuccessCost
    ring root S T L
  have hrare :
      2 ^ (compileAdvice q).K *
        bankTrialProbabilityWinMass ring root S T ≤ n ^ T := by
    have hauth :
        (compileAdvice q).useSmall = false →
        2 * (compileAdvice q).bankLeaseCap ≤ n →
        BankTrialLocalClean q S →
        ∀ word : List (Fin n),
          (bankTrialLocalRun ring root word
            (bankTrialLocalStart S)).phase = .won →
          bankTrialProbabilityHeadEvent ring root word
            (compileAdvice q).K (bankTrialLocalStart S) := by
      intro _ _ hc word hwin
      exact bankTrialDurationWinHasAllHeads
        ring root S hc hsmall hlarge word hwin
    exact (bankTrialProbabilityUpperOfHeadAuthentication
      ring root S hauth) hsmall hlarge hclean T
  exact bankTrialRenewalZeroCostArithmetic
    (2 ^ (compileAdvice q).K)
    (bankTrialRenewalPatternCost ring root S T L 0)
    (n ^ T)
    (bankTrialDurationSuccessCostMass ring root S T)
    (bankTrialProbabilityWinMass ring root S T)
    ((8 * (compileAdvice q).b + 12) *
      ((compileAdvice q).K + 1)) n hsub hcost hrare

/-- The unfiltered first-LOST length moment, with exact original
scheduler cylinder multiplicities. -/
noncomputable def bankTrialRenewalFirstLostLengthMoment
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T : Nat) : Nat :=
  ((Prob.firstStoppedPrefixes
    (bankTrialLocalNext ring root)
    bankTrialRenewalFirstLostStop T [] (bankTrialLocalStart S)).map
    (fun cut => cut.length * n ^ (T - cut.length))).sum

/-- The first-LOST Nat stop observer equals the stopped cost of
a completed LOST local trial, or zero for all other outcomes. -/
private theorem bankTrialRenewalStoppedLostCostWord
    {n q : Nat} (ring : DirectedRing n) (root : Fin n) :
    ∀ (word : List (Fin n)) (T : Nat)
      (pre : List (Fin n)) (z : BankTrialLocalState q),
      bankTrialSuccessNatStoppedWord
        (bankTrialLocalNext ring root)
        bankTrialRenewalFirstLostStop
        (fun cut _ _ _ => cut.length) T pre z word =
      if (bankTrialLocalRun ring root word z).phase = .lost then
        pre.length +
          costWord (bankTrialLocalNext ring root)
            bankTrialLocalTerminal z word
      else 0 := by
  intro word
  induction word with
  | nil =>
      intro T pre z
      by_cases hl : z.phase = .lost
      · simp [bankTrialSuccessNatStoppedWord,
          bankTrialRenewalFirstLostStop, hl,
          bankTrialLocalRun, costWord,
          K2FiniteSafeEliminationExpected.rawCost]
      · simp [bankTrialSuccessNatStoppedWord,
          bankTrialRenewalFirstLostStop, hl,
          bankTrialLocalRun]
  | cons e tail ih =>
      intro T pre z
      by_cases hl : z.phase = .lost
      · have ht : bankTrialLocalTerminal z := Or.inr hl
        have hrun :=
          bankTrialLocalRunTerminalAbsorbs ring root (e :: tail) z ht
        have hcost :
            costWord (bankTrialLocalNext ring root)
              bankTrialLocalTerminal z (e :: tail) = 0 := by
          simp only [costWord,
            K2FiniteSafeEliminationExpected.rawCost,
            if_pos ht]
        calc
          bankTrialSuccessNatStoppedWord
              (bankTrialLocalNext ring root)
              bankTrialRenewalFirstLostStop
              (fun cut _ _ _ => cut.length)
              T pre z (e :: tail) = pre.length := by
            simp [bankTrialSuccessNatStoppedWord,
              bankTrialRenewalFirstLostStop, hl]
          _ = if (bankTrialLocalRun ring root (e :: tail) z).phase =
              .lost then pre.length +
                costWord (bankTrialLocalNext ring root)
                  bankTrialLocalTerminal z (e :: tail)
              else 0 := by
            rw [hrun, hcost]
            simp [hl]
      · have hs :
            bankTrialRenewalFirstLostStop pre z = false := by
          simp [bankTrialRenewalFirstLostStop, hl]
        by_cases hw : z.phase = .won
        · have ht : bankTrialLocalTerminal z := Or.inl hw
          have hnext := bankTrialLocalTerminalAbsorbs
            ring root e z ht
          have hrun := bankTrialLocalRunTerminalAbsorbs
            ring root (e :: tail) z ht
          have hzero :
              bankTrialSuccessNatStoppedWord
                (bankTrialLocalNext ring root)
                bankTrialRenewalFirstLostStop
                (fun cut _ _ _ => cut.length)
                (T - 1) (pre ++ [e]) z tail = 0 := by
            have hh := ih (T - 1) (pre ++ [e]) z
            rw [bankTrialLocalRunTerminalAbsorbs
              ring root tail z ht] at hh
            simpa [hw] using hh
          calc
            bankTrialSuccessNatStoppedWord
                (bankTrialLocalNext ring root)
                bankTrialRenewalFirstLostStop
                (fun cut _ _ _ => cut.length)
                T pre z (e :: tail) =
              bankTrialSuccessNatStoppedWord
                (bankTrialLocalNext ring root)
                bankTrialRenewalFirstLostStop
                (fun cut _ _ _ => cut.length)
                (T - 1) (pre ++ [e]) z tail := by
              simp only [bankTrialSuccessNatStoppedWord, hs,
                Bool.false_eq_true, if_false, hnext]
            _ = 0 := hzero
            _ = if (bankTrialLocalRun ring root (e :: tail) z).phase =
                .lost then pre.length +
                  costWord (bankTrialLocalNext ring root)
                    bankTrialLocalTerminal z (e :: tail)
                else 0 := by
              rw [hrun]
              simp [hw]
        · have hnotterm : ¬ bankTrialLocalTerminal z := by
            intro ht
            cases ht with
            | inl h => exact hw h
            | inr h => exact hl h
          have hcost :
              costWord (bankTrialLocalNext ring root)
                  bankTrialLocalTerminal z (e :: tail) =
                1 + costWord (bankTrialLocalNext ring root)
                  bankTrialLocalTerminal
                  (bankTrialLocalNext ring root z e) tail := by
            simp only [costWord,
              K2FiniteSafeEliminationExpected.rawCost,
              if_neg hnotterm]
          calc
            bankTrialSuccessNatStoppedWord
                (bankTrialLocalNext ring root)
                bankTrialRenewalFirstLostStop
                (fun cut _ _ _ => cut.length)
                T pre z (e :: tail) =
              bankTrialSuccessNatStoppedWord
                (bankTrialLocalNext ring root)
                bankTrialRenewalFirstLostStop
                (fun cut _ _ _ => cut.length)
                (T - 1) (pre ++ [e])
                  (bankTrialLocalNext ring root z e) tail := by
              simp only [bankTrialSuccessNatStoppedWord, hs,
                Bool.false_eq_true, if_false]
            _ = if (bankTrialLocalRun ring root tail
                (bankTrialLocalNext ring root z e)).phase = .lost then
                (pre ++ [e]).length +
                  costWord (bankTrialLocalNext ring root)
                    bankTrialLocalTerminal
                    (bankTrialLocalNext ring root z e) tail
              else 0 := ih (T - 1) (pre ++ [e])
                (bankTrialLocalNext ring root z e)
            _ = if (bankTrialLocalRun ring root (e :: tail) z).phase =
                .lost then pre.length +
                  costWord (bankTrialLocalNext ring root)
                    bankTrialLocalTerminal z (e :: tail)
              else 0 := by
              rw [hcost]
              simp only [bankTrialLocalRun,
                List.length_append, List.length_singleton,
                Nat.add_assoc]
              rfl

/-- The first-LOST cylinder length moment is exactly the completed
failure cost mass at the SAME horizon T (before any cutoff filter). -/
theorem bankTrialRenewalFirstLostLengthMomentExact
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T : Nat) :
    bankTrialRenewalFirstLostLengthMoment ring root S T =
      bankTrialDurationFailureCostMass ring root S T := by
  unfold bankTrialRenewalFirstLostLengthMoment
  have hmap :
      ((Prob.firstStoppedPrefixes
        (bankTrialLocalNext ring root)
        bankTrialRenewalFirstLostStop T [] (bankTrialLocalStart S)).map
        (fun cut => cut.length * n ^ (T - cut.length))).sum =
      ((Prob.firstStoppedPrefixes
        (bankTrialLocalNext ring root)
        bankTrialRenewalFirstLostStop T [] (bankTrialLocalStart S)).map
        (fun cut => n ^ (T - cut.length) * cut.length)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro cut _
    exact Nat.mul_comm _ _
  calc
    ((Prob.firstStoppedPrefixes
        (bankTrialLocalNext ring root)
        bankTrialRenewalFirstLostStop T [] (bankTrialLocalStart S)).map
        (fun cut => cut.length * n ^ (T - cut.length))).sum =
      ((Prob.firstStoppedPrefixes
        (bankTrialLocalNext ring root)
        bankTrialRenewalFirstLostStop T [] (bankTrialLocalStart S)).map
        (fun cut => n ^ (T - cut.length) * cut.length)).sum := hmap
    _ = Prob.scheduleSum n T (fun word =>
          bankTrialSuccessNatStoppedWord
            (bankTrialLocalNext ring root)
            bankTrialRenewalFirstLostStop
            (fun cut _ _ _ => cut.length)
            T [] (bankTrialLocalStart S) word) :=
      (bankTrialRenewalFirstLostExtensionCount
        ring root S (fun cut _ => cut.length) T).symm
    _ = bankTrialDurationFailureCostMass ring root S T := by
      unfold bankTrialDurationFailureCostMass
      apply congrArg (Prob.scheduleSum n T)
      funext word
      have hh := bankTrialRenewalStoppedLostCostWord
        ring root word T [] (bankTrialLocalStart S)
      simpa only [List.length_nil, Nat.zero_add] using hh

/-- The cutoff-filtered first-LOST length moment is below the
unfiltered completed-LOST cost mass, at the SAME horizon. -/
private theorem bankTrialRenewalBoundedLostMomentLeFailureCost
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T L : Nat) :
    ((Prob.firstStoppedPrefixes
      (bankTrialLocalNext ring root)
      bankTrialRenewalFirstLostStop T [] (bankTrialLocalStart S)).map
      (fun cut =>
        if cut.length ≤ L then
          cut.length * n ^ (T - cut.length) else 0)).sum ≤
    bankTrialDurationFailureCostMass ring root S T := by
  have hmap := bankTrialRenewalMapSumScale 1 1
    (Prob.firstStoppedPrefixes
      (bankTrialLocalNext ring root)
      bankTrialRenewalFirstLostStop T [] (bankTrialLocalStart S))
    (fun cut =>
      if cut.length ≤ L then
        cut.length * n ^ (T - cut.length) else 0)
    (fun cut => cut.length * n ^ (T - cut.length))
    (by
      intro cut _
      split
      · exact Nat.le_refl _
      · exact Nat.zero_le _)
  calc
    ((Prob.firstStoppedPrefixes
        (bankTrialLocalNext ring root)
        bankTrialRenewalFirstLostStop T [] (bankTrialLocalStart S)).map
        (fun cut =>
          if cut.length ≤ L then
            cut.length * n ^ (T - cut.length) else 0)).sum ≤
      bankTrialRenewalFirstLostLengthMoment ring root S T := by
      unfold bankTrialRenewalFirstLostLengthMoment
      simpa only [Nat.one_mul] using hmap
    _ = bankTrialDurationFailureCostMass ring root S T :=
      bankTrialRenewalFirstLostLengthMomentExact ring root S T

/-- Opaque factor inequality: C.6 is sufficient to give the
requested f = 8b+13, even without the hLost lower premise. -/
private theorem bankTrialRenewalLostCostCoefficient
    (b n N : Nat) :
    N * ((8 * b + 12) * n) ≤ N * (n * (8 * b + 13)) := by
  have hc : 8 * b + 12 ≤ 8 * b + 13 := by omega
  calc
    N * ((8 * b + 12) * n) =
      N * (n * (8 * b + 12)) := by
      rw [Nat.mul_comm (8 * b + 12) n]
    _ ≤ N * (n * (8 * b + 13)) :=
      Nat.mul_le_mul_left N (Nat.mul_le_mul_left n hc)

/-- Fc: the requested f = 8b+13 upper bound. It follows from
the unconditional C.6 at T, which is strictly stronger than
invoking completed-failure C.7 under an hLost premise at L.
The hLost premise is therefore NOT needed for this upper bound. -/
theorem bankTrialRenewalLostCostWithinBoundHolds
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (L : Nat) :
    BankTrialRenewalLostCostWithinBound (q := q) ring root
      L (8 * (compileAdvice q).b + 13) := by
  intro S hclean T _
  have hcost := bankTrialDurationC6Holds ring root
    hn hsmall hw hpositive hK S hclean T
  calc
    ((Prob.firstStoppedPrefixes
        (bankTrialLocalNext ring root)
        bankTrialRenewalFirstLostStop T [] (bankTrialLocalStart S)).map
        (fun cut =>
          if cut.length ≤ L then
            cut.length * n ^ (T - cut.length) else 0)).sum ≤
      bankTrialDurationFailureCostMass ring root S T :=
      bankTrialRenewalBoundedLostMomentLeFailureCost
        ring root S T L
    _ ≤ costNumerator (bankTrialLocalNext ring root)
          bankTrialLocalTerminal (bankTrialLocalStart S) T :=
      bankTrialRenewalFailureCostLeTotal ring root S T
    _ ≤ n ^ T * ((8 * (compileAdvice q).b + 12) * n) := hcost
    _ ≤ n ^ T * (n * (8 * (compileAdvice q).b + 13)) :=
      bankTrialRenewalLostCostCoefficient
        (compileAdvice q).b n (n ^ T)

end L3


namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
G13-INDEX-RENEWAL: denominator-cleared lower one-trial bounds.
The W direction needs the reverse of the earlier zero-pattern witness:
local WON implies the zero-failure bounded renewal pattern.
The F direction needs a first-LOST cylinder/padding identity.
No independent-trial assumption is introduced.
-/

/-- When the local observer is not LOST and the next local state is
not LOST, the renewal scanner processes exactly the same edge,
without recording a completed failure. -/
private theorem bankTrialRenewalNoLostStep
    {n q : Nat} (ring : DirectedRing n) (root e : Fin n)
    (z : BankTrialRenewalState q)
    (hnot : z.observer.phase ≠ .lost)
    (hnext :
      (bankTrialLocalNext ring root z.observer e).phase ≠ .lost) :
    (bankTrialRenewalNext ring root z e).observer =
      bankTrialLocalNext ring root z.observer e ∧
    (bankTrialRenewalNext ring root z e).failures = z.failures ∧
    (bankTrialRenewalNext ring root z e).age ≤ z.age + 1 := by
  cases hp : z.observer.phase with
  | won =>
      have hz := bankTrialRenewalNextWon ring root e z hp
      have he := bankTrialLocalTerminalAbsorbs ring root e
        z.observer (Or.inl hp)
      rw [hz, he]
      exact ⟨rfl, rfl, Nat.le_succ _⟩
  | lost =>
      exact False.elim (hnot hp)
  | recovery =>
      simp only [bankTrialRenewalNext, hp]
      unfold bankTrialRenewalAdvance
      rw [if_neg hnext]
      exact ⟨rfl, rfl, Nat.le_refl _⟩
  | live begun =>
      simp only [bankTrialRenewalNext, hp]
      unfold bankTrialRenewalAdvance
      rw [if_neg hnext]
      exact ⟨rfl, rfl, Nat.le_refl _⟩

/-- If the local observer ends WON, it could not previously have
entered the absorbing LOST state.  Hence the renewal observer
agrees with it and adds no failures.  The current age is bounded
by its initial age plus the number of scheduler letters. -/
private theorem bankTrialRenewalLocalWonNoFailures
    {n q : Nat} (ring : DirectedRing n) (root : Fin n) :
    ∀ (word : List (Fin n)) (z : BankTrialRenewalState q),
      z.observer.phase ≠ .lost →
      (bankTrialLocalRun ring root word z.observer).phase = .won →
      (bankTrialRenewalRunFrom ring root word z).observer.phase = .won ∧
      (bankTrialRenewalRunFrom ring root word z).failures = z.failures ∧
      (bankTrialRenewalRunFrom ring root word z).age ≤
        z.age + word.length := by
  intro word
  induction word with
  | nil =>
      intro z _ hwin
      exact ⟨hwin, rfl, by simp [bankTrialRenewalRunFrom]⟩
  | cons e tail ih =>
      intro z hnot hwin
      have hnext :
          (bankTrialLocalNext ring root z.observer e).phase ≠
            .lost := by
        intro hlost
        have ht : bankTrialLocalTerminal
            (bankTrialLocalNext ring root z.observer e) :=
          Or.inr hlost
        have hfreeze := bankTrialLocalRunTerminalAbsorbs
          ring root tail (bankTrialLocalNext ring root z.observer e) ht
        change
          (bankTrialLocalRun ring root tail
            (bankTrialLocalNext ring root z.observer e)).phase =
              .won at hwin
        rw [hfreeze, hlost] at hwin
        cases hwin
      obtain ⟨hobs, hfail, hage⟩ :=
        bankTrialRenewalNoLostStep ring root e z hnot hnext
      have hchildWon :
          (bankTrialLocalRun ring root tail
            (bankTrialRenewalNext ring root z e).observer).phase =
              .won := by
        rw [hobs]
        exact hwin
      have hchildNot :
          (bankTrialRenewalNext ring root z e).observer.phase ≠
            .lost := by
        rw [hobs]
        exact hnext
      obtain ⟨hw, hf, ha⟩ :=
        ih (bankTrialRenewalNext ring root z e)
          hchildNot hchildWon
      refine ⟨hw, ?_, ?_⟩
      · change
          (bankTrialRenewalRunFrom ring root tail
            (bankTrialRenewalNext ring root z e)).failures = z.failures
        exact hf.trans hfail
      · change
          (bankTrialRenewalRunFrom ring root tail
            (bankTrialRenewalNext ring root z e)).age ≤
          z.age + (e :: tail).length
        simp only [List.length_cons]
        omega

/-- The missing reverse implication for index zero.  Unlike the
witness, it starts with local WON and proves the full
zero-failure renewal pattern, including the age cutoff. -/
theorem bankTrialRenewalLocalWonImpliesZeroPattern
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (L : Nat) (word : List (Fin n))
    (hlen : word.length ≤ L)
    (hwon :
      (bankTrialLocalRun ring root word
        (bankTrialLocalStart S)).phase = .won) :
    bankTrialRenewalPattern ring root S L 0 word = true := by
  have hnot : (bankTrialRenewalStart S).observer.phase ≠ .lost := by
    intro h
    cases h
  obtain ⟨hw, hf, ha⟩ :=
    bankTrialRenewalLocalWonNoFailures ring root word
      (bankTrialRenewalStart S) hnot hwon
  have hfail :
      (bankTrialRenewalRun ring root S word).failures = [] := by
    change (bankTrialRenewalRunFrom ring root word
      (bankTrialRenewalStart S)).failures = []
    simpa only [bankTrialRenewalStart] using hf
  have hage :
      (bankTrialRenewalRun ring root S word).age ≤ L := by
    change (bankTrialRenewalRunFrom ring root word
      (bankTrialRenewalStart S)).age ≤ L
    have hz :
        (bankTrialRenewalRunFrom ring root word
          (bankTrialRenewalStart S)).age ≤ word.length := by
      simpa only [bankTrialRenewalStart, Nat.zero_add] using ha
    exact Nat.le_trans hz hlen
  change decide
    ((bankTrialRenewalRun ring root S word).observer.phase = .won ∧
     (bankTrialRenewalRun ring root S word).failures.length = 0 ∧
     (bankTrialRenewalRun ring root S word).failures.all
       (fun age => decide (age ≤ L)) = true ∧
     (bankTrialRenewalRun ring root S word).age ≤ L) = true
  have hphase :
      (bankTrialRenewalRun ring root S word).observer.phase =
        .won := hw
  exact decide_eq_true
    ⟨hphase, by simp [hfail], by simp [hfail], hage⟩

/-- Schedule sums compare pointwise only on words of the counted
length; arbitrary off-horizon words do not need an event inclusion. -/
private theorem bankTrialRenewalScheduleSumMonoAtLength
    (n : Nat) :
    ∀ (T : Nat) (f g : List (Fin n) → Nat),
      (∀ w : List (Fin n), w.length = T → f w ≤ g w) →
      Prob.scheduleSum n T f ≤ Prob.scheduleSum n T g := by
  intro T
  induction T with
  | zero =>
      intro f g h
      rw [bankTrialProbabilityScheduleSumZero,
        bankTrialProbabilityScheduleSumZero]
      exact h [] rfl
  | succ T ih =>
      intro f g h
      rw [bankTrialProbabilityScheduleSumFirst,
        bankTrialProbabilityScheduleSumFirst]
      apply ofFn_sum_le
      intro e
      exact ih
        (fun w => f (e :: w))
        (fun w => g (e :: w))
        (fun w hw => h (e :: w)
          (by simp only [List.length_cons, hw]))

/-- The local completed WON numerator at horizon L is contained
in the index-zero renewal pattern mass at that same horizon. -/
private theorem bankTrialRenewalWonLeZeroMassAtHorizon
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (L : Nat) :
    bankTrialProbabilityWinMass ring root S L ≤
      bankTrialRenewalPatternMass ring root S L L 0 := by
  unfold bankTrialProbabilityWinMass bankTrialRenewalPatternMass
  apply bankTrialRenewalScheduleSumMonoAtLength n L
  intro word hlen
  by_cases hw :
      (bankTrialLocalRun ring root word
        (bankTrialLocalStart S)).phase = .won
  · have hpat := bankTrialRenewalLocalWonImpliesZeroPattern
      ring root S L word (by omega) hw
    simp [hw, hpat, Prob.indicator]
  · simp [hw]

/-- Count a length-(L+m) tape by its first L letters and its
remaining m letters.  This is an exact finite-word identity. -/
private theorem bankTrialRenewalScheduleSumConcat
    (n : Nat) :
    ∀ (L m : Nat) (f : List (Fin n) → Nat),
      Prob.scheduleSum n (L + m) f =
        Prob.scheduleSum n L (fun pre =>
          Prob.scheduleSum n m (fun suffix => f (pre ++ suffix))) := by
  intro L
  induction L with
  | zero =>
      intro m f
      rw [bankTrialProbabilityScheduleSumZero]
      simp only [Nat.zero_add, List.nil_append]
  | succ L ih =>
      intro m f
      have hsum : (L + 1) + m = (L + m) + 1 := by omega
      rw [hsum, bankTrialProbabilityScheduleSumFirst,
        bankTrialProbabilityScheduleSumFirst]
      apply ofFn_sum_eq
      intro e
      simpa only [List.cons_append] using
        (ih m (fun word => f (e :: word)))

/-- Completed index-zero patterns are suffix-stable, so padding
by m letters multiplies their finite-horizon mass by at least n^m. -/
private theorem bankTrialRenewalZeroMassPadding
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (L m : Nat) :
    n ^ m * bankTrialRenewalPatternMass ring root S L L 0 ≤
      bankTrialRenewalPatternMass ring root S (L + m) L 0 := by
  unfold bankTrialRenewalPatternMass
  rw [bankTrialRenewalScheduleSumConcat n L m]
  calc
    n ^ m * Prob.scheduleSum n L (fun word =>
        Prob.indicator (bankTrialRenewalPattern
          ring root S L 0 word)) =
      Prob.scheduleSum n L (fun pre =>
        n ^ m * Prob.indicator
          (bankTrialRenewalPattern ring root S L 0 pre)) :=
      (bankTrialSuccessScheduleSumScale n L (n ^ m) _).symm
    _ = Prob.scheduleSum n L (fun pre =>
          Prob.scheduleSum n m (fun _ =>
            Prob.indicator (bankTrialRenewalPattern
              ring root S L 0 pre))) := by
        apply congrArg (Prob.scheduleSum n L)
        funext pre
        rw [bankTrialProbabilityScheduleSumConst]
    _ ≤ Prob.scheduleSum n L (fun pre =>
          Prob.scheduleSum n m (fun suffix =>
            Prob.indicator (bankTrialRenewalPattern
              ring root S L 0 (pre ++ suffix)))) := by
        apply bankTrialProbabilityScheduleSumMono n L
        intro pre
        apply bankTrialProbabilityScheduleSumMono n m
        intro suffix
        cases hp : bankTrialRenewalPattern
            ring root S L 0 pre with
        | false =>
            simp [Prob.indicator, hp]
        | true =>
            have happ := bankTrialRenewalPatternAppend
              ring root S L 0 pre suffix hp
            simp [Prob.indicator, hp, happ]

/-- Pure Nat arithmetic on opaque scheduler numerators. -/
private theorem bankTrialRenewalLowerPadArithmetic
    (lo den N pad old new : Nat)
    (hbase : lo * N ≤ den * old)
    (hpad : pad * old ≤ new) :
    lo * (N * pad) ≤ den * new := by
  calc
    lo * (N * pad) = pad * (lo * N) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ pad * (den * old) :=
      Nat.mul_le_mul_left pad hbase
    _ = den * (pad * old) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ den * new :=
      Nat.mul_le_mul_left den hpad

/-- W from the uniform completed-WON cutoff, with the literal
numerator B=(8b+12)n and denominator L. -/
theorem bankTrialRenewalWonWithinBoundOfCutoff
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (L : Nat)
    (hcut : ∀ S : GrantBankReference.BankLocalReference
        (compileAdvice q).b,
      BankTrialLocalClean q S →
      ((8 * (compileAdvice q).b + 12) * n) * n ^ L ≤
        L * bankTrialProbabilityWinMass ring root S L) :
    BankTrialRenewalWonWithinBound (q := q) ring root L
      ((8 * (compileAdvice q).b + 12) * n) L := by
  intro S hclean T hLT
  have hbase :
      ((8 * (compileAdvice q).b + 12) * n) * n ^ L ≤
      L * bankTrialRenewalPatternMass ring root S L L 0 :=
    Nat.le_trans (hcut S hclean)
      (Nat.mul_le_mul_left L
        (bankTrialRenewalWonLeZeroMassAtHorizon ring root S L))
  have hsum : L + (T - L) = T := by omega
  have hpower : n ^ T = n ^ L * n ^ (T - L) := by
    calc
      n ^ T = n ^ (L + (T - L)) := by rw [hsum]
      _ = n ^ L * n ^ (T - L) := Nat.pow_add n L (T - L)
  have hpad :
      n ^ (T - L) *
        bankTrialRenewalPatternMass ring root S L L 0 ≤
      bankTrialRenewalPatternMass ring root S T L 0 := by
    have h := bankTrialRenewalZeroMassPadding
      ring root S L (T - L)
    simpa only [hsum] using h
  rw [hpower]
  exact bankTrialRenewalLowerPadArithmetic
    ((8 * (compileAdvice q).b + 12) * n) L
    (n ^ L) (n ^ (T - L))
    (bankTrialRenewalPatternMass ring root S L L 0)
    (bankTrialRenewalPatternMass ring root S T L 0)
    hbase hpad

/-- Generic finite first-stop cylinder mass with an independent
cutoff L on the length of the selected stopping pfx. -/
private def bankTrialRenewalBoundedStopMass
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (T L : Nat) (pre : List (Fin n)) (x : X) : Nat :=
  ((Prob.firstStoppedPrefixes next stop T pre x).map
    (fun cut =>
      if cut.length ≤ L then n ^ (T - cut.length) else 0)).sum

/-- An already stopped initial state contributes its empty cut. -/
private theorem bankTrialRenewalBoundedStopAtStop
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (T L : Nat) (pre : List (Fin n)) (x : X)
    (hs : stop pre x = true) :
    bankTrialRenewalBoundedStopMass next stop T L pre x =
      n ^ T := by
  cases T with
  | zero =>
      simp [bankTrialRenewalBoundedStopMass,
        Prob.firstStoppedPrefixes, hs]
  | succ T =>
      simp [bankTrialRenewalBoundedStopMass,
        Prob.firstStoppedPrefixes, hs]

/-- If the current state has not stopped, every first stopping
pfx has positive length, so none passes cutoff zero. -/
private theorem bankTrialRenewalBoundedStopZero
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (T : Nat) (pre : List (Fin n)) (x : X)
    (hs : stop pre x = false) :
    bankTrialRenewalBoundedStopMass next stop T 0 pre x =
      0 := by
  cases T with
  | zero =>
      simp [bankTrialRenewalBoundedStopMass,
        Prob.firstStoppedPrefixes, hs]
  | succ T =>
      unfold bankTrialRenewalBoundedStopMass
      simp only [Prob.firstStoppedPrefixes, hs,
        Bool.false_eq_true, if_false]
      rw [bankTrialSuccessNatStoppedFlatMap]
      simp only [List.map_ofFn, List.map_map, Function.comp_def]
      have hrow (e : Fin n) :
          ((Prob.firstStoppedPrefixes next stop T
            (pre ++ [e]) (next x e)).map
              (fun cut =>
                if (e :: cut).length ≤ 0 then
                  n ^ ((T + 1) - (e :: cut).length)
                else 0)).sum = 0 := by
        have hf :
            (fun cut : List (Fin n) =>
              if (e :: cut).length ≤ 0 then
                n ^ ((T + 1) - (e :: cut).length)
              else 0) = (fun _ => 0) := by
          funext cut
          have hfalse : ¬ (e :: cut).length ≤ 0 := by
            simp only [List.length_cons]
            omega
          simp [hfalse]
        rw [hf]
        generalize Prob.firstStoppedPrefixes next stop T
          (pre ++ [e]) (next x e) = xs
        induction xs with
        | nil => rfl
        | cons a xs ih => simp only [List.map_cons, List.sum_cons, ih]
      have hsum :
          (List.ofFn (fun e : Fin n =>
            ((Prob.firstStoppedPrefixes next stop T
              (pre ++ [e]) (next x e)).map
                (fun cut =>
                  if (e :: cut).length ≤ 0 then
                    n ^ ((T + 1) - (e :: cut).length)
                  else 0)).sum)).sum =
          (List.ofFn (fun _ : Fin n => 0)).sum :=
        ofFn_sum_eq _ _ hrow
      rw [hsum, ofFn_sum_const]
      simp

/-- Consuming one letter advances the remaining horizon and
decreases the relative cutoff by one. -/
private theorem bankTrialRenewalBoundedStopSucc
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (T L : Nat) (pre : List (Fin n)) (x : X)
    (hs : stop pre x = false) :
    bankTrialRenewalBoundedStopMass next stop (T + 1)
        (L + 1) pre x =
      (List.ofFn (fun e : Fin n =>
        bankTrialRenewalBoundedStopMass next stop T L
          (pre ++ [e]) (next x e))).sum := by
  unfold bankTrialRenewalBoundedStopMass
  simp only [Prob.firstStoppedPrefixes, hs,
    Bool.false_eq_true, if_false]
  rw [bankTrialSuccessNatStoppedFlatMap]
  simp only [List.map_ofFn, List.map_map, Function.comp_def]
  apply ofFn_sum_eq
  intro e
  apply bankTrialSuccessCutHistoryMapSumExt
  intro cut
  have hsub :
      (T + 1) - (e :: cut).length = T - cut.length := by
    simp only [List.length_cons]
    omega
  rw [hsub]
  by_cases hb : cut.length ≤ L
  · have he : (e :: cut).length ≤ L + 1 := by
      simp only [List.length_cons]
      omega
    simp [hb, he]
  · have he : ¬ (e :: cut).length ≤ L + 1 := by
      simp only [List.length_cons]
      omega
    simp [hb, he]

/-- A bounded first-stop cylinder depends only on the first L
letters; an independent suffix of m letters contributes n^m
extensions. This is a combinatorial statement, not a stochastic
independence assertion about repeated trials. -/
private theorem bankTrialRenewalBoundedStopPadding
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool) :
    ∀ (L m : Nat) (pre : List (Fin n)) (x : X),
      bankTrialRenewalBoundedStopMass next stop
          (L + m) L pre x =
        n ^ m * bankTrialRenewalBoundedStopMass
          next stop L L pre x := by
  intro L
  induction L with
  | zero =>
      intro m pre x
      simp only [Nat.zero_add]
      cases hs : stop pre x with
      | true =>
          rw [bankTrialRenewalBoundedStopAtStop
            next stop m 0 pre x hs,
            bankTrialRenewalBoundedStopAtStop
              next stop 0 0 pre x hs]
          simp
      | false =>
          rw [bankTrialRenewalBoundedStopZero
            next stop m pre x hs,
            bankTrialRenewalBoundedStopZero
              next stop 0 pre x hs]
          simp
  | succ L ih =>
      intro m pre x
      cases hs : stop pre x with
      | true =>
          rw [bankTrialRenewalBoundedStopAtStop
            next stop ((L + 1) + m) (L + 1) pre x hs,
            bankTrialRenewalBoundedStopAtStop
              next stop (L + 1) (L + 1) pre x hs,
            Nat.pow_add]
          exact Nat.mul_comm _ _
      | false =>
          have hsum : (L + 1) + m = (L + m) + 1 := by omega
          rw [hsum,
            bankTrialRenewalBoundedStopSucc
              next stop (L + m) L pre x hs,
            bankTrialRenewalBoundedStopSucc
              next stop L L pre x hs]
          calc
            (List.ofFn (fun e : Fin n =>
                bankTrialRenewalBoundedStopMass next stop
                  (L + m) L (pre ++ [e]) (next x e))).sum =
              (List.ofFn (fun e : Fin n =>
                n ^ m * bankTrialRenewalBoundedStopMass next stop
                  L L (pre ++ [e]) (next x e))).sum :=
                ofFn_sum_eq _ _ (fun e =>
                  ih m (pre ++ [e]) (next x e))
            _ = n ^ m *
                (List.ofFn (fun e : Fin n =>
                  bankTrialRenewalBoundedStopMass next stop
                    L L (pre ++ [e]) (next x e))).sum :=
                  ofFn_sum_mul_left (n ^ m) _

/-- The actual bank first-LOST extension mass obeys the same
exact cylinder padding law. -/
theorem bankTrialRenewalLostBoundedExtensionPadding
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (L m : Nat) :
    bankTrialRenewalLostBoundedExtensionMass
        ring root S (L + m) L =
      n ^ m * bankTrialRenewalLostBoundedExtensionMass
        ring root S L L := by
  change bankTrialRenewalBoundedStopMass
      (bankTrialLocalNext ring root)
      bankTrialRenewalFirstLostStop (L + m) L []
      (bankTrialLocalStart S) =
    n ^ m * bankTrialRenewalBoundedStopMass
      (bankTrialLocalNext ring root)
      bankTrialRenewalFirstLostStop L L []
      (bankTrialLocalStart S)
  exact bankTrialRenewalBoundedStopPadding
    (bankTrialLocalNext ring root)
    bankTrialRenewalFirstLostStop L m []
    (bankTrialLocalStart S)

/-- Every enumerated first stopping cut has length at most the
enumeration horizon. This variant is local, since the corresponding
lemma in BankTrialSuccess is private to that source. -/
private theorem bankTrialRenewalFirstStoppedCutLengthLe
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool) :
    ∀ (T : Nat) (pre : List (Fin n)) (x : X)
      (cut : List (Fin n)),
      cut ∈ Prob.firstStoppedPrefixes next stop T pre x →
      cut.length ≤ T := by
  intro T
  induction T with
  | zero =>
      intro pre x cut hcut
      cases hs : stop pre x with
      | true =>
          have heq : cut = [] := by
            simpa [Prob.firstStoppedPrefixes, hs] using hcut
          rw [heq]
          exact Nat.le_refl _
      | false =>
          have hempty : cut ∈ ([] : List (List (Fin n))) := by
            simpa [Prob.firstStoppedPrefixes, hs] using hcut
          cases hempty
  | succ T ih =>
      intro pre x cut hcut
      cases hs : stop pre x with
      | true =>
          have heq : cut = [] := by
            simpa [Prob.firstStoppedPrefixes, hs] using hcut
          rw [heq]
          exact Nat.zero_le _
      | false =>
          have hflat : cut ∈
              (List.ofFn (fun e : Fin n => e)).flatMap
                (fun e =>
                  (Prob.firstStoppedPrefixes next stop T
                    (pre ++ [e]) (next x e)).map (List.cons e)) := by
            simpa [Prob.firstStoppedPrefixes, hs] using hcut
          obtain ⟨e, _, hem⟩ := List.mem_flatMap.mp hflat
          obtain ⟨tail, htail, hcutEq⟩ := List.mem_map.mp hem
          rw [← hcutEq]
          have hlen := ih (pre ++ [e]) (next x e) tail htail
          simp only [List.length_cons]
          omega

/-- A mapped list sum may be rewritten using equations that hold
only on elements of that list. -/
private theorem bankTrialRenewalMapSumOnMembers
    {A : Type} (xs : List A) (f g : A → Nat)
    (h : ∀ x, x ∈ xs → f x = g x) :
    (xs.map f).sum = (xs.map g).sum := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      have hx : f x = g x := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [List.map_cons, List.sum_cons]
      rw [hx, ht]

/-- This is a first-stop count, not a duration cost: 1 is returned
exactly when the local observer reaches absorbing LOST. -/
private theorem bankTrialRenewalStoppedLostUnit
    {n q : Nat} (ring : DirectedRing n) (root : Fin n) :
    ∀ (word : List (Fin n)) (T : Nat)
      (pre : List (Fin n)) (z : BankTrialLocalState q),
      bankTrialSuccessNatStoppedWord
        (bankTrialLocalNext ring root)
        bankTrialRenewalFirstLostStop
        (fun _ _ _ _ => 1) T pre z word =
      if (bankTrialLocalRun ring root word z).phase = .lost
      then 1 else 0 := by
  intro word
  induction word with
  | nil =>
      intro T pre z
      by_cases hl : z.phase = .lost
      · simp [bankTrialSuccessNatStoppedWord,
          bankTrialRenewalFirstLostStop,
          bankTrialLocalRun, hl]
      · simp [bankTrialSuccessNatStoppedWord,
          bankTrialRenewalFirstLostStop,
          bankTrialLocalRun, hl]
  | cons e tail ih =>
      intro T pre z
      by_cases hl : z.phase = .lost
      · have ht : bankTrialLocalTerminal z := Or.inr hl
        have hfreeze := bankTrialLocalRunTerminalAbsorbs
          ring root (e :: tail) z ht
        simp [bankTrialSuccessNatStoppedWord,
          bankTrialRenewalFirstLostStop, hl, hfreeze]
      · have hchild := ih (T - 1) (pre ++ [e])
          (bankTrialLocalNext ring root z e)
        have hs : bankTrialRenewalFirstLostStop pre z = false := by
          simp [bankTrialRenewalFirstLostStop, hl]
        rw [bankTrialSuccessNatStoppedWord]
        simp only [hs, Bool.false_eq_true, if_false]
        exact hchild

/-- All unfiltered first-LOST extension cylinders have exactly
the ordinary local completed-LOST numerator at the same horizon. -/
theorem bankTrialRenewalFirstLostExtensionMassExact
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (T : Nat) :
    ((Prob.firstStoppedPrefixes
      (bankTrialLocalNext ring root)
      bankTrialRenewalFirstLostStop T []
      (bankTrialLocalStart S)).map
      (fun cut => n ^ (T - cut.length))).sum =
    bankTrialDurationFailureMass ring root S T := by
  calc
    ((Prob.firstStoppedPrefixes
        (bankTrialLocalNext ring root)
        bankTrialRenewalFirstLostStop T []
        (bankTrialLocalStart S)).map
        (fun cut => n ^ (T - cut.length))).sum =
      Prob.scheduleSum n T (fun word =>
        bankTrialSuccessNatStoppedWord
          (bankTrialLocalNext ring root)
          bankTrialRenewalFirstLostStop
          (fun _ _ _ _ => 1)
          T [] (bankTrialLocalStart S) word) := by
      simpa only [Nat.mul_one] using
        (bankTrialRenewalFirstLostExtensionCount
          ring root S (fun _ _ => 1) T).symm
    _ = bankTrialDurationFailureMass ring root S T := by
      unfold bankTrialDurationFailureMass
      apply congrArg (Prob.scheduleSum n T)
      funext word
      exact bankTrialRenewalStoppedLostUnit
        ring root word T [] (bankTrialLocalStart S)

/-- Every selected first-LOST pfx at horizon L has length <= L.
Thus the cutoff filter at L discards none of its mass. -/
theorem bankTrialRenewalLostBoundedAtHorizonExact
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b) (L : Nat) :
    bankTrialRenewalLostBoundedExtensionMass ring root S L L =
      bankTrialDurationFailureMass ring root S L := by
  unfold bankTrialRenewalLostBoundedExtensionMass
  calc
    ((Prob.firstStoppedPrefixes
        (bankTrialLocalNext ring root)
        bankTrialRenewalFirstLostStop L []
        (bankTrialLocalStart S)).map
        (fun cut =>
          if cut.length ≤ L then n ^ (L - cut.length) else 0)).sum =
      ((Prob.firstStoppedPrefixes
        (bankTrialLocalNext ring root)
        bankTrialRenewalFirstLostStop L []
        (bankTrialLocalStart S)).map
        (fun cut => n ^ (L - cut.length))).sum := by
      apply bankTrialRenewalMapSumOnMembers
      intro cut hcut
      rw [if_pos
        (bankTrialRenewalFirstStoppedCutLengthLe
          (bankTrialLocalNext ring root)
          bankTrialRenewalFirstLostStop L []
          (bankTrialLocalStart S) cut hcut)]
    _ = bankTrialDurationFailureMass ring root S L :=
      bankTrialRenewalFirstLostExtensionMassExact ring root S L

/-- Nat subtraction budget: a bound on the other two categories
gives a lower bound on the remaining category. -/
private theorem bankTrialRenewalLossComplementArithmetic
    (a c N lost other : Nat)
    (hpart : lost + other = N)
    (hother : a * other ≤ c * N) :
    (a - c) * N ≤ a * lost := by
  by_cases hc : c ≤ a
  · have hsplit : a = (a - c) + c := by omega
    have htotal : a * N = a * lost + a * other := by
      rw [← hpart, Nat.mul_add]
    have hbudget : a * N = (a - c) * N + c * N := by
      rw [← Nat.add_mul, ← hsplit]
    omega
  · have hzero : a - c = 0 := by omega
    simp [hzero]

/-- The trichotomy/rarity/ACTIVE inequality, proved on opaque
natural coefficients before any instantiation with big powers. -/
private theorem bankTrialRenewalLostLowerArithmetic
    (L Q B N W F A : Nat)
    (hpart : W + (F + A) = N)
    (hwon : Q * W ≤ N)
    (hactive : L * A ≤ N * B) :
    (L * Q - L - Q * B) * N ≤
      (L * Q) * F := by
  have hother :
      (L * Q) * (W + A) ≤ (L + Q * B) * N := by
    calc
      (L * Q) * (W + A) =
          L * (Q * W) + Q * (L * A) := by
        simp only [Nat.mul_add, Nat.mul_assoc,
          Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ L * N + Q * (N * B) :=
        Nat.add_le_add
          (Nat.mul_le_mul_left L hwon)
          (Nat.mul_le_mul_left Q hactive)
      _ = (L + Q * B) * N := by
        rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm N B]
  have hswap : F + (W + A) = N := by omega
  have hbound := bankTrialRenewalLossComplementArithmetic
    (L * Q) (L + Q * B) N F (W + A) hswap hother
  simpa only [Nat.sub_sub] using hbound

/-- F: lower first-LOST-by-L mass with the cleared coefficients
lo=L*2^K-L-2^K*(8b+12)n and den=L*2^K.
The uniform WON cutoff is NOT required for this lower bound:
trichotomy, C.4 head rarity and the unconditional ACTIVE
Markov bound already imply it. -/
theorem bankTrialRenewalLostWithinBoundOfCutoff
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (L : Nat) :
    BankTrialRenewalLostWithinBound (q := q) ring root L
      (L * 2 ^ (compileAdvice q).K - L -
        2 ^ (compileAdvice q).K *
          ((8 * (compileAdvice q).b + 12) * n))
      (L * 2 ^ (compileAdvice q).K) := by
  intro S hclean T hLT
  have hrareZero :=
    (bankTrialRenewalZeroRareWithinBoundHolds
      ring root hn hsmall hw hlarge hpositive hK L)
      S hclean L (Nat.le_refl L)
  have hlocalWonRare :
      2 ^ (compileAdvice q).K *
        bankTrialProbabilityWinMass ring root S L ≤ n ^ L :=
    Nat.le_trans
      (Nat.mul_le_mul_left (2 ^ (compileAdvice q).K)
        (bankTrialRenewalWonLeZeroMassAtHorizon ring root S L))
      hrareZero
  have hpart := bankTrialDurationMassPartition ring root S L
  have hactive := bankTrialRenewalActiveCutoff
    ring root hn hsmall hw hpositive hK S hclean L
  have hbase :
      (L * 2 ^ (compileAdvice q).K - L -
        2 ^ (compileAdvice q).K *
          ((8 * (compileAdvice q).b + 12) * n)) * n ^ L ≤
        (L * 2 ^ (compileAdvice q).K) *
          bankTrialRenewalLostBoundedExtensionMass
            ring root S L L := by
    rw [bankTrialRenewalLostBoundedAtHorizonExact ring root S L]
    exact bankTrialRenewalLostLowerArithmetic
      L (2 ^ (compileAdvice q).K)
      ((8 * (compileAdvice q).b + 12) * n)
      (n ^ L)
      (bankTrialProbabilityWinMass ring root S L)
      (bankTrialDurationFailureMass ring root S L)
      (bankTrialDurationActiveMass ring root S L)
      hpart hlocalWonRare hactive
  have hsum : L + (T - L) = T := by omega
  have hpower : n ^ T = n ^ L * n ^ (T - L) := by
    calc
      n ^ T = n ^ (L + (T - L)) := by rw [hsum]
      _ = n ^ L * n ^ (T - L) := Nat.pow_add n L (T - L)
  have hpad :
      n ^ (T - L) *
        bankTrialRenewalLostBoundedExtensionMass
          ring root S L L ≤
      bankTrialRenewalLostBoundedExtensionMass
        ring root S T L := by
    have h := bankTrialRenewalLostBoundedExtensionPadding
      ring root S L (T - L)
    rw [hsum] at h
    exact Nat.le_of_eq h.symm
  rw [hpower]
  exact bankTrialRenewalLowerPadArithmetic
    (L * 2 ^ (compileAdvice q).K - L -
      2 ^ (compileAdvice q).K *
        ((8 * (compileAdvice q).b + 12) * n))
    (L * 2 ^ (compileAdvice q).K)
    (n ^ L) (n ^ (T - L))
    (bankTrialRenewalLostBoundedExtensionMass ring root S L L)
    (bankTrialRenewalLostBoundedExtensionMass ring root S T L)
    hbase hpad

/-- Optional common-denominator W form needed when passing W and F
to the already merged mass-sandwich theorem in one application.
Multiplication by 2^K is pure cleared-integer scaling. -/
theorem bankTrialRenewalWonWithinBoundCommonDenOfCutoff
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (L : Nat)
    (hcut : ∀ S : GrantBankReference.BankLocalReference
        (compileAdvice q).b,
      BankTrialLocalClean q S →
      ((8 * (compileAdvice q).b + 12) * n) * n ^ L ≤
        L * bankTrialProbabilityWinMass ring root S L) :
    BankTrialRenewalWonWithinBound (q := q) ring root L
      (((8 * (compileAdvice q).b + 12) * n) *
        2 ^ (compileAdvice q).K)
      (L * 2 ^ (compileAdvice q).K) := by
  intro S hclean T hLT
  have h := (bankTrialRenewalWonWithinBoundOfCutoff
    ring root L hcut) S hclean T hLT
  have hscaled := Nat.mul_le_mul_left
    (2 ^ (compileAdvice q).K) h
  simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    using hscaled

end L3


namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
G13-INDEX-RENEWAL. The strengthened
window below does not need the old unused H*L <= T hypothesis.
-/

/-- Success by W, evaluated on the original renewal run's
first W letters. -/
noncomputable def bankTrialRenewalSuccessBy {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (W : Nat) (word : List (Fin n)) : Bool :=
  bankTrialRenewalHitWord ring root S W word

/-- Exact equality with the user's frozen-pfx specification. -/
theorem bankTrialRenewalSuccessByRun {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (W : Nat) (word : List (Fin n)) :
    bankTrialRenewalSuccessBy ring root S W word =
      decide ((bankTrialRenewalRun ring root S
        (word.take W)).observer.phase = .won) := by
  rfl

/-- Original length-T scheduler numerator of success by W. -/
noncomputable def bankTrialRenewalSuccessMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (T W : Nat) : Nat :=
  Prob.scheduleSum n T (fun word =>
    Prob.indicator (bankTrialRenewalSuccessBy ring root S W word))

/-- Existing HitMass counts precisely this same event. -/
theorem bankTrialRenewalSuccessMassEqHitMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (T W : Nat) :
    bankTrialRenewalSuccessMass ring root S T W =
      bankTrialRenewalHitMass ring root S T W := by
  rfl

/-- Negative form of the existing disjointness theorem: if i
occurs, no different pattern index j can occur on that word. -/
theorem bankTrialRenewalOtherPatternFalse {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (L i j : Nat) (word : List (Fin n))
    (hne : i ≠ j)
    (hi : bankTrialRenewalPattern ring root S L i word = true) :
    bankTrialRenewalPattern ring root S L j word = false := by
  cases hj : bankTrialRenewalPattern ring root S L j word with
  | false =>
      rfl
  | true =>
      have heq :=
        bankTrialRenewalPatternDisjoint ring root S L i j word hi hj
      exact False.elim (hne heq)

/-- Soundness for the newly named event: a completed pattern
charged at most W must already be WON on word.take W. -/
theorem bankTrialRenewalPatternSuccessByOfTauLe {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (L j W : Nat) (word : List (Fin n))
    (hpattern :
      bankTrialRenewalPattern ring root S L j word = true)
    (htau :
      bankTrialRenewalTau ring root S L j word ≤ W) :
    bankTrialRenewalSuccessBy ring root S W word = true := by
  exact bankTrialRenewalPatternSound
    ring root S L j W word hpattern htau

/-- Stronger window theorem under exactly W <= T, without any
condition H*L <= T. The proof itself is the original finite
wordwise inequality followed by one scheduleSum. -/
theorem bankTrialRenewalWindowInequalitySuccessMass {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (T L W H : Nat)
    (_hwindow : W ≤ T) :
    W * bankTrialSuccessStageIndexSum (fun j =>
      bankTrialRenewalPatternMass ring root S T L j) H ≤
    W * bankTrialRenewalSuccessMass ring root S T W +
      bankTrialSuccessStageIndexSum (fun j =>
        bankTrialRenewalPatternCost ring root S T L j) H := by
  calc
    W * bankTrialSuccessStageIndexSum (fun j =>
        bankTrialRenewalPatternMass ring root S T L j) H =
      W * Prob.scheduleSum n T (fun word =>
        bankTrialSuccessStageIndexSum (fun j =>
          Prob.indicator
            (bankTrialRenewalPattern ring root S L j word)) H) := by
        unfold bankTrialRenewalPatternMass
        rw [bankTrialSuccessStageIndexSumSchedule]
    _ = Prob.scheduleSum n T (fun word =>
          W * bankTrialSuccessStageIndexSum (fun j =>
            Prob.indicator
              (bankTrialRenewalPattern ring root S L j word)) H) :=
      (bankTrialSuccessScheduleSumScale n T W _).symm
    _ ≤ Prob.scheduleSum n T (fun word =>
          W * Prob.indicator
            (bankTrialRenewalSuccessBy ring root S W word) +
          bankTrialSuccessStageIndexSum (fun j =>
            bankTrialRenewalTau ring root S L j word) H) := by
        apply bankTrialProbabilityScheduleSumMono n T
        intro word
        simpa only [bankTrialRenewalSuccessBy] using
          (bankTrialRenewalWordWindow ring root S L W H word)
    _ = W * bankTrialRenewalSuccessMass ring root S T W +
          bankTrialSuccessStageIndexSum (fun j =>
            bankTrialRenewalPatternCost ring root S T L j) H := by
        rw [bankTrialC5ScheduleSumAdd,
          bankTrialSuccessScheduleSumScale]
        rw [← bankTrialSuccessStageIndexSumSchedule]
        rfl

/-- Monotonicity of finite stage sums under bounds valid only
for indices j < H. -/
private theorem bankTrialRenewalStageIndexMonoBelow
    (f g : Nat → Nat) :
    ∀ (H : Nat),
      (∀ j, j < H → f j ≤ g j) →
      bankTrialSuccessStageIndexSum f H ≤
        bankTrialSuccessStageIndexSum g H := by
  intro H
  induction H with
  | zero =>
      intro _
      exact Nat.le_refl _
  | succ k ih =>
      intro h
      change
        bankTrialSuccessStageIndexSum f k + f k ≤
          bankTrialSuccessStageIndexSum g k + g k
      have hsmall : ∀ j, j < k → f j ≤ g j := by
        intro j hj
        exact h j (by omega)
      exact Nat.add_le_add (ih hsmall) (h k (by omega))

/-- Clear den^(j+1) to den^H. The only omega calculation
is on the index identity, not on any compiled large power. -/
private theorem bankTrialRenewalCommonPowerLift
    (den lo win N H j mass : Nat)
    (hj : j + 1 ≤ H)
    (hmass :
      lo ^ j * win * N ≤ den ^ (j + 1) * mass) :
    N * (lo ^ j * win * den ^ (H - (j + 1))) ≤
      den ^ H * mass := by
  have hscaled :=
    Nat.mul_le_mul_right (den ^ (H - (j + 1))) hmass
  calc
    N * (lo ^ j * win * den ^ (H - (j + 1))) =
        (lo ^ j * win * N) * den ^ (H - (j + 1)) := by
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ (den ^ (j + 1) * mass) *
        den ^ (H - (j + 1)) := hscaled
    _ = (den ^ (j + 1) * den ^ (H - (j + 1))) *
        mass := by
          simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ = den ^ H * mass := by
          have hsum :
              (j + 1) + (H - (j + 1)) = H := by omega
          rw [← Nat.pow_add, hsum]

/-- Combine the two cleared sandwiches with one window
inequality. All factors are opaque natural numbers. -/
private theorem bankTrialRenewalCombineWindowOpaque
    (W Q N D A M hit cost B : Nat)
    (hmass : N * A ≤ D * M)
    (hwindow : W * M ≤ W * hit + cost)
    (hcost : Q * cost ≤ N * B) :
    W * Q * N * A ≤
      D * (W * Q * hit + N * B) := by
  calc
    W * Q * N * A = (W * Q) * (N * A) := by
      rw [Nat.mul_assoc]
    _ ≤ (W * Q) * (D * M) :=
      Nat.mul_le_mul_left _ hmass
    _ = (D * Q) * (W * M) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ (D * Q) * (W * hit + cost) :=
      Nat.mul_le_mul_left _ hwindow
    _ = D * (W * Q * hit + Q * cost) := by
      simp only [Nat.mul_add, Nat.mul_assoc,
        Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ D * (W * Q * hit + N * B) :=
      Nat.mul_le_mul_left D (Nat.add_le_add_left hcost _)

/-- Cleared finite-window consequence of the mass/cost sandwiches.
The (j+1)*L <= T budget holds for every index j<H because
H*L <= T. This has no positivity/divisibility premises and is
valid for H=0, den=0, or lo=0. -/
theorem bankTrialRenewalClearedWindowOfSandwiches
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (L lo win den f g H T W : Nat)
    (hwindow : W ≤ T)
    (hbudget : H * L ≤ T)
    (hmass : BankTrialRenewalMassSandwichTarget
      (q := q) ring root L lo win den)
    (hcost : BankTrialRenewalCostSandwichTarget
      (q := q) ring root L f g) :
    W * (2 ^ (compileAdvice q).K) * n ^ T *
      bankTrialSuccessStageIndexSum (fun j =>
        lo ^ j * win * den ^ (H - (j + 1))) H ≤
    den ^ H *
      (W * (2 ^ (compileAdvice q).K) *
        bankTrialRenewalSuccessMass ring root S T W +
       n ^ T * bankTrialSuccessStageIndexSum (fun j =>
         n * (g + j * f)) H) := by
  have hmassSum :
      n ^ T *
        bankTrialSuccessStageIndexSum (fun j =>
          lo ^ j * win * den ^ (H - (j + 1))) H ≤
      den ^ H * bankTrialSuccessStageIndexSum (fun j =>
        bankTrialRenewalPatternMass ring root S T L j) H := by
    have hbound :=
      bankTrialRenewalStageIndexMonoBelow
        (fun j =>
          n ^ T * (lo ^ j * win * den ^ (H - (j + 1))))
        (fun j =>
          den ^ H *
            bankTrialRenewalPatternMass ring root S T L j)
        H (by
          intro j hj
          have hindex : j + 1 ≤ H := by omega
          have hperiod : (j + 1) * L ≤ T :=
            Nat.le_trans
              (Nat.mul_le_mul_right L hindex) hbudget
          exact bankTrialRenewalCommonPowerLift
            den lo win (n ^ T) H j
            (bankTrialRenewalPatternMass ring root S T L j)
            hindex (hmass S hclean j T hperiod))
    simpa only [bankTrialRenewalStageScale] using hbound
  have hcostSum :
      (2 ^ (compileAdvice q).K) *
        bankTrialSuccessStageIndexSum (fun j =>
          bankTrialRenewalPatternCost ring root S T L j) H ≤
      n ^ T * bankTrialSuccessStageIndexSum (fun j =>
        n * (g + j * f)) H := by
    have hbound :=
      bankTrialRenewalStageIndexMonoBelow
        (fun j =>
          (2 ^ (compileAdvice q).K) *
            bankTrialRenewalPatternCost ring root S T L j)
        (fun j => n ^ T * (n * (g + j * f)))
        H (by
          intro j hj
          have hindex : j + 1 ≤ H := by omega
          have hperiod : (j + 1) * L ≤ T :=
            Nat.le_trans
              (Nat.mul_le_mul_right L hindex) hbudget
          exact hcost S hclean j T hperiod)
    simpa only [bankTrialRenewalStageScale] using hbound
  have hfinite :=
    bankTrialRenewalWindowInequalitySuccessMass
      ring root S T L W H hwindow
  exact bankTrialRenewalCombineWindowOpaque
    W (2 ^ (compileAdvice q).K) (n ^ T) (den ^ H)
    (bankTrialSuccessStageIndexSum (fun j =>
      lo ^ j * win * den ^ (H - (j + 1))) H)
    (bankTrialSuccessStageIndexSum (fun j =>
      bankTrialRenewalPatternMass ring root S T L j) H)
    (bankTrialRenewalSuccessMass ring root S T W)
    (bankTrialSuccessStageIndexSum (fun j =>
      bankTrialRenewalPatternCost ring root S T L j) H)
    (bankTrialSuccessStageIndexSum (fun j =>
      n * (g + j * f)) H)
    hmassSum hfinite hcostSum

end L3


namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
G13-INDEX-RENEWAL. The C.5 horizon is explicitly
1024 * P * D * B + 1, where P=2^K, D is the C.5 worker
denominator, and B=3(2K+1)(8b+12)n. This depends on
n and q, not on the Clean start S.
-/

/-- Explicit C.5 time, uniform over all Clean BANK starts. -/
def bankTrialSuccessThetaUniformHorizon (n q : Nat) : Nat :=
  1024 * (2 ^ (compileAdvice q).K) *
    bankTrialProbabilityC5WorkerDenominator q *
    (3 * (2 * (compileAdvice q).K + 1) *
      ((8 * (compileAdvice q).b + 12) * n)) + 1

/-- Doubled-numerator normalization on opaque Nat variables. -/
private theorem bankTrialRenewalDoubledBudgetArithmetic
    (M N D : Nat)
    (h : 2048 * M * N < D) :
    1024 * M * (2 * N) < D := by
  have heq :
      1024 * M * (2 * N) = 2048 * M * N := by
    simp only [Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm, Nat.reduceMul]
  rw [heq]
  exact h

/-- The uniform clock pays the complete C.5 terminal debt,
without evaluating any actual large power. -/
private theorem bankTrialRenewalUniformClockArithmetic
    (D M N P B : Nat)
    (hbudget : 1024 * M * N < D) :
    1024 * P * D * B ≤
      (1024 * P * D * B + 1) *
        (D - 1024 * M * N) := by
  have hgap : 1 ≤ D - 1024 * M * N := by omega
  calc
    1024 * P * D * B ≤ 1024 * P * D * B + 1 :=
      Nat.le_succ _
    _ = (1024 * P * D * B + 1) * 1 := by
      rw [Nat.mul_one]
    _ ≤ (1024 * P * D * B + 1) *
          (D - 1024 * M * N) :=
      Nat.mul_le_mul_left _ hgap

/-- The C.5 theta lower estimate at the same explicit T0
for every arbitrary Clean S. This opens the witness hidden
by the existential statement of the previous theorem. -/
theorem bankTrialSuccessThetaLowerAtUniformHorizon
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S) :
    1023 * n ^ (bankTrialSuccessThetaUniformHorizon n q) ≤
      1024 * 2 ^ (compileAdvice q).K *
        bankTrialProbabilityWinMass ring root S
          (bankTrialSuccessThetaUniformHorizon n q) := by
  have hD : 0 < bankTrialProbabilityC5WorkerDenominator q := by
    unfold bankTrialProbabilityC5WorkerDenominator
    exact Nat.pow_pos (by omega)
  have hbudget :
      1024 * (2 * (compileAdvice q).K + 1) *
          (2 * bankTrialProbabilityC5WorkerNumerator q) <
        bankTrialProbabilityC5WorkerDenominator q :=
    bankTrialRenewalDoubledBudgetArithmetic
      (2 * (compileAdvice q).K + 1)
      (bankTrialProbabilityC5WorkerNumerator q)
      (bankTrialProbabilityC5WorkerDenominator q)
      (bankTrialSuccessDoubledWorkerBudget q hsmall hK)
  have hTpos :
      0 < bankTrialSuccessThetaUniformHorizon n q := by
    unfold bankTrialSuccessThetaUniformHorizon
    exact Nat.zero_lt_succ _
  have hclock :
      1024 * 2 ^ (compileAdvice q).K *
          bankTrialProbabilityC5WorkerDenominator q *
          (3 * (2 * (compileAdvice q).K + 1) *
            ((8 * (compileAdvice q).b + 12) * n)) ≤
        bankTrialSuccessThetaUniformHorizon n q *
          (bankTrialProbabilityC5WorkerDenominator q -
            1024 * (2 * (compileAdvice q).K + 1) *
              (2 * bankTrialProbabilityC5WorkerNumerator q)) := by
    change
      1024 * 2 ^ (compileAdvice q).K *
          bankTrialProbabilityC5WorkerDenominator q *
          (3 * (2 * (compileAdvice q).K + 1) *
            ((8 * (compileAdvice q).b + 12) * n)) ≤
      (1024 * 2 ^ (compileAdvice q).K *
          bankTrialProbabilityC5WorkerDenominator q *
          (3 * (2 * (compileAdvice q).K + 1) *
            ((8 * (compileAdvice q).b + 12) * n)) + 1) *
          (bankTrialProbabilityC5WorkerDenominator q -
            1024 * (2 * (compileAdvice q).K + 1) *
              (2 * bankTrialProbabilityC5WorkerNumerator q))
    exact bankTrialRenewalUniformClockArithmetic
      (bankTrialProbabilityC5WorkerDenominator q)
      (2 * (compileAdvice q).K + 1)
      (2 * bankTrialProbabilityC5WorkerNumerator q)
      (2 ^ (compileAdvice q).K)
      (3 * (2 * (compileAdvice q).K + 1) *
        ((8 * (compileAdvice q).b + 12) * n))
      hbudget
  have hhead :
      1023 * n ^ (bankTrialSuccessThetaUniformHorizon n q) ≤
        1024 * 2 ^ (compileAdvice q).K *
          bankTrialProbabilityC5CompletedHeadMass ring root S
            (bankTrialSuccessThetaUniformHorizon n q) :=
    bankTrialC5ForwardOpaqueArithmetic
      hD hTpos hbudget hclock
      (bankTrialSuccessForwardJointAtStartCap
        ring root S hsmall hlarge hK hclean
        (bankTrialSuccessThetaUniformHorizon n q))
  have hsubset :
      bankTrialProbabilityC5CompletedHeadMass ring root S
          (bankTrialSuccessThetaUniformHorizon n q) ≤
        bankTrialProbabilityWinMass ring root S
          (bankTrialSuccessThetaUniformHorizon n q) := by
    unfold bankTrialProbabilityC5CompletedHeadMass
      bankTrialProbabilityWinMass
    apply bankTrialProbabilityScheduleSumMono
    intro word
    by_cases hc :
        bankTrialProbabilityC5CompletedHeadWord ring root S word
    · have hwon :=
        (bankTrialProbabilityC5CompletedHeadSoundHolds
          ring root S) hsmall hlarge hK hclean word hc
      simp only [if_pos hc, if_pos hwon]
      exact Nat.le_refl _
    · simp only [if_neg hc]
      exact Nat.zero_le _
  exact Nat.le_trans hhead
    (Nat.mul_le_mul_left (1024 * 2 ^ (compileAdvice q).K)
      hsubset)

/-- Uniform lower theta estimate for every T >= T0.
The original n-edge WON event is absorbing, and its
finite-horizon mass gains n^m continuations. -/
theorem bankTrialSuccessThetaLowerUniform
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (_hn : 2 ≤ n)
    (hsmall : (compileAdvice q).useSmall = false)
    (_hw : BankTrialLiveWindowNonalias n q)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (_hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b) :
    ∀ (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b),
      BankTrialLocalClean q S →
      ∀ (T : Nat), bankTrialSuccessThetaUniformHorizon n q ≤ T →
        1023 * n ^ T ≤
          1024 * 2 ^ (compileAdvice q).K *
            bankTrialProbabilityWinMass ring root S T := by
  intro S hclean T hT
  have hbase := bankTrialSuccessThetaLowerAtUniformHorizon
    ring root hsmall hlarge hK S hclean
  have hsum :
      bankTrialSuccessThetaUniformHorizon n q +
        (T - bankTrialSuccessThetaUniformHorizon n q) = T := by
    omega
  have hpow :
      n ^ T =
        n ^ (bankTrialSuccessThetaUniformHorizon n q) *
          n ^ (T - bankTrialSuccessThetaUniformHorizon n q) := by
    calc
      n ^ T =
          n ^ (bankTrialSuccessThetaUniformHorizon n q +
            (T - bankTrialSuccessThetaUniformHorizon n q)) := by
          rw [hsum]
      _ = _ := Nat.pow_add n _ _
  have hpadding :
      n ^ (T - bankTrialSuccessThetaUniformHorizon n q) *
          bankTrialProbabilityWinMass ring root S
            (bankTrialSuccessThetaUniformHorizon n q) ≤
        bankTrialProbabilityWinMass ring root S T := by
    have h := bankTrialRenewalWonMonotone ring root S
      (bankTrialSuccessThetaUniformHorizon n q)
      (T - bankTrialSuccessThetaUniformHorizon n q)
    simpa only [hsum] using h
  rw [hpow]
  exact bankTrialRenewalLowerPadArithmetic
    1023 (1024 * 2 ^ (compileAdvice q).K)
    (n ^ (bankTrialSuccessThetaUniformHorizon n q))
    (n ^ (T - bankTrialSuccessThetaUniformHorizon n q))
    (bankTrialProbabilityWinMass ring root S
      (bankTrialSuccessThetaUniformHorizon n q))
    (bankTrialProbabilityWinMass ring root S T)
    hbase hpadding

/-- Explicit threshold for the uniform C.5 success cutoff. -/
def bankTrialRenewalWonCutoffThreshold (n q : Nat) : Nat :=
  Nat.max (bankTrialSuccessThetaUniformHorizon n q)
    (1024 * 2 ^ (compileAdvice q).K *
      ((8 * (compileAdvice q).b + 12) * n))

/-- Integer-cleared cutoff implication over opaque naturals.
L >= 1024*P*B is a sufficient threshold (stronger than
1023*L >= 1024*P*B); division is never used. -/
private theorem bankTrialRenewalThetaCutoffArithmetic
    (N W L P B : Nat)
    (htheta : 1023 * N ≤ 1024 * P * W)
    (hlarge : 1024 * P * B ≤ L) :
    B * N ≤ L * W := by
  have hlargeNumber :
      B * N ≤ 1023 * (B * N) := by
    have h := Nat.mul_le_mul_right (B * N)
      (show (1 : Nat) ≤ 1023 by omega)
    simpa only [Nat.one_mul] using h
  calc
    B * N ≤ 1023 * (B * N) := hlargeNumber
    _ = B * (1023 * N) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ B * (1024 * P * W) :=
      Nat.mul_le_mul_left B htheta
    _ = (1024 * P * B) * W := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ L * W := Nat.mul_le_mul_right W hlarge

/-- The actual hcut holds simultaneously for all Clean S,
without selecting a horizon depending on the start bank. -/
theorem bankTrialRenewalWonCutoffHolds
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (L : Nat)
    (hL : bankTrialRenewalWonCutoffThreshold n q ≤ L) :
    ∀ (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b),
      BankTrialLocalClean q S →
      ((8 * (compileAdvice q).b + 12) * n) * n ^ L ≤
        L * bankTrialProbabilityWinMass ring root S L := by
  intro S hclean
  have hT :
      bankTrialSuccessThetaUniformHorizon n q ≤ L :=
    Nat.le_trans (Nat.le_max_left _ _) hL
  have hB :
      1024 * 2 ^ (compileAdvice q).K *
        ((8 * (compileAdvice q).b + 12) * n) ≤ L :=
    Nat.le_trans (Nat.le_max_right _ _) hL
  have htheta :=
    (bankTrialSuccessThetaLowerUniform
      ring root hn hsmall hw hlarge hpositive hK)
      S hclean L hT
  exact bankTrialRenewalThetaCutoffArithmetic
    (n ^ L) (bankTrialProbabilityWinMass ring root S L)
    L (2 ^ (compileAdvice q).K)
    ((8 * (compileAdvice q).b + 12) * n)
    htheta hB

/-- W with its original denominator L and no hcut premise. -/
theorem bankTrialRenewalWonWithinBoundUniform
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (L : Nat)
    (hL : bankTrialRenewalWonCutoffThreshold n q ≤ L) :
    BankTrialRenewalWonWithinBound (q := q) ring root L
      ((8 * (compileAdvice q).b + 12) * n) L := by
  exact bankTrialRenewalWonWithinBoundOfCutoff
    ring root L
    (bankTrialRenewalWonCutoffHolds
      ring root hn hsmall hw hlarge hpositive hK L hL)

/-- Common-denominator W, for combination with the existing F. -/
theorem bankTrialRenewalWonWithinBoundCommonDenUniform
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (L : Nat)
    (hL : bankTrialRenewalWonCutoffThreshold n q ≤ L) :
    BankTrialRenewalWonWithinBound (q := q) ring root L
      (((8 * (compileAdvice q).b + 12) * n) *
        2 ^ (compileAdvice q).K)
      (L * 2 ^ (compileAdvice q).K) := by
  exact bankTrialRenewalWonWithinBoundCommonDenOfCutoff
    ring root L
    (bankTrialRenewalWonCutoffHolds
      ring root hn hsmall hw hlarge hpositive hK L hL)

/-- The F lower bound was already cutoff-free; restated on
the common BANK band without any hcut. -/
theorem bankTrialRenewalLostWithinBoundUniform
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (L : Nat) :
    BankTrialRenewalLostWithinBound (q := q) ring root L
      (L * 2 ^ (compileAdvice q).K - L -
        2 ^ (compileAdvice q).K *
          ((8 * (compileAdvice q).b + 12) * n))
      (L * 2 ^ (compileAdvice q).K) := by
  exact bankTrialRenewalLostWithinBoundOfCutoff
    ring root hn hsmall hw hlarge hpositive hK L

/-- G0 with the actual doubled C.8 coefficient and no hcut. -/
theorem bankTrialRenewalZeroCostWithinBoundUniform
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (L : Nat)
    (hL : bankTrialRenewalWonCutoffThreshold n q ≤ L) :
    BankTrialRenewalZeroCostWithinBound (q := q) ring root L
      (2 * ((8 * (compileAdvice q).b + 12) *
        ((compileAdvice q).K + 1))) := by
  exact bankTrialRenewalZeroCostWithinBoundHolds
    ring root hn hsmall hw hlarge hpositive hK L
    (bankTrialRenewalWonCutoffHolds
      ring root hn hsmall hw hlarge hpositive hK L hL)

end L3


namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
Sharpened G0 (C.16 preparation).

The single uniform C.5 theta estimate remains the one already
proved above.  Only the second, elementary cutoff threshold is
multiplied by M >= 1.  This yields M times the usual C.5 mass
cutoff, and hence M * ACTIVE <= WON on every T >= L.

For C.8 write a=(8*b+12), g=a*(K+1).
Its finite stopped-cost bound is (WON+ACTIVE)*(g*n).
The stronger ACTIVE comparison gives
  (WON+ACTIVE)*g <= WON*(g+ceil(g/M)).
Thus the original G0 coefficient 2*g is replaced by
  g + (g+M-1)/M.
The nonnegative mass numerators n^T and 2^K are never opened by
omega or decide.  They occur only as opaque Nat variables in
the arithmetic lemmas below.
-/

/-- A common theta horizon plus an M-scaled C.5 cutoff.
This is independent of the actual clean starting BANK state. -/
def bankTrialRenewalWonCutoffThresholdSharp
    (n q M : Nat) : Nat :=
  Nat.max (bankTrialSuccessThetaUniformHorizon n q)
    (1024 * M * 2 ^ (compileAdvice q).K *
      ((8 * (compileAdvice q).b + 12) * n))

/-- The stronger C.5 cutoff is purely denominator-cleared
arithmetic, stated on opaque mass numerators. -/
private theorem bankTrialRenewalSharpThetaArithmetic
    (N W L P B M : Nat)
    (hTheta : 1023 * N <= 1024 * P * W)
    (hLength : 1024 * M * P * B <= L) :
    (M * B) * N <= L * W := by
  have hScaledLength :
      1024 * P * (M * B) <= L := by
    calc
      1024 * P * (M * B) =
          1024 * M * P * B := by
            simp only [Nat.mul_assoc, Nat.mul_comm,
              Nat.mul_left_comm]
      _ <= L := hLength
  exact bankTrialRenewalThetaCutoffArithmetic
    N W L P (M * B) hTheta hScaledLength

/-- Uniform strengthened C.5: the same clean-state theta bound
works for every M, at the stated longer single cutoff L. -/
theorem bankTrialRenewalWonCutoffHoldsSharp
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 2 <= n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap <= n)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (M : Nat) (_hM : 1 <= M)
    (L : Nat)
    (hL : bankTrialRenewalWonCutoffThresholdSharp n q M <= L) :
    forall (S : GrantBankReference.BankLocalReference
        (compileAdvice q).b),
      BankTrialLocalClean q S ->
      (M * ((8 * (compileAdvice q).b + 12) * n)) * n ^ L <=
        L * bankTrialProbabilityWinMass ring root S L := by
  intro S hclean
  have hT :
      bankTrialSuccessThetaUniformHorizon n q <= L :=
    Nat.le_trans (Nat.le_max_left _ _) hL
  have hLength :
      1024 * M * 2 ^ (compileAdvice q).K *
        ((8 * (compileAdvice q).b + 12) * n) <= L :=
    Nat.le_trans (Nat.le_max_right _ _) hL
  have hTheta :=
    (bankTrialSuccessThetaLowerUniform
      ring root hn hsmall hw hlarge hpositive hK)
      S hclean L hT
  exact bankTrialRenewalSharpThetaArithmetic
    (n ^ L)
    (bankTrialProbabilityWinMass ring root S L)
    L (2 ^ (compileAdvice q).K)
    ((8 * (compileAdvice q).b + 12) * n)
    M hTheta hLength

/-- Absorption of M copies of ACTIVE is a linear calculation.
N may subsequently be instantiated with the huge n^T. -/
private theorem bankTrialRenewalSharpActiveArithmetic
    (T M A N B W : Nat)
    (hT : 0 < T)
    (hActive : T * A <= N * B)
    (hCut : (M * B) * N <= T * W) :
    M * A <= W := by
  have hScaled :
      T * (M * A) <= T * W := by
    calc
      T * (M * A) = M * (T * A) := by
        simp only [Nat.mul_assoc, Nat.mul_comm,
          Nat.mul_left_comm]
      _ <= M * (N * B) :=
        Nat.mul_le_mul_left M hActive
      _ = (M * B) * N := by
        simp only [Nat.mul_assoc, Nat.mul_comm,
          Nat.mul_left_comm]
      _ <= T * W := hCut
  exact Nat.le_of_mul_le_mul_left hScaled hT

/-- The strengthened cutoff holds after every padding, so the
ACTIVE comparison also holds at every T >= L. -/
theorem bankTrialRenewalActiveLeWonSharp
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 2 <= n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap <= n)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (M : Nat) (hM : 1 <= M)
    (L : Nat)
    (hL : bankTrialRenewalWonCutoffThresholdSharp n q M <= L)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (T : Nat) (hLT : L <= T) :
    M * bankTrialDurationActiveMass ring root S T <=
      bankTrialProbabilityWinMass ring root S T := by
  have hHorizonPositive :
      0 < bankTrialSuccessThetaUniformHorizon n q := by
    unfold bankTrialSuccessThetaUniformHorizon
    exact Nat.zero_lt_succ _
  have hHorizon :
      bankTrialSuccessThetaUniformHorizon n q <= L :=
    Nat.le_trans (Nat.le_max_left _ _) hL
  have hTPositive : 0 < T :=
    Nat.lt_of_lt_of_le hHorizonPositive
      (Nat.le_trans hHorizon hLT)
  have hCutL :=
    (bankTrialRenewalWonCutoffHoldsSharp
      ring root hn hsmall hw hlarge hpositive hK
      M hM L hL) S hclean
  have hCutT :
      (M * ((8 * (compileAdvice q).b + 12) * n)) *
        n ^ T <=
      T * bankTrialProbabilityWinMass ring root S T :=
    bankTrialRenewalCutoffPad ring root S
      (M * ((8 * (compileAdvice q).b + 12) * n))
      L T hLT hCutL
  have hActive :=
    bankTrialRenewalActiveCutoff
      ring root hn hsmall hw hpositive hK S hclean T
  exact bankTrialRenewalSharpActiveArithmetic
    T M (bankTrialDurationActiveMass ring root S T)
    (n ^ T) ((8 * (compileAdvice q).b + 12) * n)
    (bankTrialProbabilityWinMass ring root S T)
    hTPositive hActive hCutT

/-- The integer ceiling is sufficient to pay the fraction g/M.
This uses only Euclidean division on opaque Nat variables. -/
private theorem bankTrialRenewalSharpCeilMul
    (g M : Nat) (hM : 1 <= M) :
    g <= M * ((g + M - 1) / M) := by
  have hPositive : 0 < M := by omega
  have hRemain :
      (g + M - 1) % M < M :=
    Nat.mod_lt (g + M - 1) hPositive
  have hDivision := Nat.mod_add_div (g + M - 1) M
  omega

/-- Improved C.8: the one ACTIVE addend costs at most
ceil(g/M) copies of WON. No quotient of scheduler masses occurs. -/
private theorem bankTrialRenewalSharpCostArithmetic
    (M g n W A C : Nat)
    (hM : 1 <= M)
    (hActive : M * A <= W)
    (hCost : C <= (W + A) * (g * n)) :
    C <=
      ((g + (g + M - 1) / M) * n) * W := by
  have hCeil :=
    bankTrialRenewalSharpCeilMul g M hM
  have hExtra :
      g * A <= ((g + M - 1) / M) * W := by
    calc
      g * A <= (M * ((g + M - 1) / M)) * A :=
        Nat.mul_le_mul_right A hCeil
      _ = ((g + M - 1) / M) * (M * A) := by
        simp only [Nat.mul_assoc, Nat.mul_comm,
          Nat.mul_left_comm]
      _ <= ((g + M - 1) / M) * W :=
        Nat.mul_le_mul_left _ hActive
  have hExtraComm :
      A * g <= W * ((g + M - 1) / M) := by
    simpa only [Nat.mul_comm] using hExtra
  have hOneFold :
      (W + A) * g <=
        W * (g + (g + M - 1) / M) := by
    calc
      (W + A) * g = W * g + A * g :=
        Nat.add_mul W A g
      _ <= W * g + W * ((g + M - 1) / M) :=
        Nat.add_le_add_left hExtraComm (W * g)
      _ = W * (g + (g + M - 1) / M) :=
        (Nat.mul_add W g ((g + M - 1) / M)).symm
  calc
    C <= (W + A) * (g * n) := hCost
    _ = ((W + A) * g) * n := by
      rw [Nat.mul_assoc]
    _ <= (W * (g + (g + M - 1) / M)) * n :=
      Nat.mul_le_mul_right n hOneFold
    _ = ((g + (g + M - 1) / M) * n) * W := by
      simp only [Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm]

/-- The original C.8 conditional cost result, with precisely
the stronger M-scaled local cutoff and a positive horizon. -/
theorem bankTrialRenewalCompletedSuccessCostSharp
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 2 <= n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap <= n)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (M : Nat) (hM : 1 <= M)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (T : Nat) (hT : 0 < T)
    (hCut :
      (M * ((8 * (compileAdvice q).b + 12) * n)) * n ^ T <=
        T * bankTrialProbabilityWinMass ring root S T) :
    bankTrialDurationSuccessCostMass ring root S T <=
      (((8 * (compileAdvice q).b + 12) *
          ((compileAdvice q).K + 1) +
          ((8 * (compileAdvice q).b + 12) *
            ((compileAdvice q).K + 1) + M - 1) / M) * n) *
        bankTrialProbabilityWinMass ring root S T := by
  have hActiveCost :=
    bankTrialRenewalActiveCutoff
      ring root hn hsmall hw hpositive hK
      S hclean T
  have hActive :=
    bankTrialRenewalSharpActiveArithmetic
      T M (bankTrialDurationActiveMass ring root S T)
      (n ^ T) ((8 * (compileAdvice q).b + 12) * n)
      (bankTrialProbabilityWinMass ring root S T)
      hT hActiveCost hCut
  have hC8 :=
    (bankTrialDurationSuccessConditionalTargetHolds
      ring root hw hsmall hlarge hpositive hK)
      S hclean T
  exact bankTrialRenewalSharpCostArithmetic
    M ((8 * (compileAdvice q).b + 12) *
       ((compileAdvice q).K + 1))
    n (bankTrialProbabilityWinMass ring root S T)
    (bankTrialDurationActiveMass ring root S T)
    (bankTrialDurationSuccessCostMass ring root S T)
    hM hActive hC8

/-- K-head rarity transports the sharpened local cost coefficient
to the G0 scale. N may later be instantiated with n^T. -/
private theorem bankTrialRenewalSharpRareCostArithmetic
    (Q E C W N n c : Nat)
    (hSub : E <= C)
    (hCost : C <= (c * n) * W)
    (hRare : Q * W <= N) :
    Q * E <= N * (n * c) := by
  calc
    Q * E <= Q * C := Nat.mul_le_mul_left Q hSub
    _ <= Q * ((c * n) * W) :=
      Nat.mul_le_mul_left Q hCost
    _ = (n * c) * (Q * W) := by
      simp only [Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm]
    _ <= (n * c) * N :=
      Nat.mul_le_mul_left _ hRare
    _ = N * (n * c) := Nat.mul_comm _ _

/-- Sharp G0 for C.16: the factor M is used solely to strengthen
the uniform C.5 cutoff. The loss and renewal bounds are unchanged.
The second summand is the exact integer ceiling of g/M. -/
theorem bankTrialRenewalZeroCostWithinBoundSharp
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 2 <= n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap <= n)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (M : Nat) (hM : 1 <= M)
    (L : Nat)
    (hL : bankTrialRenewalWonCutoffThresholdSharp n q M <= L) :
    BankTrialRenewalZeroCostWithinBound (q := q) ring root L
      ((8 * (compileAdvice q).b + 12) *
        ((compileAdvice q).K + 1) +
        ((8 * (compileAdvice q).b + 12) *
          ((compileAdvice q).K + 1) + M - 1) / M) := by
  intro S hclean T hLT
  have hHorizonPositive :
      0 < bankTrialSuccessThetaUniformHorizon n q := by
    unfold bankTrialSuccessThetaUniformHorizon
    exact Nat.zero_lt_succ _
  have hHorizon :
      bankTrialSuccessThetaUniformHorizon n q <= L :=
    Nat.le_trans (Nat.le_max_left _ _) hL
  have hT : 0 < T :=
    Nat.lt_of_lt_of_le hHorizonPositive
      (Nat.le_trans hHorizon hLT)
  have hCutL :=
    (bankTrialRenewalWonCutoffHoldsSharp
      ring root hn hsmall hw hlarge hpositive hK
      M hM L hL) S hclean
  have hCutT :
      (M * ((8 * (compileAdvice q).b + 12) * n)) * n ^ T <=
        T * bankTrialProbabilityWinMass ring root S T :=
    bankTrialRenewalCutoffPad ring root S
      (M * ((8 * (compileAdvice q).b + 12) * n))
      L T hLT hCutL
  have hCost :=
    bankTrialRenewalCompletedSuccessCostSharp
      ring root hn hsmall hw hlarge hpositive hK
      M hM S hclean T hT hCutT
  have hSub :=
    bankTrialRenewalZeroCostLeLocalSuccessCost
      ring root S T L
  have hRare :
      2 ^ (compileAdvice q).K *
        bankTrialProbabilityWinMass ring root S T <= n ^ T := by
    have hAuthentication :
        (compileAdvice q).useSmall = false ->
        2 * (compileAdvice q).bankLeaseCap <= n ->
        BankTrialLocalClean q S ->
        forall word : List (Fin n),
          (bankTrialLocalRun ring root word
            (bankTrialLocalStart S)).phase = .won ->
          bankTrialProbabilityHeadEvent ring root word
            (compileAdvice q).K (bankTrialLocalStart S) := by
      intro _ _ hc word hwin
      exact bankTrialDurationWinHasAllHeads
        ring root S hc hsmall hlarge word hwin
    exact (bankTrialProbabilityUpperOfHeadAuthentication
      ring root S hAuthentication) hsmall hlarge hclean T
  exact bankTrialRenewalSharpRareCostArithmetic
    (2 ^ (compileAdvice q).K)
    (bankTrialRenewalPatternCost ring root S T L 0)
    (bankTrialDurationSuccessCostMass ring root S T)
    (bankTrialProbabilityWinMass ring root S T)
    (n ^ T) n
    ((8 * (compileAdvice q).b + 12) *
      ((compileAdvice q).K + 1) +
      ((8 * (compileAdvice q).b + 12) *
        ((compileAdvice q).K + 1) + M - 1) / M)
    hSub hCost hRare

end L3


namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
G13-INDEX-RENEWAL.

The *only new probabilistic premise* is
hG below: the improved zero-pattern cost at M=1024. The old W/F,
Fc/R0, C.5 theta and the cleared sandwich are used as theorems.

IMPORTANT: C.16's 22517 is a LOWER BOUND on the variable number
H=floor((t-C0)/f), not a globally fixed number of trials. The last
theorem below is the exact H=22517 cleared sandwich, NOT the final
49/100 mass lower bound. That latter step also requires a controlled
geometric-power sum with H growing with W/(fn).

The cold cost c0 is absent from the Clean-start pattern cost.
It enters only when bounding the initial non-Clean warm-up, through
C0=c0+gM; its enlarged compiled window quota is proved here.
-/

/-- Keep the compiled cutoff (which contains enormous powers)
opaque when passing from an M-fold cutoff to the old one. -/
private theorem bankTrialRenewalEvalCutoffDescent
    (C L : Nat) (h : 1024 * C ≤ L) : C ≤ L := by
  omega

/-- The M=1024 improvement may be written as
gM = g + ceil(g/1024) = ceil(1025*g/1024).
The compiler's 32(b+1)(K+2) reserve actually dominates even 2*g. -/
private theorem bankTrialRenewalEvalOverheadBound
    (b K : Nat) :
    (8 * b + 12) * (K + 1) +
      (((8 * b + 12) * (K + 1) + 1023) / 1024) ≤
      32 * (b + 1) * (K + 2) := by
  have hceil : ∀ g : Nat, g + (g + 1023) / 1024 ≤ 2 * g := by
    intro g
    omega
  have hb : 2 * (8 * b + 12) ≤ 32 * (b + 1) := by omega
  have hk : K + 1 ≤ K + 2 := by omega
  have hfirst := Nat.mul_le_mul_right (K + 1) hb
  have hsecond := Nat.mul_le_mul_left (32 * (b + 1)) hk
  calc
    (8 * b + 12) * (K + 1) +
        (((8 * b + 12) * (K + 1) + 1023) / 1024) ≤
      2 * ((8 * b + 12) * (K + 1)) :=
        hceil ((8 * b + 12) * (K + 1))
    _ = (2 * (8 * b + 12)) * (K + 1) := by
      rw [Nat.mul_assoc]
    _ ≤ (32 * (b + 1)) * (K + 1) := hfirst
    _ ≤ 32 * (b + 1) * (K + 2) := hsecond

/-- Opaque integer proof of the H>=22517 endpoint quota.
Only small fixed multipliers are normalized here. -/
private theorem bankTrialRenewalEvalQuotaArithmetic
    (n R W C f : Nat)
    (hC : 1024 * C ≤ R)
    (hf : 182272 * f ≤ R)
    (hfloor : 255 * (R * n) ≤ 2048 * W) :
    n * (C + 22517 * f) ≤ W := by
  have hscaledC := Nat.mul_le_mul_right (2 * n) hC
  have hCbound : 2048 * (C * n) ≤ 2 * (R * n) := by
    calc
      2048 * (C * n) = (1024 * C) * (2 * n) := by
        simp only [Nat.mul_assoc, Nat.mul_comm,
          Nat.mul_left_comm, Nat.reduceMul]
      _ ≤ R * (2 * n) := hscaledC
      _ = 2 * (R * n) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hscaledF := Nat.mul_le_mul_right n hf
  have hFbound :
      2048 * (22517 * (f * n)) ≤ 253 * (R * n) := by
    have hcoef : 2048 * 22517 = 253 * 182272 := by decide
    have hfN : 182272 * (f * n) ≤ R * n := by
      simpa only [Nat.mul_assoc] using hscaledF
    calc
      2048 * (22517 * (f * n)) =
          (2048 * 22517) * (f * n) := by rw [Nat.mul_assoc]
      _ = (253 * 182272) * (f * n) := by rw [hcoef]
      _ = 253 * (182272 * (f * n)) := by rw [Nat.mul_assoc]
      _ ≤ 253 * (R * n) := Nat.mul_le_mul_left 253 hfN
  have hcombined :
      2048 * (C * n + 22517 * (f * n)) ≤ 255 * (R * n) := by
    calc
      _ = 2048 * (C * n) + 2048 * (22517 * (f * n)) :=
        Nat.mul_add _ _ _
      _ ≤ 2 * (R * n) + 253 * (R * n) :=
        Nat.add_le_add hCbound hFbound
      _ = 255 * (R * n) := by omega
  have hbound :
      2048 * (C * n + 22517 * (f * n)) ≤ 2048 * W :=
    Nat.le_trans hcombined hfloor
  have hresult : C * n + 22517 * (f * n) ≤ W := by omega
  calc
    n * (C + 22517 * f) = C * n + 22517 * (f * n) := by
      simp only [Nat.mul_add, Nat.mul_assoc,
        Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ W := hresult

/-- The actual compiled radius admits the improved C0M =
c0 + (g + ceil(g/1024)), and still gives the same
22517-index quota. In fact the reserve suffices even for 2*g,
so enlargement of g does not, by itself, destroy the 49/100
C.16 arithmetic constant. -/
theorem bankTrialRenewalEvalCompiledQuota
    (n R W : Nat)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hradius : (256 * R) ^ 2 ≤ n ∧
      n < (256 * (R + 1)) ^ 2)
    (hW : W = R * n / 8) :
    n * ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
        5 * (compileAdvice (ceilLogTwo n)).b + 13) +
      ((8 * (compileAdvice (ceilLogTwo n)).b + 12) *
          ((compileAdvice (ceilLogTwo n)).K + 1) +
        (((8 * (compileAdvice (ceilLogTwo n)).b + 12) *
          ((compileAdvice (ceilLogTwo n)).K + 1) + 1023) / 1024)) +
      22517 * (8 * (compileAdvice (ceilLogTwo n)).b + 13)) ≤ W := by
  have hR := grantClockSpatialRadiusCutoff
    n R hn hsp hradius
  have hcoeff := bankTrialRenewalEvalOverheadBound
    (compileAdvice (ceilLogTwo n)).b
    (compileAdvice (ceilLogTwo n)).K
  have hC :
      1024 *
        ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
            5 * (compileAdvice (ceilLogTwo n)).b + 13) +
          ((8 * (compileAdvice (ceilLogTwo n)).b + 12) *
              ((compileAdvice (ceilLogTwo n)).K + 1) +
            (((8 * (compileAdvice (ceilLogTwo n)).b + 12) *
              ((compileAdvice (ceilLogTwo n)).K + 1) + 1023) /
              1024))) ≤ R := by
    have hsum := Nat.add_le_add_left hcoeff
      (2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
        5 * (compileAdvice (ceilLogTwo n)).b + 13)
    exact Nat.le_trans (Nat.mul_le_mul_left 1024 hsum) hR
  have hRstandard :
      1024 *
        ((2 * (13 * ((compileAdvice (ceilLogTwo n)).b + 2)) +
            5 * (compileAdvice (ceilLogTwo n)).b + 13) +
          32 * ((compileAdvice (ceilLogTwo n)).b + 1) *
            ((compileAdvice (ceilLogTwo n)).K + 2)) ≤ R := by
    simpa only [Compiled.bankLeaseCap] using hR
  have hstandard := (grantClockSpatialColdAndTrialBudget
    (compileAdvice (ceilLogTwo n)).b
    (compileAdvice (ceilLogTwo n)).K R hRstandard).2
  have hq := grantClockSpatialAdviceEighty (ceilLogTwo n) hsp
  have hK := (grantClockSpatialKappaLower (ceilLogTwo n) hq).2
  have hKplus : 178 ≤ (compileAdvice (ceilLogTwo n)).K + 1 := by
    omega
  have hstep := Nat.mul_le_mul_left
    (1024 * (8 * (compileAdvice (ceilLogTwo n)).b + 13)) hKplus
  have hf :
      182272 * (8 * (compileAdvice (ceilLogTwo n)).b + 13) ≤ R := by
    calc
      182272 * (8 * (compileAdvice (ceilLogTwo n)).b + 13) =
          (1024 * (8 * (compileAdvice (ceilLogTwo n)).b + 13)) *
            178 := by
              rw [show (182272 : Nat) = 1024 * 178 by decide]
              simp only [Nat.mul_assoc, Nat.mul_comm,
                Nat.mul_left_comm]
      _ ≤ (1024 * (8 * (compileAdvice (ceilLogTwo n)).b + 13)) *
          ((compileAdvice (ceilLogTwo n)).K + 1) := hstep
      _ = 1024 * ((8 * (compileAdvice (ceilLogTwo n)).b + 13) *
          ((compileAdvice (ceilLogTwo n)).K + 1)) := by
            rw [Nat.mul_assoc]
      _ ≤ R := hstandard
  have hfloor :=
    (grantClockSpatialCompiledWindowQuotas n R W
      hn hsp hradius hW).1
  exact bankTrialRenewalEvalQuotaArithmetic n R W
    ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
        5 * (compileAdvice (ceilLogTwo n)).b + 13) +
      ((8 * (compileAdvice (ceilLogTwo n)).b + 12) *
          ((compileAdvice (ceilLogTwo n)).K + 1) +
        (((8 * (compileAdvice (ceilLogTwo n)).b + 12) *
          ((compileAdvice (ceilLogTwo n)).K + 1) + 1023) / 1024)))
    (8 * (compileAdvice (ceilLogTwo n)).b + 13)
    hC hf hfloor

/-- A theta-strengthened zero-pattern W premise.
The C.5 lower bound is for local WON. At horizon L it
passes to the zero-pattern using the existing event inclusion;
only then is it padded to every T>=L. -/
theorem bankTrialRenewalEvalThetaWonBound
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (L : Nat)
    (hL : bankTrialRenewalWonCutoffThreshold n q ≤ L) :
    BankTrialRenewalWonWithinBound (q := q) ring root L
      (1023 * L) (1024 * (L * 2 ^ (compileAdvice q).K)) := by
  intro S hclean T hLT
  have hthetaL : bankTrialSuccessThetaUniformHorizon n q ≤ L :=
    Nat.le_trans (Nat.le_max_left _ _) hL
  have htheta := (bankTrialSuccessThetaLowerUniform
    ring root hn hsmall hw hlarge hpositive hK)
    S hclean L hthetaL
  have hscaled := Nat.mul_le_mul_left L htheta
  have hbase :
      (1023 * L) * n ^ L ≤
        (1024 * (L * 2 ^ (compileAdvice q).K)) *
          bankTrialRenewalPatternMass ring root S L L 0 := by
    calc
      (1023 * L) * n ^ L = L * (1023 * n ^ L) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ L * (1024 * 2 ^ (compileAdvice q).K *
          bankTrialProbabilityWinMass ring root S L) := hscaled
      _ = (1024 * (L * 2 ^ (compileAdvice q).K)) *
          bankTrialProbabilityWinMass ring root S L := by
            simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ (1024 * (L * 2 ^ (compileAdvice q).K)) *
          bankTrialRenewalPatternMass ring root S L L 0 :=
            Nat.mul_le_mul_left _
              (bankTrialRenewalWonLeZeroMassAtHorizon ring root S L)
  have hsum : L + (T - L) = T := by omega
  have hpower : n ^ T = n ^ L * n ^ (T - L) := by
    calc
      n ^ T = n ^ (L + (T - L)) := by rw [hsum]
      _ = n ^ L * n ^ (T - L) := Nat.pow_add n L (T - L)
  have hpad :
      n ^ (T - L) * bankTrialRenewalPatternMass ring root S L L 0 ≤
        bankTrialRenewalPatternMass ring root S T L 0 := by
    have hh := bankTrialRenewalZeroMassPadding
      ring root S L (T - L)
    simpa only [hsum] using hh
  rw [hpower]
  exact bankTrialRenewalLowerPadArithmetic
    (1023 * L) (1024 * (L * 2 ^ (compileAdvice q).K))
    (n ^ L) (n ^ (T - L))
    (bankTrialRenewalPatternMass ring root S L L 0)
    (bankTrialRenewalPatternMass ring root S T L 0)
    hbase hpad

/-- The all-index theta mass sandwich, with the original
first-LOST lower bound scaled to the C.5 denominator. -/
theorem bankTrialRenewalEvalThetaMassSandwich
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (L : Nat)
    (hL : bankTrialRenewalWonCutoffThreshold n q ≤ L) :
    BankTrialRenewalMassSandwichTarget (q := q) ring root L
      (1024 * (L * 2 ^ (compileAdvice q).K - L -
        2 ^ (compileAdvice q).K *
          ((8 * (compileAdvice q).b + 12) * n)))
      (1023 * L) (1024 * (L * 2 ^ (compileAdvice q).K)) := by
  have hW := bankTrialRenewalEvalThetaWonBound
    ring root hn hsmall hw hlarge hpositive hK L hL
  have hF :
      BankTrialRenewalLostWithinBound (q := q) ring root L
        (1024 * (L * 2 ^ (compileAdvice q).K - L -
          2 ^ (compileAdvice q).K *
            ((8 * (compileAdvice q).b + 12) * n)))
        (1024 * (L * 2 ^ (compileAdvice q).K)) := by
    intro S hclean T hLT
    have hbase := (bankTrialRenewalLostWithinBoundUniform
      ring root hn hsmall hw hlarge hpositive hK L) S hclean T hLT
    have hscaled := Nat.mul_le_mul_left 1024 hbase
    simpa only [Nat.mul_assoc] using hscaled
  exact bankTrialRenewalMassSandwichOfTrialBounds
    ring root L
    (1024 * (L * 2 ^ (compileAdvice q).K - L -
      2 ^ (compileAdvice q).K *
        ((8 * (compileAdvice q).b + 12) * n)))
    (1023 * L) (1024 * (L * 2 ^ (compileAdvice q).K))
    hW hF

/-- Exact H=22517 evaluation of the existing cleared sandwich.
The only new probabilistic hypothesis is G0 at the improved
gM=g+ceil(g/1024). All powers remain untouched. -/
theorem bankTrialRenewalEvalClearedCleanWindow
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (L T W : Nat)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold n q ≤ L)
    (hwindow : W ≤ T)
    (hbudget : 22517 * L ≤ T)
    (hG : BankTrialRenewalZeroCostWithinBound (q := q)
      ring root L
      ((8 * (compileAdvice q).b + 12) *
        ((compileAdvice q).K + 1) +
       (((8 * (compileAdvice q).b + 12) *
        ((compileAdvice q).K + 1) + 1023) / 1024))) :
    W * (2 ^ (compileAdvice q).K) * n ^ T *
      bankTrialSuccessStageIndexSum (fun j =>
        (1024 * (L * 2 ^ (compileAdvice q).K - L -
          2 ^ (compileAdvice q).K *
            ((8 * (compileAdvice q).b + 12) * n))) ^ j *
        (1023 * L) *
        (1024 * (L * 2 ^ (compileAdvice q).K)) ^
          (22517 - (j + 1))) 22517 ≤
    (1024 * (L * 2 ^ (compileAdvice q).K)) ^ 22517 *
      (W * (2 ^ (compileAdvice q).K) *
         bankTrialRenewalSuccessMass ring root S T W +
       n ^ T * bankTrialSuccessStageIndexSum (fun j =>
         n * ((8 * (compileAdvice q).b + 12) *
              ((compileAdvice q).K + 1) +
           (((8 * (compileAdvice q).b + 12) *
             ((compileAdvice q).K + 1) + 1023) / 1024) +
           j * (8 * (compileAdvice q).b + 13))) 22517) := by
  have hthreshold : bankTrialRenewalWonCutoffThreshold n q ≤ L :=
    bankTrialRenewalEvalCutoffDescent
      (bankTrialRenewalWonCutoffThreshold n q) L hL
  have hmass := bankTrialRenewalEvalThetaMassSandwich
    ring root hn hsmall hw hlarge hpositive hK L hthreshold
  have hcost := bankTrialRenewalCostSandwichOfTrialBounds
    ring root L
    (8 * (compileAdvice q).b + 13)
    ((8 * (compileAdvice q).b + 12) *
        ((compileAdvice q).K + 1) +
      (((8 * (compileAdvice q).b + 12) *
        ((compileAdvice q).K + 1) + 1023) / 1024))
    hG
    (bankTrialRenewalLostCostWithinBoundHolds
      ring root hn hsmall hw hpositive hK L)
    (bankTrialRenewalZeroRareWithinBoundHolds
      ring root hn hsmall hw hlarge hpositive hK L)
  exact bankTrialRenewalClearedWindowOfSandwiches
    ring root S hclean
    L
    (1024 * (L * 2 ^ (compileAdvice q).K - L -
      2 ^ (compileAdvice q).K *
        ((8 * (compileAdvice q).b + 12) * n)))
    (1023 * L)
    (1024 * (L * 2 ^ (compileAdvice q).K))
    (8 * (compileAdvice q).b + 13)
    ((8 * (compileAdvice q).b + 12) *
        ((compileAdvice q).K + 1) +
      (((8 * (compileAdvice q).b + 12) *
        ((compileAdvice q).K + 1) + 1023) / 1024))
    22517 T W hwindow hbudget hmass hcost

/-- The corrected 49/100 *arithmetic* certificate when one
theta=1023/1024 factor is used for C.5 and the other for
the first-success-index geometric lower estimate, while
the absolute cost sandwich is not given an extra theta factor.

The strict positive difference is 70312504108000.
The separate theorem connecting this inequality to the
variable-H geometric sum has NOT been proved. -/
theorem bankTrialRenewalEvalThetaCostCertificate :
    98 * 255 ^ 2 * 1024 ^ 2 * 22517 +
        70312504108000 =
      100 * 253 *
        (255 * (2 * 1023 ^ 2 - 1024 ^ 2) -
          2 * 1024 ^ 2) * 22516 := by
  decide

end L3


namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
G13-INDEX-RENEWAL.
No assumption of a new probabilistic leaf is used.

The large scheduler powers below are not normalized in arithmetic tactics.
The fixed 22517-index sandwich is NOT itself the variable-index C.16
49/100 lower bound.
-/

/-- Multiplication of a max cutoff controls the max of its
first component and the multiplied second component. -/
private theorem bankTrialRenewalIndexMaxStretch
    (A B M : Nat) (hM : 1 ≤ M) :
    Nat.max A (M * B) ≤ M * Nat.max A B := by
  have hstretch : Nat.max A B ≤ M * Nat.max A B := by
    have hh := Nat.mul_le_mul_right (Nat.max A B) hM
    simpa only [Nat.one_mul] using hh
  exact Nat.max_le.mpr
    ⟨Nat.le_trans (Nat.le_max_left A B) hstretch,
     Nat.mul_le_mul_left M (Nat.le_max_right A B)⟩

/-- The threshold used by the cleared window is at least the M=1024
sharp threshold. The compiler powers are opaque. -/
theorem bankTrialRenewalIndexSharpCutoffCovered
    (n q L : Nat)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold n q ≤ L) :
    bankTrialRenewalWonCutoffThresholdSharp n q 1024 ≤ L := by
  have hh := bankTrialRenewalIndexMaxStretch
    (bankTrialSuccessThetaUniformHorizon n q)
    (1024 * 2 ^ (compileAdvice q).K *
      ((8 * (compileAdvice q).b + 12) * n))
    1024 (by decide)
  have hshape :
      bankTrialRenewalWonCutoffThresholdSharp n q 1024 ≤
        1024 * bankTrialRenewalWonCutoffThreshold n q := by
    unfold bankTrialRenewalWonCutoffThresholdSharp
      bankTrialRenewalWonCutoffThreshold
    simpa only [Nat.mul_assoc] using hh
  exact Nat.le_trans hshape hL

/-- The subtraction in the earlier integer ceiling is exactly the
addition of 1023 before division by 1024. -/
private theorem bankTrialRenewalIndexCeilIdentity (g : Nat) :
    (g + 1024 - 1) / 1024 = (g + 1023) / 1024 := by
  have hnum : g + 1024 - 1 = g + 1023 := by omega
  rw [hnum]

/-- The C.16 cleared window inequality for ANY finite number
of indices. Its G0 premise is discharged by the sharp
theorem with M=1024. The finite index H is not replaced by
the lower bound 22517. -/
theorem bankTrialRenewalIndexClearedCleanWindowAnyH
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (L H T W : Nat)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold n q ≤ L)
    (hwindow : W ≤ T)
    (hbudget : H * L ≤ T) :
    W * (2 ^ (compileAdvice q).K) * n ^ T *
      bankTrialSuccessStageIndexSum (fun j =>
        (1024 * (L * 2 ^ (compileAdvice q).K - L -
          2 ^ (compileAdvice q).K *
            ((8 * (compileAdvice q).b + 12) * n))) ^ j *
        (1023 * L) *
        (1024 * (L * 2 ^ (compileAdvice q).K)) ^
          (H - (j + 1))) H ≤
    (1024 * (L * 2 ^ (compileAdvice q).K)) ^ H *
      (W * (2 ^ (compileAdvice q).K) *
         bankTrialRenewalSuccessMass ring root S T W +
       n ^ T * bankTrialSuccessStageIndexSum (fun j =>
         n * ((8 * (compileAdvice q).b + 12) *
              ((compileAdvice q).K + 1) +
           (((8 * (compileAdvice q).b + 12) *
             ((compileAdvice q).K + 1) + 1023) / 1024) +
           j * (8 * (compileAdvice q).b + 13))) H) := by
  have hsharp :
      bankTrialRenewalWonCutoffThresholdSharp n q 1024 ≤ L :=
    bankTrialRenewalIndexSharpCutoffCovered n q L hL
  have hG :
      BankTrialRenewalZeroCostWithinBound (q := q)
        ring root L
        ((8 * (compileAdvice q).b + 12) *
          ((compileAdvice q).K + 1) +
         (((8 * (compileAdvice q).b + 12) *
           ((compileAdvice q).K + 1) + 1023) / 1024)) := by
    have hGsharp := bankTrialRenewalZeroCostWithinBoundSharp
      ring root hn hsmall hw hlarge hpositive hK
      1024 (by decide) L hsharp
    simpa only [bankTrialRenewalIndexCeilIdentity] using hGsharp
  have hthreshold :
      bankTrialRenewalWonCutoffThreshold n q ≤ L :=
    bankTrialRenewalEvalCutoffDescent
      (bankTrialRenewalWonCutoffThreshold n q) L hL
  have hmass := bankTrialRenewalEvalThetaMassSandwich
    ring root hn hsmall hw hlarge hpositive hK L hthreshold
  have hcost := bankTrialRenewalCostSandwichOfTrialBounds
    ring root L
    (8 * (compileAdvice q).b + 13)
    ((8 * (compileAdvice q).b + 12) *
        ((compileAdvice q).K + 1) +
      (((8 * (compileAdvice q).b + 12) *
        ((compileAdvice q).K + 1) + 1023) / 1024))
    hG
    (bankTrialRenewalLostCostWithinBoundHolds
      ring root hn hsmall hw hpositive hK L)
    (bankTrialRenewalZeroRareWithinBoundHolds
      ring root hn hsmall hw hlarge hpositive hK L)
  exact bankTrialRenewalClearedWindowOfSandwiches
    ring root S hclean
    L
    (1024 * (L * 2 ^ (compileAdvice q).K - L -
      2 ^ (compileAdvice q).K *
        ((8 * (compileAdvice q).b + 12) * n)))
    (1023 * L)
    (1024 * (L * 2 ^ (compileAdvice q).K))
    (8 * (compileAdvice q).b + 13)
    ((8 * (compileAdvice q).b + 12) *
        ((compileAdvice q).K + 1) +
      (((8 * (compileAdvice q).b + 12) *
        ((compileAdvice q).K + 1) + 1023) / 1024))
    H T W hwindow hbudget hmass hcost

/-- The exact existing H=22517 statement, now with no
unproved hG supplied by the caller. -/
theorem bankTrialRenewalIndexClearedCleanWindow
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (hsmall : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (L T W : Nat)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold n q ≤ L)
    (hwindow : W ≤ T)
    (hbudget : 22517 * L ≤ T) :
    W * (2 ^ (compileAdvice q).K) * n ^ T *
      bankTrialSuccessStageIndexSum (fun j =>
        (1024 * (L * 2 ^ (compileAdvice q).K - L -
          2 ^ (compileAdvice q).K *
            ((8 * (compileAdvice q).b + 12) * n))) ^ j *
        (1023 * L) *
        (1024 * (L * 2 ^ (compileAdvice q).K)) ^
          (22517 - (j + 1))) 22517 ≤
    (1024 * (L * 2 ^ (compileAdvice q).K)) ^ 22517 *
      (W * (2 ^ (compileAdvice q).K) *
         bankTrialRenewalSuccessMass ring root S T W +
       n ^ T * bankTrialSuccessStageIndexSum (fun j =>
         n * ((8 * (compileAdvice q).b + 12) *
              ((compileAdvice q).K + 1) +
           (((8 * (compileAdvice q).b + 12) *
             ((compileAdvice q).K + 1) + 1023) / 1024) +
           j * (8 * (compileAdvice q).b + 13))) 22517) := by
  exact bankTrialRenewalIndexClearedCleanWindowAnyH
    ring root hn hsmall hw hlarge hpositive hK
    S hclean L 22517 T W hL hwindow hbudget

/-- The C.5 paper theta numerator/denominator, squared and
multiplied by 49/100, has the exact coprime-unreduced
integer clearing shown here. This is a normalization, not a
probability lower bound. -/
theorem bankTrialRenewalIndexThetaSquareClearing
    (W N f n P S : Nat) :
    (49 * 1023 ^ 2 * W * N ≤
      100 * 1024 ^ 2 * f * n * P * S) ↔
    (51279921 * W * N ≤
      104857600 * f * n * P * S) := by
  rw [show (49 * 1023 ^ 2 : Nat) = 51279921 by decide,
    show (100 * 1024 ^ 2 : Nat) = 104857600 by decide]

/-- A positive integer gap implies a strict comparison, with
the possibly huge operands opaque to omega. -/
private theorem bankTrialRenewalIndexPositiveGap
    (a b gap : Nat)
    (hgap : 0 < gap) (hidentity : a + gap = b) :
    a < b := by
  omega

/-- The earlier exact theta-squared cost coefficient certificate
has a strictly positive gap of 70312504108000. -/
theorem bankTrialRenewalIndexThetaCostStrict :
    98 * 255 ^ 2 * 1024 ^ 2 * 22517 <
      100 * 253 *
        (255 * (2 * 1023 ^ 2 - 1024 ^ 2) -
          2 * 1024 ^ 2) * 22516 := by
  exact bankTrialRenewalIndexPositiveGap
    (98 * 255 ^ 2 * 1024 ^ 2 * 22517)
    (100 * 253 *
      (255 * (2 * 1023 ^ 2 - 1024 ^ 2) -
        2 * 1024 ^ 2) * 22516)
    70312504108000
    (by decide)
    bankTrialRenewalEvalThetaCostCertificate

/-- One is below every power of two, using only Nat arithmetic. -/
private theorem bankTrialRenewalIndexOneLeTwoPow (k : Nat) :
    1 ≤ 2 ^ k := by
  induction k with
  | zero =>
      decide
  | succ k ih =>
      calc
        1 ≤ 1 * 2 := by decide
        _ ≤ (2 ^ k) * 2 := Nat.mul_le_mul_right 2 ih
        _ = 2 ^ (k + 1) := (Nat.pow_succ 2 k).symm

/-- The positive compiled K makes its scheduler denominator
at least two. -/
private theorem bankTrialRenewalIndexTwoLePositivePower
    (k : Nat) (hk : 0 < k) :
    2 ≤ 2 ^ k := by
  cases k with
  | zero =>
      omega
  | succ k =>
      have hpow := bankTrialRenewalIndexOneLeTwoPow k
      calc
        2 = 1 * 2 := by decide
        _ ≤ (2 ^ k) * 2 := Nat.mul_le_mul_right 2 hpow
        _ = 2 ^ (k + 1) := (Nat.pow_succ 2 k).symm

private theorem bankTrialRenewalIndexStretchBound (x : Nat) :
    x ≤ 1024 * (1024 * x) := by
  omega

private theorem bankTrialRenewalIndexDenBudget
    (L P B : Nat)
    (hP : 2 ≤ P) (hBP : P * B ≤ L) :
    L + P * B ≤ L * P := by
  have htwo : L + P * B ≤ L * 2 := by omega
  exact Nat.le_trans htwo (Nat.mul_le_mul_left L hP)

/-- The same cutoff also makes the LOST numerator's
two successive Nat subtractions exact: L + P*B <= L*P. -/
theorem bankTrialRenewalIndexLostDenLower
    (n q L : Nat)
    (hpositive : 0 < (compileAdvice q).K)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold n q ≤ L) :
    L + 2 ^ (compileAdvice q).K *
      ((8 * (compileAdvice q).b + 12) * n) ≤
    L * 2 ^ (compileAdvice q).K := by
  have hcut :
      1024 * 2 ^ (compileAdvice q).K *
        ((8 * (compileAdvice q).b + 12) * n) ≤
      bankTrialRenewalWonCutoffThreshold n q := by
    unfold bankTrialRenewalWonCutoffThreshold
    exact Nat.le_max_right _ _
  have hmult := Nat.mul_le_mul_left 1024 hcut
  have hBP :
      2 ^ (compileAdvice q).K *
        ((8 * (compileAdvice q).b + 12) * n) ≤ L := by
    calc
      2 ^ (compileAdvice q).K *
          ((8 * (compileAdvice q).b + 12) * n) ≤
        1024 * (1024 *
          (2 ^ (compileAdvice q).K *
            ((8 * (compileAdvice q).b + 12) * n))) :=
              bankTrialRenewalIndexStretchBound _
      _ = 1024 * (1024 * 2 ^ (compileAdvice q).K *
          ((8 * (compileAdvice q).b + 12) * n)) := by
            simp only [Nat.mul_assoc]
      _ ≤ 1024 * bankTrialRenewalWonCutoffThreshold n q := hmult
      _ ≤ L := hL
  exact bankTrialRenewalIndexDenBudget
    L (2 ^ (compileAdvice q).K)
    ((8 * (compileAdvice q).b + 12) * n)
    (bankTrialRenewalIndexTwoLePositivePower
      (compileAdvice q).K hpositive)
    hBP

/-- Nat subtraction cancellation for the exact LOST gap.
No rational probability is postulated. -/
private theorem bankTrialRenewalIndexDenDecompose
    (D L B : Nat) (h : L + B ≤ D) :
    1024 * (D - L - B) + 1024 * (L + B) = 1024 * D := by
  have hc : (D - L - B) + (L + B) = D := by omega
  calc
    1024 * (D - L - B) + 1024 * (L + B) =
      1024 * ((D - L - B) + (L + B)) :=
        (Nat.mul_add _ _ _).symm
    _ = 1024 * D := by rw [hc]

/-- In the actual theta-enhanced sandwich, LOST numerator
plus its exact loss is the common denominator:
lo + 1024*(L+P*B) = den, P=2^K, B=(8b+12)n. -/
theorem bankTrialRenewalIndexLostDenIdentity
    (n q L : Nat)
    (hpositive : 0 < (compileAdvice q).K)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold n q ≤ L) :
    1024 * (L * 2 ^ (compileAdvice q).K - L -
      2 ^ (compileAdvice q).K *
        ((8 * (compileAdvice q).b + 12) * n)) +
    1024 * (L + 2 ^ (compileAdvice q).K *
      ((8 * (compileAdvice q).b + 12) * n)) =
    1024 * (L * 2 ^ (compileAdvice q).K) := by
  exact bankTrialRenewalIndexDenDecompose
    (L * 2 ^ (compileAdvice q).K) L
    (2 ^ (compileAdvice q).K *
      ((8 * (compileAdvice q).b + 12) * n))
    (bankTrialRenewalIndexLostDenLower n q L hpositive hL)

end L3


namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-!
Variable-index continuation.
No extra probabilistic premise is postulated.

The exact geometric-budget certificate needed to complete
the paper's C.16 reduction is recorded after the code.
-/

private theorem bankTrialRenewalIndexSumStep
    (a f k s : Nat)
    (hk : k * f ≤ a)
    (h : 2 * s + f * k * (k + 1) = 2 * k * (a + f)) :
    2 * (s + (a - k * f)) +
      f * (k + 1) * (k + 2) =
      2 * (k + 1) * (a + f) := by
  have hc : a - k * f + k * f = a :=
    Nat.sub_add_cancel hk
  have hnext :
      f * (k + 1) * (k + 2) =
        f * k * (k + 1) + 2 * (f * (k + 1)) := by
    calc
      f * (k + 1) * (k + 2) =
          f * (k + 1) * k + f * (k + 1) * 2 := by
            rw [Nat.mul_add (f * (k + 1)) k 2]
      _ = f * k * (k + 1) + 2 * (f * (k + 1)) := by
            simp only [Nat.mul_assoc, Nat.mul_left_comm,
              Nat.mul_comm]
  have hadd :
      (a - k * f) + f * (k + 1) = a + f := by
    calc
      (a - k * f) + f * (k + 1) =
          (a - k * f) + (k * f + f) := by
            rw [Nat.mul_add f k 1, Nat.mul_one, Nat.mul_comm f k]
      _ = ((a - k * f) + k * f) + f := by
            simp only [Nat.add_assoc]
      _ = a + f := by rw [hc]
  have htwice :
      2 * (a - k * f) + 2 * (f * (k + 1)) =
        2 * (a + f) := by
    calc
      _ = 2 * ((a - k * f) + f * (k + 1)) :=
        (Nat.mul_add _ _ _).symm
      _ = 2 * (a + f) := by rw [hadd]
  have hright :
      2 * k * (a + f) + 2 * (a + f) =
        2 * (k + 1) * (a + f) := by
    have hkstep : 2 * k + 2 = 2 * (k + 1) := by omega
    calc
      _ = (2 * k + 2) * (a + f) :=
        (Nat.add_mul _ _ _).symm
      _ = (2 * (k + 1)) * (a + f) := by rw [hkstep]
      _ = 2 * (k + 1) * (a + f) := rfl
  calc
    2 * (s + (a - k * f)) + f * (k + 1) * (k + 2) =
        2 * s + 2 * (a - k * f) +
          (f * k * (k + 1) + 2 * (f * (k + 1))) := by
            rw [hnext, Nat.mul_add 2 s (a - k * f)]
    _ = (2 * s + f * k * (k + 1)) +
          (2 * (a - k * f) + 2 * (f * (k + 1))) := by
            omega
    _ = 2 * k * (a + f) + 2 * (a + f) := by
          rw [h, htwice]
    _ = 2 * (k + 1) * (a + f) := hright

private theorem bankTrialRenewalIndexSumIdentity
    (a f : Nat) :
    ∀ H, H * f ≤ a →
      2 * bankTrialSuccessStageIndexSum
          (fun j => a - j * f) H +
        f * H * (H + 1) = 2 * H * (a + f) := by
  intro H
  induction H with
  | zero =>
      intro _
      simp [bankTrialSuccessStageIndexSum]
  | succ k ih =>
      intro h
      have hk : k * f ≤ a :=
        Nat.le_trans
          (Nat.mul_le_mul_right f (Nat.le_succ k)) h
      change
        2 * (bankTrialSuccessStageIndexSum
          (fun j => a - j * f) k + (a - k * f)) +
          f * (k + 1) * (k + 2) =
        2 * (k + 1) * (a + f)
      exact bankTrialRenewalIndexSumStep a f k
        (bankTrialSuccessStageIndexSum
          (fun j => a - j * f) k) hk (ih hk)

private theorem bankTrialRenewalIndexSumTriangle
    (a f H : Nat) (hH : H * f ≤ a) :
    f * H * (H + 1) ≤
      2 * bankTrialSuccessStageIndexSum
        (fun j => a - j * f) H := by
  have hstep : (H + 1) * f ≤ a + f := by
    have h := Nat.add_le_add_right hH f
    simpa only [Nat.add_mul, Nat.one_mul] using h
  have hscaled := Nat.mul_le_mul_left (2 * H) hstep
  have hdouble :
      2 * (f * H * (H + 1)) ≤
        2 * H * (a + f) := by
    simpa only [Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm] using hscaled
  have hid := bankTrialRenewalIndexSumIdentity a f H hH
  omega

/-- Stronger than 49/100; the surplus pays for index losses. -/
theorem bankTrialRenewalIndexSumStrong
    (u C f H : Nat)
    (hf : 0 < f)
    (hC : 255 * C ≤ 2 * u)
    (hfloor : H = (u - C) / f)
    (hlarge : 22517 ≤ H) :
    491 * u * u ≤
      1000 * f *
        bankTrialSuccessStageIndexSum
          (fun j => u - C - j * f) H := by
  have hCle : C ≤ u := by omega
  have hdiv : (u - C) % f + f * H = u - C := by
    rw [hfloor]
    exact Nat.mod_add_div (u - C) f
  have hrem : (u - C) % f < f :=
    Nat.mod_lt (u - C) hf
  have hlow : H * f ≤ u - C := by
    have hh : f * H ≤ u - C := by omega
    simpa only [Nat.mul_comm] using hh
  have hupp : u - C ≤ f * (H + 1) := by
    rw [Nat.mul_add]
    omega
  have hsub : u - C + C = u := Nat.sub_add_cancel hCle
  have hratio : 253 * u ≤ 255 * (u - C) := by omega
  have hcap : 253 * u ≤ 255 * f * (H + 1) := by
    calc
      253 * u ≤ 255 * (u - C) := hratio
      _ ≤ 255 * (f * (H + 1)) :=
        Nat.mul_le_mul_left 255 hupp
      _ = 255 * f * (H + 1) := by
        rw [Nat.mul_assoc]
  have hcoef :
      491 * 255 ^ 2 * (H + 1) ≤
        500 * 253 ^ 2 * H := by
    rw [show (491 * 255 ^ 2 : Nat) = 31927275 by decide,
      show (500 * 253 ^ 2 : Nat) = 32004500 by decide]
    omega
  have hsquare := Nat.mul_le_mul hcap hcap
  have htriangle :=
    bankTrialRenewalIndexSumTriangle (u - C) f H hlow
  have hscaled :
      253 ^ 2 * (491 * u * u) ≤
        253 ^ 2 * (1000 * f *
          bankTrialSuccessStageIndexSum
            (fun j => u - C - j * f) H) := by
    calc
      253 ^ 2 * (491 * u * u) =
          491 * ((253 * u) * (253 * u)) := by
            simp only [Nat.pow_succ, Nat.pow_zero,
              Nat.mul_one, Nat.one_mul, Nat.mul_assoc,
              Nat.mul_left_comm, Nat.mul_comm]
      _ ≤ 491 * ((255 * f * (H + 1)) *
            (255 * f * (H + 1))) :=
          Nat.mul_le_mul_left 491 hsquare
      _ = (491 * 255 ^ 2 * (H + 1)) *
            (f * f * (H + 1)) := by
            simp only [Nat.pow_succ, Nat.pow_zero,
              Nat.mul_one, Nat.one_mul, Nat.mul_assoc,
              Nat.mul_left_comm, Nat.mul_comm]
      _ ≤ (500 * 253 ^ 2 * H) *
            (f * f * (H + 1)) :=
          Nat.mul_le_mul_right _ hcoef
      _ = (500 * 253 ^ 2 * f) *
            (f * H * (H + 1)) := by
            simp only [Nat.mul_assoc, Nat.mul_left_comm,
              Nat.mul_comm]
      _ ≤ (500 * 253 ^ 2 * f) *
            (2 * bankTrialSuccessStageIndexSum
              (fun j => u - C - j * f) H) :=
          Nat.mul_le_mul_left _ htriangle
      _ = 253 ^ 2 * (1000 * f *
            bankTrialSuccessStageIndexSum
              (fun j => u - C - j * f) H) := by
            rw [show (1000 : Nat) = 500 * 2 by decide]
            simp only [Nat.mul_assoc, Nat.mul_left_comm,
              Nat.mul_comm]
  exact Nat.le_of_mul_le_mul_left hscaled
    (by decide : 0 < (253 ^ 2 : Nat))

/-- Requested cleared variable-H sum inequality. -/
theorem bankTrialRenewalIndexSumFortyNine
    (u C f H : Nat)
    (hf : 0 < f)
    (hC : 255 * C ≤ 2 * u)
    (hfloor : H = (u - C) / f)
    (hlarge : 22517 ≤ H) :
    49 * u * u ≤
      100 * f *
        bankTrialSuccessStageIndexSum
          (fun j => u - C - j * f) H := by
  have hs := bankTrialRenewalIndexSumStrong
    u C f H hf hC hfloor hlarge
  have hnormalized :
      491 * (u * u) ≤
        1000 * (f * bankTrialSuccessStageIndexSum
          (fun j => u - C - j * f) H) := by
    simpa only [Nat.mul_assoc] using hs
  have hweak :
      490 * (u * u) ≤
        1000 * (f * bankTrialSuccessStageIndexSum
          (fun j => u - C - j * f) H) := by
    omega
  have hten :
      10 * (49 * u * u) ≤
        10 * (100 * f *
          bankTrialSuccessStageIndexSum
            (fun j => u - C - j * f) H) := by
    calc
      10 * (49 * u * u) = (10 * 49) * (u * u) := by
        simp only [Nat.mul_assoc]
      _ = 490 * (u * u) := by
        rw [show (10 * 49 : Nat) = 490 by decide]
      _ ≤ 1000 * (f * bankTrialSuccessStageIndexSum
            (fun j => u - C - j * f) H) := hweak
      _ = (10 * 100) *
            (f * bankTrialSuccessStageIndexSum
              (fun j => u - C - j * f) H) := by
        rw [show (10 * 100 : Nat) = 1000 by decide]
      _ = 10 * (100 * f *
            bankTrialSuccessStageIndexSum
              (fun j => u - C - j * f) H) := by
        simp only [Nat.mul_assoc]
  exact Nat.le_of_mul_le_mul_left hten
    (by decide : 0 < (10 : Nat))

private theorem bankTrialRenewalIndexPowerMono
    (lo den j : Nat) (hle : lo ≤ den) :
    lo ^ j ≤ den ^ j := by
  induction j with
  | zero => exact Nat.le_refl _
  | succ j ih =>
      rw [Nat.pow_succ, Nat.pow_succ]
      exact Nat.mul_le_mul ih hle

private theorem bankTrialRenewalIndexPowerDifference
    (lo gap den : Nat)
    (hden : lo + gap = den) :
    ∀ j, den ^ (j + 1) ≤
      lo ^ (j + 1) + (j + 1) * gap * den ^ j := by
  intro j
  induction j with
  | zero =>
      simpa using (Nat.le_of_eq hden.symm)
  | succ k ih =>
      have hp : lo ^ (k + 1) ≤ den ^ (k + 1) :=
        bankTrialRenewalIndexPowerMono lo den (k + 1)
          (by omega)
      have hs := Nat.mul_le_mul_right den ih
      have hprod :
          lo ^ (k + 1) * den =
            lo ^ (k + 1 + 1) + gap * lo ^ (k + 1) := by
        calc
          lo ^ (k + 1) * den =
              lo ^ (k + 1) * (lo + gap) := by rw [hden]
          _ = lo ^ (k + 1 + 1) + gap * lo ^ (k + 1) := by
                rw [Nat.mul_add, ← Nat.pow_succ]
                rw [Nat.mul_comm (lo ^ (k + 1)) gap]
      have hstepProd :
          ((k + 1) * gap * den ^ k) * den =
            (k + 1) * gap * den ^ (k + 1) := by
        rw [Nat.pow_succ]
        simp only [Nat.mul_assoc, Nat.mul_left_comm,
          Nat.mul_comm]
      have hg := Nat.mul_le_mul_left gap hp
      have htail :
          gap * den ^ (k + 1) +
              (k + 1) * gap * den ^ (k + 1) =
            ((k + 1) + 1) * gap * den ^ (k + 1) := by
        have hcoef :
            gap + (k + 1) * gap = ((k + 1) + 1) * gap := by
          calc
            _ = (k + 1) * gap + gap := Nat.add_comm _ _
            _ = ((k + 1) + 1) * gap := by
                  rw [Nat.add_mul (k + 1) 1 gap, Nat.one_mul]
        calc
          _ = (gap + (k + 1) * gap) * den ^ (k + 1) := by
                rw [Nat.add_mul gap ((k + 1) * gap) (den ^ (k + 1))]
          _ = ((k + 1) + 1) * gap * den ^ (k + 1) := by
                rw [hcoef]
      calc
        den ^ (k + 1 + 1) = den ^ (k + 1) * den := by
          rw [Nat.pow_succ]
        _ ≤ (lo ^ (k + 1) +
              (k + 1) * gap * den ^ k) * den := hs
        _ = lo ^ (k + 1 + 1) +
              gap * lo ^ (k + 1) +
              (k + 1) * gap * den ^ (k + 1) := by
            calc
              (lo ^ (k + 1) +
                (k + 1) * gap * den ^ k) * den =
                  lo ^ (k + 1) * den +
                    ((k + 1) * gap * den ^ k) * den := by
                      rw [Nat.add_mul (lo ^ (k + 1))
                        ((k + 1) * gap * den ^ k) den]
              _ = (lo ^ (k + 1 + 1) + gap * lo ^ (k + 1)) +
                    ((k + 1) * gap * den ^ k) * den := by
                      rw [hprod]
              _ = lo ^ (k + 1 + 1) +
                    gap * lo ^ (k + 1) +
                    (k + 1) * gap * den ^ (k + 1) := by
                      rw [hstepProd]
        _ ≤ lo ^ (k + 1 + 1) +
              gap * den ^ (k + 1) +
              (k + 1) * gap * den ^ (k + 1) :=
            Nat.add_le_add_right
              (Nat.add_le_add_left hg _) _
        _ = lo ^ (k + 1 + 1) +
              ((k + 1) + 1) * gap * den ^ (k + 1) := by
            calc
              lo ^ (k + 1 + 1) + gap * den ^ (k + 1) +
                (k + 1) * gap * den ^ (k + 1) =
                  lo ^ (k + 1 + 1) +
                    (gap * den ^ (k + 1) +
                      (k + 1) * gap * den ^ (k + 1)) := by
                        rw [Nat.add_assoc
                          (lo ^ (k + 1 + 1))
                          (gap * den ^ (k + 1))
                          ((k + 1) * gap * den ^ (k + 1))]
              _ = lo ^ (k + 1 + 1) +
                    ((k + 1) + 1) * gap * den ^ (k + 1) := by
                        rw [htail]

private theorem bankTrialRenewalIndexBernoulliFinish
    (a b : Nat)
    (h : 1024 * a ≤ 1024 * b + a) :
    1023 * a ≤ 1024 * b := by
  omega

/-- Geometric loss: 1024*lo^j >= 1023*den^j for j<H. -/
theorem bankTrialRenewalIndexBernoulli
    (lo gap den H j : Nat)
    (hden : lo + gap = den)
    (hgap : H * gap ≤ den / 1024)
    (hj : j < H) :
    1023 * den ^ j ≤ 1024 * lo ^ j := by
  have hmon := Nat.mul_le_mul_right gap (Nat.le_of_lt hj)
  have hsc := Nat.mul_le_mul_left 1024
    (Nat.le_trans hmon hgap)
  have hdiv := Nat.mod_add_div den 1024
  have hbound : 1024 * (j * gap) ≤ den := by omega
  cases j with
  | zero =>
      simp only [Nat.pow_zero, Nat.mul_one]
      decide
  | succ k =>
      have hp := bankTrialRenewalIndexPowerDifference
        lo gap den hden k
      have hps := Nat.mul_le_mul_left 1024 hp
      have hgapPow := Nat.mul_le_mul_right (den ^ k) hbound
      have htail :
          1024 * ((k + 1) * gap * den ^ k) ≤
            den ^ (k + 1) := by
        calc
          1024 * ((k + 1) * gap * den ^ k) =
              (1024 * ((k + 1) * gap)) * den ^ k := by
                simp only [Nat.mul_assoc]
          _ ≤ den * den ^ k := hgapPow
          _ = den ^ (k + 1) := by
                rw [Nat.pow_succ]
                rw [Nat.mul_comm]
      have hpow :
          1024 * den ^ (k + 1) ≤
            1024 * lo ^ (k + 1) + den ^ (k + 1) := by
        calc
          1024 * den ^ (k + 1) ≤
              1024 * (lo ^ (k + 1) +
                (k + 1) * gap * den ^ k) := hps
          _ = 1024 * lo ^ (k + 1) +
              1024 * ((k + 1) * gap * den ^ k) :=
                Nat.mul_add _ _ _
          _ ≤ 1024 * lo ^ (k + 1) + den ^ (k + 1) :=
                Nat.add_le_add_left htail _
      exact bankTrialRenewalIndexBernoulliFinish
        (den ^ (k + 1)) (lo ^ (k + 1)) hpow

end L3

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
G13: quota arithmetic.
Opaque arithmetic is used for compiler powers and scheduler powers.
The compiled quotas use W = (R*n)/8 (Nat division).
The geometric lemma admits every W with 8*W <= R*n.
-/

def bankTrialRenewalIndexZeroCharge (q : Nat) : Nat :=
  (8 * (compileAdvice q).b + 12) *
    ((compileAdvice q).K + 1) +
  (((8 * (compileAdvice q).b + 12) *
    ((compileAdvice q).K + 1) + 1023) / 1024)

def bankTrialRenewalIndexColdCharge (q : Nat) : Nat :=
  (2 * (compileAdvice q).bankLeaseCap +
    5 * (compileAdvice q).b + 13) +
    bankTrialRenewalIndexZeroCharge q

def bankTrialRenewalIndexStepCharge (q : Nat) : Nat :=
  8 * (compileAdvice q).b + 13

def bankTrialRenewalIndexWindowCount
    (n q W : Nat) : Nat :=
  (W - n * bankTrialRenewalIndexColdCharge q) /
    (n * bankTrialRenewalIndexStepCharge q)

/-- This copies the compiler's cold-overhead reserve, with the
M=1024 enlarged zero-pattern cost rather than its old g. -/
theorem bankTrialRenewalIndexCompiledColdReserve
    (n R : Nat)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hradius : (256 * R) ^ 2 ≤ n ∧
      n < (256 * (R + 1)) ^ 2) :
    1024 * bankTrialRenewalIndexColdCharge (ceilLogTwo n) ≤ R := by
  have hR := grantClockSpatialRadiusCutoff
    n R hn hsp hradius
  have hcoeff := bankTrialRenewalEvalOverheadBound
    (compileAdvice (ceilLogTwo n)).b
    (compileAdvice (ceilLogTwo n)).K
  have hsum := Nat.add_le_add_left hcoeff
    (2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
      5 * (compileAdvice (ceilLogTwo n)).b + 13)
  unfold bankTrialRenewalIndexColdCharge
    bankTrialRenewalIndexZeroCharge
  exact Nat.le_trans (Nat.mul_le_mul_left 1024 hsum) hR

/-- The quotient window estimate and the cold reserve imply
255*n*C <= 2*W without division in the goal. -/
private theorem bankTrialRenewalIndexRatioOpaque
    (n C R W : Nat)
    (hC : 1024 * C ≤ R)
    (hW : 255 * (R * n) ≤ 2048 * W) :
    255 * (n * C) ≤ 2 * W := by
  have hm := Nat.mul_le_mul_left (255 * n) hC
  have hscaled :
      1024 * (255 * (n * C)) ≤ 2048 * W := by
    calc
      1024 * (255 * (n * C)) =
          (255 * n) * (1024 * C) := by
            simp only [Nat.mul_assoc, Nat.mul_left_comm,
              Nat.mul_comm]
      _ ≤ (255 * n) * R := hm
      _ = 255 * (R * n) := by
            simp only [Nat.mul_assoc, Nat.mul_left_comm,
              Nat.mul_comm]
      _ ≤ 2048 * W := hW
  omega

/-- Both quota obligations hold for the
paper's W = (R*n)/8, not independent new assumptions. -/
theorem bankTrialRenewalIndexCompiledQuotas
    (n R W : Nat)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hradius : (256 * R) ^ 2 ≤ n ∧
      n < (256 * (R + 1)) ^ 2)
    (hW : W = R * n / 8) :
    255 * (n * bankTrialRenewalIndexColdCharge
      (ceilLogTwo n)) ≤ 2 * W ∧
    n * (bankTrialRenewalIndexColdCharge (ceilLogTwo n) +
      22517 * bankTrialRenewalIndexStepCharge
        (ceilLogTwo n)) ≤ W := by
  constructor
  · exact bankTrialRenewalIndexRatioOpaque
      n (bankTrialRenewalIndexColdCharge (ceilLogTwo n)) R W
      (bankTrialRenewalIndexCompiledColdReserve
        n R hn hsp hradius)
      (grantClockSpatialCompiledWindowQuotas
        n R W hn hsp hradius hW).1
  · have hquota := bankTrialRenewalEvalCompiledQuota
      n R W hn hsp hradius hW
    simpa only [bankTrialRenewalIndexColdCharge,
      bankTrialRenewalIndexZeroCharge,
      bankTrialRenewalIndexStepCharge] using hquota

/-- For x^2 <= n, a natural x is itself at most n. -/
private theorem bankTrialRenewalIndexSquareToLinear
    (x n : Nat) (h : x ^ 2 ≤ n) : x ≤ n := by
  have hself : x ≤ x * x := by
    cases x with
    | zero => simp
    | succ k =>
        have hpos : 1 ≤ k + 1 := by omega
        have hh := Nat.mul_le_mul_left (k + 1) hpos
        simpa only [Nat.mul_one] using hh
  calc
    x ≤ x * x := hself
    _ = x ^ 2 := by rw [Nat.pow_two]
    _ ≤ n := h

/-- n <= 2^K follows from q=ceilLogTwo n and K=2q+kappa.
The large 2^K is not normalized by omega. -/
private theorem bankTrialRenewalIndexPowerDominatesPopulation
    (n : Nat) (hn : 5 ≤ n) :
    n ≤ 2 ^ (compileAdvice (ceilLogTwo n)).K := by
  have hq : ceilLogTwo n ≤
      (compileAdvice (ceilLogTwo n)).K := by
    change ceilLogTwo n ≤
      2 * ceilLogTwo n + productionKappa (ceilLogTwo n)
    omega
  have hp := Nat.pow_le_pow_right
    (by decide : 0 < (2 : Nat)) hq
  exact Nat.le_trans (ceilLogTwo_spec n (by omega)).2 hp

/-- Opaque denominator-cleared gap argument. The exact division
by 1024 is evaluated only at the final arithmetic identity. -/
private theorem bankTrialRenewalIndexGapOpaque
    (H L P B : Nat)
    (hPB : P * B ≤ L)
    (hH : 2048 * H ≤ P) :
    H * (1024 * (L + P * B)) ≤
      (1024 * (L * P)) / 1024 := by
  have hsum : L + P * B ≤ 2 * L := by omega
  have hscaled := Nat.mul_le_mul_left (1024 * H) hsum
  have hdiv : (1024 * (L * P)) / 1024 = L * P := by
    simp
  calc
    H * (1024 * (L + P * B)) =
        (1024 * H) * (L + P * B) := by
          simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    _ ≤ (1024 * H) * (2 * L) := hscaled
    _ = (2048 * H) * L := by
          simp only [Nat.mul_assoc, Nat.mul_left_comm,
            Nat.mul_comm, Nat.reduceMul]
    _ ≤ P * L := Nat.mul_le_mul_right L hH
    _ = L * P := Nat.mul_comm _ _
    _ = (1024 * (L * P)) / 1024 := hdiv.symm

/-- The consumer window is the largest Nat W satisfying
8 * W <= R * n; this lemma uses the Euclidean remainder. -/
private theorem bankTrialRenewalIndexConsumerWindowCap
    (n R W : Nat) (hW : W = R * n / 8) :
    8 * W ≤ R * n := by
  have hmod := Nat.mod_add_div (R * n) 8
  rw [hW]
  omega

/-- Genuine compiler-based geometric budget for 8 * W <= R * n.
C can be any initial charge: subtracting it only decreases H.
No inequality involving giant powers is passed to omega. -/
theorem bankTrialRenewalIndexCompiledGeometricBudget
    (n R W C L : Nat)
    (hn : 5 ≤ n)
    (hradius : (256 * R) ^ 2 ≤ n)
    (hWcap : 8 * W ≤ R * n)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold
      n (ceilLogTwo n) ≤ L) :
    ((W - n * C) /
      (n * bankTrialRenewalIndexStepCharge (ceilLogTwo n))) *
      (1024 * (L + 2 ^ (compileAdvice (ceilLogTwo n)).K *
        ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n))) ≤
      (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K)) /
        1024 := by
  have hf : 1 ≤ bankTrialRenewalIndexStepCharge
      (ceilLogTwo n) := by
    unfold bankTrialRenewalIndexStepCharge
    omega
  have hquot := Nat.mod_add_div
    (W - n * C)
    (n * bankTrialRenewalIndexStepCharge (ceilLogTwo n))
  have hindex :
      (n * bankTrialRenewalIndexStepCharge (ceilLogTwo n)) *
        ((W - n * C) /
          (n * bankTrialRenewalIndexStepCharge (ceilLogTwo n))) ≤ W := by
    have hs : W - n * C ≤ W := Nat.sub_le _ _
    omega
  have hWscaled : 8 * W ≤ R * n := hWcap
  have hperiod :
      8 * ((W - n * C) /
          (n * bankTrialRenewalIndexStepCharge (ceilLogTwo n))) *
        bankTrialRenewalIndexStepCharge (ceilLogTwo n) ≤ R := by
    have hN :
        n * (8 * ((W - n * C) /
            (n * bankTrialRenewalIndexStepCharge
              (ceilLogTwo n))) *
          bankTrialRenewalIndexStepCharge (ceilLogTwo n)) ≤
          n * R := by
      calc
        _ = 8 * ((n * bankTrialRenewalIndexStepCharge
            (ceilLogTwo n)) *
            ((W - n * C) /
              (n * bankTrialRenewalIndexStepCharge
                (ceilLogTwo n)))) := by
              simp only [Nat.mul_assoc, Nat.mul_left_comm,
                Nat.mul_comm]
        _ ≤ 8 * W := Nat.mul_le_mul_left 8 hindex
        _ ≤ R * n := hWscaled
        _ = n * R := Nat.mul_comm _ _
    exact Nat.le_of_mul_le_mul_left hN (by omega)
  have hHbound :
      2048 * ((W - n * C) /
        (n * bankTrialRenewalIndexStepCharge (ceilLogTwo n))) ≤
        2 ^ (compileAdvice (ceilLogTwo n)).K := by
    have hh := Nat.mul_le_mul_left 256 hperiod
    have hsmall :
        2048 * ((W - n * C) /
          (n * bankTrialRenewalIndexStepCharge (ceilLogTwo n))) ≤
        256 * R := by
      calc
        _ ≤ (2048 * ((W - n * C) /
            (n * bankTrialRenewalIndexStepCharge
              (ceilLogTwo n)))) *
              bankTrialRenewalIndexStepCharge (ceilLogTwo n) := by
                have hm := Nat.mul_le_mul_left
                  (2048 * ((W - n * C) /
                    (n * bankTrialRenewalIndexStepCharge
                      (ceilLogTwo n)))) hf
                simpa only [Nat.mul_one] using hm
        _ ≤ 256 * R := by
              simpa only [Nat.mul_assoc, Nat.mul_left_comm,
                Nat.mul_comm, Nat.reduceMul] using hh
    exact Nat.le_trans hsmall
      (Nat.le_trans
        (bankTrialRenewalIndexSquareToLinear (256 * R) n hradius)
        (bankTrialRenewalIndexPowerDominatesPopulation n hn))
  have hcut :
      1024 * 2 ^ (compileAdvice (ceilLogTwo n)).K *
          ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n) ≤
        bankTrialRenewalWonCutoffThreshold
          n (ceilLogTwo n) := by
    unfold bankTrialRenewalWonCutoffThreshold
    exact Nat.le_max_right _ _
  have hscaled := Nat.mul_le_mul_left 1024 hcut
  have hPB :
      2 ^ (compileAdvice (ceilLogTwo n)).K *
        ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n) ≤ L := by
    calc
      _ ≤ 1024 * (1024 *
        (2 ^ (compileAdvice (ceilLogTwo n)).K *
          ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n))) :=
            bankTrialRenewalIndexStretchBound _
      _ = 1024 * (1024 *
            2 ^ (compileAdvice (ceilLogTwo n)).K *
            ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n)) := by
              simp only [Nat.mul_assoc]
      _ ≤ 1024 * bankTrialRenewalWonCutoffThreshold
          n (ceilLogTwo n) := hscaled
      _ ≤ L := hL
  exact bankTrialRenewalIndexGapOpaque
    ((W - n * C) /
      (n * bankTrialRenewalIndexStepCharge (ceilLogTwo n)))
    L (2 ^ (compileAdvice (ceilLogTwo n)).K)
    ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n)
    hPB hHbound

/-- Elementary monotonicity of quotient floors without Nat.find. -/
private theorem bankTrialRenewalIndexFloorLower
    (a f H : Nat)
    (hf : 0 < f)
    (h : H * f ≤ a) :
    H ≤ a / f := by
  by_cases hc : H ≤ a / f
  · exact hc
  · have hnext : a / f + 1 ≤ H := by omega
    have hm := Nat.mul_le_mul_right f hnext
    have hdiv : a % f + (a / f) * f = a := by
      simpa only [Nat.mul_comm] using Nat.mod_add_div a f
    have hrem : a % f < f := Nat.mod_lt a hf
    have hupper : a < (a / f + 1) * f := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    omega

private theorem bankTrialRenewalIndexCostComplement
    (W C G F : Nat) (hG : G ≤ C) :
    ∀ H, C + H * F ≤ W →
      bankTrialSuccessStageIndexSum (fun j => G + j * F) H +
        bankTrialSuccessStageIndexSum
          (fun j => W - C - j * F) H ≤ W * H := by
  intro H
  induction H with
  | zero =>
      intro _
      exact Nat.zero_le _
  | succ k ih =>
      intro h
      have hstep := Nat.mul_le_mul_right F (Nat.le_succ k)
      have hsF : (k + 1) * F = k * F + F := Nat.succ_mul k F
      have hsF' : k.succ * F = k * F + F := Nat.succ_mul k F
      have hk : C + k * F ≤ W := by omega
      have hitem : G + k * F + (W - C - k * F) ≤ W := by
        omega
      have hprev := ih hk
      change
        (bankTrialSuccessStageIndexSum (fun j => G + j * F) k +
          (G + k * F)) +
        (bankTrialSuccessStageIndexSum
          (fun j => W - C - j * F) k +
          (W - C - k * F)) ≤ W * (k + 1)
      rw [Nat.mul_add, Nat.mul_one]
      omega

private theorem bankTrialRenewalIndexConstantStageSum
    (a H : Nat) :
    bankTrialSuccessStageIndexSum (fun _ => a) H = H * a := by
  induction H with
  | zero => simp [bankTrialSuccessStageIndexSum]
  | succ k ih =>
      change bankTrialSuccessStageIndexSum (fun _ => a) k + a =
        (k + 1) * a
      rw [ih, Nat.add_mul]
      simp

/-- A geometric point, normalized with an opaque denominator;
only small fixed multipliers are evaluated. -/
private theorem bankTrialRenewalIndexWeightedPoint
    (lo den L P H j : Nat)
    (hden : den = 1024 * L * P)
    (hj : j < H)
    (hgeo : 1023 * den ^ j ≤ 1024 * lo ^ j) :
    1046529 * den ^ H ≤
      1048576 * P *
        (lo ^ j * (1023 * L) * den ^ (H - (j + 1))) := by
  have hsum : j + (H - (j + 1)) + 1 = H := by omega
  have hpower :
      den ^ j * den ^ (H - (j + 1)) * den = den ^ H := by
    calc
      _ = den ^ (j + (H - (j + 1))) * den := by
        rw [Nat.pow_add]
      _ = den ^ (j + (H - (j + 1)) + 1) := by
        rw [Nat.pow_succ]
      _ = den ^ H := by rw [hsum]
  have hfac :
      1024 * (1023 * den) =
        1048576 * P * (1023 * L) := by
    rw [hden, show (1048576 : Nat) = 1024 * 1024 by decide]
    simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have hscaled := Nat.mul_le_mul_left
    (1023 * den * den ^ (H - (j + 1))) hgeo
  calc
    1046529 * den ^ H =
        (1023 * den * den ^ (H - (j + 1))) *
          (1023 * den ^ j) := by
      rw [show (1046529 : Nat) = 1023 * 1023 by decide,
        ← hpower]
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    _ ≤ (1023 * den * den ^ (H - (j + 1))) *
          (1024 * lo ^ j) := hscaled
    _ = (1024 * (1023 * den)) *
          (lo ^ j * den ^ (H - (j + 1))) := by
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    _ = (1048576 * P * (1023 * L)) *
          (lo ^ j * den ^ (H - (j + 1))) := by rw [hfac]
    _ = 1048576 * P *
          (lo ^ j * (1023 * L) * den ^ (H - (j + 1))) := by
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

private theorem bankTrialRenewalIndexWeightedSum
    (lo den L P H : Nat)
    (hden : den = 1024 * L * P)
    (hgeo : ∀ j, j < H →
      1023 * den ^ j ≤ 1024 * lo ^ j) :
    1046529 * H * den ^ H ≤
      1048576 * P *
        bankTrialSuccessStageIndexSum (fun j =>
          lo ^ j * (1023 * L) *
            den ^ (H - (j + 1))) H := by
  have hs := bankTrialRenewalStageIndexMonoBelow
    (fun _ => 1046529 * den ^ H)
    (fun j => 1048576 * P *
      (lo ^ j * (1023 * L) * den ^ (H - (j + 1))))
    H (by
      intro j hj
      exact bankTrialRenewalIndexWeightedPoint
        lo den L P H j hden hj (hgeo j hj))
  rw [bankTrialRenewalIndexConstantStageSum] at hs
  rw [bankTrialRenewalStageScale] at hs
  simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    using hs

private theorem bankTrialRenewalIndexMassLinear
    (W P N M H cost lo den L : Nat)
    (hdenpos : 0 < den)
    (hweighted :
      1046529 * H * den ^ H ≤
        1048576 * P *
          bankTrialSuccessStageIndexSum (fun j =>
            lo ^ j * (1023 * L) *
              den ^ (H - (j + 1))) H)
    (hwin :
      W * P * N *
        bankTrialSuccessStageIndexSum (fun j =>
          lo ^ j * (1023 * L) *
            den ^ (H - (j + 1))) H ≤
      den ^ H * (W * P * M + N * cost)) :
    1046529 * (W * H * N) ≤
      1048576 * (W * P * M + N * cost) := by
  have hdpos : 0 < den ^ H := Nat.pow_pos hdenpos
  have hh :
      den ^ H * (1046529 * (W * H * N)) ≤
      den ^ H * (1048576 * (W * P * M + N * cost)) := by
    calc
      den ^ H * (1046529 * (W * H * N)) =
          (W * N) * (1046529 * H * den ^ H) := by
        simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      _ ≤ (W * N) * (1048576 * P *
          bankTrialSuccessStageIndexSum (fun j =>
            lo ^ j * (1023 * L) *
              den ^ (H - (j + 1))) H) :=
        Nat.mul_le_mul_left _ hweighted
      _ = 1048576 * (W * P * N *
          bankTrialSuccessStageIndexSum (fun j =>
            lo ^ j * (1023 * L) *
              den ^ (H - (j + 1))) H) := by
        simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      _ ≤ 1048576 * (den ^ H *
            (W * P * M + N * cost)) :=
        Nat.mul_le_mul_left 1048576 hwin
      _ = den ^ H *
            (1048576 * (W * P * M + N * cost)) := by
        simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  exact Nat.le_of_mul_le_mul_left hh hdpos

/-- The 491/1000 sum reserve pays all 2047/1048576
geometric thinning. The fixed arithmetic margin is 4606. -/
private theorem bankTrialRenewalIndexMassPayoff
    (W F H P N M cost s : Nat)
    (hW : 0 < W)
    (hFH : F * H ≤ W)
    (hS : 491 * W * W ≤ 1000 * F * s)
    (hcost : cost + s ≤ W * H)
    (hmass :
      1046529 * (W * H * N) ≤
        1048576 * (W * P * M + N * cost)) :
    51279921 * W * N ≤ 104857600 * F * P * M := by
  have hc := Nat.mul_le_mul_left N hcost
  have hcscaled : N * cost + N * s ≤ W * H * N := by
    simpa only [Nat.mul_add, Nat.mul_assoc,
      Nat.mul_left_comm, Nat.mul_comm] using hc
  have hbridge :
      1048576 * (N * s) ≤
        1048576 * (W * P * M) + 2047 * (W * H * N) := by
    have hcc := Nat.mul_le_mul_left 1048576 hcscaled
    simp only [Nat.mul_add] at hcc hmass
    omega
  have hgapBound :
      (1000 * F) * (2047 * (W * H * N)) ≤
        1000 * 2047 * (W * W * N) := by
    have hs := Nat.mul_le_mul_left (1000 * 2047 * W * N) hFH
    simpa only [Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm] using hs
  have hpaid :
      491 * 1048576 * (W * W * N) ≤
        1000 * 1048576 * (W * F * P * M) +
          1000 * 2047 * (W * W * N) := by
    calc
      491 * 1048576 * (W * W * N) ≤
          (1000 * F) * (1048576 * (N * s)) := by
        have hs := Nat.mul_le_mul_left (1048576 * N) hS
        simpa only [Nat.mul_assoc, Nat.mul_left_comm,
          Nat.mul_comm] using hs
      _ ≤ (1000 * F) *
            (1048576 * (W * P * M) +
              2047 * (W * H * N)) :=
        Nat.mul_le_mul_left _ hbridge
      _ = 1000 * 1048576 * (W * F * P * M) +
            (1000 * F) * (2047 * (W * H * N)) := by
        simp only [Nat.mul_add, Nat.mul_assoc,
          Nat.mul_left_comm, Nat.mul_comm]
      _ ≤ 1000 * 1048576 * (W * F * P * M) +
            1000 * 2047 * (W * W * N) :=
        Nat.add_le_add_left hgapBound _
  have hcoef :
      490 * 1046529 * (W * W * N) ≤
        1000 * 1048576 * (W * F * P * M) := by
    have hstrict :
        490 * 1046529 + 1000 * 2047 ≤
          491 * 1048576 := by decide
    have hstrictScaled := Nat.mul_le_mul_right
      (W * W * N) hstrict
    have hstrictNormal :
        (490 * 1046529) * (W * W * N) +
          (1000 * 2047) * (W * W * N) ≤
        (491 * 1048576) * (W * W * N) := by
      simpa only [Nat.add_mul, Nat.mul_assoc] using hstrictScaled
    omega
  have hcancel :
      490 * 1046529 * (W * N) ≤
        1000 * 1048576 * (F * P * M) := by
    have hh :
        W * (490 * 1046529 * (W * N)) ≤
          W * (1000 * 1048576 * (F * P * M)) := by
      simpa only [Nat.mul_assoc, Nat.mul_left_comm,
        Nat.mul_comm] using hcoef
    exact Nat.le_of_mul_le_mul_left hh hW
  have hten :
      10 * (49 * 1046529 * W * N) ≤
        10 * (100 * 1048576 * F * P * M) := by
    have e1 : 10 * (49 * 1046529 * W * N) = 490 * 1046529 * (W * N) := by
      rw [show (490 : Nat) = 10 * 49 by decide]
      ac_rfl
    have e2 : 10 * (100 * 1048576 * F * P * M) =
        1000 * 1048576 * (F * P * M) := by
      rw [show (1000 : Nat) = 10 * 100 by decide]
      ac_rfl
    rw [e1, e2]
    exact hcancel
  have hfinal := Nat.le_of_mul_le_mul_left hten
    (by decide : 0 < (10 : Nat))
  have hpaper :
      49 * 1023 ^ 2 * W * N ≤
        100 * 1024 ^ 2 * F * 1 * P * M := by
    simpa only [
      show (1023 ^ 2 : Nat) = 1046529 by decide,
      show (1024 ^ 2 : Nat) = 1048576 by decide,
      Nat.mul_one, Nat.mul_assoc] using hfinal
  have hcleared :=
    (bankTrialRenewalIndexThetaSquareClearing W N F 1 P M).mp
      hpaper
  simpa only [Nat.mul_one, Nat.mul_assoc] using hcleared

/-- Pure Nat reduction with exactly the AnyH window sandwich.
Every hypothesis will be supplied by the compiled window below. -/
private theorem bankTrialRenewalIndexVariableMassArithmetic
    (W F H P N M C G L lo den : Nat)
    (hW : 0 < W)
    (hF : 0 < F)
    (hfloor : H = (W - C) / F)
    (hratio : 255 * C ≤ 2 * W)
    (hlarge : 22517 ≤ H)
    (hG : G ≤ C)
    (hden : den = 1024 * L * P)
    (hdenpos : 0 < den)
    (hgeo : ∀ j, j < H →
      1023 * den ^ j ≤ 1024 * lo ^ j)
    (hwin :
      W * P * N *
        bankTrialSuccessStageIndexSum (fun j =>
          lo ^ j * (1023 * L) *
            den ^ (H - (j + 1))) H ≤
      den ^ H *
        (W * P * M + N *
          bankTrialSuccessStageIndexSum
            (fun j => G + j * F) H)) :
    51279921 * W * N ≤ 104857600 * F * P * M := by
  have hCle : C ≤ W := by omega
  have hdiv : (W - C) % F + ((W - C) / F) * F =
      W - C := by
    simpa only [Nat.mul_comm] using Nat.mod_add_div (W - C) F
  have hHF : H * F ≤ W - C := by
    rw [hfloor]
    omega
  have hCbudget : C + H * F ≤ W := by
    have hsub := Nat.sub_add_cancel hCle
    omega
  have hFH : F * H ≤ W := by
    calc
      F * H = H * F := Nat.mul_comm _ _
      _ ≤ W - C := hHF
      _ ≤ W := Nat.sub_le _ _
  have hsum := bankTrialRenewalIndexSumStrong
    W C F H hF hratio hfloor hlarge
  have hcomp := bankTrialRenewalIndexCostComplement
    W C G F hG H hCbudget
  have hweighted := bankTrialRenewalIndexWeightedSum
    lo den L P H hden hgeo
  have hlin := bankTrialRenewalIndexMassLinear
    W P N M H
    (bankTrialSuccessStageIndexSum (fun j => G + j * F) H)
    lo den L hdenpos hweighted hwin
  exact bankTrialRenewalIndexMassPayoff
    W F H P N M
    (bankTrialSuccessStageIndexSum (fun j => G + j * F) H)
    (bankTrialSuccessStageIndexSum (fun j => W - C - j * F) H)
    hW hFH hsum hcomp hlin

/-- Final variable-index C.16 bound with the actual compiled
cold charge, K, radius, and W=(R*n)/8. The arbitrary-horizon
condition H_* * L <= T is exactly AnyH's finite-word requirement.
No extra probabilistic or geometric premise is introduced. -/
theorem bankTrialRenewalIndexSuccessMassLower
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (hlarge :
      2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice (ceilLogTwo n)).b)
    (hclean : BankTrialLocalClean (ceilLogTwo n) S)
    (R L T W : Nat)
    (hradius : (256 * R) ^ 2 ≤ n ∧
      n < (256 * (R + 1)) ^ 2)
    (hW : W = R * n / 8)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold
      n (ceilLogTwo n) ≤ L)
    (hwindow : W ≤ T)
    (hbudget :
      bankTrialRenewalIndexWindowCount
        n (ceilLogTwo n) W * L ≤ T) :
    51279921 * W * n ^ T ≤
      104857600 * (8 * (compileAdvice (ceilLogTwo n)).b + 13) *
        n * 2 ^ (compileAdvice (ceilLogTwo n)).K *
        bankTrialRenewalSuccessMass ring root S T W := by
  have hq : 3 ≤ ceilLogTwo n := by
    have hspec := (ceilLogTwo_spec n (by omega)).2
    by_cases hc : ceilLogTwo n ≤ 2
    · have hp := Nat.pow_le_pow_right
        (by decide : 0 < (2 : Nat)) hc
      have hfour : (2 : Nat) ^ 2 = 4 := by decide
      omega
    · omega
  have hpositive :
      0 < (compileAdvice (ceilLogTwo n)).K := by
    change 0 < 2 * ceilLogTwo n +
      productionKappa (ceilLogTwo n)
    omega
  have hK :
      (compileAdvice (ceilLogTwo n)).K <
        2 ^ (compileAdvice (ceilLogTwo n)).b :=
    Nat.lt_trans (Nat.lt_succ_self _)
      (compileAdvice_K_lt_two_pow_b (ceilLogTwo n) hq)
  have hquota := bankTrialRenewalIndexCompiledQuotas
    n R W hn hsmall hradius hW
  have hf :
      0 < n * bankTrialRenewalIndexStepCharge
        (ceilLogTwo n) := by
    apply Nat.mul_pos (by omega)
    unfold bankTrialRenewalIndexStepCharge
    omega
  have hquotaExpanded :
      n * bankTrialRenewalIndexColdCharge (ceilLogTwo n) +
        22517 * (n * bankTrialRenewalIndexStepCharge
          (ceilLogTwo n)) ≤ W := by
    simpa only [Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm] using hquota.2
  have hWpos : 0 < W := by
    have ht : 0 < 22517 *
        (n * bankTrialRenewalIndexStepCharge (ceilLogTwo n)) :=
      Nat.mul_pos (by decide) hf
    omega
  have hCle :
      n * bankTrialRenewalIndexColdCharge (ceilLogTwo n) ≤ W := by
    omega
  have hFloorBudget :
      22517 * (n * bankTrialRenewalIndexStepCharge
        (ceilLogTwo n)) ≤
      W - n * bankTrialRenewalIndexColdCharge
        (ceilLogTwo n) := by
    have hsub := Nat.sub_add_cancel hCle
    omega
  have hFloor :
      22517 ≤ bankTrialRenewalIndexWindowCount
        n (ceilLogTwo n) W := by
    unfold bankTrialRenewalIndexWindowCount
    exact bankTrialRenewalIndexFloorLower
      (W - n * bankTrialRenewalIndexColdCharge (ceilLogTwo n))
      (n * bankTrialRenewalIndexStepCharge (ceilLogTwo n))
      22517 hf hFloorBudget
  have hcover :
      bankTrialRenewalIndexZeroCharge (ceilLogTwo n) ≤
        bankTrialRenewalIndexColdCharge (ceilLogTwo n) := by
    unfold bankTrialRenewalIndexColdCharge
    omega
  have hcoverScaled :=
    Nat.mul_le_mul_left n hcover
  have hPpos :
      0 < 2 ^ (compileAdvice (ceilLogTwo n)).K :=
    Nat.two_pow_pos _
  have hBasePos :
      0 < 1024 * 2 ^ (compileAdvice (ceilLogTwo n)).K *
        ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n) :=
    Nat.mul_pos (Nat.mul_pos (by decide) hPpos)
      (Nat.mul_pos (by omega) (by omega))
  have hCutPos :
      0 < bankTrialRenewalWonCutoffThreshold
        n (ceilLogTwo n) := by
    have hbase :
        1024 * 2 ^ (compileAdvice (ceilLogTwo n)).K *
          ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n) ≤
        bankTrialRenewalWonCutoffThreshold
          n (ceilLogTwo n) := by
      unfold bankTrialRenewalWonCutoffThreshold
      exact Nat.le_max_right _ _
    exact Nat.lt_of_lt_of_le hBasePos hbase
  have hLpos : 0 < L := by
    have hm := Nat.mul_pos
      (by decide : 0 < (1024 : Nat)) hCutPos
    omega
  have hdenpos :
      0 < 1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K) :=
    Nat.mul_pos (by decide) (Nat.mul_pos hLpos hPpos)
  have hGap := bankTrialRenewalIndexCompiledGeometricBudget
    n R W
    (bankTrialRenewalIndexColdCharge (ceilLogTwo n))
    L hn hradius.1
    (bankTrialRenewalIndexConsumerWindowCap n R W hW) hL
  have hGapActual :
      bankTrialRenewalIndexWindowCount n (ceilLogTwo n) W *
        (1024 * (L + 2 ^ (compileAdvice (ceilLogTwo n)).K *
          ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n))) ≤
        (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K)) /
          1024 := by
    simpa only [bankTrialRenewalIndexWindowCount,
      bankTrialRenewalIndexStepCharge] using hGap
  have hDenIdentity := bankTrialRenewalIndexLostDenIdentity
    n (ceilLogTwo n) L hpositive hL
  have hgeo (j : Nat)
      (hj : j < bankTrialRenewalIndexWindowCount
        n (ceilLogTwo n) W) :
      1023 *
        (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K)) ^ j ≤
      1024 *
        (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K -
          L - 2 ^ (compileAdvice (ceilLogTwo n)).K *
            ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n))) ^ j := by
    exact bankTrialRenewalIndexBernoulli
      (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K -
        L - 2 ^ (compileAdvice (ceilLogTwo n)).K *
          ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n)))
      (1024 * (L + 2 ^ (compileAdvice (ceilLogTwo n)).K *
        ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n)))
      (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K))
      (bankTrialRenewalIndexWindowCount n (ceilLogTwo n) W)
      j hDenIdentity hGapActual hj
  have hwin := bankTrialRenewalIndexClearedCleanWindowAnyH
    ring root (by omega) hsmall hw hlarge hpositive hK
    S hclean L
    (bankTrialRenewalIndexWindowCount n (ceilLogTwo n) W)
    T W hL hwindow hbudget
  have hwinOpaque :
      W * (2 ^ (compileAdvice (ceilLogTwo n)).K) * n ^ T *
        bankTrialSuccessStageIndexSum (fun j =>
          (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K -
            L - 2 ^ (compileAdvice (ceilLogTwo n)).K *
              ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n))) ^ j *
          (1023 * L) *
          (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K)) ^
            (bankTrialRenewalIndexWindowCount
              n (ceilLogTwo n) W - (j + 1)))
          (bankTrialRenewalIndexWindowCount n (ceilLogTwo n) W) ≤
      (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K)) ^
        (bankTrialRenewalIndexWindowCount n (ceilLogTwo n) W) *
        (W * (2 ^ (compileAdvice (ceilLogTwo n)).K) *
          bankTrialRenewalSuccessMass ring root S T W +
          n ^ T *
            bankTrialSuccessStageIndexSum (fun j =>
              n * bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
              j * (n * bankTrialRenewalIndexStepCharge
                (ceilLogTwo n)))
              (bankTrialRenewalIndexWindowCount
                n (ceilLogTwo n) W)) := by
    simpa only [bankTrialRenewalIndexZeroCharge,
      bankTrialRenewalIndexStepCharge, Nat.mul_add,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hwin
  have hDenShape :
      1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K) =
        1024 * L * 2 ^ (compileAdvice (ceilLogTwo n)).K := by
    simp only [Nat.mul_assoc]
  have hresult := bankTrialRenewalIndexVariableMassArithmetic
    W (n * bankTrialRenewalIndexStepCharge (ceilLogTwo n))
    (bankTrialRenewalIndexWindowCount n (ceilLogTwo n) W)
    (2 ^ (compileAdvice (ceilLogTwo n)).K)
    (n ^ T)
    (bankTrialRenewalSuccessMass ring root S T W)
    (n * bankTrialRenewalIndexColdCharge (ceilLogTwo n))
    (n * bankTrialRenewalIndexZeroCharge (ceilLogTwo n))
    L
    (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K -
      L - 2 ^ (compileAdvice (ceilLogTwo n)).K *
        ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n)))
    (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K))
    hWpos hf rfl hquota.1 hFloor
    hcoverScaled hDenShape hdenpos hgeo hwinOpaque
  simpa only [bankTrialRenewalIndexStepCharge,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hresult

end L3


namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
Physical cold stop -> clean-reference custody and exact
finite first-stop accounting.

This block does NOT assert an unconditional arbitrary-cold-start
success lower bound. The cold observer has three absorbing outcomes
(clean, grant, defect), and its stopped cost alone gives no
per-suffix success bound after a random cold duration.
-/

/-- A physical CLEAN state projects to a Clean local BANK reference.
Unlike a physical-success coupling, this structural fact does not
need a grant-free hypothesis: the reference's success latch is false
by construction. -/
theorem bankTrialRenewalColdCleanReference {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (D : Counter.Config q n)
    (hc : Counter.ResetClockBankClean ring D root) :
    BankTrialLocalClean q
      (GrantBankReference.bankLocalReferenceStart ring root D) := by
  unfold BankTrialLocalClean
  refine ⟨rfl, ?_, ?_, ?_⟩
  · change (D root).mode = .ARMED
    exact hc.2.1
  · intro j hj hbound
    change (D (Counter.site ring root j)).bit = false ∧
      (D (Counter.site ring root j)).tok = .E
    exact hc.2.2 j hj hbound
  · intro j hj
    change (D (Counter.site ring root j)).lease.val ≤
      (compileAdvice q).bankLeaseCap
    have hlt :
        (D (Counter.site ring root j)).lease.val <
          (compileAdvice q).bankLeaseCap + 1 :=
      (D (Counter.site ring root j)).lease.isLt
    omega

/-- A sound CLEAN-labelled cold terminal is not arbitrary forged
private scratch: its physical D satisfies the existing CLEAN
predicate, hence its reference image satisfies BankTrialLocalClean. -/
theorem bankTrialRenewalColdSoundCleanReference {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (D : Counter.Config q n)
    (hsound : Counter.resetColdObserverSound ring root
      ((.inr (.inr (D, .clean)) :
        Counter.ResetClockBankColdState (q := q) ring root))) :
    BankTrialLocalClean q
      (GrantBankReference.bankLocalReferenceStart ring root D) := by
  change Counter.ResetClockBankClean ring D root at hsound
  exact bankTrialRenewalColdCleanReference ring root D hsound

/-- A cold terminal is exactly a stopped outcome, never a
fresh live local trial. All three stop reasons remain distinct. -/
theorem bankTrialRenewalColdTerminalShape {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : Counter.ResetClockBankColdState (q := q) ring root)
    (ht : Counter.resetClockBankColdTerminal ring root z) :
    ∃ D : Counter.Config q n, ∃ reason : Counter.ResetClockBankStop,
      z = .inr (.inr (D, reason)) := by
  cases z with
  | inl x =>
      exact False.elim ht
  | inr y =>
      cases y with
      | inl a =>
          exact False.elim ht
      | inr out =>
          exact ⟨out.1, out.2, rfl⟩

/-- A sound terminal has one of the three physical outcomes,
including the OLD-edge defect witness. This is the exact
terminal-custody lemma already established by CounterCold. -/
theorem bankTrialRenewalColdTerminalPhysicalCases {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (z : Counter.ResetClockBankColdState (q := q) ring root)
    (hsound : Counter.resetColdObserverSound ring root z)
    (ht : Counter.resetClockBankColdTerminal ring root z) :
    Counter.ResetClockBankClean ring
      (Counter.resetClockBankColdConfig ring root z) root ∨
    (∃ s : Fin n,
      ((Counter.resetClockBankColdConfig ring root z) s).grant =
        true) ∨
    ∃ Cbefore : Counter.Config q n, ∃ e : Fin n,
      Counter.ResetClockBankDefectEntry ring Cbefore root e ∧
        Counter.resetClockBankColdConfig ring root z =
          (protocol q).step ring Cbefore e := by
  exact Counter.resetColdTerminalPhysicalExit ring root z hsound ht

/-- The Boolean stopping predicate for the genuine cold observer.
The prefix is a bookkeeping argument only; the terminal test is
on the observer's terminal constructor. -/
def bankTrialRenewalColdStop {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (_pre : List (Fin n))
    (z : Counter.ResetClockBankColdState (q := q) ring root) :
    Bool :=
  match z with
  | .inr (.inr _) => true
  | _ => false

theorem bankTrialRenewalColdStopCorrect {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (pre : List (Fin n))
    (z : Counter.ResetClockBankColdState (q := q) ring root) :
    bankTrialRenewalColdStop ring root pre z = true ↔
      Counter.resetClockBankColdTerminal ring root z := by
  cases z with
  | inl x =>
      simp [bankTrialRenewalColdStop,
        Counter.resetClockBankColdTerminal]
  | inr y =>
      cases y with
      | inl a =>
          simp [bankTrialRenewalColdStop,
            Counter.resetClockBankColdTerminal,
            Counter.resetClockBankRenewalTarget]
      | inr out =>
          simp [bankTrialRenewalColdStop,
            Counter.resetClockBankColdTerminal,
            Counter.resetClockBankRenewalTarget]

/-- The exact first-stop cylinder decomposition for the cold
observer on the ORIGINAL Fin n scheduler. It does not assume
independence of the cold stopping time or termination by W. -/
theorem bankTrialRenewalColdFirstStopFactor
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (F : List (Fin n) →
      Counter.ResetClockBankColdState
        (q := ceilLogTwo n) ring root →
      List (Fin n) → Nat)
    (T : Nat) :
    Prob.scheduleSum n T (fun word =>
      bankTrialSuccessNatStoppedWord
        (Counter.resetClockBankColdNext ring root hsp)
        (bankTrialRenewalColdStop ring root)
        (fun cut z _ suffix => F cut z suffix)
        T [] (Counter.resetClockBankColdStart ring root x) word) =
    ((Prob.firstStoppedPrefixes
      (Counter.resetClockBankColdNext ring root hsp)
      (bankTrialRenewalColdStop ring root)
      T [] (Counter.resetClockBankColdStart ring root x)).map
      (fun cut =>
        Prob.scheduleSum n (T - cut.length) (fun suffix =>
          F cut
            (Prob.stoppedTapeRun
              (Counter.resetClockBankColdNext ring root hsp)
              cut (Counter.resetClockBankColdStart ring root x))
            suffix))).sum := by
  exact bankTrialSuccessNatStoppedFactorization
    (Counter.resetClockBankColdNext ring root hsp)
    (bankTrialRenewalColdStop ring root)
    (fun cut z _ suffix => F cut z suffix)
    (Counter.resetClockBankColdStart ring root x) T

/-- This is ONLY a cold-stopped comparison weight, not the real
arbitrary-start success event. Grants by W count immediately;
CLEAN cuts use the projected reference's remaining suffix window;
defects count zero. A CLEAN outcome whose root is already granted
also counts immediately. -/
noncomputable def bankTrialRenewalColdProxyWeight {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (W : Nat) (cut : List (Fin n))
    (z : Counter.ResetClockBankColdState (q := q) ring root)
    (suffix : List (Fin n)) : Nat :=
  if cut.length ≤ W then
    match z with
    | .inr (.inr (D, .grant)) => 1
    | .inr (.inr (D, .clean)) =>
        if (D root).grant = true then 1
        else Prob.indicator
          (bankTrialRenewalSuccessBy ring root
            (GrantBankReference.bankLocalReferenceStart ring root D)
            (W - cut.length) suffix)
    | _ => 0
  else 0

theorem bankTrialRenewalColdProxyDefectZero {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (D : Counter.Config q n)
    (W : Nat) (cut suffix : List (Fin n)) :
    bankTrialRenewalColdProxyWeight ring root W cut
      ((.inr (.inr (D, .defect)) :
        Counter.ResetClockBankColdState (q := q) ring root))
      suffix = 0 := by
  unfold bankTrialRenewalColdProxyWeight
  split <;> rfl

/-- The first-stop proxy is a concrete finite-word numerator.
It still needs a physical-success comparison and a cold-time
weighted lower bound before it can yield the paper's probability. -/
noncomputable def bankTrialRenewalColdProxyMass {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T W : Nat) : Nat :=
  Prob.scheduleSum n T (fun word =>
    bankTrialSuccessNatStoppedWord
      (Counter.resetClockBankColdNext ring root hsp)
      (bankTrialRenewalColdStop ring root)
      (fun cut z _ suffix =>
        bankTrialRenewalColdProxyWeight ring root W cut z suffix)
      T [] (Counter.resetClockBankColdStart ring root x) word)

/-- Exact cold-first mass factorization with three distinguishable
outcomes. This equality is independent of the two cost bounds. -/
theorem bankTrialRenewalColdProxyFactor {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T W : Nat) :
    bankTrialRenewalColdProxyMass ring root hsp x T W =
    ((Prob.firstStoppedPrefixes
      (Counter.resetClockBankColdNext ring root hsp)
      (bankTrialRenewalColdStop ring root)
      T [] (Counter.resetClockBankColdStart ring root x)).map
      (fun cut =>
        Prob.scheduleSum n (T - cut.length) (fun suffix =>
          bankTrialRenewalColdProxyWeight ring root W cut
            (Prob.stoppedTapeRun
              (Counter.resetClockBankColdNext ring root hsp)
              cut (Counter.resetClockBankColdStart ring root x))
            suffix))).sum := by
  unfold bankTrialRenewalColdProxyMass
  exact bankTrialRenewalColdFirstStopFactor
    ring root hsp x
    (fun cut z suffix =>
      bankTrialRenewalColdProxyWeight ring root W cut z suffix) T

/-- The actual carrier's C.3 and C.2 stopped costs are both
available with no new drift-potential hypotheses. -/
theorem bankTrialRenewalColdCostBundle {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root) (T : Nat) :
    costNumerator (Counter.resetClockBankColdNext ring root hsp)
      (Counter.resetClockBankColdPhaseTarget ring root)
      (Counter.resetClockBankColdStart ring root x) T ≤
      n ^ T *
        ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
          (compileAdvice (ceilLogTwo n)).b + 7) * n) ∧
    costNumerator (Counter.resetClockBankColdNext ring root hsp)
      (Counter.resetClockBankColdTerminal ring root)
      (Counter.resetClockBankColdStart ring root x) T ≤
      n ^ T *
        ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
          5 * (compileAdvice (ceilLogTwo n)).b + 13) * n) := by
  exact ⟨Counter.resetClockBankColdFirstCost ring root hsp x T,
    Counter.resetClockBankColdStoppedCost ring root hsp x T⟩

/-- On a SOUND cold CLEAN terminal the Clean lower bound
is instantiated, not assumed. This is a bound for a fresh
full window after the handoff, not yet for the smaller
remaining window W - cut.length. -/
theorem bankTrialRenewalColdSoundCleanMassLower
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (hlarge :
      2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n)
    (D : Counter.Config (ceilLogTwo n) n)
    (hsound : Counter.resetColdObserverSound ring root
      ((.inr (.inr (D, .clean)) :
        Counter.ResetClockBankColdState
          (q := ceilLogTwo n) ring root)))
    (R L T W : Nat)
    (hradius : (256 * R) ^ 2 ≤ n ∧
      n < (256 * (R + 1)) ^ 2)
    (hW : W = R * n / 8)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold
      n (ceilLogTwo n) ≤ L)
    (hwindow : W ≤ T)
    (hbudget :
      bankTrialRenewalIndexWindowCount
        n (ceilLogTwo n) W * L ≤ T) :
    51279921 * W * n ^ T ≤
      104857600 *
        (8 * (compileAdvice (ceilLogTwo n)).b + 13) * n *
        2 ^ (compileAdvice (ceilLogTwo n)).K *
        bankTrialRenewalSuccessMass ring root
          (GrantBankReference.bankLocalReferenceStart ring root D)
          T W := by
  exact bankTrialRenewalIndexSuccessMassLower
    ring root hn hsp hw hlarge
    (GrantBankReference.bankLocalReferenceStart ring root D)
    (bankTrialRenewalColdSoundCleanReference ring root D hsound)
    R L T W hradius hW hL hwindow hbudget

end L3


namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
Cold-segment certificates.

These lemmas deliberately do not assert
bankTrialRenewalColdSuccessMassLower: the current physical cold
carrier lacks the paper's buffered, correct-exterior-role predicate,
and the first-stop/C.16 conditional-cost transfer is not yet proved.
The twenty-site witness below is for the literal Lean ColdCarrier
(Complete and GrantFree), NOT for the stronger paper selection.
-/

/-- A non-RESET physical cold carrier starts on the actual cold side,
not in the pre-injected renewal observer. -/
theorem bankTrialRenewalColdStartNonReset {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : Counter.ResetClockBankColdCarrier (q := q) ring root)
    (hm : (x.val root).mode ≠ .RESET) :
    Counter.resetClockBankColdStart ring root x = .inl x := by
  unfold Counter.resetClockBankColdStart
  simp only [Counter.resetClockBankColdLift, dif_neg hm]

/-- Every OLD supported defect on the initial cold physical edge
immediately produces the actual .defect terminal. No extra scheduler
letter or comparison-only transition is inserted. -/
theorem bankTrialRenewalColdImmediateDefect {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier (q := q) ring root)
    (e : Fin n)
    (hm : (x.val root).mode ≠ .RESET)
    (hd : Counter.ResetClockBankDefectEntry ring x.val root e) :
    Counter.resetClockBankColdNext ring root hsp
      (Counter.resetClockBankColdStart ring root x) e =
        .inr (.inr (((protocol q).step ring x.val e), .defect)) := by
  rw [bankTrialRenewalColdStartNonReset ring root x hm]
  exact Counter.resetClockBankColdNextDefect ring root hsp x e hd

/-- A no-defect OLD edge cannot acquire a .defect label merely
from the next-state grant or RESET tests. -/
theorem bankTrialRenewalColdImmediateNoDefect {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier (q := q) ring root)
    (e : Fin n)
    (hm : (x.val root).mode ≠ .RESET)
    (hd : ¬ Counter.ResetClockBankDefectEntry ring x.val root e) :
    ∀ D : Counter.Config q n,
      Counter.resetClockBankColdNext ring root hsp
        (Counter.resetClockBankColdStart ring root x) e ≠
          .inr (.inr (D, .defect)) := by
  intro D hbad
  rw [bankTrialRenewalColdStartNonReset ring root x hm] at hbad
  by_cases hg :
      Counter.GrantFree ((protocol q).step ring x.val e) root
  · rw [Counter.resetClockBankColdNextContinue
        ring root hsp x e hd hg] at hbad
    unfold Counter.resetClockBankColdLift at hbad
    split at hbad <;> cases hbad
  · rw [Counter.resetClockBankColdNextGrant
        ring root hsp x e hd hg] at hbad
    cases hbad

/-- One-step form of the frozen-role assertion: an OLD good pair
together with physical preservation of protected PACK roles excludes
the cold defect guard. This is not an invariant assertion for all
future physical scheduler letters. -/
theorem bankTrialRenewalColdFrozenGoodEdge {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier (q := q) ring root)
    (e : Fin n)
    (hm : (x.val root).mode ≠ .RESET)
    (hgood : goodPair (compileAdvice q).b
      (x.val e).pack
      (x.val (ring.rightNeighbor e)).pack = true)
    (hstable : Counter.RoleStableEdge ring root x.val e) :
    ∀ D : Counter.Config q n,
      Counter.resetClockBankColdNext ring root hsp
        (Counter.resetClockBankColdStart ring root x) e ≠
          .inr (.inr (D, .defect)) := by
  have hno : ¬ Counter.ResetClockBankDefectEntry
      ring x.val root e := by
    intro hbad
    rcases hbad.2 with hp | hr
    · have hc := hgood
      rw [hp] at hc
      cases hc
    · exact hr hstable
  exact bankTrialRenewalColdImmediateNoDefect
    ring root hsp x e hm hno

/-- Existential, genuinely physical counterexample to removing the
.defect constructor from the *current Lean ColdCarrier*. It reuses
Counter's already checked twenty-site launch and its incoming
edge 19. The two private example objects in Counter.lean are inferred
from its public theorem types, not renamed or redefined here.

This witness does NOT satisfy the paper's large buffered selection:
it proves that Complete + GrantFree alone is insufficient. -/
theorem bankTrialRenewalColdDefectConcrete :
    ∃ (ring : DirectedRing 20) (root edge : Fin 20)
      (x : Counter.ResetClockBankColdCarrier (q := 80) ring root)
      (hsp : (compileAdvice 80).useSmall = false),
      Counter.resetClockBankColdNext ring root hsp
        (Counter.resetClockBankColdStart ring root x) edge =
          .inr (.inr (((protocol 80).step ring x.val edge),
            .defect)) := by
  have hw := Counter.resetClockBankEarlyRoleFailureAfterLaunch
  have hlaunch := hw.2.1
  refine ⟨_, (0 : Fin 20), (19 : Fin 20),
    ⟨_, ⟨hlaunch.1, hlaunch.2.1⟩⟩, hw.1, ?_⟩
  apply bankTrialRenewalColdImmediateDefect
  · intro hm
    have hwait := hlaunch.2.2.2.1.1
    rw [hm] at hwait
    cases hwait
  · exact Counter.resetClockBankEarlyRoleExitIsDefect

/-- The frozen local BANK reference is its OWN support-only process.
No second stochastic process or outside-site field is present in
this equality. The original physical word remains unchanged. -/
theorem bankTrialRenewalFrozenSupportIdentity {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (word : List (Fin n)) :
    GrantBankReference.bankLocalReferenceWordClamped ring root
      (GrantBankReference.bankLocalReferenceSupportSubword
        (q := q) ring root word) S =
    GrantBankReference.bankLocalReferenceWordClamped
      ring root word S := by
  exact GrantBankReference.bankLocalReferenceWordLocalityClamped
    ring root word S

/-- Comparison with the ACTUAL physical configuration at every
prefix of a safe physical suffix. SafeWord explicitly requires
grant-free cuts, no supported OLD defect, and no earlier root
BANK success. It cannot be silently dropped at a physical intrusion. -/
theorem bankTrialRenewalFrozenSafePhysicalPrefix {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (D : Counter.Config q n)
    (hc : Counter.ResetClockBankClean ring D root)
    (u v : List (Fin n))
    (hsafe : GrantBankReference.bankLocalReferenceSafeWord
      ring root D (u ++ v)) :
    GrantBankReference.bankLocalReferenceFieldsAgree ring
      (Counter.Word ring u D) root
      (GrantBankReference.bankLocalReferenceWordClamped ring root
        (GrantBankReference.bankLocalReferenceSupportSubword
          (q := q) ring root u)
        (GrantBankReference.bankLocalReferenceStart ring root D)) := by
  exact bankTrialLocalSafePrefixSupportFieldsAgree ring root hsp
    D (GrantBankReference.bankLocalReferenceStart ring root D)
    hc.1
    (GrantBankReference.bankLocalReferenceStartAgrees ring D root)
    rfl u v hsafe

/-- If a genuine root BANK success is the first such event after a
safe physical prefix, the frozen support-only latch detects it on
that SAME final scheduler edge (which need not itself be safe). -/
theorem bankTrialRenewalFrozenFirstPhysicalSuccess {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (D : Counter.Config q n)
    (hc : Counter.ResetClockBankClean ring D root)
    (pre : List (Fin n)) (e : Fin n)
    (hsafe : GrantBankReference.bankLocalReferenceSafeWord
      ring root D pre)
    (hwin : GrantBankReference.bankLocalReferenceRealSuccessEvent
      ring root (Counter.Word ring pre D) e = true) :
    (GrantBankReference.bankLocalReferenceWordClamped ring root
      (GrantBankReference.bankLocalReferenceSupportSubword
        (q := q) ring root (pre ++ [e]))
      (GrantBankReference.bankLocalReferenceStart ring root D)).success =
        true := by
  rw [GrantBankReference.bankLocalReferenceWordLocalityClamped
    ring root (pre ++ [e])
    (GrantBankReference.bankLocalReferenceStart ring root D)]
  exact bankTrialLocalPhysicalRootSuccessReflected
    ring root hsp D
    (GrantBankReference.bankLocalReferenceStart ring root D)
    hc.1
    (GrantBankReference.bankLocalReferenceStartAgrees ring D root)
    rfl pre e hsafe hwin

/-- The existing first-stop comparison ALWAYS uses W-cut.length
at a sound, grant-free CLEAN handoff; it does not restart a full
window W. -/
theorem bankTrialRenewalColdCleanRemainingWindow {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (D : Counter.Config q n)
    (W : Nat) (cut suffix : List (Fin n))
    (hcut : cut.length ≤ W)
    (hg : (D root).grant = false) :
    bankTrialRenewalColdProxyWeight ring root W cut
      ((.inr (.inr (D, .clean)) :
        Counter.ResetClockBankColdState (q := q) ring root))
      suffix =
    Prob.indicator (bankTrialRenewalSuccessBy ring root
      (GrantBankReference.bankLocalReferenceStart ring root D)
      (W - cut.length) suffix) := by
  unfold bankTrialRenewalColdProxyWeight
  rw [if_pos hcut]
  simp only [hg]
  rfl

/-- A grant-labelled first stop within the window is already
successful for the comparison indicator; it costs no Clean suffix. -/
theorem bankTrialRenewalColdGrantWithinWindow {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (D : Counter.Config q n)
    (W : Nat) (cut suffix : List (Fin n))
    (hcut : cut.length ≤ W) :
    bankTrialRenewalColdProxyWeight ring root W cut
      ((.inr (.inr (D, .grant)) :
        Counter.ResetClockBankColdState (q := q) ring root))
      suffix = 1 := by
  unfold bankTrialRenewalColdProxyWeight
  rw [if_pos hcut]

/-- The C.2 cold stopped-cost coefficient fits INSIDE the compiled
C_0 reserve. This charge is measured from the block entrance, not
from the subsequent Clean cut. It is a mean-cost statement, not
a deterministic bound on any realized cold stopping time. -/
theorem bankTrialRenewalColdCostInsideReserve {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root) (T : Nat) :
    costNumerator (Counter.resetClockBankColdNext ring root hsp)
      (Counter.resetClockBankColdTerminal ring root)
      (Counter.resetClockBankColdStart ring root x) T ≤
    n ^ T * (n *
      bankTrialRenewalIndexColdCharge (ceilLogTwo n)) := by
  have hcoeff :
      2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
        5 * (compileAdvice (ceilLogTwo n)).b + 13 ≤
      bankTrialRenewalIndexColdCharge (ceilLogTwo n) := by
    unfold bankTrialRenewalIndexColdCharge
    omega
  calc
    costNumerator (Counter.resetClockBankColdNext ring root hsp)
        (Counter.resetClockBankColdTerminal ring root)
        (Counter.resetClockBankColdStart ring root x) T ≤
      n ^ T *
        ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
          5 * (compileAdvice (ceilLogTwo n)).b + 13) * n) :=
      Counter.resetClockBankColdStoppedCost ring root hsp x T
    _ ≤ n ^ T *
        (bankTrialRenewalIndexColdCharge (ceilLogTwo n) * n) :=
      Nat.mul_le_mul_left _
        (Nat.mul_le_mul_right n hcoeff)
    _ = n ^ T *
        (n * bankTrialRenewalIndexColdCharge (ceilLogTwo n)) := by
      rw [Nat.mul_comm
        (bankTrialRenewalIndexColdCharge (ceilLogTwo n)) n]

end L3

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
G13-INDEX-RENEWAL.

This is the actual cold-entrance, cost-weighted window inequality.
It does not replace the whole-clock Markov charge by a Clean
bound at the random residual window. The index mass and its
conditional duration are still to be bounded at a random stop.
-/

/-- The exact Clean first-success-index Markov inequality from the
block entrance. The charge includes the cold prefix length, not
just the regenerated suffix age. This does not assume that the
duration of the last trial is independent of its success event. -/
theorem bankTrialRenewalColdCleanIndexCutWindow {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (D : Counter.Config q n)
    (W L H : Nat) (cut suffix : List (Fin n)) :
    W * bankTrialSuccessStageIndexSum (fun j =>
      Prob.indicator (bankTrialRenewalPattern ring root
        (GrantBankReference.bankLocalReferenceStart ring root D)
        L j suffix)) H ≤
    W * bankTrialRenewalColdProxyWeight ring root W cut
      ((.inr (.inr (D, .clean)) :
        Counter.ResetClockBankColdState (q := q) ring root))
      suffix +
    cut.length +
    bankTrialSuccessStageIndexSum (fun j =>
      bankTrialRenewalTau ring root
        (GrantBankReference.bankLocalReferenceStart ring root D)
        L j suffix) H := by
  have hone :=
    bankTrialRenewalPatternOneHot ring root
      (GrantBankReference.bankLocalReferenceStart ring root D)
      L H suffix
  by_cases hcut : cut.length ≤ W
  · by_cases hg : (D root).grant = true
    · have hproxy :
          bankTrialRenewalColdProxyWeight ring root W cut
            ((.inr (.inr (D, .clean)) :
              Counter.ResetClockBankColdState (q := q) ring root))
            suffix = 1 := by
        simp [bankTrialRenewalColdProxyWeight, hcut, hg]
      have hsum :
          W * bankTrialSuccessStageIndexSum (fun j =>
            Prob.indicator (bankTrialRenewalPattern ring root
              (GrantBankReference.bankLocalReferenceStart
                ring root D) L j suffix)) H ≤ W := by
        simpa only [Nat.mul_one] using
          (Nat.mul_le_mul_left W hone)
      rw [hproxy]
      simp only [Nat.mul_one]
      omega
    · have hproxy :
          bankTrialRenewalColdProxyWeight ring root W cut
            ((.inr (.inr (D, .clean)) :
              Counter.ResetClockBankColdState (q := q) ring root))
            suffix =
          Prob.indicator (bankTrialRenewalSuccessBy ring root
            (GrantBankReference.bankLocalReferenceStart ring root D)
            (W - cut.length) suffix) := by
        simp [bankTrialRenewalColdProxyWeight, hcut, hg]
      have hwindow :
          (W - cut.length) *
            bankTrialSuccessStageIndexSum (fun j =>
              Prob.indicator (bankTrialRenewalPattern ring root
                (GrantBankReference.bankLocalReferenceStart
                  ring root D) L j suffix)) H ≤
          (W - cut.length) *
            Prob.indicator (bankTrialRenewalSuccessBy ring root
              (GrantBankReference.bankLocalReferenceStart
                ring root D) (W - cut.length) suffix) +
          bankTrialSuccessStageIndexSum (fun j =>
            bankTrialRenewalTau ring root
              (GrantBankReference.bankLocalReferenceStart
                ring root D) L j suffix) H :=
        bankTrialRenewalWordWindow ring root
          (GrantBankReference.bankLocalReferenceStart ring root D)
          L (W - cut.length) H suffix
      have hsplit :
          W * bankTrialSuccessStageIndexSum (fun j =>
            Prob.indicator (bankTrialRenewalPattern ring root
              (GrantBankReference.bankLocalReferenceStart
                ring root D) L j suffix)) H =
          (W - cut.length) *
            bankTrialSuccessStageIndexSum (fun j =>
              Prob.indicator (bankTrialRenewalPattern ring root
                (GrantBankReference.bankLocalReferenceStart
                  ring root D) L j suffix)) H +
          cut.length *
            bankTrialSuccessStageIndexSum (fun j =>
              Prob.indicator (bankTrialRenewalPattern ring root
                (GrantBankReference.bankLocalReferenceStart
                  ring root D) L j suffix)) H := by
        calc
          _ = ((W - cut.length) + cut.length) *
                bankTrialSuccessStageIndexSum (fun j =>
                  Prob.indicator (bankTrialRenewalPattern ring root
                    (GrantBankReference.bankLocalReferenceStart
                      ring root D) L j suffix)) H := by
              rw [Nat.sub_add_cancel hcut]
          _ = _ := Nat.add_mul _ _ _
      have hprefixCharge :
          cut.length *
            bankTrialSuccessStageIndexSum (fun j =>
              Prob.indicator (bankTrialRenewalPattern ring root
                (GrantBankReference.bankLocalReferenceStart
                  ring root D) L j suffix)) H ≤ cut.length := by
        simpa only [Nat.mul_one] using
          (Nat.mul_le_mul_left cut.length hone)
      have hsuccessScale :
          (W - cut.length) *
            Prob.indicator (bankTrialRenewalSuccessBy ring root
              (GrantBankReference.bankLocalReferenceStart
                ring root D) (W - cut.length) suffix) ≤
          W *
            Prob.indicator (bankTrialRenewalSuccessBy ring root
              (GrantBankReference.bankLocalReferenceStart
                ring root D) (W - cut.length) suffix) :=
        Nat.mul_le_mul_right _
          (Nat.sub_le W cut.length)
      rw [hproxy, hsplit]
      omega
  · have hproxy :
        bankTrialRenewalColdProxyWeight ring root W cut
          ((.inr (.inr (D, .clean)) :
            Counter.ResetClockBankColdState (q := q) ring root))
          suffix = 0 := by
      simp [bankTrialRenewalColdProxyWeight, hcut]
    have hsum :
        W * bankTrialSuccessStageIndexSum (fun j =>
          Prob.indicator (bankTrialRenewalPattern ring root
            (GrantBankReference.bankLocalReferenceStart
              ring root D) L j suffix)) H ≤ W := by
      simpa only [Nat.mul_one] using
        (Nat.mul_le_mul_left W hone)
    have hlate : W ≤ cut.length := by omega
    rw [hproxy]
    simp only [Nat.mul_zero, Nat.zero_add]
    omega

/-- A stopped index contributes only at a CLEAN terminal. Grants
are already counted by the comparison event; defects contribute zero.
The index is the number of failures before the successful trial. -/
noncomputable def bankTrialRenewalColdIndexStageWeight {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (L H : Nat) (_cut : List (Fin n))
    (z : Counter.ResetClockBankColdState (q := q) ring root)
    (suffix : List (Fin n)) : Nat :=
  match z with
  | .inr (.inr (D, .clean)) =>
      bankTrialSuccessStageIndexSum (fun j =>
        Prob.indicator (bankTrialRenewalPattern ring root
          (GrantBankReference.bankLocalReferenceStart ring root D)
          L j suffix)) H
  | _ => 0

/-- In a CLEAN branch, charge the first-success index by the
entire cold time plus the outcome-masked regenerated duration.
No truncation of the cold time is made before summation. -/
noncomputable def bankTrialRenewalColdIndexStageCost {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (L H : Nat) (cut : List (Fin n))
    (z : Counter.ResetClockBankColdState (q := q) ring root)
    (suffix : List (Fin n)) : Nat :=
  match z with
  | .inr (.inr (D, .clean)) =>
      cut.length + bankTrialSuccessStageIndexSum (fun j =>
        bankTrialRenewalTau ring root
          (GrantBankReference.bankLocalReferenceStart ring root D)
          L j suffix) H
  | _ => 0

/-- The entrance-clock Markov inequality at an arbitrary FIRST
cold stop, including non-CLEAN endpoints. -/
theorem bankTrialRenewalColdIndexCutWindow {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (W L H : Nat) (cut : List (Fin n))
    (z : Counter.ResetClockBankColdState (q := q) ring root)
    (suffix : List (Fin n)) :
    W * bankTrialRenewalColdIndexStageWeight
      ring root L H cut z suffix ≤
    W * bankTrialRenewalColdProxyWeight
      ring root W cut z suffix +
    bankTrialRenewalColdIndexStageCost
      ring root L H cut z suffix := by
  cases z with
  | inl a =>
      simp [bankTrialRenewalColdIndexStageWeight,
        bankTrialRenewalColdIndexStageCost]
  | inr y =>
      cases y with
      | inl a =>
          simp [bankTrialRenewalColdIndexStageWeight,
            bankTrialRenewalColdIndexStageCost]
      | inr outcome =>
          cases outcome with
          | mk D reason =>
              cases reason with
              | clean =>
                  simpa only [
                    bankTrialRenewalColdIndexStageWeight,
                    bankTrialRenewalColdIndexStageCost,
                    Nat.add_assoc] using
                    (bankTrialRenewalColdCleanIndexCutWindow
                      ring root D W L H cut suffix)
              | grant =>
                  simp [bankTrialRenewalColdIndexStageWeight,
                    bankTrialRenewalColdIndexStageCost]
              | defect =>
                  simp [bankTrialRenewalColdIndexStageWeight,
                    bankTrialRenewalColdIndexStageCost]

/-- A pointwise first-stop inequality lifts to the original
scheduler word, WITHOUT independence of prefix and outcome. -/
private theorem bankTrialRenewalColdStoppedWeightedWord
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (f g c : List (Fin n) → X → List (Fin n) → Nat)
    (W : Nat)
    (hrow : ∀ cut z suffix,
      W * f cut z suffix ≤ W * g cut z suffix +
        c cut z suffix) :
    ∀ (T : Nat) (pre : List (Fin n)) (z : X)
      (word : List (Fin n)),
      W * bankTrialSuccessNatStoppedWord next stop
        (fun cut z _ suffix => f cut z suffix) T pre z word ≤
      W * bankTrialSuccessNatStoppedWord next stop
        (fun cut z _ suffix => g cut z suffix) T pre z word +
      bankTrialSuccessNatStoppedWord next stop
        (fun cut z _ suffix => c cut z suffix) T pre z word := by
  intro T pre z word
  induction word generalizing T pre z with
  | nil =>
      cases hs : stop pre z with
      | true =>
          simpa [bankTrialSuccessNatStoppedWord, hs] using
            (hrow pre z [])
      | false =>
          simp [bankTrialSuccessNatStoppedWord, hs]
  | cons e tail ih =>
      cases hs : stop pre z with
      | true =>
          simpa [bankTrialSuccessNatStoppedWord, hs] using
            (hrow pre z (e :: tail))
      | false =>
          simp only [bankTrialSuccessNatStoppedWord, hs,
            Bool.false_eq_true, if_false]
          exact ih (T - 1) (pre ++ [e]) (next z e)

/-- Original Fin n schedule-sum lifting of the stopped-word bound. -/
private theorem bankTrialRenewalColdStoppedWeightedSchedule
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (f g c : List (Fin n) → X → List (Fin n) → Nat)
    (W T : Nat) (x : X)
    (hrow : ∀ cut z suffix,
      W * f cut z suffix ≤ W * g cut z suffix +
        c cut z suffix) :
    W * Prob.scheduleSum n T (fun word =>
      bankTrialSuccessNatStoppedWord next stop
        (fun cut z _ suffix => f cut z suffix) T [] x word) ≤
    W * Prob.scheduleSum n T (fun word =>
      bankTrialSuccessNatStoppedWord next stop
        (fun cut z _ suffix => g cut z suffix) T [] x word) +
    Prob.scheduleSum n T (fun word =>
      bankTrialSuccessNatStoppedWord next stop
        (fun cut z _ suffix => c cut z suffix) T [] x word) := by
  calc
    W * Prob.scheduleSum n T (fun word =>
        bankTrialSuccessNatStoppedWord next stop
          (fun cut z _ suffix => f cut z suffix) T [] x word) =
      Prob.scheduleSum n T (fun word =>
        W * bankTrialSuccessNatStoppedWord next stop
          (fun cut z _ suffix => f cut z suffix) T [] x word) :=
        (bankTrialSuccessScheduleSumScale n T W _).symm
    _ ≤ Prob.scheduleSum n T (fun word =>
        W * bankTrialSuccessNatStoppedWord next stop
          (fun cut z _ suffix => g cut z suffix) T [] x word +
        bankTrialSuccessNatStoppedWord next stop
          (fun cut z _ suffix => c cut z suffix) T [] x word) := by
        apply bankTrialProbabilityScheduleSumMono n T
        intro word
        exact bankTrialRenewalColdStoppedWeightedWord
          next stop f g c W hrow T [] x word
    _ = W * Prob.scheduleSum n T (fun word =>
        bankTrialSuccessNatStoppedWord next stop
          (fun cut z _ suffix => g cut z suffix) T [] x word) +
      Prob.scheduleSum n T (fun word =>
        bankTrialSuccessNatStoppedWord next stop
          (fun cut z _ suffix => c cut z suffix) T [] x word) := by
        rw [bankTrialC5ScheduleSumAdd,
          bankTrialSuccessScheduleSumScale]

/-- First-success index numerator, sampled through the genuine
cold first-stop observer on the SAME original length-T tape. -/
noncomputable def bankTrialRenewalColdIndexStageMass {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T L H : Nat) : Nat :=
  Prob.scheduleSum n T (fun word =>
    bankTrialSuccessNatStoppedWord
      (Counter.resetClockBankColdNext ring root hsp)
      (bankTrialRenewalColdStop ring root)
      (fun cut z _ suffix =>
        bankTrialRenewalColdIndexStageWeight
          ring root L H cut z suffix)
      T [] (Counter.resetClockBankColdStart ring root x) word)

/-- Joint first-stop numerator of the cold and outcome-conditioned
regenerated clock costs. -/
noncomputable def bankTrialRenewalColdIndexStageCostMass {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T L H : Nat) : Nat :=
  Prob.scheduleSum n T (fun word =>
    bankTrialSuccessNatStoppedWord
      (Counter.resetClockBankColdNext ring root hsp)
      (bankTrialRenewalColdStop ring root)
      (fun cut z _ suffix =>
        bankTrialRenewalColdIndexStageCost
          ring root L H cut z suffix)
      T [] (Counter.resetClockBankColdStart ring root x) word)

/-- First-stop factorization of the exact CLEAN index numerator. -/
theorem bankTrialRenewalColdIndexStageMassFactor {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T L H : Nat) :
    bankTrialRenewalColdIndexStageMass
      ring root hsp x T L H =
    ((Prob.firstStoppedPrefixes
      (Counter.resetClockBankColdNext ring root hsp)
      (bankTrialRenewalColdStop ring root)
      T [] (Counter.resetClockBankColdStart ring root x)).map
      (fun cut =>
        Prob.scheduleSum n (T - cut.length) (fun suffix =>
          bankTrialRenewalColdIndexStageWeight ring root L H cut
            (Prob.stoppedTapeRun
              (Counter.resetClockBankColdNext ring root hsp)
              cut (Counter.resetClockBankColdStart ring root x))
            suffix))).sum := by
  unfold bankTrialRenewalColdIndexStageMass
  exact bankTrialRenewalColdFirstStopFactor ring root hsp x
    (fun cut z suffix =>
      bankTrialRenewalColdIndexStageWeight
        ring root L H cut z suffix) T

/-- First-stop factorization of the WHOLE cost of each successful
index. This is a joint moment, not a product of unconditional means. -/
theorem bankTrialRenewalColdIndexStageCostFactor {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T L H : Nat) :
    bankTrialRenewalColdIndexStageCostMass
      ring root hsp x T L H =
    ((Prob.firstStoppedPrefixes
      (Counter.resetClockBankColdNext ring root hsp)
      (bankTrialRenewalColdStop ring root)
      T [] (Counter.resetClockBankColdStart ring root x)).map
      (fun cut =>
        Prob.scheduleSum n (T - cut.length) (fun suffix =>
          bankTrialRenewalColdIndexStageCost ring root L H cut
            (Prob.stoppedTapeRun
              (Counter.resetClockBankColdNext ring root hsp)
              cut (Counter.resetClockBankColdStart ring root x))
            suffix))).sum := by
  unfold bankTrialRenewalColdIndexStageCostMass
  exact bankTrialRenewalColdFirstStopFactor ring root hsp x
    (fun cut z suffix =>
      bankTrialRenewalColdIndexStageCost
        ring root L H cut z suffix) T

/-- G13 cold-first-stop C.16 window inequality. Success is
counted only within W FROM BLOCK ENTRANCE and defect contributes
neither pattern mass nor success. The full cold length is charged.
No conditional independence of trial duration and outcome is used. -/
theorem bankTrialRenewalColdIndexWeightedWindow {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T W L H : Nat) :
    W * bankTrialRenewalColdIndexStageMass
      ring root hsp x T L H ≤
    W * bankTrialRenewalColdProxyMass ring root hsp x T W +
      bankTrialRenewalColdIndexStageCostMass
        ring root hsp x T L H := by
  unfold bankTrialRenewalColdIndexStageMass
    bankTrialRenewalColdProxyMass
    bankTrialRenewalColdIndexStageCostMass
  exact bankTrialRenewalColdStoppedWeightedSchedule
    (Counter.resetClockBankColdNext ring root hsp)
    (bankTrialRenewalColdStop ring root)
    (fun cut z suffix =>
      bankTrialRenewalColdIndexStageWeight
        ring root L H cut z suffix)
    (fun cut z suffix =>
      bankTrialRenewalColdProxyWeight ring root W cut z suffix)
    (fun cut z suffix =>
      bankTrialRenewalColdIndexStageCost
        ring root L H cut z suffix)
    W T (Counter.resetClockBankColdStart ring root x)
    (fun cut z suffix =>
      bankTrialRenewalColdIndexCutWindow
        ring root W L H cut z suffix)

/-- The compiled cold charge fits the SAME window quota used in
With denominator-cleared Markov scaling. This is a bound
on the initial cold clock, not on the later index-conditioned cost. -/
theorem bankTrialRenewalColdMarkovReserve {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (R T W : Nat)
    (hradius : (256 * R) ^ 2 ≤ n ∧
      n < (256 * (R + 1)) ^ 2)
    (hW : W = R * n / 8) :
    255 * costNumerator
      (Counter.resetClockBankColdNext ring root hsp)
      (Counter.resetClockBankColdTerminal ring root)
      (Counter.resetClockBankColdStart ring root x) T ≤
    2 * W * n ^ T := by
  have hquota :=
    (bankTrialRenewalIndexCompiledQuotas
      n R W hn hsp hradius hW).1
  have hcost :=
    bankTrialRenewalColdCostInsideReserve
      ring root hsp x T
  calc
    255 * costNumerator
        (Counter.resetClockBankColdNext ring root hsp)
        (Counter.resetClockBankColdTerminal ring root)
        (Counter.resetClockBankColdStart ring root x) T ≤
      255 * (n ^ T *
        (n * bankTrialRenewalIndexColdCharge (ceilLogTwo n))) :=
      Nat.mul_le_mul_left 255 hcost
    _ = n ^ T *
        (255 * (n * bankTrialRenewalIndexColdCharge
          (ceilLogTwo n))) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ n ^ T * (2 * W) :=
      Nat.mul_le_mul_left _ hquota
    _ = 2 * W * n ^ T := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

end L3

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
Cold buffered start.

This is the local role-correct projection of the paper's buffered
start. The geometric distance at least 2R from external defects
belongs to the block-entrance selection/coupling argument; the
frozen support-only observer uses its consequence that every OLD
supported pair, INCLUDING the incoming predecessor, is good.
No assertion about unrestricted physical words after intrusion.
-/

/-- Every boundary-inclusive support edge is a correct OLD PACK pair.
The cold carrier already carries Complete and GrantFree. -/
def BankTrialBufferedColdRoles {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n) : Prop :=
  ∀ e : Fin n, Counter.Support q ring root e →
    goodPair (compileAdvice q).b
      (C e).pack (C (ring.rightNeighbor e)).pack = true

def BankTrialBufferedColdStart {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : Counter.ResetClockBankColdCarrier (q := q) ring root) : Prop :=
  BankTrialBufferedColdRoles ring root x.val

/-- Missing C.15 block-entrance selection interface. To apply this
to its selected roots, the physical packing argument must establish
this proposition from the 2R defect buffer and correct role interval.
It is a definition, NOT an asserted selection theorem. -/
def BankTrialBufferedSelectionAtBlockEntrance {n q : Nat}
    (ring : DirectedRing n) (C : Counter.Config q n)
    (selected : List (Fin n)) : Prop :=
  ∀ root : Fin n, root ∈ selected →
    Counter.Complete ring C root ∧
      Counter.GrantFree C root ∧
      BankTrialBufferedColdRoles ring root C

theorem bankTrialBufferedColdSelected {n q : Nat}
    (ring : DirectedRing n) (C : Counter.Config q n)
    (selected : List (Fin n))
    (hs : BankTrialBufferedSelectionAtBlockEntrance ring C selected)
    (root : Fin n) (hr : root ∈ selected) :
    ∃ x : Counter.ResetClockBankColdCarrier (q := q) ring root,
      x.val = C ∧ BankTrialBufferedColdStart ring root x := by
  obtain ⟨hc, hg, hb⟩ := hs root hr
  exact ⟨⟨C, ⟨hc, hg⟩⟩, rfl, hb⟩

/-- The exact role_step / roleWordStep_of_good calculation fixes
ALL PACK sites, not only the two endpoints of a supported letter. -/
theorem bankTrialBufferedColdGoodEdgeFrame {n q : Nat}
    (ring : DirectedRing n) (C : Counter.Config q n)
    (e : Fin n)
    (hg : goodPair (compileAdvice q).b
      (C e).pack (C (ring.rightNeighbor e)).pack = true) :
    (fun i => (((protocol q).step ring C e) i).pack) =
      (fun i => (C i).pack) := by
  calc
    _ = roleWordStep (compileAdvice q).b ring
        (fun i => (C i).pack) e := role_step ring C e
    _ = (fun i => (C i).pack) :=
      roleWordStep_of_good _ ring _ _ hg

/-- Correctness of every supported OLD pair is inductive under
each supported physical edge, including the incoming-root edge. -/
theorem bankTrialBufferedColdRolesStep {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (hb : BankTrialBufferedColdRoles ring root C)
    (e : Fin n) (he : Counter.Support q ring root e) :
    BankTrialBufferedColdRoles ring root
      ((protocol q).step ring C e) := by
  have hp := bankTrialBufferedColdGoodEdgeFrame ring C e (hb e he)
  intro f hf
  have hleft := congrFun hp f
  have hright := congrFun hp (ring.rightNeighbor f)
  change goodPair (compileAdvice q).b
    (((protocol q).step ring C e) f).pack
    (((protocol q).step ring C e) (ring.rightNeighbor f)).pack = true
  rw [hleft, hright]
  exact hb f hf

/-- No supported OLD bad pair and no supported PACK-role change.
This excludes BOTH disjuncts of ResetClockBankDefectEntry. -/
theorem bankTrialBufferedColdNoDefectEntry {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (C : Counter.Config q n)
    (hb : BankTrialBufferedColdRoles ring root C)
    (e : Fin n) :
    ¬ Counter.ResetClockBankDefectEntry ring C root e := by
  intro hd
  rcases hd with ⟨hs, hbad⟩
  rcases hbad with hp | hu
  · have hg := hb e hs
    rw [hp] at hg
    cases hg
  · apply hu
    intro j _
    exact congrFun
      (bankTrialBufferedColdGoodEdgeFrame ring C e (hb e hs))
      (Counter.site ring root j)

/-- For every finite support-only word the entire physical PACK
function equals its initial value, without any scratch invariant. -/
theorem bankTrialBufferedColdSupportWordPack {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (w : List (Fin n)) (C : Counter.Config q n),
      BankTrialBufferedColdRoles ring root C →
      (∀ e : Fin n, e ∈ w → Counter.Support q ring root e) →
      ∀ i : Fin n,
        (Counter.Word ring w C i).pack = (C i).pack := by
  intro w
  induction w with
  | nil =>
      intro C _ _ i
      rfl
  | cons e es ih =>
      intro C hb hletters i
      have he : Counter.Support q ring root e :=
        hletters e (by simp)
      have htail : ∀ f : Fin n, f ∈ es →
          Counter.Support q ring root f := by
        intro f hf
        exact hletters f (by simp [hf])
      have hn := bankTrialBufferedColdRolesStep ring root C hb e he
      have hp := bankTrialBufferedColdGoodEdgeFrame ring C e (hb e he)
      change (Counter.Word ring es
        ((protocol q).step ring C e) i).pack = (C i).pack
      calc
        _ = (((protocol q).step ring C e) i).pack :=
          ih _ hn htail i
        _ = (C i).pack := congrFun hp i

/-- The frozen observer has correct support roles while active;
a stopped node is allowed only if its reason is not defect.
This is a ghost property, not a new protocol state. -/
def BankTrialBufferedColdLive {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    Counter.ResetClockBankColdState (q := q) ring root → Prop
  | .inl x => BankTrialBufferedColdRoles ring root x.val
  | .inr (.inl a) =>
      BankTrialBufferedColdRoles ring root
        (Counter.resetClockBankAttemptConfig ring root a)
  | .inr (.inr (_, reason)) => reason ≠ .defect

theorem bankTrialBufferedColdLiveStart {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : Counter.ResetClockBankColdCarrier (q := q) ring root)
    (hb : BankTrialBufferedColdStart ring root x) :
    BankTrialBufferedColdLive ring root
      (Counter.resetClockBankColdStart ring root x) := by
  change BankTrialBufferedColdLive ring root
    (Counter.resetClockBankColdLift ring root x.val
      x.property.1 x.property.2)
  by_cases hm : (x.val root).mode = .RESET
  · rw [Counter.resetClockBankColdLiftReset ring root
      x.val x.property.1 x.property.2 hm]
    change BankTrialBufferedColdRoles ring root x.val
    exact hb
  · simp only [Counter.resetClockBankColdLift, dif_neg hm,
      BankTrialBufferedColdLive]
    exact hb

/-- A single real cold-observer service cannot produce a defect
terminal when its OLD physical support edges are all good. This
claim does not assume that an unsupported service preserves the
buffered start for subsequent steps. -/
theorem bankTrialBufferedColdNextNotDefect {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (z : Counter.ResetClockBankColdState (q := q) ring root)
    (hz : BankTrialBufferedColdLive ring root z)
    (e : Fin n) (D : Counter.Config q n) :
    Counter.resetClockBankColdNext ring root hsp z e ≠
      .inr (.inr (D, .defect)) := by
  cases z with
  | inl x =>
      have hb : BankTrialBufferedColdRoles ring root x.val := hz
      have hno := bankTrialBufferedColdNoDefectEntry ring root x.val hb e
      by_cases hg : Counter.GrantFree
          ((protocol q).step ring x.val e) root
      · rw [Counter.resetClockBankColdNextContinue
          ring root hsp x e hno hg]
        unfold Counter.resetClockBankColdLift
        split
        · intro hh
          cases hh
        · intro hh
          cases hh
      · rw [Counter.resetClockBankColdNextGrant
          ring root hsp x e hno hg]
        intro hh
        cases hh
  | inr y =>
      cases y with
      | inl a =>
          have hb : BankTrialBufferedColdRoles ring root
              (Counter.resetClockBankAttemptConfig ring root a) := hz
          have hno := bankTrialBufferedColdNoDefectEntry ring root
            (Counter.resetClockBankAttemptConfig ring root a) hb e
          change
            (Sum.inr (Counter.resetClockBankResultObserve ring root
              (Counter.resetClockBankAttemptService ring root hsp a e)) :
              Counter.ResetClockBankColdState (q := q) ring root) ≠
                .inr (.inr (D, .defect))
          cases hs : Counter.resetClockBankAttemptService
              ring root hsp a e with
          | active a' =>
              intro hh
              cases hh
          | retry seed =>
              intro hh
              cases hh
          | stop C reason =>
              cases reason with
              | clean =>
                  intro hh
                  cases hh
              | grant =>
                  intro hh
                  cases hh
              | defect =>
                  have hmeaning := Counter.resetClockBankServiceStopSound
                    ring root hsp a e C .defect hs
                  change Counter.ResetClockBankDefectEntry ring
                    (Counter.resetClockBankAttemptConfig ring root a)
                    root e at hmeaning
                  exact False.elim (hno hmeaning)
      | inr out =>
          cases out with
          | mk C reason =>
              have hreason : reason ≠ .defect := hz
              cases reason with
              | clean =>
                  intro hh
                  cases hh
              | grant =>
                  intro hh
                  cases hh
              | defect =>
                  exact False.elim (hreason rfl)

/-- A nonterminal observer service has the actual physical step,
so whole-PACK preservation transports supported-pair correctness
even through a C.3 to C.2 handoff or an authentic C.2 retry. -/
private theorem bankTrialBufferedColdLiveStepNonterminal {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (z : Counter.ResetClockBankColdState (q := q) ring root)
    (ht : ¬ Counter.resetClockBankColdTerminal ring root z)
    (hb : BankTrialBufferedColdRoles ring root
      (Counter.resetClockBankColdConfig ring root z))
    (e : Fin n) (he : Counter.Support q ring root e)
    (hno : ∀ D : Counter.Config q n,
      Counter.resetClockBankColdNext ring root hsp z e ≠
        .inr (.inr (D, .defect))) :
    BankTrialBufferedColdLive ring root
      (Counter.resetClockBankColdNext ring root hsp z e) := by
  have hp := Counter.resetClockBankColdPhysical
    ring root hsp z ht e
  have hbnext : BankTrialBufferedColdRoles ring root
      (Counter.resetClockBankColdConfig ring root
        (Counter.resetClockBankColdNext ring root hsp z e)) := by
    rw [hp]
    exact bankTrialBufferedColdRolesStep ring root
      (Counter.resetClockBankColdConfig ring root z) hb e he
  cases hn : Counter.resetClockBankColdNext ring root hsp z e with
  | inl x =>
      rw [hn] at hbnext
      change BankTrialBufferedColdRoles ring root x.val at hbnext
      exact hbnext
  | inr y =>
      cases y with
      | inl a =>
          rw [hn] at hbnext
          change BankTrialBufferedColdRoles ring root
            (Counter.resetClockBankAttemptConfig ring root a) at hbnext
          exact hbnext
      | inr out =>
          cases out with
          | mk D reason =>
              cases reason with
              | clean =>
                  intro hh
                  cases hh
              | grant =>
                  intro hh
                  cases hh
              | defect =>
                  exact False.elim (hno D hn)

/-- Induction step for ALL selected support letters. No grant
hypothesis is needed: a grant stop is an allowed successful exit. -/
theorem bankTrialBufferedColdLiveStep {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (z : Counter.ResetClockBankColdState (q := q) ring root)
    (hz : BankTrialBufferedColdLive ring root z)
    (e : Fin n) (he : Counter.Support q ring root e) :
    BankTrialBufferedColdLive ring root
      (Counter.resetClockBankColdNext ring root hsp z e) := by
  have hno : ∀ D : Counter.Config q n,
      Counter.resetClockBankColdNext ring root hsp z e ≠
        .inr (.inr (D, .defect)) := by
    intro D
    exact bankTrialBufferedColdNextNotDefect
      ring root hsp z hz e D
  cases z with
  | inl x =>
      have ht : ¬ Counter.resetClockBankColdTerminal ring root
          ((.inl x) :
            Counter.ResetClockBankColdState (q := q) ring root) := by
        intro hh
        exact hh
      exact bankTrialBufferedColdLiveStepNonterminal
        ring root hsp (.inl x) ht hz e he hno
  | inr y =>
      cases y with
      | inl a =>
          have ht : ¬ Counter.resetClockBankColdTerminal ring root
              ((.inr (.inl a)) :
                Counter.ResetClockBankColdState (q := q) ring root) := by
            intro hh
            exact hh
          exact bankTrialBufferedColdLiveStepNonterminal
            ring root hsp (.inr (.inl a)) ht hz e he hno
      | inr out =>
          change BankTrialBufferedColdLive ring root (.inr (.inr out))
          exact hz

/-- Finite word evaluation of the SAME cold observer on physical
scheduler letters. Terminals remain absorbing. -/
noncomputable def bankTrialBufferedColdRun {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false) :
    List (Fin n) →
      Counter.ResetClockBankColdState (q := q) ring root →
        Counter.ResetClockBankColdState (q := q) ring root
  | [], z => z
  | e :: es, z =>
      bankTrialBufferedColdRun ring root hsp es
        (Counter.resetClockBankColdNext ring root hsp z e)

/-- All-time observer invariant for EVERY support-only word. -/
theorem bankTrialBufferedColdRunInvariant {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false) :
    ∀ (w : List (Fin n))
      (z : Counter.ResetClockBankColdState (q := q) ring root),
      (∀ e : Fin n, e ∈ w → Counter.Support q ring root e) →
      BankTrialBufferedColdLive ring root z →
      BankTrialBufferedColdLive ring root
        (bankTrialBufferedColdRun ring root hsp w z) := by
  intro w
  induction w with
  | nil =>
      intro z _ hz
      exact hz
  | cons e es ih =>
      intro z hletters hz
      have he : Counter.Support q ring root e :=
        hletters e (by simp)
      have htail : ∀ f : Fin n, f ∈ es →
          Counter.Support q ring root f := by
        intro f hf
        exact hletters f (by simp [hf])
      change BankTrialBufferedColdLive ring root
        (bankTrialBufferedColdRun ring root hsp es
          (Counter.resetClockBankColdNext ring root hsp z e))
      exact ih _ htail
        (bankTrialBufferedColdLiveStep ring root hsp z hz e he)

/-- The clamped reference ignores every nonsupport clock letter.
Every retained letter is supported by construction. -/
private theorem bankTrialBufferedColdSubwordSupported {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (word : List (Fin n)) :
    ∀ e : Fin n,
      e ∈ GrantBankReference.bankLocalReferenceSupportSubword
          (q := q) ring root word →
        Counter.Support q ring root e := by
  intro e he
  unfold GrantBankReference.bankLocalReferenceSupportSubword at he
  exact of_decide_eq_true ((List.mem_filter.mp he).2)

/-- Support roles cannot change along the clamped reference's
physical support word, even if the private BANK scratch is arbitrary. -/
theorem bankTrialBufferedColdFrozenRoles {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (x : Counter.ResetClockBankColdCarrier (q := q) ring root)
    (hb : BankTrialBufferedColdStart ring root x)
    (word : List (Fin n)) :
    ∀ i : Fin n,
      (Counter.Word ring
        (GrantBankReference.bankLocalReferenceSupportSubword
          (q := q) ring root word) x.val i).pack =
        (x.val i).pack := by
  exact bankTrialBufferedColdSupportWordPack ring root
    (GrantBankReference.bankLocalReferenceSupportSubword
      (q := q) ring root word) x.val hb
    (bankTrialBufferedColdSubwordSupported ring root word)

/-- All-time stopped-observer invariant on the frozen local word.
This is the missing role induction; it does not invoke a
physical run with outside intrusion. -/
theorem bankTrialBufferedColdFrozenInvariant {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier (q := q) ring root)
    (hb : BankTrialBufferedColdStart ring root x)
    (word : List (Fin n)) :
    BankTrialBufferedColdLive ring root
      (bankTrialBufferedColdRun ring root hsp
        (GrantBankReference.bankLocalReferenceSupportSubword
          (q := q) ring root word)
        (Counter.resetClockBankColdStart ring root x)) := by
  exact bankTrialBufferedColdRunInvariant ring root hsp
    (GrantBankReference.bankLocalReferenceSupportSubword
      (q := q) ring root word)
    (Counter.resetClockBankColdStart ring root x)
    (bankTrialBufferedColdSubwordSupported ring root word)
    (bankTrialBufferedColdLiveStart ring root x hb)

/-- The physical frozen word and the clamped BANK reference use
the same ordered supported letters; locality does not assert
physical field equality after an intrusion. -/
theorem bankTrialBufferedColdReferenceLocality {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (word : List (Fin n)) :
    GrantBankReference.bankLocalReferenceWordClamped ring root
      (GrantBankReference.bankLocalReferenceSupportSubword
        (q := q) ring root word) S =
    GrantBankReference.bankLocalReferenceWordClamped
      ring root word S := by
  exact GrantBankReference.bankLocalReferenceWordLocalityClamped
    ring root word S

/-- A frozen cold first stop is CLEAN, or physical grant success.
In particular no DEFECT first stop can occur from this start. -/
theorem bankTrialBufferedColdFrozenFirstStop {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier (q := q) ring root)
    (hb : BankTrialBufferedColdStart ring root x)
    (word : List (Fin n))
    (hterm : Counter.resetClockBankColdTerminal ring root
      (bankTrialBufferedColdRun ring root hsp
        (GrantBankReference.bankLocalReferenceSupportSubword
          (q := q) ring root word)
        (Counter.resetClockBankColdStart ring root x))) :
    ∃ D : Counter.Config q n,
      bankTrialBufferedColdRun ring root hsp
        (GrantBankReference.bankLocalReferenceSupportSubword
          (q := q) ring root word)
        (Counter.resetClockBankColdStart ring root x) =
          .inr (.inr (D, .clean)) ∨
      bankTrialBufferedColdRun ring root hsp
        (GrantBankReference.bankLocalReferenceSupportSubword
          (q := q) ring root word)
        (Counter.resetClockBankColdStart ring root x) =
          .inr (.inr (D, .grant)) := by
  obtain ⟨D, reason, hshape⟩ :=
    bankTrialRenewalColdTerminalShape ring root
      (bankTrialBufferedColdRun ring root hsp
        (GrantBankReference.bankLocalReferenceSupportSubword
          (q := q) ring root word)
        (Counter.resetClockBankColdStart ring root x)) hterm
  have hinv := bankTrialBufferedColdFrozenInvariant
    ring root hsp x hb word
  rw [hshape] at hinv
  change reason ≠ .defect at hinv
  cases reason with
  | clean =>
      exact ⟨D, Or.inl hshape⟩
  | grant =>
      exact ⟨D, Or.inr hshape⟩
  | defect =>
      exact False.elim (hinv rfl)

/-- The earlier genuine n=20 early-defect witness is outside the
buffered start class. No private example constants are referenced. -/
theorem bankTrialBufferedColdConcreteWitnessExcluded :
    ∃ (ring : DirectedRing 20) (root edge : Fin 20)
      (x : Counter.ResetClockBankColdCarrier (q := 80) ring root)
      (hsp : (compileAdvice 80).useSmall = false),
      Counter.resetClockBankColdNext ring root hsp
        (Counter.resetClockBankColdStart ring root x) edge =
          .inr (.inr (((protocol 80).step ring x.val edge),
            .defect)) ∧
      ¬ BankTrialBufferedColdStart ring root x := by
  obtain ⟨ring, root, edge, x, hsp, hbad⟩ :=
    bankTrialRenewalColdDefectConcrete
  refine ⟨ring, root, edge, x, hsp, hbad, ?_⟩
  intro hb
  have hstart := bankTrialBufferedColdLiveStart ring root x hb
  have hno := bankTrialBufferedColdNextNotDefect
    ring root hsp (Counter.resetClockBankColdStart ring root x)
    hstart edge ((protocol 80).step ring x.val edge)
  exact hno hbad

end L3

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
Cold-prefix indexed accounting.

The suffix horizon H*L is supplied by W+H*L <= T for
every actual first stop with cut.length <= W.
No independence of success and duration is assumed.
-/

/-- The strengthened entrance-horizon hypothesis suffices for
each successful-index estimate after any early cold stopping cut. -/
theorem bankTrialRenewalColdIndexSuffixBudget
    (W H L T cutLength j : Nat)
    (hbudget : W + H * L ≤ T)
    (hcut : cutLength ≤ W)
    (hj : j < H) :
    (j + 1) * L ≤ T - cutLength := by
  have hindex : j + 1 ≤ H := by omega
  have hproduct : (j + 1) * L ≤ H * L :=
    Nat.mul_le_mul_right L hindex
  omega

/-- A joint successful-index charge: the cold length MUST be
multiplied by the success indicator. The rarity bound then pays
its coefficient once, rather than introducing a spurious 2^K. -/
private theorem bankTrialRenewalColdIndexedChargeOpaque
    (P N cold event duration other : Nat)
    (hrare : P * event ≤ N)
    (hcost : P * duration ≤ N * other) :
    P * (cold * event + duration) ≤
      N * (cold + other) := by
  calc
    P * (cold * event + duration) =
        cold * (P * event) + P * duration := by
      simp only [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm]
    _ ≤ cold * N + N * other :=
      Nat.add_le_add (Nat.mul_le_mul_left cold hrare) hcost
    _ = N * (cold + other) := by
      simp only [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm]

/-- The cost coefficient available to a cold entrance is exactly
c0+gM. In particular gM may not be charged twice. -/
theorem bankTrialRenewalColdIndexChargeSplit (q : Nat) :
    bankTrialRenewalIndexColdCharge q =
      (2 * (compileAdvice q).bankLeaseCap +
        5 * (compileAdvice q).b + 13) +
        bankTrialRenewalIndexZeroCharge q := by
  rfl

/-- The first-success-index sandwich is valid on a CLEAN
cold suffix whenever the entire cold cut fits inside W. Both
the mass and the duration are for the SAME index-j event.
This is a per-cut result, before taking the first-stop list sum. -/
theorem bankTrialRenewalColdCleanIndexCutBounds
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 2 ≤ n)
    (hsp : (compileAdvice q).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n q)
    (hlarge : 2 * (compileAdvice q).bankLeaseCap ≤ n)
    (hpositive : 0 < (compileAdvice q).K)
    (hK : (compileAdvice q).K < 2 ^ (compileAdvice q).b)
    (S : GrantBankReference.BankLocalReference
      (compileAdvice q).b)
    (hclean : BankTrialLocalClean q S)
    (L W H T j : Nat)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold n q ≤ L)
    (hbudgetCold : W + H * L ≤ T)
    (cut : List (Fin n)) (hcut : cut.length ≤ W)
    (hj : j < H) :
    (1024 * (L * 2 ^ (compileAdvice q).K -
      L - 2 ^ (compileAdvice q).K *
        ((8 * (compileAdvice q).b + 12) * n))) ^ j *
      (1023 * L) * n ^ (T - cut.length) ≤
    (1024 * (L * 2 ^ (compileAdvice q).K)) ^ (j + 1) *
      bankTrialRenewalPatternMass ring root S
        (T - cut.length) L j ∧
    2 ^ (compileAdvice q).K *
      (cut.length * bankTrialRenewalPatternMass
        ring root S (T - cut.length) L j +
        bankTrialRenewalPatternCost
          ring root S (T - cut.length) L j) ≤
    n ^ (T - cut.length) *
      (cut.length + n * (bankTrialRenewalIndexZeroCharge q +
        j * bankTrialRenewalIndexStepCharge q)) := by
  have hremaining : (j + 1) * L ≤ T - cut.length :=
    bankTrialRenewalColdIndexSuffixBudget
      W H L T cut.length j hbudgetCold hcut hj
  have hthreshold :
      bankTrialRenewalWonCutoffThreshold n q ≤ L :=
    bankTrialRenewalEvalCutoffDescent
      (bankTrialRenewalWonCutoffThreshold n q) L hL
  have hmass := (bankTrialRenewalEvalThetaMassSandwich
    ring root hn hsp hw hlarge hpositive hK L hthreshold)
    S hclean j (T - cut.length) hremaining
  have hsharp :
      bankTrialRenewalWonCutoffThresholdSharp n q 1024 ≤ L :=
    bankTrialRenewalIndexSharpCutoffCovered n q L hL
  have hG :
      BankTrialRenewalZeroCostWithinBound (q := q)
        ring root L (bankTrialRenewalIndexZeroCharge q) := by
    unfold bankTrialRenewalIndexZeroCharge
    have hGsharp := bankTrialRenewalZeroCostWithinBoundSharp
      ring root hn hsp hw hlarge hpositive hK
      1024 (by decide) L hsharp
    simpa only [bankTrialRenewalIndexCeilIdentity] using hGsharp
  have hFc :
      BankTrialRenewalLostCostWithinBound (q := q)
        ring root L (bankTrialRenewalIndexStepCharge q) := by
    unfold bankTrialRenewalIndexStepCharge
    exact bankTrialRenewalLostCostWithinBoundHolds
      ring root hn hsp hw hpositive hK L
  have hR := bankTrialRenewalZeroRareWithinBoundHolds
    ring root hn hsp hw hlarge hpositive hK L
  have hcost := (bankTrialRenewalCostSandwichOfTrialBounds
    ring root L (bankTrialRenewalIndexStepCharge q)
    (bankTrialRenewalIndexZeroCharge q) hG hFc hR)
    S hclean j (T - cut.length) hremaining
  have hrare := (bankTrialRenewalRareAllOfZero
    ring root L hR) j S hclean
    (T - cut.length) hremaining
  have hjoint := bankTrialRenewalColdIndexedChargeOpaque
    (2 ^ (compileAdvice q).K)
    (n ^ (T - cut.length))
    cut.length
    (bankTrialRenewalPatternMass
      ring root S (T - cut.length) L j)
    (bankTrialRenewalPatternCost
      ring root S (T - cut.length) L j)
    (n * (bankTrialRenewalIndexZeroCharge q +
      j * bankTrialRenewalIndexStepCharge q))
    hrare hcost
  exact ⟨hmass, hjoint⟩

/-- Specialization to the genuine sound physical CLEAN terminal.
No new Clean assumption: it follows from its recorded terminal
soundness. The compiler's K and width conditions are derived as
in the proof rather than added as independent premises. -/
theorem bankTrialRenewalColdSoundIndexCutBounds
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (hlarge :
      2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n)
    (D : Counter.Config (ceilLogTwo n) n)
    (hsound : Counter.resetColdObserverSound ring root
      ((.inr (.inr (D, .clean)) :
        Counter.ResetClockBankColdState
          (q := ceilLogTwo n) ring root)))
    (L W H T j : Nat)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold
      n (ceilLogTwo n) ≤ L)
    (hbudgetCold : W + H * L ≤ T)
    (cut : List (Fin n)) (hcut : cut.length ≤ W)
    (hj : j < H) :
    (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K -
      L - 2 ^ (compileAdvice (ceilLogTwo n)).K *
        ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n))) ^ j *
      (1023 * L) * n ^ (T - cut.length) ≤
    (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K)) ^ (j + 1) *
      bankTrialRenewalPatternMass ring root
        (GrantBankReference.bankLocalReferenceStart ring root D)
        (T - cut.length) L j ∧
    2 ^ (compileAdvice (ceilLogTwo n)).K *
      (cut.length * bankTrialRenewalPatternMass ring root
        (GrantBankReference.bankLocalReferenceStart ring root D)
        (T - cut.length) L j +
        bankTrialRenewalPatternCost ring root
          (GrantBankReference.bankLocalReferenceStart ring root D)
          (T - cut.length) L j) ≤
    n ^ (T - cut.length) *
      (cut.length + n *
        (bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
          j * bankTrialRenewalIndexStepCharge
            (ceilLogTwo n))) := by
  have hq : 3 ≤ ceilLogTwo n := by
    have hspec := (ceilLogTwo_spec n (by omega)).2
    by_cases hc : ceilLogTwo n ≤ 2
    · have hp := Nat.pow_le_pow_right
        (by decide : 0 < (2 : Nat)) hc
      have hfour : (2 : Nat) ^ 2 = 4 := by decide
      omega
    · omega
  have hpositive :
      0 < (compileAdvice (ceilLogTwo n)).K := by
    change 0 < 2 * ceilLogTwo n +
      productionKappa (ceilLogTwo n)
    omega
  have hK :
      (compileAdvice (ceilLogTwo n)).K <
        2 ^ (compileAdvice (ceilLogTwo n)).b :=
    Nat.lt_trans (Nat.lt_succ_self _)
      (compileAdvice_K_lt_two_pow_b (ceilLogTwo n) hq)
  exact bankTrialRenewalColdCleanIndexCutBounds
    ring root (by omega) hsp hw hlarge hpositive hK
    (GrantBankReference.bankLocalReferenceStart ring root D)
    (bankTrialRenewalColdSoundCleanReference ring root D hsound)
    L W H T j hL hbudgetCold cut hcut hj

end L3

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-!
G13-INDEX-RENEWAL, buffered spatial selection at the
first-grant entrance.

The C.9--C.10 spatial bridge is PACK-only. It cannot imply
GrantFree without restricting the stage to its pre-grant branch.
The exact restriction is purified AND not grant-ready. A
grant-ready or generated cut is already a terminal alternative.
-/

/-- The source's B.6 bad-edge convention is the Boolean negation
of the literal physical goodPair test. -/
theorem bankTrialBufferedBadRoleZeroGood {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (e : Fin n)
    (hbad : badRoleEdge
      (compileAdvice (ceilLogTwo n)).b ring
      (fun i : Fin n => (C i).pack) e = 0) :
    goodPair (compileAdvice (ceilLogTwo n)).b
      (C e).pack (C (ring.rightNeighbor e)).pack = true := by
  exact (headlineGrantGoodEdgeIff
    (compileAdvice (ceilLogTwo n)).b ring
    (fun i : Fin n => (C i).pack) e).1 hbad

/-- If the first-grant stage has not yet reached its target,
a purified physical configuration has no grant token anywhere.
There is no claim that headlineGrantReady itself implies this. -/
theorem bankTrialBufferedPreGrantFree {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (hpurified : headlinePurified ring C)
    (hnotready : ¬ headlineGrantReady ring C) :
    ∀ root : Fin n, Counter.GrantFree C root := by
  intro root
  change (C root).grant = false
  cases hg : (C root).grant with
  | false =>
      rfl
  | true =>
      have hready : headlineGrantReady ring C :=
        Or.inr ⟨hpurified, ⟨root, hg⟩⟩
      exact False.elim (hnotready hready)

/-- The precise projection requested by C.15. The per-root
buffered conjunct supplies Complete and every inclusive good
pair; the independent per-root grant-free conjunct is essential. -/
theorem bankTrialBufferedSelectionOfBufferedCounters {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (radius : Nat) (selected : List (Fin n))
    (hbuffered : ∀ root : Fin n, root ∈ selected →
      HeadlineGrantBufferedCounter ring C radius root)
    (hfree : ∀ root : Fin n, root ∈ selected →
      Counter.GrantFree C root) :
    BankTrialBufferedSelectionAtBlockEntrance
      (q := ceilLogTwo n) ring C selected := by
  intro root hr
  have hh := hbuffered root hr
  refine ⟨hh.1, hfree root hr, ?_⟩
  intro e he
  exact bankTrialBufferedBadRoleZeroGood ring C e
    (hh.2.1 e he)

/-- On the genuine pre-grant branch, no separate grant-free leaf
is needed: it is forced by the first-grant stopping predicate. -/
theorem bankTrialBufferedSelectionBeforeGrant {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (radius : Nat) (selected : List (Fin n))
    (hpurified : headlinePurified ring C)
    (hnotready : ¬ headlineGrantReady ring C)
    (hbuffered : ∀ root : Fin n, root ∈ selected →
      HeadlineGrantBufferedCounter ring C radius root) :
    BankTrialBufferedSelectionAtBlockEntrance
      (q := ceilLogTwo n) ring C selected := by
  apply bankTrialBufferedSelectionOfBufferedCounters
    ring C radius selected hbuffered
  intro root _
  exact bankTrialBufferedPreGrantFree
    ring C hpurified hnotready root

/-- A literal Cartesian physical configuration with the SAME
PACK data and every grant bit set. This demonstrates why C.9's
PACK-only selection cannot establish GrantFree unconditionally. -/
def bankTrialBufferedGrantSaturated {n : Nat}
    (C : HeadlineConfiguration n) : HeadlineConfiguration n :=
  fun i => { C i with grant := true }

/-- Saturating all grant bits preserves every geometric buffered
conjunct but fails the required C.15 selected-root grant freedom.
This is a structural counterexample, conditional only on the
existence of any buffered root at the given physical PACK cut. -/
theorem bankTrialBufferedGrantNotFromGeometry {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n)
    (radius : Nat) (root : Fin n)
    (hb : HeadlineGrantBufferedCounter ring C radius root) :
    HeadlineGrantBufferedCounter ring
      (bankTrialBufferedGrantSaturated C) radius root ∧
    ¬ BankTrialBufferedSelectionAtBlockEntrance
      (q := ceilLogTwo n) ring
      (bankTrialBufferedGrantSaturated C) [root] := by
  have hc : Counter.Complete ring
      (bankTrialBufferedGrantSaturated C) root := by
    intro j hj
    change (C (Counter.site ring root j)).pack.val = j
    exact hb.1 j hj
  have hgood : ∀ e : Fin n,
      Counter.Support (ceilLogTwo n) ring root e →
      badRoleEdge (compileAdvice (ceilLogTwo n)).b ring
        (fun i : Fin n =>
          ((bankTrialBufferedGrantSaturated C) i).pack) e = 0 := by
    intro e he
    change badRoleEdge (compileAdvice (ceilLogTwo n)).b ring
      (fun i : Fin n => (C i).pack) e = 0
    exact hb.2.1 e he
  have hbehind : ∀ e : Fin n,
      badRoleEdge (compileAdvice (ceilLogTwo n)).b ring
        (fun i : Fin n =>
          ((bankTrialBufferedGrantSaturated C) i).pack) e = 1 →
      ∀ d : Nat, 1 ≤ d → d ≤ 2 * radius →
        Counter.site ring e d ≠ root := by
    intro e he d hd hdb
    change badRoleEdge (compileAdvice (ceilLogTwo n)).b ring
      (fun i : Fin n => (C i).pack) e = 1 at he
    exact hb.2.2 e he d hd hdb
  refine ⟨⟨hc, hgood, hbehind⟩, ?_⟩
  intro hs
  have hf : Counter.GrantFree
      (bankTrialBufferedGrantSaturated C) root :=
    (hs root (by simp)).2.1
  change true = false at hf
  cases hf

/-- No defect at any terminal of the genuinely frozen support
word. The physical run is the cold observer, not the
unrestricted global scheduler or an invented projection. -/
def BankTrialBufferedFrozenNoDefect {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice q).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier (q := q) ring root) :
    Prop :=
  ∀ word : List (Fin n),
    Counter.resetClockBankColdTerminal ring root
      (bankTrialBufferedColdRun ring root hsp
        (GrantBankReference.bankLocalReferenceSupportSubword
          (q := q) ring root word)
        (Counter.resetClockBankColdStart ring root x)) →
    ∃ D : Counter.Config q n,
      bankTrialBufferedColdRun ring root hsp
        (GrantBankReference.bankLocalReferenceSupportSubword
          (q := q) ring root word)
        (Counter.resetClockBankColdStart ring root x) =
          .inr (.inr (D, .clean)) ∨
      bankTrialBufferedColdRun ring root hsp
        (GrantBankReference.bankLocalReferenceSupportSubword
          (q := q) ring root word)
        (Counter.resetClockBankColdStart ring root x) =
          .inr (.inr (D, .grant))

/-- Combine the exact selected-root interface, the earlier carrier
constructor, and its frozen first-stop exclusion of .defect. -/
theorem bankTrialBufferedSelectedFrozenNoDefect {n : Nat}
    (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (selected : List (Fin n))
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hs : BankTrialBufferedSelectionAtBlockEntrance
      (q := ceilLogTwo n) ring C selected)
    (root : Fin n) (hr : root ∈ selected) :
    ∃ x : Counter.ResetClockBankColdCarrier
        (q := ceilLogTwo n) ring root,
      x.val = C ∧
      BankTrialBufferedColdStart ring root x ∧
      BankTrialBufferedFrozenNoDefect ring root hsp x := by
  obtain ⟨x, heq, hb⟩ :=
    bankTrialBufferedColdSelected ring C selected hs root hr
  refine ⟨x, heq, hb, ?_⟩
  intro word ht
  exact bankTrialBufferedColdFrozenFirstStop
    ring root hsp x hb word ht

/-- Actual C.9--C.10 root selection, restricted to the pending
first-grant branch. Its selected roots satisfy C.15
without any new assumed leaf. The rear-buffer, disjointness
and 489/1000 density certificates are retained. -/
theorem bankTrialBufferedSpatialPreGrantFrozen {n : Nat}
    (ring : DirectedRing n)
    (C : HeadlineConfiguration n) (radius : Nat)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hsize :
      (4096 * ((compileAdvice (ceilLogTwo n)).b + 2)) ^ 2 ≤ n)
    (hlower : (256 * radius) ^ 2 ≤ n)
    (hupper : n < (256 * (radius + 1)) ^ 2)
    (hdensity : defects ring C * defects ring C ≤ 4 * n)
    (hpurified : headlinePurified ring C)
    (hnotready : ¬ headlineGrantReady ring C) :
    ∃ selected : List (Fin n),
      selected.Nodup ∧
      BankTrialBufferedSelectionAtBlockEntrance
        (q := ceilLogTwo n) ring C selected ∧
      (∀ root : Fin n, root ∈ selected →
        ∃ x : Counter.ResetClockBankColdCarrier
            (q := ceilLogTwo n) ring root,
          x.val = C ∧
          BankTrialBufferedColdStart ring root x ∧
          BankTrialBufferedFrozenNoDefect ring root hsp x) ∧
      (∀ root other : Fin n,
        root ∈ selected → other ∈ selected → root ≠ other →
          ∀ e : Fin n,
            ¬ (Counter.Support (ceilLogTwo n) ring root e ∧
               Counter.Support (ceilLogTwo n) ring other e)) ∧
      489 * n <
        1000 * selected.length *
          ((compileAdvice (ceilLogTwo n)).b + 2) := by
  obtain ⟨selected, hnodup, hbuffered, hdisjoint, hcount⟩ :=
    (headlineGrantSpatialSupportBridgeProved ring)
      C radius hsize hlower hupper hdensity
  have hs : BankTrialBufferedSelectionAtBlockEntrance
      (q := ceilLogTwo n) ring C selected :=
    bankTrialBufferedSelectionBeforeGrant
      ring C radius selected hpurified hnotready hbuffered
  refine ⟨selected, hnodup, hs, ?_, hdisjoint, hcount⟩
  intro root hr
  exact bankTrialBufferedSelectedFrozenNoDefect
    ring C selected hsp hs root hr

end L3


namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
G13-INDEX-RENEWAL.

Part (a) is the actual first-stop CLEAN prefix sum of the
event-masked per-cut estimates. Part (b) bounds the event that
the cold observer has not stopped through time W by the censored
cold first-hit cost. The sum does not use the earlier unmasked
bankTrialRenewalColdIndexStageCostMass.
The final C.16 mass-partition and numerical payoff are not
asserted here.
-/

/-- Every finite cold observer tape, including a terminal one,
retains CounterCold's physical stop-reason soundness. -/
private theorem bankTrialRenewalColdRunSound {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (cut : List (Fin n)) :
    Counter.resetColdObserverSound ring root
      (Prob.stoppedTapeRun
        (Counter.resetClockBankColdNext ring root hsp)
        cut (Counter.resetClockBankColdStart ring root x)) := by
  have hrun :
      ∀ (word : List (Fin n))
        (z : Counter.ResetClockBankColdState
          (q := ceilLogTwo n) ring root),
        Counter.resetColdObserverSound ring root z →
        Counter.resetColdObserverSound ring root
          (Prob.stoppedTapeRun
            (Counter.resetClockBankColdNext ring root hsp)
            word z) := by
    intro word
    induction word with
    | nil =>
        intro z hz
        exact hz
    | cons e tail ih =>
        intro z hz
        change Counter.resetColdObserverSound ring root
          (Prob.stoppedTapeRun
            (Counter.resetClockBankColdNext ring root hsp)
            tail (Counter.resetClockBankColdNext ring root hsp z e))
        exact ih _
          (Counter.resetColdObserverSoundStep
            ring root hsp z hz e)
  exact hrun cut _
    (Counter.resetColdObserverSoundStart ring root x)

/-- The enumerator's cuts are genuine cold terminal snapshots,
not arbitrary lists with a fabricated CLEAN outcome. -/
theorem bankTrialRenewalColdAuthenticFirstStop {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T : Nat) (cut : List (Fin n))
    (hmem : cut ∈ Prob.firstStoppedPrefixes
      (Counter.resetClockBankColdNext ring root hsp)
      (bankTrialRenewalColdStop ring root)
      T [] (Counter.resetClockBankColdStart ring root x)) :
    Counter.resetClockBankColdTerminal ring root
      (Prob.stoppedTapeRun
        (Counter.resetClockBankColdNext ring root hsp)
        cut (Counter.resetClockBankColdStart ring root x)) := by
  have hs := bankTrialSuccessStoppedPrefixesSound
    (Counter.resetClockBankColdNext ring root hsp)
    (bankTrialRenewalColdStop ring root)
    T [] (Counter.resetClockBankColdStart ring root x)
    cut hmem
  exact (bankTrialRenewalColdStopCorrect
    ring root ([] ++ cut)
    (Prob.stoppedTapeRun
      (Counter.resetClockBankColdNext ring root hsp)
      cut (Counter.resetClockBankColdStart ring root x))).mp hs

/-- All actual early CLEAN cuts, weighted by any function of
their own sound terminal D. All non-CLEAN and late cuts have
weight zero; there is no independence or forged terminal
configuration in this definition. -/
noncomputable def bankTrialRenewalColdEarlyCleanSum {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T W : Nat)
    (F : List (Fin n) →
      Counter.Config (ceilLogTwo n) n → Nat) : Nat :=
  ((Prob.firstStoppedPrefixes
    (Counter.resetClockBankColdNext ring root hsp)
    (bankTrialRenewalColdStop ring root)
    T [] (Counter.resetClockBankColdStart ring root x)).map
    (fun cut =>
      if cut.length ≤ W then
        match Prob.stoppedTapeRun
            (Counter.resetClockBankColdNext ring root hsp)
            cut (Counter.resetClockBankColdStart ring root x) with
        | .inr (.inr (D, .clean)) => F cut D
        | _ => 0
      else 0)).sum

/-- Scalar inequalities over a finite list sum without Finset.
Both factors may be large symbolic naturals. -/
private theorem bankTrialRenewalColdListMulSum
    {α : Type} (A B : α → Nat) (p q : Nat) :
    ∀ xs : List α,
      (∀ a, a ∈ xs → p * A a ≤ q * B a) →
      p * (xs.map A).sum ≤ q * (xs.map B).sum := by
  intro xs
  induction xs with
  | nil =>
      intro _
      simp
  | cons a xs ih =>
      intro h
      have ha : p * A a ≤ q * B a :=
        h a (by simp)
      have ht : ∀ b, b ∈ xs →
          p * A b ≤ q * B b := by
        intro b hb
        exact h b (by simp [hb])
      have hs := ih ht
      simpa only [List.map_cons, List.sum_cons, Nat.mul_add] using
        (Nat.add_le_add ha hs)

/-- An arbitrary sound-CLEAN per-cut inequality can be summed over
the ACTUAL first-stopped prefixes with the cutoff cut.length ≤ W.
The stopped-tape soundness is proved, not postulated. -/
private theorem bankTrialRenewalColdEarlyCleanSumMono {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T W : Nat)
    (A B : List (Fin n) →
      Counter.Config (ceilLogTwo n) n → Nat)
    (p q : Nat)
    (hrow : ∀ cut D, cut.length ≤ W →
      Counter.resetColdObserverSound ring root
        ((.inr (.inr (D, .clean)) :
          Counter.ResetClockBankColdState
            (q := ceilLogTwo n) ring root)) →
      p * A cut D ≤ q * B cut D) :
    p * bankTrialRenewalColdEarlyCleanSum
      ring root hsp x T W A ≤
    q * bankTrialRenewalColdEarlyCleanSum
      ring root hsp x T W B := by
  unfold bankTrialRenewalColdEarlyCleanSum
  apply bankTrialRenewalColdListMulSum
  intro cut _
  by_cases hcut : cut.length ≤ W
  · cases hz : Prob.stoppedTapeRun
        (Counter.resetClockBankColdNext ring root hsp)
        cut (Counter.resetClockBankColdStart ring root x) with
    | inl y =>
        simp [hcut, hz]
    | inr y =>
        cases y with
        | inl a =>
            simp [hcut, hz]
        | inr outcome =>
            cases outcome with
            | mk D reason =>
                cases reason with
                | clean =>
                    have hsound :
                        Counter.resetColdObserverSound ring root
                          ((.inr (.inr (D, .clean)) :
                            Counter.ResetClockBankColdState
                              (q := ceilLogTwo n) ring root)) := by
                      have hs := bankTrialRenewalColdRunSound
                        ring root hsp x cut
                      rw [hz] at hs
                      exact hs
                    simpa [hcut, hz] using
                      (hrow cut D hcut hsound)
                | grant =>
                    simp [hcut, hz]
                | defect =>
                    simp [hcut, hz]
  · simp [hcut]

/-- (a), mass half. The theta/first-LOST lower bounds are
summed at every authentic CLEAN first stop with remaining horizon
T-cut.length. The scalar lo and den are never unfolded into omega. -/
theorem bankTrialRenewalColdEarlyCleanIndexMassBound {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (hlarge : 2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (L W H T j : Nat)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold
      n (ceilLogTwo n) ≤ L)
    (hbudgetCold : W + H * L ≤ T)
    (hj : j < H) :
    (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K -
      L - 2 ^ (compileAdvice (ceilLogTwo n)).K *
        ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n))) ^ j *
      (1023 * L) *
      bankTrialRenewalColdEarlyCleanSum ring root hsp x T W
        (fun cut _ => n ^ (T - cut.length)) ≤
    (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K)) ^ (j + 1) *
      bankTrialRenewalColdEarlyCleanSum ring root hsp x T W
        (fun cut D =>
          bankTrialRenewalPatternMass ring root
            (GrantBankReference.bankLocalReferenceStart ring root D)
            (T - cut.length) L j) := by
  apply bankTrialRenewalColdEarlyCleanSumMono
  intro cut D hcut hsound
  exact (bankTrialRenewalColdSoundIndexCutBounds
    ring root hn hsp hw hlarge D hsound
    L W H T j hL hbudgetCold cut hcut hj).1

/-- (a), joint event-masked cost half. Note the factor cut.length
MULTIPLIES the actual E_j pattern mass. There is no term charging
cut.length for a CLEAN cut without a successful j-th index. -/
theorem bankTrialRenewalColdEarlyCleanIndexChargeBound {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (hlarge : 2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (L W H T j : Nat)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold
      n (ceilLogTwo n) ≤ L)
    (hbudgetCold : W + H * L ≤ T)
    (hj : j < H) :
    2 ^ (compileAdvice (ceilLogTwo n)).K *
      bankTrialRenewalColdEarlyCleanSum ring root hsp x T W
        (fun cut D =>
          cut.length * bankTrialRenewalPatternMass ring root
            (GrantBankReference.bankLocalReferenceStart ring root D)
            (T - cut.length) L j +
          bankTrialRenewalPatternCost ring root
            (GrantBankReference.bankLocalReferenceStart ring root D)
            (T - cut.length) L j) ≤
    bankTrialRenewalColdEarlyCleanSum ring root hsp x T W
      (fun cut _ =>
        n ^ (T - cut.length) *
          (cut.length + n *
            (bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
              j * bankTrialRenewalIndexStepCharge
                (ceilLogTwo n)))) := by
  have hs := bankTrialRenewalColdEarlyCleanSumMono
    ring root hsp x T W
    (fun cut D =>
      cut.length * bankTrialRenewalPatternMass ring root
        (GrantBankReference.bankLocalReferenceStart ring root D)
        (T - cut.length) L j +
      bankTrialRenewalPatternCost ring root
        (GrantBankReference.bankLocalReferenceStart ring root D)
        (T - cut.length) L j)
    (fun cut _ =>
      n ^ (T - cut.length) *
        (cut.length + n *
          (bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
            j * bankTrialRenewalIndexStepCharge
              (ceilLogTwo n))))
    (2 ^ (compileAdvice (ceilLogTwo n)).K) 1
    (by
      intro cut D hcut hsound
      simpa only [Nat.one_mul] using
        (bankTrialRenewalColdSoundIndexCutBounds
          ring root hn hsp hw hlarge D hsound
          L W H T j hL hbudgetCold cut hcut hj).2)
  simpa only [Nat.one_mul] using hs

/-- Survival THROUGH W selected letters: the initial state and
every state at elapsed times 1,...,W are nonterminal. This is
strictly the late/no-stop outcome, not a CLEAN first stop. -/
private def bankTrialRenewalColdNoStopThrough
    {X : Type} {n : Nat}
    (next : X → Fin n → X) (target : X → Prop) :
    Nat → X → List (Fin n) → Prop
  | 0, z, _ => ¬ target z
  | _ + 1, _, [] => False
  | w + 1, z, e :: tail =>
      ¬ target z ∧
        bankTrialRenewalColdNoStopThrough next target
          w (next z e) tail

/-- A word that has not reached the target through W costs at
least W in the censored first-hit numerator. No closure assumption
and no distributional independence is needed for this direction. -/
private theorem bankTrialRenewalColdNoStopWordCost
    {X : Type} {n : Nat}
    (next : X → Fin n → X) (target : X → Prop) :
    ∀ (W : Nat) (z : X) (word : List (Fin n)),
      W ≤ word.length →
      bankTrialRenewalColdNoStopThrough next target W z word →
      W ≤ costWord next target z word := by
  intro W
  induction W with
  | zero =>
      intro z word _ _
      exact Nat.zero_le _
  | succ W ih =>
      intro z word hlen hnstop
      cases word with
      | nil =>
          simp only [List.length_nil] at hlen
          omega
      | cons e tail =>
          change ¬ target z ∧
            bankTrialRenewalColdNoStopThrough next target
              W (next z e) tail at hnstop
          obtain ⟨hactive, htail⟩ := hnstop
          have hlenTail : W ≤ tail.length := by
            simp only [List.length_cons] at hlen
            omega
          have hc := ih (next z e) tail hlenTail htail
          simp only [costWord,
            K2FiniteSafeEliminationExpected.rawCost,
            if_neg hactive]
          first
          | omega
          | (simp only [costWord] at hc; omega)
          | (unfold costWord at hc; omega)

/-- Original length-T scheduler mass of trajectories with no cold
first stop by W (and enough letters for the W-prefix). The length
guard makes its Markov inequality pointwise on arbitrary words. -/
noncomputable def bankTrialRenewalColdLateMass {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T W : Nat) : Nat := by
  classical
  exact Prob.scheduleSum n T (fun word =>
    if W ≤ word.length ∧
      bankTrialRenewalColdNoStopThrough
        (Counter.resetClockBankColdNext ring root hsp)
        (Counter.resetClockBankColdTerminal ring root)
        W (Counter.resetClockBankColdStart ring root x) word
    then 1 else 0)

/-- (b), exact censored Markov step. Every late trajectory is
charged W actual interactions in the original cold costNumerator. -/
theorem bankTrialRenewalColdLateMassMarkov {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T W : Nat) :
    W * bankTrialRenewalColdLateMass
      ring root hsp x T W ≤
    costNumerator
      (Counter.resetClockBankColdNext ring root hsp)
      (Counter.resetClockBankColdTerminal ring root)
      (Counter.resetClockBankColdStart ring root x) T := by
  classical
  calc
    W * bankTrialRenewalColdLateMass ring root hsp x T W =
      Prob.scheduleSum n T (fun word =>
        W * (if W ≤ word.length ∧
          bankTrialRenewalColdNoStopThrough
            (Counter.resetClockBankColdNext ring root hsp)
            (Counter.resetClockBankColdTerminal ring root)
            W (Counter.resetClockBankColdStart ring root x) word
          then 1 else 0)) := by
            unfold bankTrialRenewalColdLateMass
            exact (bankTrialSuccessScheduleSumScale n T W _).symm
    _ ≤ Prob.scheduleSum n T (costWord
      (Counter.resetClockBankColdNext ring root hsp)
      (Counter.resetClockBankColdTerminal ring root)
      (Counter.resetClockBankColdStart ring root x)) := by
        apply bankTrialProbabilityScheduleSumMono n T
        intro word
        by_cases hlate : W ≤ word.length ∧
          bankTrialRenewalColdNoStopThrough
            (Counter.resetClockBankColdNext ring root hsp)
            (Counter.resetClockBankColdTerminal ring root)
            W (Counter.resetClockBankColdStart ring root x) word
        · simp only [if_pos hlate, Nat.mul_one]
          exact bankTrialRenewalColdNoStopWordCost
            (Counter.resetClockBankColdNext ring root hsp)
            (Counter.resetClockBankColdTerminal ring root)
            W (Counter.resetClockBankColdStart ring root x)
            word hlate.1 hlate.2
        · simp only [if_neg hlate, Nat.mul_zero]
          exact Nat.zero_le _
    _ = costNumerator
      (Counter.resetClockBankColdNext ring root hsp)
      (Counter.resetClockBankColdTerminal ring root)
      (Counter.resetClockBankColdStart ring root x) T := rfl

/-- (b), the cold stopped-cost coefficient is already reserved
in the earlier accounting; this is the same cost, not a second unconditional charge. -/
theorem bankTrialRenewalColdLateMassReserve {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T W : Nat) :
    W * bankTrialRenewalColdLateMass ring root hsp x T W ≤
      n ^ T *
        (n * bankTrialRenewalIndexColdCharge (ceilLogTwo n)) := by
  exact Nat.le_trans
    (bankTrialRenewalColdLateMassMarkov
      ring root hsp x T W)
    (bankTrialRenewalColdCostInsideReserve
      ring root hsp x T)

/-- The window quota gives the denominator-cleared version
of the same late/no-stop Markov event. -/
theorem bankTrialRenewalColdLateMassRatio {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (R T W : Nat)
    (hradius : (256 * R) ^ 2 ≤ n ∧
      n < (256 * (R + 1)) ^ 2)
    (hW : W = R * n / 8) :
    255 * (W * bankTrialRenewalColdLateMass
        ring root hsp x T W) ≤
      2 * W * n ^ T := by
  have hlate := bankTrialRenewalColdLateMassMarkov
    ring root hsp x T W
  have hreserve := bankTrialRenewalColdMarkovReserve
    ring root hn hsp x R T W hradius hW
  exact Nat.le_trans (Nat.mul_le_mul_left 255 hlate)
    hreserve

/-- The exact hdefect condition for the ACTUAL cold first-stop
prefix list, not a condition on arbitrary post-stop observer states.
supplies a frozen support-subword version. Extending it to
all real prefixes requires the supported-prefix/physical coupling. -/
def BankTrialRenewalColdNoDefectFirstStops {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T : Nat) : Prop :=
  ∀ cut : List (Fin n),
    cut ∈ Prob.firstStoppedPrefixes
      (Counter.resetClockBankColdNext ring root hsp)
      (bankTrialRenewalColdStop ring root)
      T [] (Counter.resetClockBankColdStart ring root x) →
    ∀ D : Counter.Config (ceilLogTwo n) n,
      Prob.stoppedTapeRun
        (Counter.resetClockBankColdNext ring root hsp)
        cut (Counter.resetClockBankColdStart ring root x) ≠
          .inr (.inr (D, .defect))

/-- (c), pointwise original-tape outcome credit: a grant cut
inside W has weight one and a defect cut has weight zero.
The separate hdefect predicate above is required to delete
defect cylinders from a global mass partition. -/
theorem bankTrialRenewalColdGrantDefectWeights {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (D : Counter.Config q n)
    (W : Nat) (cut suffix : List (Fin n))
    (hcut : cut.length ≤ W) :
    bankTrialRenewalColdProxyWeight ring root W cut
      ((.inr (.inr (D, .grant)) :
        Counter.ResetClockBankColdState (q := q) ring root))
      suffix = 1 ∧
    bankTrialRenewalColdProxyWeight ring root W cut
      ((.inr (.inr (D, .defect)) :
        Counter.ResetClockBankColdState (q := q) ring root))
      suffix = 0 := by
  exact ⟨bankTrialRenewalColdGrantWithinWindow
    ring root D W cut suffix hcut,
    bankTrialRenewalColdProxyDefectZero
      ring root D W cut suffix⟩

end L3

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
Authentic first-stop partition, with DEFECT cylinders retained.

The final C.16 index-payoff theorem is NOT asserted below.
-/


end L3

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
Authentic first-stop partition, with DEFECT cylinders retained.

The final C.16 index-payoff theorem is NOT asserted below.
-/

/-- The actual first-stop mass without an outcome label, truncated
at elapsed W, on the ORIGINAL horizon T. -/
private noncomputable def bankTrialColdStopUnitMass
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (T W : Nat) (pre : List (Fin n)) (z : X) : Nat :=
  ((Prob.firstStoppedPrefixes next stop T pre z).map
    (fun cut => if cut.length ≤ W then
      n ^ (T - cut.length) else 0)).sum

/-- Companion no-stop mass uses the censored prefix predicate.
The explicit length condition is important at arbitrary short tapes. -/
private noncomputable def bankTrialColdNoStopUnitMass
    {X : Type} {n : Nat}
    (next : X → Fin n → X) (target : X → Prop)
    (z : X) (T W : Nat) : Nat :=
  Prob.scheduleSum n T (fun word =>
    if W ≤ word.length ∧
      bankTrialRenewalColdNoStopThrough next target W z word
    then 1 else 0)

/-- Finite flatMap sum, not a Finset or an independent scheduler. -/
private theorem bankTrialColdFlatMapSum
    {U V : Type} (xs : List U) (ys : U → List V)
    (f : V → Nat) :
    ((xs.flatMap ys).map f).sum =
      (xs.map (fun a => ((ys a).map f).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [ih]

private theorem bankTrialColdStopUnitAtRoot
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (T W : Nat) (pre : List (Fin n)) (z : X)
    (hs : stop pre z = true) :
    bankTrialColdStopUnitMass next stop T W pre z =
      n ^ T := by
  unfold bankTrialColdStopUnitMass
  cases T with
  | zero => simp [Prob.firstStoppedPrefixes, hs]
  | succ t => simp [Prob.firstStoppedPrefixes, hs]

private theorem bankTrialColdStopUnitZeroOfNonstop
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (T : Nat) (pre : List (Fin n)) (z : X)
    (hs : stop pre z = false) :
    bankTrialColdStopUnitMass next stop T 0 pre z = 0 := by
  unfold bankTrialColdStopUnitMass
  cases T with
  | zero =>
      simp [Prob.firstStoppedPrefixes, hs]
  | succ t =>
      simp only [Prob.firstStoppedPrefixes, hs,
        Bool.false_eq_true, if_false]
      rw [bankTrialColdFlatMapSum]
      simp only [List.map_ofFn, Function.comp_def]
      have hzero (e : Fin n) :
          (((Prob.firstStoppedPrefixes next stop t
            (pre ++ [e]) (next z e)).map (List.cons e)).map
              (fun cut => if cut.length ≤ 0 then
                n ^ ((t + 1) - cut.length) else 0)).sum = 0 := by
        simp only [List.map_map, Function.comp_def]
        have hf :
            (fun u : List (Fin n) =>
              if (e :: u).length ≤ 0 then
                n ^ ((t + 1) - (e :: u).length) else 0) =
            (fun _ => 0) := by
          funext u
          have hnot : ¬ (e :: u).length ≤ 0 := by simp
          simp only [if_neg hnot]
        rw [hf]
        induction Prob.firstStoppedPrefixes next stop t
            (pre ++ [e]) (next z e) with
        | nil => rfl
        | cons u us ih =>
            simp only [List.map_cons, List.sum_cons, ih,
              Nat.zero_add]
      rw [ofFn_sum_eq _ (fun _ : Fin n => 0) hzero]
      simp only [ofFn_sum_const, Nat.mul_zero]


/-- An additional consumed source letter shifts both the remaining
horizon and the cutoff by one, without changing the suffix mass. -/
private theorem bankTrialColdStopUnitStep
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (T W : Nat) (pre : List (Fin n)) (z : X)
    (hs : stop pre z = false) :
    bankTrialColdStopUnitMass next stop
        (T + 1) (W + 1) pre z =
      (List.ofFn (fun e : Fin n =>
        bankTrialColdStopUnitMass next stop T W
          (pre ++ [e]) (next z e))).sum := by
  unfold bankTrialColdStopUnitMass
  simp only [Prob.firstStoppedPrefixes, hs,
    Bool.false_eq_true, if_false]
  rw [bankTrialColdFlatMapSum]
  simp only [List.map_ofFn]
  apply ofFn_sum_eq
  intro e
  simp only [List.map_map, Function.comp_def]
  have hfun :
      (fun u : List (Fin n) =>
        if (e :: u).length ≤ W + 1 then
          n ^ ((T + 1) - (e :: u).length) else 0) =
      (fun u : List (Fin n) =>
        if u.length ≤ W then n ^ (T - u.length) else 0) := by
    funext u
    by_cases hu : u.length ≤ W
    · have hc : (e :: u).length ≤ W + 1 := by
        simp only [List.length_cons]
        omega
      simp only [if_pos hc, if_pos hu]
      have hsub :
          (T + 1) - (e :: u).length = T - u.length := by
        simp only [List.length_cons]
        omega
      rw [hsub]
    · have hc : ¬ (e :: u).length ≤ W + 1 := by
        simp only [List.length_cons]
        omega
      simp only [if_neg hc, if_neg hu]
  rw [hfun]

private theorem bankTrialColdNoStopUnitAtRoot
    {X : Type} {n : Nat}
    (next : X → Fin n → X) (target : X → Prop)
    (z : X) (T W : Nat) (htarget : target z) :
    bankTrialColdNoStopUnitMass next target z T W = 0 := by
  unfold bankTrialColdNoStopUnitMass
  have hf :
      (fun word : List (Fin n) =>
        if W ≤ word.length ∧
          bankTrialRenewalColdNoStopThrough next target W z word
        then 1 else 0) =
      (fun _ : List (Fin n) => 0) := by
    funext word
    cases W with
    | zero =>
        simp [bankTrialRenewalColdNoStopThrough, htarget]
    | succ w =>
        cases word with
        | nil => simp [bankTrialRenewalColdNoStopThrough]
        | cons e tail =>
            simp [bankTrialRenewalColdNoStopThrough, htarget]
  rw [hf, bankTrialProbabilityScheduleSumConst]
  simp

private theorem bankTrialColdNoStopUnitZeroWindow
    {X : Type} {n : Nat}
    (next : X → Fin n → X) (target : X → Prop)
    (z : X) (T : Nat) (hn : ¬ target z) :
    bankTrialColdNoStopUnitMass next target z T 0 =
      n ^ T := by
  unfold bankTrialColdNoStopUnitMass
  have hf :
      (fun word : List (Fin n) =>
        if 0 ≤ word.length ∧
          bankTrialRenewalColdNoStopThrough next target 0 z word
        then 1 else 0) =
      (fun _ : List (Fin n) => 1) := by
    funext word
    simp [bankTrialRenewalColdNoStopThrough, hn]
  rw [hf, bankTrialProbabilityScheduleSumConst]
  simp

private theorem bankTrialColdNoStopUnitStep
    {X : Type} {n : Nat}
    (next : X → Fin n → X) (target : X → Prop)
    (z : X) (T W : Nat) (hn : ¬ target z) :
    bankTrialColdNoStopUnitMass next target z
        (T + 1) (W + 1) =
      (List.ofFn (fun e : Fin n =>
        bankTrialColdNoStopUnitMass next target
          (next z e) T W)).sum := by
  unfold bankTrialColdNoStopUnitMass
  rw [bankTrialProbabilityScheduleSumFirst]
  apply ofFn_sum_eq
  intro e
  apply congrArg (Prob.scheduleSum n T)
  funext tail
  have hlen :
      (W + 1 ≤ (e :: tail).length) ↔ W ≤ tail.length := by
    simp only [List.length_cons]
    omega
  have hno :
      bankTrialRenewalColdNoStopThrough next target
          (W + 1) z (e :: tail) ↔
        bankTrialRenewalColdNoStopThrough next target
          W (next z e) tail := by
    change (¬ target z ∧
        bankTrialRenewalColdNoStopThrough next target
          W (next z e) tail) ↔ _
    simp [hn]
  have heq :
      (W + 1 ≤ (e :: tail).length ∧
        bankTrialRenewalColdNoStopThrough next target
          (W + 1) z (e :: tail)) =
      (W ≤ tail.length ∧
        bankTrialRenewalColdNoStopThrough next target
          W (next z e) tail) := by
    apply propext
    exact and_congr hlen hno
  by_cases hl :
      W + 1 ≤ (e :: tail).length ∧
        bankTrialRenewalColdNoStopThrough next target
          (W + 1) z (e :: tail)
  · have hr :
        W ≤ tail.length ∧
          bankTrialRenewalColdNoStopThrough next target
            W (next z e) tail := Eq.mp heq hl
    simp only [if_pos hl, if_pos hr]
  · have hr :
        ¬ (W ≤ tail.length ∧
          bankTrialRenewalColdNoStopThrough next target
            W (next z e) tail) := by
      intro h
      exact hl (Eq.mp heq.symm h)
    simp only [if_neg hl, if_neg hr]


/-- Exact stopped-tree partition with an arbitrary sound Boolean
terminal test. Every original length-T tape either first stops
by W or survives through W. No absorbing-state assumption,
independence or defect suppression is used. -/
private theorem bankTrialColdGenericPrefixPartition
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (target : X → Prop)
    (hreflect : ∀ pre z, stop pre z = true ↔ target z) :
    ∀ (T W : Nat) (pre : List (Fin n)) (z : X),
      W ≤ T →
      bankTrialColdStopUnitMass next stop T W pre z +
        bankTrialColdNoStopUnitMass next target z T W =
          n ^ T := by
  intro T
  induction T with
  | zero =>
      intro W pre z hWT
      have hW : W = 0 := by omega
      subst W
      cases hs : stop pre z with
      | true =>
          have ht : target z := (hreflect pre z).mp hs
          rw [bankTrialColdStopUnitAtRoot next stop
              0 0 pre z hs,
            bankTrialColdNoStopUnitAtRoot next target z 0 0 ht]
          simp
      | false =>
          have ht : ¬ target z := by
            intro h
            have htrue := (hreflect pre z).mpr h
            rw [hs] at htrue
            cases htrue
          rw [bankTrialColdStopUnitZeroOfNonstop next stop
              0 pre z hs,
            bankTrialColdNoStopUnitZeroWindow next target z 0 ht]
          simp
  | succ T ih =>
      intro W pre z hWT
      cases W with
      | zero =>
          cases hs : stop pre z with
          | true =>
              have ht : target z := (hreflect pre z).mp hs
              rw [bankTrialColdStopUnitAtRoot next stop
                  (T + 1) 0 pre z hs,
                bankTrialColdNoStopUnitAtRoot next target z
                  (T + 1) 0 ht]
              simp
          | false =>
              have ht : ¬ target z := by
                intro h
                have htrue := (hreflect pre z).mpr h
                rw [hs] at htrue
                cases htrue
              rw [bankTrialColdStopUnitZeroOfNonstop next stop
                  (T + 1) pre z hs,
                bankTrialColdNoStopUnitZeroWindow next target z
                  (T + 1) ht]
              simp
      | succ W =>
          have hW : W ≤ T := by omega
          cases hs : stop pre z with
          | true =>
              have ht : target z := (hreflect pre z).mp hs
              rw [bankTrialColdStopUnitAtRoot next stop
                  (T + 1) (W + 1) pre z hs,
                bankTrialColdNoStopUnitAtRoot next target z
                  (T + 1) (W + 1) ht]
              simp
          | false =>
              have ht : ¬ target z := by
                intro h
                have htrue := (hreflect pre z).mpr h
                rw [hs] at htrue
                cases htrue
              rw [bankTrialColdStopUnitStep next stop
                T W pre z hs,
                bankTrialColdNoStopUnitStep next target
                  z T W ht]
              calc
                (List.ofFn (fun e : Fin n =>
                    bankTrialColdStopUnitMass next stop T W
                      (pre ++ [e]) (next z e))).sum +
                  (List.ofFn (fun e : Fin n =>
                    bankTrialColdNoStopUnitMass next target
                      (next z e) T W)).sum =
                  (List.ofFn (fun e : Fin n =>
                    bankTrialColdStopUnitMass next stop T W
                        (pre ++ [e]) (next z e) +
                      bankTrialColdNoStopUnitMass next target
                        (next z e) T W)).sum := by
                    rw [ofFn_sum_add]
                _ = (List.ofFn (fun _ : Fin n => n ^ T)).sum := by
                    apply ofFn_sum_eq
                    intro e
                    exact ih W (pre ++ [e]) (next z e) hW
                _ = n ^ (T + 1) := by
                    rw [ofFn_sum_const]
                    simp only [Nat.mul_one, Nat.pow_succ,
                      Nat.mul_comm]

/-- Real GRANT-labelled first-stop cylinder mass, with the same
firstStoppedPrefixes and original horizon as the earlier CLEAN mass. -/
noncomputable def bankTrialRenewalColdEarlyGrantMass {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T W : Nat) : Nat :=
  ((Prob.firstStoppedPrefixes
    (Counter.resetClockBankColdNext ring root hsp)
    (bankTrialRenewalColdStop ring root)
    T [] (Counter.resetClockBankColdStart ring root x)).map
    (fun cut =>
      if cut.length ≤ W then
        match Prob.stoppedTapeRun
            (Counter.resetClockBankColdNext ring root hsp)
            cut (Counter.resetClockBankColdStart ring root x) with
        | .inr (.inr (_, .grant)) => n ^ (T - cut.length)
        | _ => 0
      else 0)).sum

/-- The requested DEFECT cylinder mass. A defect is charged rather
than assumed absent: the earlier frozen support-subword proof is NOT
a proof that the full cold scheduler cannot encounter defects. -/
noncomputable def bankTrialRenewalColdDefectMass {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T W : Nat) : Nat :=
  ((Prob.firstStoppedPrefixes
    (Counter.resetClockBankColdNext ring root hsp)
    (bankTrialRenewalColdStop ring root)
    T [] (Counter.resetClockBankColdStart ring root x)).map
    (fun cut =>
      if cut.length ≤ W then
        match Prob.stoppedTapeRun
            (Counter.resetClockBankColdNext ring root hsp)
            cut (Counter.resetClockBankColdStart ring root x) with
        | .inr (.inr (_, .defect)) => n ^ (T - cut.length)
        | _ => 0
      else 0)).sum

/-- A finite list decomposes into three named outcome sums if each
element has exactly one of those outcomes. Arithmetic is over
opaque naturals; no protocol powers are exposed to omega. -/
private theorem bankTrialColdSumThree {α : Type}
    (xs : List α) (a b c total : α → Nat)
    (h : ∀ z, z ∈ xs →
      total z = a z + b z + c z) :
    (xs.map total).sum =
      (xs.map a).sum + (xs.map b).sum +
        (xs.map c).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht : ∀ z, z ∈ xs →
          total z = a z + b z + c z := by
        intro z hz
        exact h z (by simp [hz])
      have hsum := ih ht
      simp only [List.map_cons, List.sum_cons]
      rw [hx, hsum]
      omega

/-- Every authenticated first-stop cut is exactly CLEAN, GRANT or
DEFECT, so its unit cylinder belongs to precisely one of the three
labelled sums. The assertion is only on actual enumerated cuts. -/
private theorem bankTrialColdLabelledSum
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T W : Nat) :
    bankTrialColdStopUnitMass
        (Counter.resetClockBankColdNext ring root hsp)
        (bankTrialRenewalColdStop ring root)
        T W [] (Counter.resetClockBankColdStart ring root x) =
      bankTrialRenewalColdEarlyCleanSum
          ring root hsp x T W
          (fun cut _ => n ^ (T - cut.length)) +
        bankTrialRenewalColdEarlyGrantMass ring root hsp x T W +
        bankTrialRenewalColdDefectMass ring root hsp x T W := by
  unfold bankTrialColdStopUnitMass
    bankTrialRenewalColdEarlyCleanSum
    bankTrialRenewalColdEarlyGrantMass
    bankTrialRenewalColdDefectMass
  apply bankTrialColdSumThree
  intro cut hmem
  by_cases hcut : cut.length ≤ W
  · have hterm := bankTrialRenewalColdAuthenticFirstStop
      ring root hsp x T cut hmem
    obtain ⟨D, reason, hstate⟩ :=
      bankTrialRenewalColdTerminalShape
        ring root
        (Prob.stoppedTapeRun
          (Counter.resetClockBankColdNext ring root hsp)
          cut (Counter.resetClockBankColdStart ring root x))
        hterm
    cases reason with
    | clean => simp [hcut, hstate]
    | grant => simp [hcut, hstate]
    | defect => simp [hcut, hstate]
  · simp [hcut]

/-- (1) EXACT disjoint partition of the original length-T tapes.
Defect is a genuine fourth contribution, not an hdefect assumption.
The proof is a stopped-tree counting identity, not a Markov bound. -/
theorem bankTrialRenewalColdFirstStopPartition {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T W : Nat) (hwindow : W ≤ T) :
    n ^ T =
      bankTrialRenewalColdEarlyCleanSum ring root hsp x T W
          (fun cut _ => n ^ (T - cut.length)) +
        bankTrialRenewalColdEarlyGrantMass ring root hsp x T W +
        bankTrialRenewalColdDefectMass ring root hsp x T W +
        bankTrialRenewalColdLateMass ring root hsp x T W := by
  have hreflection (pre : List (Fin n))
      (z : Counter.ResetClockBankColdState
        (q := ceilLogTwo n) ring root) :
      bankTrialRenewalColdStop ring root pre z = true ↔
        Counter.resetClockBankColdTerminal ring root z :=
    bankTrialRenewalColdStopCorrect ring root pre z
  have htree := bankTrialColdGenericPrefixPartition
    (Counter.resetClockBankColdNext ring root hsp)
    (bankTrialRenewalColdStop ring root)
    (Counter.resetClockBankColdTerminal ring root)
    hreflection T W [] (Counter.resetClockBankColdStart ring root x)
    hwindow
  have hlabelled := bankTrialColdLabelledSum
    ring root hsp x T W
  have hlate :
      bankTrialColdNoStopUnitMass
          (Counter.resetClockBankColdNext ring root hsp)
          (Counter.resetClockBankColdTerminal ring root)
          (Counter.resetClockBankColdStart ring root x)
          T W =
        bankTrialRenewalColdLateMass ring root hsp x T W := rfl
  rw [hlabelled, hlate] at htree
  simpa only [Nat.add_assoc] using htree.symm

/-- Genuine hdefect on the ACTUAL first-stop list eliminates the
defect term; frozen support-subword evidence alone does not. -/
theorem bankTrialRenewalColdDefectMassZero {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T W : Nat)
    (hdefect : BankTrialRenewalColdNoDefectFirstStops
      ring root hsp x T) :
    bankTrialRenewalColdDefectMass
      ring root hsp x T W = 0 := by
  unfold bankTrialRenewalColdDefectMass
  have hzero (cut : List (Fin n))
      (hmem : cut ∈ Prob.firstStoppedPrefixes
        (Counter.resetClockBankColdNext ring root hsp)
        (bankTrialRenewalColdStop ring root)
        T [] (Counter.resetClockBankColdStart ring root x)) :
      (if cut.length ≤ W then
        match Prob.stoppedTapeRun
            (Counter.resetClockBankColdNext ring root hsp)
            cut (Counter.resetClockBankColdStart ring root x) with
        | .inr (.inr (_, .defect)) => n ^ (T - cut.length)
        | _ => 0
      else 0) = 0 := by
    by_cases hc : cut.length ≤ W
    · cases hz : Prob.stoppedTapeRun
          (Counter.resetClockBankColdNext ring root hsp)
          cut (Counter.resetClockBankColdStart ring root x) with
      | inl z => simp [hc, hz]
      | inr y =>
          cases y with
          | inl a => simp [hc, hz]
          | inr outcome =>
              cases outcome with
              | mk D reason =>
                  cases reason with
                  | clean => simp [hc, hz]
                  | grant => simp [hc, hz]
                  | defect =>
                      exact False.elim
                        (hdefect cut hmem D hz)
    · simp [hc]
  have hsum :
      ∀ (xs : List (List (Fin n))),
        (∀ cut, cut ∈ xs →
          cut ∈ Prob.firstStoppedPrefixes
            (Counter.resetClockBankColdNext ring root hsp)
            (bankTrialRenewalColdStop ring root)
            T [] (Counter.resetClockBankColdStart ring root x)) →
        (xs.map (fun cut =>
          if cut.length ≤ W then
            match Prob.stoppedTapeRun
                (Counter.resetClockBankColdNext ring root hsp)
                cut (Counter.resetClockBankColdStart ring root x) with
            | .inr (.inr (_, .defect)) =>
                n ^ (T - cut.length)
            | _ => 0
          else 0)).sum = 0 := by
    intro xs
    induction xs with
    | nil =>
        intro _
        simp
    | cons cut xs ih =>
        intro h
        have hc := hzero cut (h cut (by simp))
        have ht : ∀ v, v ∈ xs →
            v ∈ Prob.firstStoppedPrefixes
              (Counter.resetClockBankColdNext ring root hsp)
              (bankTrialRenewalColdStop ring root)
              T [] (Counter.resetClockBankColdStart ring root x) := by
          intro v hv
          exact h v (by simp [hv])
        simp only [List.map_cons, List.sum_cons]
        rw [hc, ih ht]
  exact hsum _ (fun cut h => h)

private theorem bankTrialColdCensoredArithmetic
    (W N early late : Nat)
    (hpartition : N = early + late)
    (hmarkov : 255 * (W * late) ≤ 2 * W * N) :
    253 * W * N ≤ 255 * W * early := by
  have hdecomp :
      255 * (W * N) =
        255 * (W * early) + 255 * (W * late) := by
    rw [hpartition, Nat.mul_add, Nat.mul_add]
  have hb :
      255 * (W * N) ≤
        255 * (W * early) + 2 * (W * N) := by
    calc
      _ = 255 * (W * early) + 255 * (W * late) := hdecomp
      _ ≤ 255 * (W * early) + 2 * W * N :=
        Nat.add_le_add_left hmarkov _
      _ = 255 * (W * early) + 2 * (W * N) := by
        simp only [Nat.mul_assoc]
  have hcoef : (255 : Nat) = 253 + 2 := by decide
  rw [hcoef, Nat.add_mul] at hb
  have hnormal :
      253 * (W * N) ≤ 255 * (W * early) := by
    omega
  simpa only [Nat.mul_assoc] using hnormal


/-- (2) The exact early-stop mass remaining after the cold
censored correction. This is a rigorously named arithmetic cost:
only 253/255 of the entrance mass is available without an
additional sharper estimate. -/
theorem bankTrialRenewalColdEarlyMassAfterCensor {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (R T W : Nat)
    (hradius : (256 * R) ^ 2 ≤ n ∧
      n < (256 * (R + 1)) ^ 2)
    (hW : W = R * n / 8)
    (hwindow : W ≤ T) :
    253 * W * n ^ T ≤
      255 * W *
        (bankTrialRenewalColdEarlyCleanSum
            ring root hsp x T W
            (fun cut _ => n ^ (T - cut.length)) +
          bankTrialRenewalColdEarlyGrantMass
            ring root hsp x T W +
          bankTrialRenewalColdDefectMass
            ring root hsp x T W) := by
  have hpartition := bankTrialRenewalColdFirstStopPartition
    ring root hsp x T W hwindow
  have hlate := bankTrialRenewalColdLateMassRatio
    ring root hn hsp x R T W hradius hW
  exact bankTrialColdCensoredArithmetic
    W (n ^ T)
    (bankTrialRenewalColdEarlyCleanSum
      ring root hsp x T W
      (fun cut _ => n ^ (T - cut.length)) +
     bankTrialRenewalColdEarlyGrantMass ring root hsp x T W +
     bankTrialRenewalColdDefectMass ring root hsp x T W)
    (bankTrialRenewalColdLateMass ring root hsp x T W)
    hpartition hlate

end L3

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
G13-INDEX-RENEWAL.
No unproved leaf. This restores the event mask lost in the
unconditional Clean cost and supplies true first-stop weighted
infrastructure. It does not assert the final cold-success theorem.
-/

/-- Additive stage sum, with the cold length multiplied ONLY by
the successful-index event. -/
private theorem bankTrialColdMaskedStageSum
    (cold : Nat) (f g : Nat → Nat) :
    ∀ H : Nat,
      bankTrialSuccessStageIndexSum
        (fun j => cold * f j + g j) H =
      cold * bankTrialSuccessStageIndexSum f H +
        bankTrialSuccessStageIndexSum g H := by
  intro H
  induction H with
  | zero =>
      rfl
  | succ k ih =>
      change bankTrialSuccessStageIndexSum
          (fun j => cold * f j + g j) k +
            (cold * f k + g k) =
        cold * (bankTrialSuccessStageIndexSum f k + f k) +
          (bankTrialSuccessStageIndexSum g k + g k)
      rw [ih, Nat.mul_add]
      omega

theorem bankTrialRenewalColdCleanMaskedWord {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (D : Counter.Config q n)
    (W L H : Nat) (cut suffix : List (Fin n)) :
    W * bankTrialSuccessStageIndexSum (fun j =>
      Prob.indicator (bankTrialRenewalPattern ring root
        (GrantBankReference.bankLocalReferenceStart ring root D)
        L j suffix)) H ≤
    W * bankTrialRenewalColdProxyWeight ring root W cut
      ((.inr (.inr (D, .clean)) :
        Counter.ResetClockBankColdState (q := q) ring root))
      suffix +
    bankTrialSuccessStageIndexSum (fun j =>
      cut.length * Prob.indicator (bankTrialRenewalPattern ring root
        (GrantBankReference.bankLocalReferenceStart ring root D)
        L j suffix) +
      bankTrialRenewalTau ring root
        (GrantBankReference.bankLocalReferenceStart ring root D)
        L j suffix) H := by
  have hone :=
    bankTrialRenewalPatternOneHot ring root
      (GrantBankReference.bankLocalReferenceStart ring root D)
      L H suffix
  have hcost :
      bankTrialSuccessStageIndexSum (fun j =>
        cut.length * Prob.indicator (bankTrialRenewalPattern ring root
          (GrantBankReference.bankLocalReferenceStart ring root D)
          L j suffix) +
        bankTrialRenewalTau ring root
          (GrantBankReference.bankLocalReferenceStart ring root D)
          L j suffix) H =
      cut.length * bankTrialSuccessStageIndexSum (fun j =>
        Prob.indicator (bankTrialRenewalPattern ring root
          (GrantBankReference.bankLocalReferenceStart ring root D)
          L j suffix)) H +
      bankTrialSuccessStageIndexSum (fun j =>
        bankTrialRenewalTau ring root
          (GrantBankReference.bankLocalReferenceStart ring root D)
          L j suffix) H :=
    bankTrialColdMaskedStageSum cut.length _ _ H
  by_cases hcut : cut.length ≤ W
  · by_cases hg : (D root).grant = true
    · have hproxy :
          bankTrialRenewalColdProxyWeight ring root W cut
            ((.inr (.inr (D, .clean)) :
              Counter.ResetClockBankColdState (q := q) ring root))
            suffix = 1 := by
        simp [bankTrialRenewalColdProxyWeight, hcut, hg]
      have hsum :
          W * bankTrialSuccessStageIndexSum (fun j =>
            Prob.indicator (bankTrialRenewalPattern ring root
              (GrantBankReference.bankLocalReferenceStart
                ring root D) L j suffix)) H ≤ W := by
        simpa only [Nat.mul_one] using
          (Nat.mul_le_mul_left W hone)
      rw [hproxy, hcost]
      simp only [Nat.mul_one]
      omega
    · have hproxy :
          bankTrialRenewalColdProxyWeight ring root W cut
            ((.inr (.inr (D, .clean)) :
              Counter.ResetClockBankColdState (q := q) ring root))
            suffix =
          Prob.indicator (bankTrialRenewalSuccessBy ring root
            (GrantBankReference.bankLocalReferenceStart ring root D)
            (W - cut.length) suffix) := by
        simp [bankTrialRenewalColdProxyWeight, hcut, hg]
      have hwindow :
          (W - cut.length) *
            bankTrialSuccessStageIndexSum (fun j =>
              Prob.indicator (bankTrialRenewalPattern ring root
                (GrantBankReference.bankLocalReferenceStart
                  ring root D) L j suffix)) H ≤
          (W - cut.length) *
            Prob.indicator (bankTrialRenewalSuccessBy ring root
              (GrantBankReference.bankLocalReferenceStart
                ring root D) (W - cut.length) suffix) +
          bankTrialSuccessStageIndexSum (fun j =>
            bankTrialRenewalTau ring root
              (GrantBankReference.bankLocalReferenceStart
                ring root D) L j suffix) H :=
        bankTrialRenewalWordWindow ring root
          (GrantBankReference.bankLocalReferenceStart ring root D)
          L (W - cut.length) H suffix
      have hsplit :
          W * bankTrialSuccessStageIndexSum (fun j =>
            Prob.indicator (bankTrialRenewalPattern ring root
              (GrantBankReference.bankLocalReferenceStart
                ring root D) L j suffix)) H =
          (W - cut.length) *
            bankTrialSuccessStageIndexSum (fun j =>
              Prob.indicator (bankTrialRenewalPattern ring root
                (GrantBankReference.bankLocalReferenceStart
                  ring root D) L j suffix)) H +
          cut.length *
            bankTrialSuccessStageIndexSum (fun j =>
              Prob.indicator (bankTrialRenewalPattern ring root
                (GrantBankReference.bankLocalReferenceStart
                  ring root D) L j suffix)) H := by
        calc
          _ = ((W - cut.length) + cut.length) *
                bankTrialSuccessStageIndexSum (fun j =>
                  Prob.indicator (bankTrialRenewalPattern ring root
                    (GrantBankReference.bankLocalReferenceStart
                      ring root D) L j suffix)) H := by
              rw [Nat.sub_add_cancel hcut]
          _ = _ := Nat.add_mul _ _ _
      have hprefixCharge :
          cut.length *
            bankTrialSuccessStageIndexSum (fun j =>
              Prob.indicator (bankTrialRenewalPattern ring root
                (GrantBankReference.bankLocalReferenceStart
                  ring root D) L j suffix)) H ≤ cut.length := by
        simpa only [Nat.mul_one] using
          (Nat.mul_le_mul_left cut.length hone)
      have hsuccessScale :
          (W - cut.length) *
            Prob.indicator (bankTrialRenewalSuccessBy ring root
              (GrantBankReference.bankLocalReferenceStart
                ring root D) (W - cut.length) suffix) ≤
          W *
            Prob.indicator (bankTrialRenewalSuccessBy ring root
              (GrantBankReference.bankLocalReferenceStart
                ring root D) (W - cut.length) suffix) :=
        Nat.mul_le_mul_right _
          (Nat.sub_le W cut.length)
      rw [hproxy, hsplit, hcost]
      omega
  · have hproxy :
        bankTrialRenewalColdProxyWeight ring root W cut
          ((.inr (.inr (D, .clean)) :
            Counter.ResetClockBankColdState (q := q) ring root))
          suffix = 0 := by
      simp [bankTrialRenewalColdProxyWeight, hcut]
    have hsum :
        W * bankTrialSuccessStageIndexSum (fun j =>
          Prob.indicator (bankTrialRenewalPattern ring root
            (GrantBankReference.bankLocalReferenceStart
              ring root D) L j suffix)) H ≤ W := by
      simpa only [Nat.mul_one] using
        (Nat.mul_le_mul_left W hone)
    have hlate : W ≤ cut.length := by omega
    have hscaled :
        W * bankTrialSuccessStageIndexSum (fun j =>
          Prob.indicator (bankTrialRenewalPattern ring root
            (GrantBankReference.bankLocalReferenceStart ring root D)
            L j suffix)) H ≤
        cut.length * bankTrialSuccessStageIndexSum (fun j =>
          Prob.indicator (bankTrialRenewalPattern ring root
            (GrantBankReference.bankLocalReferenceStart ring root D)
            L j suffix)) H :=
      Nat.mul_le_mul_right _ hlate
    rw [hproxy, hcost]
    simp only [Nat.mul_zero, Nat.zero_add]
    exact Nat.le_trans hscaled (Nat.le_add_right _ _)


end L3

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
No assumptions are introduced by definition:
L1 is the explicit Prop interface; the L2 theorem is conditional
on a proof of that exact L1.
-/

/-- L1, EXACT proposed cold first-stop C.16 inequality.
It is a Prop interface, NOT an asserted theorem or an axiom.
The only difference from the Clean window is the cold carrier,
the proxy-plus-defect mass, and the cold C.2+C.3 coefficient. -/
def BankTrialRenewalColdClearedWindowProperty {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (L H T W : Nat) : Prop :=
  W * (2 ^ (compileAdvice (ceilLogTwo n)).K) * n ^ T *
    bankTrialSuccessStageIndexSum (fun j =>
      (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K -
        L - 2 ^ (compileAdvice (ceilLogTwo n)).K *
          ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n))) ^ j *
      (1023 * L) *
      (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K)) ^
        (H - (j + 1))) H ≤
  (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K)) ^ H *
    (W * (2 ^ (compileAdvice (ceilLogTwo n)).K) *
      (bankTrialRenewalColdProxyMass ring root hsp x T W +
       bankTrialRenewalColdDefectMass ring root hsp x T W) +
     n ^ T * bankTrialSuccessStageIndexSum (fun j =>
       n * ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
          5 * (compileAdvice (ceilLogTwo n)).b + 13) +
          bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
          j * bankTrialRenewalIndexStepCharge (ceilLogTwo n))) H)

/-- The earlier arithmetic step, transported literally to L1.
The separate hL1 premise prevents using an unfinished global
cold first-stop inequality as an assumed proof leaf. -/
theorem bankTrialRenewalColdSuccessMassLower_ofClearedWindow
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (hlarge :
      2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (R L T W : Nat)
    (hradius : (256 * R) ^ 2 ≤ n ∧
      n < (256 * (R + 1)) ^ 2)
    (hW : W = R * n / 8)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold
      n (ceilLogTwo n) ≤ L)
    (hwindow : W ≤ T)
    (hbudgetCold :
      W + bankTrialRenewalIndexWindowCount
        n (ceilLogTwo n) W * L ≤ T)
    (hL1 : BankTrialRenewalColdClearedWindowProperty
      ring root hsmall x L
      (bankTrialRenewalIndexWindowCount
        n (ceilLogTwo n) W) T W) :
    51279921 * W * n ^ T ≤
      104857600 * (8 * (compileAdvice (ceilLogTwo n)).b + 13) *
        n * 2 ^ (compileAdvice (ceilLogTwo n)).K *
        (bankTrialRenewalColdProxyMass ring root hsmall x T W +
         bankTrialRenewalColdDefectMass ring root hsmall x T W) := by
  have hq : 3 ≤ ceilLogTwo n := by
    have hspec := (ceilLogTwo_spec n (by omega)).2
    by_cases hc : ceilLogTwo n ≤ 2
    · have hp := Nat.pow_le_pow_right
        (by decide : 0 < (2 : Nat)) hc
      have hfour : (2 : Nat) ^ 2 = 4 := by decide
      omega
    · omega
  have hpositive :
      0 < (compileAdvice (ceilLogTwo n)).K := by
    change 0 < 2 * ceilLogTwo n +
      productionKappa (ceilLogTwo n)
    omega
  have hK :
      (compileAdvice (ceilLogTwo n)).K <
        2 ^ (compileAdvice (ceilLogTwo n)).b :=
    Nat.lt_trans (Nat.lt_succ_self _)
      (compileAdvice_K_lt_two_pow_b (ceilLogTwo n) hq)
  have hquota := bankTrialRenewalIndexCompiledQuotas
    n R W hn hsmall hradius hW
  have hf :
      0 < n * bankTrialRenewalIndexStepCharge
        (ceilLogTwo n) := by
    apply Nat.mul_pos (by omega)
    unfold bankTrialRenewalIndexStepCharge
    omega
  have hquotaExpanded :
      n * bankTrialRenewalIndexColdCharge (ceilLogTwo n) +
        22517 * (n * bankTrialRenewalIndexStepCharge
          (ceilLogTwo n)) ≤ W := by
    simpa only [Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm] using hquota.2
  have hWpos : 0 < W := by
    have ht : 0 < 22517 *
        (n * bankTrialRenewalIndexStepCharge (ceilLogTwo n)) :=
      Nat.mul_pos (by decide) hf
    omega
  have hCle :
      n * bankTrialRenewalIndexColdCharge (ceilLogTwo n) ≤ W := by
    omega
  have hFloorBudget :
      22517 * (n * bankTrialRenewalIndexStepCharge
        (ceilLogTwo n)) ≤
      W - n * bankTrialRenewalIndexColdCharge
        (ceilLogTwo n) := by
    have hsub := Nat.sub_add_cancel hCle
    omega
  have hFloor :
      22517 ≤ bankTrialRenewalIndexWindowCount
        n (ceilLogTwo n) W := by
    unfold bankTrialRenewalIndexWindowCount
    exact bankTrialRenewalIndexFloorLower
      (W - n * bankTrialRenewalIndexColdCharge (ceilLogTwo n))
      (n * bankTrialRenewalIndexStepCharge (ceilLogTwo n))
      22517 hf hFloorBudget
  have hcover :
      (2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
        5 * (compileAdvice (ceilLogTwo n)).b + 13) +
          bankTrialRenewalIndexZeroCharge (ceilLogTwo n) ≤
        bankTrialRenewalIndexColdCharge (ceilLogTwo n) := by
    calc
      _ = bankTrialRenewalIndexColdCharge (ceilLogTwo n) :=
        (bankTrialRenewalColdIndexChargeSplit (ceilLogTwo n)).symm
      _ ≤ _ := Nat.le_refl _
  have hcoverScaled :=
    Nat.mul_le_mul_left n hcover
  have hPpos :
      0 < 2 ^ (compileAdvice (ceilLogTwo n)).K :=
    Nat.two_pow_pos _
  have hBasePos :
      0 < 1024 * 2 ^ (compileAdvice (ceilLogTwo n)).K *
        ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n) :=
    Nat.mul_pos (Nat.mul_pos (by decide) hPpos)
      (Nat.mul_pos (by omega) (by omega))
  have hCutPos :
      0 < bankTrialRenewalWonCutoffThreshold
        n (ceilLogTwo n) := by
    have hbase :
        1024 * 2 ^ (compileAdvice (ceilLogTwo n)).K *
          ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n) ≤
        bankTrialRenewalWonCutoffThreshold
          n (ceilLogTwo n) := by
      unfold bankTrialRenewalWonCutoffThreshold
      exact Nat.le_max_right _ _
    exact Nat.lt_of_lt_of_le hBasePos hbase
  have hLpos : 0 < L := by
    have hm := Nat.mul_pos
      (by decide : 0 < (1024 : Nat)) hCutPos
    omega
  have hdenpos :
      0 < 1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K) :=
    Nat.mul_pos (by decide) (Nat.mul_pos hLpos hPpos)
  have hGap := bankTrialRenewalIndexCompiledGeometricBudget
    n R W
    (bankTrialRenewalIndexColdCharge (ceilLogTwo n))
    L hn hradius.1
    (bankTrialRenewalIndexConsumerWindowCap n R W hW) hL
  have hGapActual :
      bankTrialRenewalIndexWindowCount n (ceilLogTwo n) W *
        (1024 * (L + 2 ^ (compileAdvice (ceilLogTwo n)).K *
          ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n))) ≤
        (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K)) /
          1024 := by
    simpa only [bankTrialRenewalIndexWindowCount,
      bankTrialRenewalIndexStepCharge] using hGap
  have hDenIdentity := bankTrialRenewalIndexLostDenIdentity
    n (ceilLogTwo n) L hpositive hL
  have hgeo (j : Nat)
      (hj : j < bankTrialRenewalIndexWindowCount
        n (ceilLogTwo n) W) :
      1023 *
        (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K)) ^ j ≤
      1024 *
        (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K -
          L - 2 ^ (compileAdvice (ceilLogTwo n)).K *
            ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n))) ^ j := by
    exact bankTrialRenewalIndexBernoulli
      (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K -
        L - 2 ^ (compileAdvice (ceilLogTwo n)).K *
          ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n)))
      (1024 * (L + 2 ^ (compileAdvice (ceilLogTwo n)).K *
        ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n)))
      (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K))
      (bankTrialRenewalIndexWindowCount n (ceilLogTwo n) W)
      j hDenIdentity hGapActual hj
  have hwin := hL1
  have hwinOpaque :
      W * (2 ^ (compileAdvice (ceilLogTwo n)).K) * n ^ T *
        bankTrialSuccessStageIndexSum (fun j =>
          (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K -
            L - 2 ^ (compileAdvice (ceilLogTwo n)).K *
              ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n))) ^ j *
          (1023 * L) *
          (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K)) ^
            (bankTrialRenewalIndexWindowCount
              n (ceilLogTwo n) W - (j + 1)))
          (bankTrialRenewalIndexWindowCount n (ceilLogTwo n) W) ≤
      (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K)) ^
        (bankTrialRenewalIndexWindowCount n (ceilLogTwo n) W) *
        (W * (2 ^ (compileAdvice (ceilLogTwo n)).K) *
          (bankTrialRenewalColdProxyMass ring root hsmall x T W +
           bankTrialRenewalColdDefectMass ring root hsmall x T W) +
          n ^ T *
            bankTrialSuccessStageIndexSum (fun j =>
              n * ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
                5 * (compileAdvice (ceilLogTwo n)).b + 13) +
                bankTrialRenewalIndexZeroCharge (ceilLogTwo n)) +
              j * (n * bankTrialRenewalIndexStepCharge
                (ceilLogTwo n)))
              (bankTrialRenewalIndexWindowCount
                n (ceilLogTwo n) W)) := by
    simpa only [BankTrialRenewalColdClearedWindowProperty,
      bankTrialRenewalIndexStepCharge, Nat.mul_add,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hwin
  have hDenShape :
      1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K) =
        1024 * L * 2 ^ (compileAdvice (ceilLogTwo n)).K := by
    simp only [Nat.mul_assoc]
  have hresult := bankTrialRenewalIndexVariableMassArithmetic
    W (n * bankTrialRenewalIndexStepCharge (ceilLogTwo n))
    (bankTrialRenewalIndexWindowCount n (ceilLogTwo n) W)
    (2 ^ (compileAdvice (ceilLogTwo n)).K)
    (n ^ T)
    (bankTrialRenewalColdProxyMass ring root hsmall x T W +
      bankTrialRenewalColdDefectMass ring root hsmall x T W)
    (n * bankTrialRenewalIndexColdCharge (ceilLogTwo n))
    (n * ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
      5 * (compileAdvice (ceilLogTwo n)).b + 13) +
      bankTrialRenewalIndexZeroCharge (ceilLogTwo n)))
    L
    (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K -
      L - 2 ^ (compileAdvice (ceilLogTwo n)).K *
        ((8 * (compileAdvice (ceilLogTwo n)).b + 12) * n)))
    (1024 * (L * 2 ^ (compileAdvice (ceilLogTwo n)).K))
    hWpos hf rfl hquota.1 hFloor
    hcoverScaled hDenShape hdenpos hgeo hwinOpaque
  simpa only [bankTrialRenewalIndexStepCharge,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hresult

end L3

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-! Exact first-stop joint cost on the original tape. -/

/-- Early first-stop cylinders weighted by the elapsed prefix length. -/
private noncomputable def bankTrialColdEarlyLengthMass
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (T W : Nat) (pre : List (Fin n)) (z : X) : Nat :=
  ((Prob.firstStoppedPrefixes next stop T pre z).map
    (fun cut => if cut.length ≤ W then
      cut.length * n ^ (T - cut.length) else 0)).sum

private theorem bankTrialColdEarlyLengthZero
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (T : Nat) (pre : List (Fin n)) (z : X) :
    bankTrialColdEarlyLengthMass next stop T 0 pre z = 0 := by
  unfold bankTrialColdEarlyLengthMass
  have hf :
      (fun cut : List (Fin n) =>
        if cut.length ≤ 0 then
          cut.length * n ^ (T - cut.length) else 0) =
      (fun _ : List (Fin n) => 0) := by
    funext cut
    cases cut with
    | nil => simp
    | cons e tail => simp
  rw [hf]
  induction Prob.firstStoppedPrefixes next stop T pre z with
  | nil => rfl
  | cons cut cuts ih =>
      simp only [List.map_cons, List.sum_cons, ih, Nat.zero_add]


private theorem bankTrialColdEarlyLengthAtRoot
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (T W : Nat) (pre : List (Fin n)) (z : X)
    (hs : stop pre z = true) :
    bankTrialColdEarlyLengthMass next stop T W pre z = 0 := by
  unfold bankTrialColdEarlyLengthMass
  cases T with
  | zero => simp [Prob.firstStoppedPrefixes, hs]
  | succ t => simp [Prob.firstStoppedPrefixes, hs]

private theorem bankTrialColdEarlyLengthStep
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (T W : Nat) (pre : List (Fin n)) (z : X)
    (hs : stop pre z = false) :
    bankTrialColdEarlyLengthMass next stop
        (T + 1) (W + 1) pre z =
      (List.ofFn (fun e : Fin n =>
        bankTrialColdStopUnitMass next stop T W
            (pre ++ [e]) (next z e) +
          bankTrialColdEarlyLengthMass next stop T W
            (pre ++ [e]) (next z e))).sum := by
  unfold bankTrialColdEarlyLengthMass
  simp only [Prob.firstStoppedPrefixes, hs,
    Bool.false_eq_true, if_false]
  rw [bankTrialColdFlatMapSum]
  simp only [List.map_ofFn, Function.comp_def]
  apply ofFn_sum_eq
  intro e
  have hpoint (u : List (Fin n)) :
      (if (e :: u).length ≤ W + 1 then
        (e :: u).length *
          n ^ ((T + 1) - (e :: u).length)
       else 0) =
      (if u.length ≤ W then n ^ (T - u.length) else 0) +
      (if u.length ≤ W then
        u.length * n ^ (T - u.length) else 0) := by
    by_cases hu : u.length ≤ W
    · have hc : (e :: u).length ≤ W + 1 := by
        simp only [List.length_cons]
        omega
      have hsub :
          (T + 1) - (e :: u).length = T - u.length := by
        simp only [List.length_cons]
        omega
      simp only [List.length_cons, if_pos hu]
      split
      · have hrem :
            T + 1 - (1 + u.length) = T - u.length := by omega
        have hremAlt :
            T + 1 - (u.length + 1) = T - u.length := by omega
        first
        | rw [hrem]
        | rw [hremAlt]
        simp only [Nat.add_mul, Nat.one_mul]
        omega
      · omega
    · have hc : ¬ (e :: u).length ≤ W + 1 := by
        simp only [List.length_cons]
        omega
      simp only [if_neg hc, if_neg hu, Nat.zero_add]
  calc
    (((Prob.firstStoppedPrefixes next stop T
        (pre ++ [e]) (next z e)).map (List.cons e)).map
        (fun cut => if cut.length ≤ W + 1 then
          cut.length * n ^ ((T + 1) - cut.length) else 0)).sum =
      ((Prob.firstStoppedPrefixes next stop T
        (pre ++ [e]) (next z e)).map
        (fun u =>
          (if u.length ≤ W then n ^ (T - u.length) else 0) +
          (if u.length ≤ W then
            u.length * n ^ (T - u.length) else 0))).sum := by
          simp only [List.map_map, Function.comp_def]
          apply congrArg List.sum
          apply List.map_congr_left
          intro u _
          exact hpoint u
    _ = bankTrialColdStopUnitMass next stop T W
          (pre ++ [e]) (next z e) +
        bankTrialColdEarlyLengthMass next stop T W
          (pre ++ [e]) (next z e) := by
          rw [bankTrialRenewalNatMapSumAdd]
          rfl


/-- Algebra with opaque Nat arguments, avoiding large-power omega. -/
private theorem bankTrialColdOneServiceCostArithmetic
    (E U L C N W : Nat)
    (hpartition : U + L = N)
    (htail : E + W * L ≤ C) :
    (U + E) + (W + 1) * L ≤ N + C := by
  have hstep : (W + 1) * L = W * L + L := by
    rw [Nat.add_mul, Nat.one_mul]
  rw [hstep]
  omega

/-- The generic censored first-hit theorem: early cut-length mass
plus W times late/no-stop mass is ONE first-hit cost numerator. -/
private theorem bankTrialColdJointFirstHitCost
    {X : Type} {n : Nat}
    (next : X → Fin n → X)
    (stop : List (Fin n) → X → Bool)
    (target : X → Prop)
    (hreflect : ∀ pre z, stop pre z = true ↔ target z) :
    ∀ (T W : Nat) (pre : List (Fin n)) (z : X),
      W ≤ T →
      bankTrialColdEarlyLengthMass next stop T W pre z +
        W * bankTrialColdNoStopUnitMass next target z T W ≤
      costNumerator next target z T := by
  intro T
  induction T with
  | zero =>
      intro W pre z hW
      have hzero : W = 0 := by omega
      subst W
      rw [bankTrialColdEarlyLengthZero]
      simp
  | succ T ih =>
      intro W pre z hW
      cases W with
      | zero =>
          rw [bankTrialColdEarlyLengthZero]
          simp
      | succ W =>
          have hsmall : W ≤ T := by omega
          by_cases ht : target z
          · have hs : stop pre z = true :=
              (hreflect pre z).mpr ht
            rw [bankTrialColdEarlyLengthAtRoot next stop
                (T + 1) (W + 1) pre z hs,
              bankTrialColdNoStopUnitAtRoot next target
                z (T + 1) (W + 1) ht,
              costNumerator_terminal next target z ht (T + 1)]
            simp
          · have hs : stop pre z = false := by
              cases hb : stop pre z with
              | false => rfl
              | true =>
                  exact False.elim (ht ((hreflect pre z).mp hb))
            rw [bankTrialColdEarlyLengthStep next stop
                T W pre z hs,
              bankTrialColdNoStopUnitStep next target
                z T W ht,
              costNumerator_succ next target z ht T]
            have hchild (e : Fin n) :
                bankTrialColdEarlyLengthMass next stop T W
                    (pre ++ [e]) (next z e) +
                  W * bankTrialColdNoStopUnitMass next target
                    (next z e) T W ≤
                costNumerator next target (next z e) T :=
              ih W (pre ++ [e]) (next z e) hsmall
            have hpartition (e : Fin n) :
                bankTrialColdStopUnitMass next stop T W
                    (pre ++ [e]) (next z e) +
                  bankTrialColdNoStopUnitMass next target
                    (next z e) T W = n ^ T :=
              bankTrialColdGenericPrefixPartition
                next stop target hreflect
                T W (pre ++ [e]) (next z e) hsmall
            have hpoint (e : Fin n) :
                (bankTrialColdStopUnitMass next stop T W
                    (pre ++ [e]) (next z e) +
                  bankTrialColdEarlyLengthMass next stop T W
                    (pre ++ [e]) (next z e)) +
                  (W + 1) *
                    bankTrialColdNoStopUnitMass next target
                      (next z e) T W ≤
                n ^ T +
                  costNumerator next target (next z e) T :=
              bankTrialColdOneServiceCostArithmetic
                (bankTrialColdEarlyLengthMass next stop T W
                  (pre ++ [e]) (next z e))
                (bankTrialColdStopUnitMass next stop T W
                  (pre ++ [e]) (next z e))
                (bankTrialColdNoStopUnitMass next target
                  (next z e) T W)
                (costNumerator next target (next z e) T)
                (n ^ T) W (hpartition e) (hchild e)
            have hsum := ofFn_sum_le
              (fun e : Fin n =>
                (bankTrialColdStopUnitMass next stop T W
                    (pre ++ [e]) (next z e) +
                  bankTrialColdEarlyLengthMass next stop T W
                    (pre ++ [e]) (next z e)) +
                  (W + 1) *
                    bankTrialColdNoStopUnitMass next target
                      (next z e) T W)
              (fun e : Fin n =>
                n ^ T + costNumerator next target (next z e) T)
              hpoint
            simpa only [ofFn_sum_add, ofFn_sum_mul_left,
              ofFn_sum_const, Nat.pow_succ,
              Nat.mul_add, Nat.add_assoc,
              Nat.mul_comm] using hsum

/-- The actual cold observer's original-scheduler stopped cost
charges early CLEAN/GRANT/DEFECT cut lengths plus W times late mass. -/
theorem bankTrialRenewalColdJointFirstStopCost {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T W : Nat) (hwindow : W ≤ T) :
    bankTrialColdEarlyLengthMass
        (Counter.resetClockBankColdNext ring root hsp)
        (bankTrialRenewalColdStop ring root)
        T W [] (Counter.resetClockBankColdStart ring root x) +
      W * bankTrialRenewalColdLateMass ring root hsp x T W ≤
    costNumerator
      (Counter.resetClockBankColdNext ring root hsp)
      (Counter.resetClockBankColdTerminal ring root)
      (Counter.resetClockBankColdStart ring root x) T := by
  have h := bankTrialColdJointFirstHitCost
    (Counter.resetClockBankColdNext ring root hsp)
    (bankTrialRenewalColdStop ring root)
    (Counter.resetClockBankColdTerminal ring root)
    (fun pre z =>
      bankTrialRenewalColdStopCorrect ring root pre z)
    T W [] (Counter.resetClockBankColdStart ring root x) hwindow
  simpa only [bankTrialColdNoStopUnitMass,
    bankTrialRenewalColdLateMass] using h

/-- The SAME charge lies inside the existing cold stopped-cost
coefficient c. Early and late events never spend separate reserves. -/
theorem bankTrialRenewalColdJointFirstStopReserve {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T W : Nat) (hwindow : W ≤ T) :
    bankTrialColdEarlyLengthMass
        (Counter.resetClockBankColdNext ring root hsp)
        (bankTrialRenewalColdStop ring root)
        T W [] (Counter.resetClockBankColdStart ring root x) +
      W * bankTrialRenewalColdLateMass ring root hsp x T W ≤
    n ^ T *
      ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
        5 * (compileAdvice (ceilLogTwo n)).b + 13) * n) := by
  exact Nat.le_trans
    (bankTrialRenewalColdJointFirstStopCost
      ring root hsp x T W hwindow)
    (Counter.resetClockBankColdStoppedCost ring root hsp x T)

end L3

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
These are lemmas for the missing
cold C.16 proof. They do not assert the unproved L1 interface.
-/

/-- Finite-list arithmetic: a length charge and a scalar unit
charge are summed without a Finset. -/
private theorem bankTrialColdListBudget
    {α : Type} (xs : List α) (a b c : α → Nat) (g : Nat)
    (h : ∀ z, z ∈ xs → a z ≤ b z + g * c z) :
    (xs.map a).sum ≤
      (xs.map b).sum + g * (xs.map c).sum := by
  induction xs with
  | nil =>
      simp
  | cons z zs ih =>
      have hz : a z ≤ b z + g * c z := h z (by simp)
      have ht : ∀ u, u ∈ zs → a u ≤ b u + g * c u := by
        intro u hu
        exact h u (by simp [hu])
      have hs := ih ht
      simp only [List.map_cons, List.sum_cons, Nat.mul_add]
      omega

private theorem bankTrialColdEarlyCleanBudget {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T W g : Nat) :
    bankTrialRenewalColdEarlyCleanSum ring root hsp x T W
      (fun cut _ =>
        n ^ (T - cut.length) * (cut.length + g)) ≤
    bankTrialColdEarlyLengthMass
        (Counter.resetClockBankColdNext ring root hsp)
        (bankTrialRenewalColdStop ring root)
        T W [] (Counter.resetClockBankColdStart ring root x) +
      g * bankTrialColdStopUnitMass
        (Counter.resetClockBankColdNext ring root hsp)
        (bankTrialRenewalColdStop ring root)
        T W [] (Counter.resetClockBankColdStart ring root x) := by
  unfold bankTrialRenewalColdEarlyCleanSum
    bankTrialColdEarlyLengthMass bankTrialColdStopUnitMass
  apply bankTrialColdListBudget
  intro cut _
  by_cases hcut : cut.length ≤ W
  · cases hz : Prob.stoppedTapeRun
        (Counter.resetClockBankColdNext ring root hsp)
        cut (Counter.resetClockBankColdStart ring root x) with
    | inl z =>
        simp [hcut, hz]
    | inr z =>
        cases z with
        | inl a =>
            simp [hcut, hz]
        | inr outcome =>
            cases outcome with
            | mk D reason =>
                cases reason with
                | clean =>
                    simp only [if_pos hcut, hz]
                    simp only [Nat.mul_add, Nat.mul_assoc,
                      Nat.mul_comm, Nat.mul_left_comm]
                    exact Nat.le_of_eq (Nat.add_mul _ _ _)
                | grant =>
                    simp [hcut, hz]
                | defect =>
                    simp [hcut, hz]
  · simp [hcut]


/-- Exact first-stop partition implies that the unit mass of
all early cuts is at most the original scheduler mass. -/
private theorem bankTrialColdStopUnitWithin {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T W : Nat) (hwindow : W ≤ T) :
    bankTrialColdStopUnitMass
      (Counter.resetClockBankColdNext ring root hsp)
      (bankTrialRenewalColdStop ring root)
      T W [] (Counter.resetClockBankColdStart ring root x) ≤
    n ^ T := by
  have hpart := bankTrialColdGenericPrefixPartition
    (Counter.resetClockBankColdNext ring root hsp)
    (bankTrialRenewalColdStop ring root)
    (Counter.resetClockBankColdTerminal ring root)
    (fun pre z =>
      bankTrialRenewalColdStopCorrect ring root pre z)
    T W [] (Counter.resetClockBankColdStart ring root x)
    hwindow
  calc
    bankTrialColdStopUnitMass
        (Counter.resetClockBankColdNext ring root hsp)
        (bankTrialRenewalColdStop ring root)
        T W [] (Counter.resetClockBankColdStart ring root x) ≤
      bankTrialColdStopUnitMass
          (Counter.resetClockBankColdNext ring root hsp)
          (bankTrialRenewalColdStop ring root)
          T W [] (Counter.resetClockBankColdStart ring root x) +
        bankTrialColdNoStopUnitMass
          (Counter.resetClockBankColdNext ring root hsp)
          (Counter.resetClockBankColdTerminal ring root)
          (Counter.resetClockBankColdStart ring root x)
          T W := Nat.le_add_right _ _
    _ = n ^ T := hpart

/-- Pure arithmetic: the same c pays masked early length AND late
censored time. Products in this lemma are opaque natural numbers. -/
private theorem bankTrialColdJointIndexArithmetic
    (P M E N g W Z c : Nat)
    (hclean : P * M ≤ E + N * g)
    (hjoint : E + W * Z ≤ N * c) :
    P * M + W * Z ≤ N * (c + g) := by
  have ha := Nat.add_le_add_right hclean (W * Z)
  have hb := Nat.add_le_add_right hjoint (N * g)
  rw [Nat.mul_add]
  omega

/-- Genuine per-index joint expense. This is the cost half of the
cold C.16 Markov inequality, with no independent late reserve:
the stopped first-hit coefficient c is paid once at each j.
It uses the actual cold first-stopped list, not a fabricated CLEAN D. -/
theorem bankTrialRenewalColdJointIndexCharge {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (hlarge :
      2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (L W H T j : Nat)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold
      n (ceilLogTwo n) ≤ L)
    (hbudgetCold : W + H * L ≤ T)
    (hj : j < H) :
    2 ^ (compileAdvice (ceilLogTwo n)).K *
      bankTrialRenewalColdEarlyCleanSum ring root hsp x T W
        (fun cut D =>
          cut.length * bankTrialRenewalPatternMass ring root
            (GrantBankReference.bankLocalReferenceStart ring root D)
            (T - cut.length) L j +
          bankTrialRenewalPatternCost ring root
            (GrantBankReference.bankLocalReferenceStart ring root D)
            (T - cut.length) L j) +
      W * bankTrialRenewalColdLateMass ring root hsp x T W ≤
    n ^ T * (n *
      ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
          5 * (compileAdvice (ceilLogTwo n)).b + 13) +
        bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
        j * bankTrialRenewalIndexStepCharge (ceilLogTwo n))) := by
  have hwindow : W ≤ T :=
    Nat.le_trans (Nat.le_add_right W (H * L)) hbudgetCold
  have hsource := bankTrialRenewalColdEarlyCleanIndexChargeBound
    ring root hn hsp hw hlarge x L W H T j
    hL hbudgetCold hj
  have hbudget := bankTrialColdEarlyCleanBudget
    ring root hsp x T W
    (n * (bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
      j * bankTrialRenewalIndexStepCharge (ceilLogTwo n)))
  have hunit := bankTrialColdStopUnitWithin
    ring root hsp x T W hwindow
  have hunitScaled := Nat.mul_le_mul_left
    (n * (bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
      j * bankTrialRenewalIndexStepCharge (ceilLogTwo n))) hunit
  have hclean :
      2 ^ (compileAdvice (ceilLogTwo n)).K *
        bankTrialRenewalColdEarlyCleanSum ring root hsp x T W
          (fun cut D =>
            cut.length * bankTrialRenewalPatternMass ring root
              (GrantBankReference.bankLocalReferenceStart ring root D)
              (T - cut.length) L j +
            bankTrialRenewalPatternCost ring root
              (GrantBankReference.bankLocalReferenceStart ring root D)
              (T - cut.length) L j) ≤
      bankTrialColdEarlyLengthMass
          (Counter.resetClockBankColdNext ring root hsp)
          (bankTrialRenewalColdStop ring root)
          T W [] (Counter.resetClockBankColdStart ring root x) +
        n ^ T * (n *
          (bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
            j * bankTrialRenewalIndexStepCharge (ceilLogTwo n))) := by
    calc
      _ ≤ bankTrialRenewalColdEarlyCleanSum
          ring root hsp x T W
          (fun cut _ => n ^ (T - cut.length) *
            (cut.length + n *
              (bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
                j * bankTrialRenewalIndexStepCharge
                  (ceilLogTwo n)))) := hsource
      _ ≤ bankTrialColdEarlyLengthMass
            (Counter.resetClockBankColdNext ring root hsp)
            (bankTrialRenewalColdStop ring root)
            T W [] (Counter.resetClockBankColdStart ring root x) +
          (n * (bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
            j * bankTrialRenewalIndexStepCharge (ceilLogTwo n))) *
          bankTrialColdStopUnitMass
            (Counter.resetClockBankColdNext ring root hsp)
            (bankTrialRenewalColdStop ring root)
            T W [] (Counter.resetClockBankColdStart ring root x) :=
              hbudget
      _ ≤ bankTrialColdEarlyLengthMass
            (Counter.resetClockBankColdNext ring root hsp)
            (bankTrialRenewalColdStop ring root)
            T W [] (Counter.resetClockBankColdStart ring root x) +
          (n * (bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
            j * bankTrialRenewalIndexStepCharge (ceilLogTwo n))) *
              n ^ T := Nat.add_le_add_left hunitScaled _
      _ = _ := by
            rw [Nat.mul_comm
              (n * (bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
                j * bankTrialRenewalIndexStepCharge (ceilLogTwo n)))
              (n ^ T)]
  have hjoint := bankTrialRenewalColdJointFirstStopReserve
    ring root hsp x T W hwindow
  have hpaid := bankTrialColdJointIndexArithmetic
    (2 ^ (compileAdvice (ceilLogTwo n)).K)
    (bankTrialRenewalColdEarlyCleanSum ring root hsp x T W
      (fun cut D =>
        cut.length * bankTrialRenewalPatternMass ring root
          (GrantBankReference.bankLocalReferenceStart ring root D)
          (T - cut.length) L j +
        bankTrialRenewalPatternCost ring root
          (GrantBankReference.bankLocalReferenceStart ring root D)
          (T - cut.length) L j))
    (bankTrialColdEarlyLengthMass
      (Counter.resetClockBankColdNext ring root hsp)
      (bankTrialRenewalColdStop ring root)
      T W [] (Counter.resetClockBankColdStart ring root x))
    (n ^ T)
    (n * (bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
      j * bankTrialRenewalIndexStepCharge (ceilLogTwo n)))
    W (bankTrialRenewalColdLateMass ring root hsp x T W)
    ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
      5 * (compileAdvice (ceilLogTwo n)).b + 13) * n)
    hclean hjoint
  simpa only [Nat.mul_add, Nat.add_assoc, Nat.mul_assoc,
    Nat.mul_comm, Nat.mul_left_comm] using hpaid

/-- Monotonicity of powers, keeping the compiler's large exponent
opaque to arithmetic tactics. -/
private theorem bankTrialColdPowerMonotone
    (a d j : Nat) (ha : a ≤ d) :
    a ^ j ≤ d ^ j := by
  induction j with
  | zero =>
      exact Nat.le_refl _
  | succ j ih =>
      calc
        a ^ (j + 1) = a ^ j * a := Nat.pow_succ a j
        _ ≤ d ^ j * d := Nat.mul_le_mul ih ha
        _ = d ^ (j + 1) := (Nat.pow_succ d j).symm

/-- On one index, the geometric numerator times P fits in den^H.
This is the multiplier required to charge late mass by W per index. -/
private theorem bankTrialColdGeometricOneTerm
    (lo win den P H j : Nat)
    (hj : j < H)
    (hlo : lo ≤ den)
    (hwin : P * win ≤ den) :
    P * (lo ^ j * win * den ^ (H - (j + 1))) ≤
      den ^ H := by
  have hpow := bankTrialColdPowerMonotone lo den j hlo
  have hhead : lo ^ j * (P * win) ≤ den ^ j * den :=
    Nat.mul_le_mul hpow hwin
  have hscaled :=
    Nat.mul_le_mul_right (den ^ (H - (j + 1))) hhead
  have hindex : (j + 1) + (H - (j + 1)) = H := by omega
  calc
    P * (lo ^ j * win * den ^ (H - (j + 1))) =
        (lo ^ j * (P * win)) * den ^ (H - (j + 1)) := by
          simp only [Nat.mul_assoc, Nat.mul_comm,
            Nat.mul_left_comm]
    _ ≤ (den ^ j * den) * den ^ (H - (j + 1)) := hscaled
    _ = den ^ (j + 1) * den ^ (H - (j + 1)) := by
          rw [Nat.pow_succ]
    _ = den ^ H := by rw [← Nat.pow_add, hindex]

/-- Concrete late-mass multiplier, independent of any additional
radius or cost hypothesis. -/
theorem bankTrialRenewalColdLateIndexWeight
    (n q L H j : Nat) (hj : j < H) :
    2 ^ (compileAdvice q).K *
      ((1024 * (L * 2 ^ (compileAdvice q).K -
        L - 2 ^ (compileAdvice q).K *
          ((8 * (compileAdvice q).b + 12) * n))) ^ j *
        (1023 * L) *
        (1024 * (L * 2 ^ (compileAdvice q).K)) ^
          (H - (j + 1))) ≤
    (1024 * (L * 2 ^ (compileAdvice q).K)) ^ H := by
  have hlo :
      1024 * (L * 2 ^ (compileAdvice q).K -
        L - 2 ^ (compileAdvice q).K *
          ((8 * (compileAdvice q).b + 12) * n)) ≤
      1024 * (L * 2 ^ (compileAdvice q).K) :=
    Nat.mul_le_mul_left 1024
      (Nat.le_trans
        (Nat.sub_le
          (L * 2 ^ (compileAdvice q).K - L)
          (2 ^ (compileAdvice q).K *
            ((8 * (compileAdvice q).b + 12) * n)))
        (Nat.sub_le (L * 2 ^ (compileAdvice q).K) L))
  have hwin :
      2 ^ (compileAdvice q).K * (1023 * L) ≤
      1024 * (L * 2 ^ (compileAdvice q).K) := by
    have hs := Nat.mul_le_mul_right
      (L * 2 ^ (compileAdvice q).K)
      (show (1023 : Nat) ≤ 1024 by decide)
    simpa only [Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm] using hs
  exact bankTrialColdGeometricOneTerm
    (1024 * (L * 2 ^ (compileAdvice q).K -
      L - 2 ^ (compileAdvice q).K *
        ((8 * (compileAdvice q).b + 12) * n)))
    (1023 * L)
    (1024 * (L * 2 ^ (compileAdvice q).K))
    (2 ^ (compileAdvice q).K) H j hj hlo hwin

end L3

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
The global masked stopped-word window and
the ONE coefficient-sum grant/defect credit. No assumed leaf.
-/

/-- At a true early first stop, the proxy consumes one grant
cylinder or the unique successful CLEAN index; defects and
late cuts have zero window reward. -/
private noncomputable def bankTrialColdEarlyRewardWeight {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (W L H : Nat) (cut : List (Fin n))
    (z : Counter.ResetClockBankColdState (q := q) ring root)
    (suffix : List (Fin n)) : Nat :=
  if cut.length ≤ W then
    match z with
    | .inr (.inr (_, .grant)) => 1
    | .inr (.inr (D, .clean)) =>
        bankTrialSuccessStageIndexSum (fun j =>
          Prob.indicator (bankTrialRenewalPattern ring root
            (GrantBankReference.bankLocalReferenceStart ring root D)
            L j suffix)) H
    | _ => 0
  else 0

/-- This cost is masked by exactly the same successful-index event.
In particular, there is no H-times-cold-length charge. -/
private noncomputable def bankTrialColdEarlyMaskedCostWeight {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (W L H : Nat) (cut : List (Fin n))
    (z : Counter.ResetClockBankColdState (q := q) ring root)
    (suffix : List (Fin n)) : Nat :=
  if cut.length ≤ W then
    match z with
    | .inr (.inr (D, .clean)) =>
        bankTrialSuccessStageIndexSum (fun j =>
          cut.length * Prob.indicator (bankTrialRenewalPattern
            ring root
            (GrantBankReference.bankLocalReferenceStart ring root D)
            L j suffix) +
          bankTrialRenewalTau ring root
            (GrantBankReference.bankLocalReferenceStart ring root D)
            L j suffix) H
    | _ => 0
  else 0

/-- Genuine pointwise early first-stop window: GRANT is paid
once by the proxy; only CLEAN can pay an index-dependent cost. -/
theorem bankTrialColdEarlyRewardCutWindow {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (W L H : Nat) (cut : List (Fin n))
    (z : Counter.ResetClockBankColdState (q := q) ring root)
    (suffix : List (Fin n)) :
    W * bankTrialColdEarlyRewardWeight
      ring root W L H cut z suffix ≤
    W * bankTrialRenewalColdProxyWeight ring root W cut z suffix +
      bankTrialColdEarlyMaskedCostWeight
        ring root W L H cut z suffix := by
  by_cases hcut : cut.length ≤ W
  · cases z with
    | inl a =>
        simp [bankTrialColdEarlyRewardWeight,
          bankTrialColdEarlyMaskedCostWeight,
          bankTrialRenewalColdProxyWeight, hcut]
    | inr z =>
        cases z with
        | inl a =>
            simp [bankTrialColdEarlyRewardWeight,
              bankTrialColdEarlyMaskedCostWeight,
              bankTrialRenewalColdProxyWeight, hcut]
        | inr outcome =>
            cases outcome with
            | mk D reason =>
                cases reason with
                | clean =>
                    simpa [bankTrialColdEarlyRewardWeight,
                      bankTrialColdEarlyMaskedCostWeight, hcut] using
                      (bankTrialRenewalColdCleanMaskedWord
                        ring root D W L H cut suffix)
                | grant =>
                    simp [bankTrialColdEarlyRewardWeight,
                      bankTrialColdEarlyMaskedCostWeight,
                      bankTrialRenewalColdProxyWeight, hcut]
                | defect =>
                    simp [bankTrialColdEarlyRewardWeight,
                      bankTrialColdEarlyMaskedCostWeight,
                      bankTrialRenewalColdProxyWeight, hcut]
  · simp [bankTrialColdEarlyRewardWeight,
      bankTrialColdEarlyMaskedCostWeight,
      bankTrialRenewalColdProxyWeight, hcut]

/-- The total reward is measured on the ORIGINAL length-T tapes,
not an independently restarted scheduler. -/
private noncomputable def bankTrialColdEarlyRewardMass {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T W L H : Nat) : Nat :=
  Prob.scheduleSum n T (fun word =>
    bankTrialSuccessNatStoppedWord
      (Counter.resetClockBankColdNext ring root hsp)
      (bankTrialRenewalColdStop ring root)
      (fun cut z _ suffix =>
        bankTrialColdEarlyRewardWeight ring root W L H
          cut z suffix)
      T [] (Counter.resetClockBankColdStart ring root x) word)

private noncomputable def bankTrialColdEarlyMaskedCostMass {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T W L H : Nat) : Nat :=
  Prob.scheduleSum n T (fun word =>
    bankTrialSuccessNatStoppedWord
      (Counter.resetClockBankColdNext ring root hsp)
      (bankTrialRenewalColdStop ring root)
      (fun cut z _ suffix =>
        bankTrialColdEarlyMaskedCostWeight
          ring root W L H cut z suffix)
      T [] (Counter.resetClockBankColdStart ring root x) word)

/-- Global first-stop masked-window inequality. The previous
stopped-weighted schedule proof inducts on the ACTUAL tape;
the result contains ONE proxy, never one proxy per j.
The early GRANT unit is already inside the reward on the left. -/
theorem bankTrialRenewalColdGlobalMaskedWindow {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T W L H : Nat) :
    W * bankTrialColdEarlyRewardMass
      ring root hsp x T W L H ≤
    W * bankTrialRenewalColdProxyMass ring root hsp x T W +
      bankTrialColdEarlyMaskedCostMass
        ring root hsp x T W L H := by
  unfold bankTrialColdEarlyRewardMass
    bankTrialRenewalColdProxyMass
    bankTrialColdEarlyMaskedCostMass
  exact bankTrialRenewalColdStoppedWeightedSchedule
    (Counter.resetClockBankColdNext ring root hsp)
    (bankTrialRenewalColdStop ring root)
    (fun cut z suffix =>
      bankTrialColdEarlyRewardWeight ring root W L H cut z suffix)
    (fun cut z suffix =>
      bankTrialRenewalColdProxyWeight ring root W cut z suffix)
    (fun cut z suffix =>
      bankTrialColdEarlyMaskedCostWeight
        ring root W L H cut z suffix)
    W T (Counter.resetClockBankColdStart ring root x)
    (fun cut z suffix =>
      bankTrialColdEarlyRewardCutWindow
        ring root W L H cut z suffix)

/-- Explicitly exhibit the unique stopped-prefix list in the
global reward; there is no extra factorization assumption. -/
theorem bankTrialColdEarlyRewardFirstStopFactor {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T W L H : Nat) :
    bankTrialColdEarlyRewardMass ring root hsp x T W L H =
    ((Prob.firstStoppedPrefixes
      (Counter.resetClockBankColdNext ring root hsp)
      (bankTrialRenewalColdStop ring root)
      T [] (Counter.resetClockBankColdStart ring root x)).map
      (fun cut =>
        Prob.scheduleSum n (T - cut.length) (fun suffix =>
          bankTrialColdEarlyRewardWeight ring root W L H cut
            (Prob.stoppedTapeRun
              (Counter.resetClockBankColdNext ring root hsp)
              cut (Counter.resetClockBankColdStart ring root x))
            suffix))).sum := by
  unfold bankTrialColdEarlyRewardMass
  exact bankTrialRenewalColdFirstStopFactor ring root hsp x
    (fun cut z suffix =>
      bankTrialColdEarlyRewardWeight
        ring root W L H cut z suffix) T

theorem bankTrialColdEarlyMaskedCostFirstStopFactor {n : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T W L H : Nat) :
    bankTrialColdEarlyMaskedCostMass ring root hsp x T W L H =
    ((Prob.firstStoppedPrefixes
      (Counter.resetClockBankColdNext ring root hsp)
      (bankTrialRenewalColdStop ring root)
      T [] (Counter.resetClockBankColdStart ring root x)).map
      (fun cut =>
        Prob.scheduleSum n (T - cut.length) (fun suffix =>
          bankTrialColdEarlyMaskedCostWeight ring root W L H cut
            (Prob.stoppedTapeRun
              (Counter.resetClockBankColdNext ring root hsp)
              cut (Counter.resetClockBankColdStart ring root x))
            suffix))).sum := by
  unfold bankTrialColdEarlyMaskedCostMass
  exact bankTrialRenewalColdFirstStopFactor ring root hsp x
    (fun cut z suffix =>
      bankTrialColdEarlyMaskedCostWeight
        ring root W L H cut z suffix) T

/-- Stage sums respect pointwise equality restricted to j < H. -/
private theorem bankTrialColdStageIndexCongr
    (f g : Nat → Nat) :
    ∀ H : Nat, (∀ j, j < H → f j = g j) →
      bankTrialSuccessStageIndexSum f H =
      bankTrialSuccessStageIndexSum g H := by
  intro H
  induction H with
  | zero =>
      intro _
      rfl
  | succ k ih =>
      intro h
      change bankTrialSuccessStageIndexSum f k + f k =
        bankTrialSuccessStageIndexSum g k + g k
      rw [ih (fun j hj => h j (by omega)), h k (by omega)]

/-- Finite geometric convolution recurrence, with all
powers symbolic and only index arithmetic given to omega. -/
private theorem bankTrialColdGeometricStep
    (lo win den H : Nat) :
    bankTrialSuccessStageIndexSum (fun j =>
      lo ^ j * win * den ^ ((H + 1) - (j + 1))) (H + 1) =
    den * bankTrialSuccessStageIndexSum (fun j =>
      lo ^ j * win * den ^ (H - (j + 1))) H +
      lo ^ H * win := by
  change bankTrialSuccessStageIndexSum (fun j =>
      lo ^ j * win * den ^ ((H + 1) - (j + 1))) H +
        lo ^ H * win * den ^ ((H + 1) - (H + 1)) = _
  have hterms :
      bankTrialSuccessStageIndexSum (fun j =>
        lo ^ j * win * den ^ ((H + 1) - (j + 1))) H =
      bankTrialSuccessStageIndexSum (fun j =>
        den * (lo ^ j * win * den ^ (H - (j + 1)))) H := by
    apply bankTrialColdStageIndexCongr
    intro j hj
    have hsub :
        (H + 1) - (j + 1) = (H - (j + 1)) + 1 := by omega
    rw [hsub, Nat.pow_succ]
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [hterms, bankTrialSuccessStageIndexSumScale]
  simp only [Nat.sub_self, Nat.pow_zero, Nat.mul_one]

/-- A purely symbolic nonlinear rearrangement. -/
private theorem bankTrialColdGeometricArithmetic
    (S a den lo win : Nat)
    (hlo : lo + win ≤ den) :
    den * S + a * win + a * lo ≤ den * (S + a) := by
  have hrel : win + lo ≤ den := by
    simpa only [Nat.add_comm] using hlo
  have hmul := Nat.mul_le_mul_left a hrel
  calc
    den * S + a * win + a * lo =
      den * S + a * (win + lo) := by
        simp only [Nat.mul_add, Nat.add_assoc]
    _ ≤ den * S + a * den := Nat.add_le_add_left hmul _
    _ = den * (S + a) := by
          simp only [Nat.mul_add, Nat.mul_comm]

/-- Stronger than the needed coefficient-sum bound:
the unused geometric tail lo^H remains explicitly available. -/
private theorem bankTrialColdGeometricComplement
    (lo win den : Nat) (hlo : lo + win ≤ den) :
    ∀ H : Nat,
      bankTrialSuccessStageIndexSum (fun j =>
        lo ^ j * win * den ^ (H - (j + 1))) H +
        lo ^ H ≤ den ^ H := by
  intro H
  induction H with
  | zero =>
      simp [bankTrialSuccessStageIndexSum]
  | succ k ih =>
      rw [bankTrialColdGeometricStep, Nat.pow_succ lo k,
        Nat.pow_succ den k]
      calc
        den * bankTrialSuccessStageIndexSum (fun j =>
            lo ^ j * win * den ^ (k - (j + 1))) k +
          lo ^ k * win + lo ^ k * lo ≤
        den * (bankTrialSuccessStageIndexSum (fun j =>
          lo ^ j * win * den ^ (k - (j + 1))) k +
          lo ^ k) :=
            bankTrialColdGeometricArithmetic _ _ _ _ _ hlo
        _ ≤ den * den ^ k := Nat.mul_le_mul_left den ih
        _ = den ^ k * den := Nat.mul_comm _ _

/-- A saturation-free bound on the Nat subtraction in lo.
The lemma is over opaque A,L,B, never huge compiled powers. -/
private theorem bankTrialColdLoWinArithmetic
    (A L B : Nat) (hL : L ≤ A) :
    1024 * (A - L - B) + 1023 * L ≤ 1024 * A := by
  have hdrop : A - L - B ≤ A - L := Nat.sub_le _ _
  have hm := Nat.mul_le_mul_left 1024 hdrop
  have hh : 1023 * L ≤ 1024 * L :=
    Nat.mul_le_mul_right L (by decide)
  have hsum : (A - L) + L = A := Nat.sub_add_cancel hL
  calc
    1024 * (A - L - B) + 1023 * L ≤
      1024 * (A - L) + 1023 * L :=
        Nat.add_le_add_right hm _
    _ ≤ 1024 * (A - L) + 1024 * L :=
      Nat.add_le_add_left hh _
    _ = 1024 * ((A - L) + L) :=
      (Nat.mul_add 1024 (A - L) L).symm
    _ = 1024 * A := congrArg (fun z => 1024 * z) hsum

/-- ONE coefficient sum for ALL early GRANT and DEFECT cuts.
This has no H multiplier on any cylinder mass. -/
theorem bankTrialRenewalColdGeometricCoefficientSumBound
    (n q L H : Nat) :
    bankTrialSuccessStageIndexSum (fun j =>
      (1024 * (L * 2 ^ (compileAdvice q).K -
        L - 2 ^ (compileAdvice q).K *
          ((8 * (compileAdvice q).b + 12) * n))) ^ j *
      (1023 * L) *
      (1024 * (L * 2 ^ (compileAdvice q).K)) ^
        (H - (j + 1))) H ≤
    (1024 * (L * 2 ^ (compileAdvice q).K)) ^ H := by
  have hP : 1 ≤ 2 ^ (compileAdvice q).K :=
    bankTrialRenewalIndexOneLeTwoPow (compileAdvice q).K
  have hL : L ≤ L * 2 ^ (compileAdvice q).K := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left L hP
  have hlo := bankTrialColdLoWinArithmetic
    (L * 2 ^ (compileAdvice q).K) L
    (2 ^ (compileAdvice q).K *
      ((8 * (compileAdvice q).b + 12) * n)) hL
  have hstrong := bankTrialColdGeometricComplement
    (1024 * (L * 2 ^ (compileAdvice q).K -
      L - 2 ^ (compileAdvice q).K *
        ((8 * (compileAdvice q).b + 12) * n)))
    (1023 * L)
    (1024 * (L * 2 ^ (compileAdvice q).K))
    hlo H
  exact Nat.le_trans (Nat.le_add_right _ _) hstrong

/-- One simultaneous credit for GRANT and DEFECT, rather
than a new copy of their mass at every index j < H. -/
theorem bankTrialRenewalColdGrantDefectSingleCredit
    (n q L H W grant defect : Nat) :
    W * 2 ^ (compileAdvice q).K * (grant + defect) *
      bankTrialSuccessStageIndexSum (fun j =>
        (1024 * (L * 2 ^ (compileAdvice q).K -
          L - 2 ^ (compileAdvice q).K *
            ((8 * (compileAdvice q).b + 12) * n))) ^ j *
        (1023 * L) *
        (1024 * (L * 2 ^ (compileAdvice q).K)) ^
          (H - (j + 1))) H ≤
    (1024 * (L * 2 ^ (compileAdvice q).K)) ^ H *
      (W * 2 ^ (compileAdvice q).K * (grant + defect)) := by
  have hsum :=
    bankTrialRenewalColdGeometricCoefficientSumBound n q L H
  have hmul := Nat.mul_le_mul_left
    (W * 2 ^ (compileAdvice q).K * (grant + defect)) hsum
  simpa only [Nat.mul_assoc, Nat.mul_comm,
    Nat.mul_left_comm] using hmul

end L3

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-!
Generic stage-index/finite-list exchange and
opaque-naturals algebra for the eventual cold L1 assembly.
-/

private theorem bankTrialColdStageListExchange
    {α : Type} (xs : List α) (F : Nat → α → Nat) :
    ∀ H : Nat,
      (xs.map (fun z =>
        bankTrialSuccessStageIndexSum (fun j => F j z) H)).sum =
      bankTrialSuccessStageIndexSum
        (fun j => (xs.map (F j)).sum) H := by
  intro H
  induction H with
  | zero =>
      change (xs.map (fun _ => 0)).sum = 0
      induction xs with
      | nil =>
          rfl
      | cons z zs ih =>
          simp only [List.map_cons, List.sum_cons, ih, Nat.zero_add]
  | succ k ih =>
      change
        (xs.map (fun z =>
          bankTrialSuccessStageIndexSum
              (fun j => F j z) k + F k z)).sum =
        bankTrialSuccessStageIndexSum
          (fun j => (xs.map (F j)).sum) k +
          (xs.map (F k)).sum
      rw [bankTrialRenewalNatMapSumAdd]
      exact congrArg
        (fun v => v + (xs.map (F k)).sum) ih


/-- Entire remaining L1 combination reduces to six opaque Nat
hypotheses, including a ONE-unit GRANT window and a joint
late-plus-masked-CLEAN expense. This lemma has no theorem leaf. -/
private theorem bankTrialColdWindowCompositionArithmetic
    (W P N den sumCoeff clean grant defect late
      cleanPattern proxy maskedCost charge H : Nat)
    (hpartition : N = clean + grant + defect + late)
    (hmass : clean * sumCoeff ≤ den * cleanPattern)
    (hgeom : sumCoeff ≤ den)
    (hlate : P * sumCoeff ≤ den * H)
    (hwindow :
      W * (cleanPattern + grant) ≤ W * proxy + maskedCost)
    (hcost :
      P * maskedCost + H * (W * late) ≤ N * charge) :
    W * P * N * sumCoeff ≤
      den * (W * P * (proxy + defect) + N * charge) := by
  have ha := Nat.mul_le_mul_left (W * P) hmass
  have hb := Nat.mul_le_mul_left (W * P)
    (Nat.mul_le_mul_left (grant + defect) hgeom)
  have hc := Nat.mul_le_mul_left (W * late) hlate
  have hfirst :
      W * P * N * sumCoeff ≤
      den * (W * P * (cleanPattern + grant + defect) +
        H * (W * late)) := by
    calc
      W * P * N * sumCoeff =
        W * P * (clean * sumCoeff) +
          W * P * ((grant + defect) * sumCoeff) +
          (W * late) * (P * sumCoeff) := by
            rw [hpartition]
            simp only [Nat.mul_add, Nat.add_mul,
              Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      _ ≤ W * P * (den * cleanPattern) +
            W * P * ((grant + defect) * den) +
            (W * late) * (den * H) :=
              Nat.add_le_add (Nat.add_le_add ha hb) hc
      _ = den *
          (W * P * (cleanPattern + grant + defect) +
            H * (W * late)) := by
              simp only [Nat.mul_add, Nat.add_mul,
                Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hw := Nat.mul_le_mul_left P hwindow
  have hsecond :
      W * P * (cleanPattern + grant + defect) +
          H * (W * late) ≤
      W * P * (proxy + defect) +
          (P * maskedCost + H * (W * late)) := by
    calc
      W * P * (cleanPattern + grant + defect) +
          H * (W * late) =
        P * (W * (cleanPattern + grant)) +
          W * P * defect + H * (W * late) := by
            simp only [Nat.mul_add, Nat.add_mul,
              Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      _ ≤ P * (W * proxy + maskedCost) +
            W * P * defect + H * (W * late) :=
              Nat.add_le_add_right
                (Nat.add_le_add_right hw (W * P * defect))
                (H * (W * late))
      _ = W * P * (proxy + defect) +
            (P * maskedCost + H * (W * late)) := by
              simp only [Nat.mul_add, Nat.add_mul,
                Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hthird :
      W * P * (cleanPattern + grant + defect) +
          H * (W * late) ≤
      W * P * (proxy + defect) + N * charge :=
    Nat.le_trans hsecond
      (Nat.add_le_add_left hcost _)
  exact Nat.le_trans hfirst
    (Nat.mul_le_mul_left den hthird)

end L3

-- Reward factor bridge (not yet proved):
-- bankTrialColdEarlyRewardMass ring root hsp x T W L H
--   = bankTrialSuccessStageIndexSum (fun j =>
--       bankTrialRenewalColdEarlyCleanSum ring root hsp x T W
--         (fun cut D =>
--           bankTrialRenewalPatternMass ring root
--             (GrantBankReference.bankLocalReferenceStart ring root D)
--             (T - cut.length) L j)) H
--     + bankTrialRenewalColdEarlyGrantMass ring root hsp x T W
--
-- Masked-cost factor bridge (not yet proved):
-- bankTrialColdEarlyMaskedCostMass ring root hsp x T W L H
--   = bankTrialSuccessStageIndexSum (fun j =>
--       bankTrialRenewalColdEarlyCleanSum ring root hsp x T W
--         (fun cut D =>
--           cut.length * bankTrialRenewalPatternMass ring root
--             (GrantBankReference.bankLocalReferenceStart ring root D)
--             (T - cut.length) L j +
--           bankTrialRenewalPatternCost ring root
--             (GrantBankReference.bankLocalReferenceStart ring root D)
--             (T - cut.length) L j)) H

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-! Finite first-stop reward and masked-cost factor bridges. -/

private theorem bankTrialColdScheduleZero (n T : Nat) :
    Prob.scheduleSum n T (fun _ => 0) = 0 := by
  simpa only [Nat.mul_zero] using
    bankTrialProbabilityScheduleSumConst n T 0

private theorem bankTrialColdScheduleOne (n T : Nat) :
    Prob.scheduleSum n T (fun _ => 1) = n ^ T := by
  simpa only [Nat.mul_one] using
    bankTrialProbabilityScheduleSumConst n T 1

private noncomputable def bankTrialColdEarlyCleanPatternCut
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T W L j : Nat) (cut : List (Fin n)) : Nat :=
  if cut.length ≤ W then
    match Prob.stoppedTapeRun
        (Counter.resetClockBankColdNext ring root hsp)
        cut (Counter.resetClockBankColdStart ring root x) with
    | .inr (.inr (D, .clean)) =>
        bankTrialRenewalPatternMass ring root
          (GrantBankReference.bankLocalReferenceStart ring root D)
          (T - cut.length) L j
    | _ => 0
  else 0

private noncomputable def bankTrialColdEarlyCleanMaskedCostCut
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T W L j : Nat) (cut : List (Fin n)) : Nat :=
  if cut.length ≤ W then
    match Prob.stoppedTapeRun
        (Counter.resetClockBankColdNext ring root hsp)
        cut (Counter.resetClockBankColdStart ring root x) with
    | .inr (.inr (D, .clean)) =>
        cut.length * bankTrialRenewalPatternMass ring root
          (GrantBankReference.bankLocalReferenceStart ring root D)
          (T - cut.length) L j +
        bankTrialRenewalPatternCost ring root
          (GrantBankReference.bankLocalReferenceStart ring root D)
          (T - cut.length) L j
    | _ => 0
  else 0

private noncomputable def bankTrialColdEarlyGrantCut
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T W : Nat) (cut : List (Fin n)) : Nat :=
  if cut.length ≤ W then
    match Prob.stoppedTapeRun
        (Counter.resetClockBankColdNext ring root hsp)
        cut (Counter.resetClockBankColdStart ring root x) with
    | .inr (.inr (_, .grant)) => n ^ (T - cut.length)
    | _ => 0
  else 0

private theorem bankTrialColdScheduleMaskedIndex
    {n q : Nat} (ring : DirectedRing n) (root : Fin n)
    (D : Counter.Config q n) (cut : List (Fin n))
    (T L H : Nat) :
    Prob.scheduleSum n (T - cut.length) (fun suffix =>
      bankTrialSuccessStageIndexSum (fun j =>
        cut.length * Prob.indicator (bankTrialRenewalPattern
          ring root
          (GrantBankReference.bankLocalReferenceStart ring root D)
          L j suffix) +
        bankTrialRenewalTau ring root
          (GrantBankReference.bankLocalReferenceStart ring root D)
          L j suffix) H) =
    bankTrialSuccessStageIndexSum (fun j =>
      cut.length * bankTrialRenewalPatternMass ring root
        (GrantBankReference.bankLocalReferenceStart ring root D)
        (T - cut.length) L j +
      bankTrialRenewalPatternCost ring root
        (GrantBankReference.bankLocalReferenceStart ring root D)
        (T - cut.length) L j) H := by
  calc
    _ = bankTrialSuccessStageIndexSum (fun j =>
          Prob.scheduleSum n (T - cut.length) (fun suffix =>
            cut.length * Prob.indicator (bankTrialRenewalPattern
              ring root
              (GrantBankReference.bankLocalReferenceStart ring root D)
              L j suffix) +
            bankTrialRenewalTau ring root
              (GrantBankReference.bankLocalReferenceStart ring root D)
              L j suffix)) H :=
          (bankTrialSuccessStageIndexSumSchedule
            n (T - cut.length) H _).symm
    _ = _ := by
      apply bankTrialColdStageIndexCongr
      intro j _
      rw [bankTrialC5ScheduleSumAdd,
        bankTrialSuccessScheduleSumScale]
      rfl

/-- Cutwise reward equals all CLEAN indexed cylinders plus ONE
grant cylinder. DEFECT and late cuts contribute zero. -/
private theorem bankTrialColdRewardCutDecomposition
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T W L H : Nat) (cut : List (Fin n)) :
    Prob.scheduleSum n (T - cut.length) (fun suffix =>
      bankTrialColdEarlyRewardWeight ring root W L H cut
        (Prob.stoppedTapeRun
          (Counter.resetClockBankColdNext ring root hsp)
          cut (Counter.resetClockBankColdStart ring root x))
        suffix) =
    bankTrialSuccessStageIndexSum (fun j =>
      bankTrialColdEarlyCleanPatternCut
        ring root hsp x T W L j cut) H +
    bankTrialColdEarlyGrantCut ring root hsp x T W cut := by
  by_cases hc : cut.length ≤ W
  · cases hz : Prob.stoppedTapeRun
        (Counter.resetClockBankColdNext ring root hsp)
        cut (Counter.resetClockBankColdStart ring root x) with
    | inl a =>
        simp [bankTrialColdEarlyRewardWeight,
          bankTrialColdEarlyCleanPatternCut,
          bankTrialColdEarlyGrantCut, hc, hz,
          bankTrialColdScheduleZero,
          bankTrialSuccessStageIndexSumZero]
    | inr z =>
        cases z with
        | inl a =>
            simp [bankTrialColdEarlyRewardWeight,
              bankTrialColdEarlyCleanPatternCut,
              bankTrialColdEarlyGrantCut, hc, hz,
              bankTrialColdScheduleZero,
              bankTrialSuccessStageIndexSumZero]
        | inr outcome =>
            cases outcome with
            | mk D reason =>
                cases reason with
                | clean =>
                    simp [bankTrialColdEarlyRewardWeight,
                      bankTrialColdEarlyCleanPatternCut,
                      bankTrialColdEarlyGrantCut, hc, hz,
                      bankTrialRenewalPatternMass,
                      bankTrialSuccessStageIndexSumSchedule]
                | grant =>
                    simp [bankTrialColdEarlyRewardWeight,
                      bankTrialColdEarlyCleanPatternCut,
                      bankTrialColdEarlyGrantCut, hc, hz,
                      bankTrialColdScheduleOne,
                      bankTrialSuccessStageIndexSumZero]
                | defect =>
                    simp [bankTrialColdEarlyRewardWeight,
                      bankTrialColdEarlyCleanPatternCut,
                      bankTrialColdEarlyGrantCut, hc, hz,
                      bankTrialColdScheduleZero,
                      bankTrialSuccessStageIndexSumZero]
  · simp [bankTrialColdEarlyRewardWeight,
      bankTrialColdEarlyCleanPatternCut,
      bankTrialColdEarlyGrantCut, hc,
      bankTrialColdScheduleZero, bankTrialSuccessStageIndexSumZero]

private theorem bankTrialColdMaskedCostCutDecomposition
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T W L H : Nat) (cut : List (Fin n)) :
    Prob.scheduleSum n (T - cut.length) (fun suffix =>
      bankTrialColdEarlyMaskedCostWeight ring root W L H cut
        (Prob.stoppedTapeRun
          (Counter.resetClockBankColdNext ring root hsp)
          cut (Counter.resetClockBankColdStart ring root x))
        suffix) =
    bankTrialSuccessStageIndexSum (fun j =>
      bankTrialColdEarlyCleanMaskedCostCut
        ring root hsp x T W L j cut) H := by
  by_cases hc : cut.length ≤ W
  · cases hz : Prob.stoppedTapeRun
        (Counter.resetClockBankColdNext ring root hsp)
        cut (Counter.resetClockBankColdStart ring root x) with
    | inl a =>
        simp [bankTrialColdEarlyMaskedCostWeight,
          bankTrialColdEarlyCleanMaskedCostCut, hc, hz,
          bankTrialColdScheduleZero,
          bankTrialSuccessStageIndexSumZero]
    | inr z =>
        cases z with
        | inl a =>
            simp [bankTrialColdEarlyMaskedCostWeight,
              bankTrialColdEarlyCleanMaskedCostCut, hc, hz,
              bankTrialColdScheduleZero,
              bankTrialSuccessStageIndexSumZero]
        | inr outcome =>
            cases outcome with
            | mk D reason =>
                cases reason with
                | clean =>
                    simpa only [bankTrialColdEarlyMaskedCostWeight,
                      bankTrialColdEarlyCleanMaskedCostCut,
                      if_pos hc, hz] using
                      (bankTrialColdScheduleMaskedIndex
                        ring root D cut T L H)
                | grant =>
                    simp [bankTrialColdEarlyMaskedCostWeight,
                      bankTrialColdEarlyCleanMaskedCostCut, hc, hz,
                      bankTrialColdScheduleZero,
                      bankTrialSuccessStageIndexSumZero]
                | defect =>
                    simp [bankTrialColdEarlyMaskedCostWeight,
                      bankTrialColdEarlyCleanMaskedCostCut, hc, hz,
                      bankTrialColdScheduleZero,
                      bankTrialSuccessStageIndexSumZero]
  · simp [bankTrialColdEarlyMaskedCostWeight,
      bankTrialColdEarlyCleanMaskedCostCut, hc,
      bankTrialColdScheduleZero, bankTrialSuccessStageIndexSumZero]

/-- Distribute a pointwise cutwise reward into its indexed
CLEAN and one-time terminal grant parts on a finite list. -/
private theorem bankTrialColdListRewardConvolution
    {α : Type} (xs : List α)
    (f g : α → Nat) (A : Nat → α → Nat) (H : Nat)
    (h : ∀ z, z ∈ xs →
      f z = bankTrialSuccessStageIndexSum
        (fun j => A j z) H + g z) :
    (xs.map f).sum =
      bankTrialSuccessStageIndexSum
        (fun j => (xs.map (A j)).sum) H +
      (xs.map g).sum := by
  calc
    (xs.map f).sum =
      (xs.map (fun z =>
        bankTrialSuccessStageIndexSum
          (fun j => A j z) H + g z)).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro z hz
        exact h z hz
    _ = (xs.map (fun z =>
          bankTrialSuccessStageIndexSum
            (fun j => A j z) H)).sum + (xs.map g).sum :=
          bankTrialRenewalNatMapSumAdd _ _ _
    _ = _ := congrArg
      (fun v => v + (xs.map g).sum)
      (bankTrialColdStageListExchange xs A H)

private theorem bankTrialColdListMaskedConvolution
    {α : Type} (xs : List α)
    (f : α → Nat) (A : Nat → α → Nat) (H : Nat)
    (h : ∀ z, z ∈ xs →
      f z = bankTrialSuccessStageIndexSum (fun j => A j z) H) :
    (xs.map f).sum =
      bankTrialSuccessStageIndexSum
        (fun j => (xs.map (A j)).sum) H := by
  calc
    (xs.map f).sum =
      (xs.map (fun z =>
        bankTrialSuccessStageIndexSum (fun j => A j z) H)).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro z hz
        exact h z hz
    _ = _ := bankTrialColdStageListExchange xs A H

/-- The exact reward bridge on the same first-stop cut list. -/
theorem bankTrialColdEarlyRewardMassBridge
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T W L H : Nat) :
    bankTrialColdEarlyRewardMass ring root hsp x T W L H =
      bankTrialSuccessStageIndexSum (fun j =>
        bankTrialRenewalColdEarlyCleanSum ring root hsp x T W
          (fun cut D =>
            bankTrialRenewalPatternMass ring root
              (GrantBankReference.bankLocalReferenceStart ring root D)
              (T - cut.length) L j)) H +
      bankTrialRenewalColdEarlyGrantMass ring root hsp x T W := by
  rw [bankTrialColdEarlyRewardFirstStopFactor]
  change
    ((Prob.firstStoppedPrefixes
      (Counter.resetClockBankColdNext ring root hsp)
      (bankTrialRenewalColdStop ring root)
      T [] (Counter.resetClockBankColdStart ring root x)).map
      (fun cut =>
        Prob.scheduleSum n (T - cut.length) (fun suffix =>
          bankTrialColdEarlyRewardWeight ring root W L H cut
            (Prob.stoppedTapeRun
              (Counter.resetClockBankColdNext ring root hsp)
              cut (Counter.resetClockBankColdStart ring root x))
            suffix))).sum =
    bankTrialSuccessStageIndexSum (fun j =>
      ((Prob.firstStoppedPrefixes
        (Counter.resetClockBankColdNext ring root hsp)
        (bankTrialRenewalColdStop ring root)
        T [] (Counter.resetClockBankColdStart ring root x)).map
        (bankTrialColdEarlyCleanPatternCut
          ring root hsp x T W L j)).sum) H +
      ((Prob.firstStoppedPrefixes
        (Counter.resetClockBankColdNext ring root hsp)
        (bankTrialRenewalColdStop ring root)
        T [] (Counter.resetClockBankColdStart ring root x)).map
        (bankTrialColdEarlyGrantCut ring root hsp x T W)).sum
  apply bankTrialColdListRewardConvolution
  intro cut _
  exact bankTrialColdRewardCutDecomposition
    ring root hsp x T W L H cut

/-- The exact masked-cost bridge on the same first-stop cut list. -/
theorem bankTrialColdEarlyMaskedCostMassBridge
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (T W L H : Nat) :
    bankTrialColdEarlyMaskedCostMass ring root hsp x T W L H =
      bankTrialSuccessStageIndexSum (fun j =>
        bankTrialRenewalColdEarlyCleanSum ring root hsp x T W
          (fun cut D =>
            cut.length * bankTrialRenewalPatternMass ring root
              (GrantBankReference.bankLocalReferenceStart ring root D)
              (T - cut.length) L j +
            bankTrialRenewalPatternCost ring root
              (GrantBankReference.bankLocalReferenceStart ring root D)
              (T - cut.length) L j)) H := by
  rw [bankTrialColdEarlyMaskedCostFirstStopFactor]
  change
    ((Prob.firstStoppedPrefixes
      (Counter.resetClockBankColdNext ring root hsp)
      (bankTrialRenewalColdStop ring root)
      T [] (Counter.resetClockBankColdStart ring root x)).map
      (fun cut =>
        Prob.scheduleSum n (T - cut.length) (fun suffix =>
          bankTrialColdEarlyMaskedCostWeight ring root W L H cut
            (Prob.stoppedTapeRun
              (Counter.resetClockBankColdNext ring root hsp)
              cut (Counter.resetClockBankColdStart ring root x))
            suffix))).sum =
    bankTrialSuccessStageIndexSum (fun j =>
      ((Prob.firstStoppedPrefixes
        (Counter.resetClockBankColdNext ring root hsp)
        (bankTrialRenewalColdStop ring root)
        T [] (Counter.resetClockBankColdStart ring root x)).map
        (bankTrialColdEarlyCleanMaskedCostCut
          ring root hsp x T W L j)).sum) H
  apply bankTrialColdListMaskedConvolution
  intro cut _
  exact bankTrialColdMaskedCostCutDecomposition
    ring root hsp x T W L H cut

end L3

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-! Coefficientwise mass/cost convolution on the original cold tape. -/

private def bankTrialColdLowerBase (n q L : Nat) : Nat :=
  1024 * (L * 2 ^ (compileAdvice q).K - L -
    2 ^ (compileAdvice q).K *
      ((8 * (compileAdvice q).b + 12) * n))

private def bankTrialColdDenominatorBase (q L : Nat) : Nat :=
  1024 * (L * 2 ^ (compileAdvice q).K)

private def bankTrialColdCoefficient
    (n q L H j : Nat) : Nat :=
  (bankTrialColdLowerBase n q L) ^ j * (1023 * L) *
    (bankTrialColdDenominatorBase q L) ^ (H - (j + 1))

/-- The earlier per-index theta/LOST mass, lifted to a shared den^H
and summed over the exact original first-stopped CLEAN list. -/
theorem bankTrialColdMassConvolution
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (hlarge :
      2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (L W H T : Nat)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold
      n (ceilLogTwo n) ≤ L)
    (hbudgetCold : W + H * L ≤ T) :
    bankTrialRenewalColdEarlyCleanSum ring root hsp x T W
        (fun cut _ => n ^ (T - cut.length)) *
      bankTrialSuccessStageIndexSum
        (bankTrialColdCoefficient n (ceilLogTwo n) L H) H ≤
    (bankTrialColdDenominatorBase (ceilLogTwo n) L) ^ H *
      bankTrialSuccessStageIndexSum (fun j =>
        bankTrialRenewalColdEarlyCleanSum ring root hsp x T W
          (fun cut D =>
            bankTrialRenewalPatternMass ring root
              (GrantBankReference.bankLocalReferenceStart ring root D)
              (T - cut.length) L j)) H := by
  have hindex := bankTrialRenewalStageIndexMonoBelow
    (fun j =>
      bankTrialRenewalColdEarlyCleanSum ring root hsp x T W
        (fun cut _ => n ^ (T - cut.length)) *
      bankTrialColdCoefficient n (ceilLogTwo n) L H j)
    (fun j =>
      (bankTrialColdDenominatorBase (ceilLogTwo n) L) ^ H *
      bankTrialRenewalColdEarlyCleanSum ring root hsp x T W
        (fun cut D =>
          bankTrialRenewalPatternMass ring root
            (GrantBankReference.bankLocalReferenceStart ring root D)
            (T - cut.length) L j))
    H (by
      intro j hj
      have hle : j + 1 ≤ H := by omega
      have hrow := bankTrialRenewalColdEarlyCleanIndexMassBound
        ring root hn hsp hw hlarge x L W H T j
        hL hbudgetCold hj
      have hscaled := bankTrialRenewalCommonPowerLift
        (bankTrialColdDenominatorBase (ceilLogTwo n) L)
        (bankTrialColdLowerBase n (ceilLogTwo n) L)
        (1023 * L)
        (bankTrialRenewalColdEarlyCleanSum ring root hsp x T W
          (fun cut _ => n ^ (T - cut.length)))
        H j
        (bankTrialRenewalColdEarlyCleanSum ring root hsp x T W
          (fun cut D =>
            bankTrialRenewalPatternMass ring root
              (GrantBankReference.bankLocalReferenceStart ring root D)
              (T - cut.length) L j))
        hle (by
          simpa only [bankTrialColdDenominatorBase,
            bankTrialColdLowerBase] using hrow)
      simpa only [bankTrialColdCoefficient] using hscaled)
  simpa only [bankTrialSuccessStageIndexSumScale] using hindex

/-- Each coefficient has P times its weight bounded by den^H;
summing contributes H late/no-stop charges, not H copies of an
unmasked early CLEAN prefix. -/
theorem bankTrialColdLateConvolution
    (n q L H : Nat) :
    2 ^ (compileAdvice q).K *
      bankTrialSuccessStageIndexSum
        (bankTrialColdCoefficient n q L H) H ≤
      (bankTrialColdDenominatorBase q L) ^ H * H := by
  have hindex := bankTrialRenewalStageIndexMonoBelow
    (fun j =>
      2 ^ (compileAdvice q).K *
        bankTrialColdCoefficient n q L H j)
    (fun _ => (bankTrialColdDenominatorBase q L) ^ H)
    H (by
      intro j hj
      simpa only [bankTrialColdCoefficient,
        bankTrialColdLowerBase, bankTrialColdDenominatorBase] using
        (bankTrialRenewalColdLateIndexWeight n q L H j hj))
  rw [bankTrialSuccessStageIndexSumScale,
    bankTrialSuccessStageIndexSumConstant] at hindex
  rw [Nat.mul_comm ((bankTrialColdDenominatorBase q L) ^ H) H]
  exact hindex

private theorem bankTrialColdStageAdd
    (f g : Nat → Nat) :
    ∀ H : Nat,
      bankTrialSuccessStageIndexSum
        (fun j => f j + g j) H =
      bankTrialSuccessStageIndexSum f H +
        bankTrialSuccessStageIndexSum g H := by
  intro H
  induction H with
  | zero =>
      rfl
  | succ k ih =>
      change bankTrialSuccessStageIndexSum
          (fun j => f j + g j) k + (f k + g k) =
        (bankTrialSuccessStageIndexSum f k + f k) +
          (bankTrialSuccessStageIndexSum g k + g k)
      rw [ih]
      omega

/-- The earlier genuine joint charge is paid once per *index*;
exchange the index sum and the masked first-stop cost via the
proved cost bridge. -/
theorem bankTrialColdMaskedCostConvolution
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (hlarge :
      2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (L W H T : Nat)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold
      n (ceilLogTwo n) ≤ L)
    (hbudgetCold : W + H * L ≤ T) :
    2 ^ (compileAdvice (ceilLogTwo n)).K *
        bankTrialColdEarlyMaskedCostMass ring root hsp x T W L H +
      H * (W * bankTrialRenewalColdLateMass
        ring root hsp x T W) ≤
    n ^ T * bankTrialSuccessStageIndexSum (fun j =>
      n * ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
          5 * (compileAdvice (ceilLogTwo n)).b + 13) +
        bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
        j * bankTrialRenewalIndexStepCharge (ceilLogTwo n))) H := by
  have hindex := bankTrialRenewalStageIndexMonoBelow
    (fun j =>
      2 ^ (compileAdvice (ceilLogTwo n)).K *
        bankTrialRenewalColdEarlyCleanSum ring root hsp x T W
          (fun cut D =>
            cut.length * bankTrialRenewalPatternMass ring root
              (GrantBankReference.bankLocalReferenceStart ring root D)
              (T - cut.length) L j +
            bankTrialRenewalPatternCost ring root
              (GrantBankReference.bankLocalReferenceStart ring root D)
              (T - cut.length) L j) +
      W * bankTrialRenewalColdLateMass ring root hsp x T W)
    (fun j =>
      n ^ T * (n *
        ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
            5 * (compileAdvice (ceilLogTwo n)).b + 13) +
          bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
          j * bankTrialRenewalIndexStepCharge (ceilLogTwo n))))
    H (by
      intro j hj
      exact bankTrialRenewalColdJointIndexCharge
        ring root hn hsp hw hlarge x L W H T j
        hL hbudgetCold hj)
  calc
    2 ^ (compileAdvice (ceilLogTwo n)).K *
        bankTrialColdEarlyMaskedCostMass ring root hsp x T W L H +
      H * (W * bankTrialRenewalColdLateMass
        ring root hsp x T W) =
      bankTrialSuccessStageIndexSum (fun j =>
        2 ^ (compileAdvice (ceilLogTwo n)).K *
          bankTrialRenewalColdEarlyCleanSum ring root hsp x T W
            (fun cut D =>
              cut.length * bankTrialRenewalPatternMass ring root
                (GrantBankReference.bankLocalReferenceStart ring root D)
                (T - cut.length) L j +
              bankTrialRenewalPatternCost ring root
                (GrantBankReference.bankLocalReferenceStart ring root D)
                (T - cut.length) L j) +
        W * bankTrialRenewalColdLateMass ring root hsp x T W) H := by
          rw [bankTrialColdStageAdd,
            bankTrialSuccessStageIndexSumScale,
            bankTrialSuccessStageIndexSumConstant,
            bankTrialColdEarlyMaskedCostMassBridge]
    _ ≤ bankTrialSuccessStageIndexSum (fun j =>
        n ^ T * (n *
          ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
              5 * (compileAdvice (ceilLogTwo n)).b + 13) +
            bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
            j * bankTrialRenewalIndexStepCharge (ceilLogTwo n)))) H :=
            hindex
    _ = _ := bankTrialSuccessStageIndexSumScale _ _ H

end L3

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-! Cold cleared-window conclusion and the paper's coefficient bound. -/

/-- The cold version of the Clean AnyH window, with its full first
stop partition and one joint stopped-cost charge per successful
index. No hypothetical leaf is supplied by the caller. -/
theorem bankTrialRenewalColdClearedWindowAnyH
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 5 ≤ n)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (hlarge :
      2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (L H T W : Nat)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold
      n (ceilLogTwo n) ≤ L)
    (hwindow : W ≤ T)
    (hbudgetCold : W + H * L ≤ T) :
    BankTrialRenewalColdClearedWindowProperty
      ring root hsp x L H T W := by
  have hpartition := bankTrialRenewalColdFirstStopPartition
    ring root hsp x T W hwindow
  have hmass := bankTrialColdMassConvolution
    ring root hn hsp hw hlarge x L W H T hL hbudgetCold
  have hgeo :
      bankTrialSuccessStageIndexSum
        (bankTrialColdCoefficient n (ceilLogTwo n) L H) H ≤
      (bankTrialColdDenominatorBase (ceilLogTwo n) L) ^ H := by
    exact bankTrialRenewalColdGeometricCoefficientSumBound
      n (ceilLogTwo n) L H
  have hlate := bankTrialColdLateConvolution
    n (ceilLogTwo n) L H
  have hwindowMass := bankTrialRenewalColdGlobalMaskedWindow
    ring root hsp x T W L H
  rw [bankTrialColdEarlyRewardMassBridge] at hwindowMass
  have hcost := bankTrialColdMaskedCostConvolution
    ring root hn hsp hw hlarge x L W H T hL hbudgetCold
  have hcombined := bankTrialColdWindowCompositionArithmetic
    W
    (2 ^ (compileAdvice (ceilLogTwo n)).K)
    (n ^ T)
    ((bankTrialColdDenominatorBase (ceilLogTwo n) L) ^ H)
    (bankTrialSuccessStageIndexSum
      (bankTrialColdCoefficient n (ceilLogTwo n) L H) H)
    (bankTrialRenewalColdEarlyCleanSum ring root hsp x T W
      (fun cut _ => n ^ (T - cut.length)))
    (bankTrialRenewalColdEarlyGrantMass ring root hsp x T W)
    (bankTrialRenewalColdDefectMass ring root hsp x T W)
    (bankTrialRenewalColdLateMass ring root hsp x T W)
    (bankTrialSuccessStageIndexSum (fun j =>
      bankTrialRenewalColdEarlyCleanSum ring root hsp x T W
        (fun cut D =>
          bankTrialRenewalPatternMass ring root
            (GrantBankReference.bankLocalReferenceStart ring root D)
            (T - cut.length) L j)) H)
    (bankTrialRenewalColdProxyMass ring root hsp x T W)
    (bankTrialColdEarlyMaskedCostMass ring root hsp x T W L H)
    (bankTrialSuccessStageIndexSum (fun j =>
      n * ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
          5 * (compileAdvice (ceilLogTwo n)).b + 13) +
        bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
        j * bankTrialRenewalIndexStepCharge (ceilLogTwo n))) H)
    H hpartition hmass hgeo hlate hwindowMass hcost
  change
    W * 2 ^ (compileAdvice (ceilLogTwo n)).K * n ^ T *
      bankTrialSuccessStageIndexSum
        (bankTrialColdCoefficient n (ceilLogTwo n) L H) H ≤
    (bankTrialColdDenominatorBase (ceilLogTwo n) L) ^ H *
      (W * 2 ^ (compileAdvice (ceilLogTwo n)).K *
        (bankTrialRenewalColdProxyMass ring root hsp x T W +
         bankTrialRenewalColdDefectMass ring root hsp x T W) +
       n ^ T * bankTrialSuccessStageIndexSum (fun j =>
         n * ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
             5 * (compileAdvice (ceilLogTwo n)).b + 13) +
           bankTrialRenewalIndexZeroCharge (ceilLogTwo n) +
           j * bankTrialRenewalIndexStepCharge (ceilLogTwo n))) H)
  exact hcombined

/-- Unconditional cold proxy-plus-defect probability lower bound.
The only hypotheses are the earlier cutoffs and the cold
window budget; L1 is discharged internally. -/
theorem bankTrialRenewalColdSuccessMassLower
    {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (hn : 5 ≤ n)
    (hsmall : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hw : BankTrialLiveWindowNonalias n (ceilLogTwo n))
    (hlarge :
      2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap ≤ n)
    (x : Counter.ResetClockBankColdCarrier
      (q := ceilLogTwo n) ring root)
    (R L T W : Nat)
    (hradius : (256 * R) ^ 2 ≤ n ∧
      n < (256 * (R + 1)) ^ 2)
    (hW : W = R * n / 8)
    (hL : 1024 * bankTrialRenewalWonCutoffThreshold
      n (ceilLogTwo n) ≤ L)
    (hwindow : W ≤ T)
    (hbudgetCold :
      W + bankTrialRenewalIndexWindowCount
        n (ceilLogTwo n) W * L ≤ T) :
    51279921 * W * n ^ T ≤
      104857600 * (8 * (compileAdvice (ceilLogTwo n)).b + 13) *
        n * 2 ^ (compileAdvice (ceilLogTwo n)).K *
        (bankTrialRenewalColdProxyMass ring root hsmall x T W +
         bankTrialRenewalColdDefectMass ring root hsmall x T W) := by
  exact bankTrialRenewalColdSuccessMassLower_ofClearedWindow
    ring root hn hsmall hw hlarge x R L T W
    hradius hW hL hwindow hbudgetCold
    (bankTrialRenewalColdClearedWindowAnyH
      ring root hn hsmall hw hlarge x L
      (bankTrialRenewalIndexWindowCount n (ceilLogTwo n) W)
      T W hL hwindow hbudgetCold)

end L3



#print axioms L3.bankTrialRenewalActiveCutoff
#print axioms L3.bankTrialRenewalWonStep
#print axioms L3.bankTrialRenewalWonMonotone
#print axioms L3.bankTrialRenewalCompletedSuccessCost
#print axioms L3.bankTrialRenewalCompletedFailureCost
#print axioms L3.bankTrialRenewalAdvanceElapsed
#print axioms L3.bankTrialRenewalNextWon
#print axioms L3.bankTrialRenewalNextElapsed
#print axioms L3.bankTrialRenewalRunFromAppend
#print axioms L3.bankTrialRenewalRunFromWon
#print axioms L3.bankTrialRenewalRunFromElapsedMono
#print axioms L3.bankTrialRenewalWonWithinCutoff
#print axioms L3.bankTrialRenewalPatternDisjoint
#print axioms L3.bankTrialRenewalPatternSound
#print axioms L3.bankTrialRenewalWordWindow
#print axioms L3.bankTrialRenewalWindowInequality
#print axioms L3.bankTrialRenewalFirstLostFactor
#print axioms L3.bankTrialRenewalFirstLostExtensionCount
#print axioms L3.bankTrialRenewalAdvanceShift
#print axioms L3.bankTrialRenewalNextShift
#print axioms L3.bankTrialRenewalRunShift
#print axioms L3.bankTrialRenewalLostRestartLetter
#print axioms L3.bankTrialRenewalLostRestartSuffix
#print axioms L3.bankTrialRenewalPatternAppend
#print axioms L3.bankTrialRenewalFirstLostCutSound
#print axioms L3.bankTrialRenewalFirstLostCutoffKernel
#print axioms L3.bankTrialRenewalFirstLostScanner
#print axioms L3.bankTrialRenewalFirstLostScannerSuffix
#print axioms L3.bankTrialRenewalFirstLostCutClean
#print axioms L3.bankTrialRenewalPatternFirstLostSuffix
#print axioms L3.bankTrialRenewalTauFirstLostSuffix
#print axioms L3.bankTrialRenewalPatternFromStart
#print axioms L3.bankTrialRenewalWholeEvent
#print axioms L3.bankTrialRenewalMassFirstLostExact
#print axioms L3.bankTrialRenewalMassSandwichOfTrialBounds
#print axioms L3.bankTrialRenewalCostFirstLostExact
#print axioms L3.bankTrialRenewalFirstLostCylinderLe
#print axioms L3.bankTrialRenewalLostBoundedExtensionLe
#print axioms L3.bankTrialRenewalCostSandwichOfTrialBounds
#print axioms L3.bankTrialRenewalZeroRareWithinBoundHolds
#print axioms L3.bankTrialRenewalZeroCostWithinBoundHolds
#print axioms L3.bankTrialRenewalFirstLostLengthMomentExact
#print axioms L3.bankTrialRenewalLostCostWithinBoundHolds
#print axioms L3.bankTrialRenewalLocalWonImpliesZeroPattern
#print axioms L3.bankTrialRenewalWonWithinBoundOfCutoff
#print axioms L3.bankTrialRenewalLostBoundedExtensionPadding
#print axioms L3.bankTrialRenewalFirstLostExtensionMassExact
#print axioms L3.bankTrialRenewalLostBoundedAtHorizonExact
#print axioms L3.bankTrialRenewalLostWithinBoundOfCutoff
#print axioms L3.bankTrialRenewalWonWithinBoundCommonDenOfCutoff
#print axioms L3.bankTrialRenewalSuccessByRun
#print axioms L3.bankTrialRenewalSuccessMassEqHitMass
#print axioms L3.bankTrialRenewalOtherPatternFalse
#print axioms L3.bankTrialRenewalPatternSuccessByOfTauLe
#print axioms L3.bankTrialRenewalWindowInequalitySuccessMass
#print axioms L3.bankTrialRenewalClearedWindowOfSandwiches
#print axioms L3.bankTrialSuccessThetaLowerAtUniformHorizon
#print axioms L3.bankTrialSuccessThetaLowerUniform
#print axioms L3.bankTrialRenewalWonCutoffHolds
#print axioms L3.bankTrialRenewalWonWithinBoundUniform
#print axioms L3.bankTrialRenewalWonWithinBoundCommonDenUniform
#print axioms L3.bankTrialRenewalLostWithinBoundUniform
#print axioms L3.bankTrialRenewalZeroCostWithinBoundUniform
#print axioms L3.bankTrialRenewalWonCutoffHoldsSharp
#print axioms L3.bankTrialRenewalActiveLeWonSharp
#print axioms L3.bankTrialRenewalCompletedSuccessCostSharp
#print axioms L3.bankTrialRenewalZeroCostWithinBoundSharp
#print axioms L3.bankTrialRenewalEvalCompiledQuota
#print axioms L3.bankTrialRenewalEvalThetaWonBound
#print axioms L3.bankTrialRenewalEvalThetaMassSandwich
#print axioms L3.bankTrialRenewalEvalClearedCleanWindow
#print axioms L3.bankTrialRenewalEvalThetaCostCertificate
#print axioms L3.bankTrialRenewalIndexSharpCutoffCovered
#print axioms L3.bankTrialRenewalIndexClearedCleanWindowAnyH
#print axioms L3.bankTrialRenewalIndexClearedCleanWindow
#print axioms L3.bankTrialRenewalIndexThetaSquareClearing
#print axioms L3.bankTrialRenewalIndexThetaCostStrict
#print axioms L3.bankTrialRenewalIndexLostDenLower
#print axioms L3.bankTrialRenewalIndexLostDenIdentity
#print axioms L3.bankTrialRenewalIndexSumStrong
#print axioms L3.bankTrialRenewalIndexSumFortyNine
#print axioms L3.bankTrialRenewalIndexBernoulli
#print axioms L3.bankTrialRenewalIndexCompiledColdReserve
#print axioms L3.bankTrialRenewalIndexCompiledQuotas
#print axioms L3.bankTrialRenewalIndexCompiledGeometricBudget
#print axioms L3.bankTrialRenewalIndexSuccessMassLower
#print axioms L3.bankTrialRenewalColdCleanReference
#print axioms L3.bankTrialRenewalColdSoundCleanReference
#print axioms L3.bankTrialRenewalColdTerminalShape
#print axioms L3.bankTrialRenewalColdTerminalPhysicalCases
#print axioms L3.bankTrialRenewalColdStopCorrect
#print axioms L3.bankTrialRenewalColdFirstStopFactor
#print axioms L3.bankTrialRenewalColdProxyDefectZero
#print axioms L3.bankTrialRenewalColdProxyFactor
#print axioms L3.bankTrialRenewalColdCostBundle
#print axioms L3.bankTrialRenewalColdSoundCleanMassLower
#print axioms L3.bankTrialRenewalColdStartNonReset
#print axioms L3.bankTrialRenewalColdImmediateDefect
#print axioms L3.bankTrialRenewalColdImmediateNoDefect
#print axioms L3.bankTrialRenewalColdFrozenGoodEdge
#print axioms L3.bankTrialRenewalColdDefectConcrete
#print axioms L3.bankTrialRenewalFrozenSupportIdentity
#print axioms L3.bankTrialRenewalFrozenSafePhysicalPrefix
#print axioms L3.bankTrialRenewalFrozenFirstPhysicalSuccess
#print axioms L3.bankTrialRenewalColdCleanRemainingWindow
#print axioms L3.bankTrialRenewalColdGrantWithinWindow
#print axioms L3.bankTrialRenewalColdCostInsideReserve
#print axioms L3.bankTrialRenewalColdCleanIndexCutWindow
#print axioms L3.bankTrialRenewalColdIndexCutWindow
#print axioms L3.bankTrialRenewalColdIndexStageMassFactor
#print axioms L3.bankTrialRenewalColdIndexStageCostFactor
#print axioms L3.bankTrialRenewalColdIndexWeightedWindow
#print axioms L3.bankTrialRenewalColdMarkovReserve
#print axioms L3.bankTrialBufferedColdSelected
#print axioms L3.bankTrialBufferedColdGoodEdgeFrame
#print axioms L3.bankTrialBufferedColdRolesStep
#print axioms L3.bankTrialBufferedColdNoDefectEntry
#print axioms L3.bankTrialBufferedColdSupportWordPack
#print axioms L3.bankTrialBufferedColdLiveStart
#print axioms L3.bankTrialBufferedColdNextNotDefect
#print axioms L3.bankTrialBufferedColdLiveStep
#print axioms L3.bankTrialBufferedColdRunInvariant
#print axioms L3.bankTrialBufferedColdFrozenRoles
#print axioms L3.bankTrialBufferedColdFrozenInvariant
#print axioms L3.bankTrialBufferedColdReferenceLocality
#print axioms L3.bankTrialBufferedColdFrozenFirstStop
#print axioms L3.bankTrialBufferedColdConcreteWitnessExcluded
#print axioms L3.bankTrialRenewalColdIndexSuffixBudget
#print axioms L3.bankTrialRenewalColdIndexChargeSplit
#print axioms L3.bankTrialRenewalColdCleanIndexCutBounds
#print axioms L3.bankTrialRenewalColdSoundIndexCutBounds
#print axioms L3.bankTrialBufferedBadRoleZeroGood
#print axioms L3.bankTrialBufferedPreGrantFree
#print axioms L3.bankTrialBufferedSelectionOfBufferedCounters
#print axioms L3.bankTrialBufferedSelectionBeforeGrant
#print axioms L3.bankTrialBufferedGrantNotFromGeometry
#print axioms L3.bankTrialBufferedSelectedFrozenNoDefect
#print axioms L3.bankTrialBufferedSpatialPreGrantFrozen
#print axioms L3.bankTrialRenewalColdAuthenticFirstStop
#print axioms L3.bankTrialRenewalColdEarlyCleanIndexMassBound
#print axioms L3.bankTrialRenewalColdEarlyCleanIndexChargeBound
#print axioms L3.bankTrialRenewalColdLateMassMarkov
#print axioms L3.bankTrialRenewalColdLateMassReserve
#print axioms L3.bankTrialRenewalColdLateMassRatio
#print axioms L3.bankTrialRenewalColdGrantDefectWeights
#print axioms L3.bankTrialRenewalColdFirstStopPartition
#print axioms L3.bankTrialRenewalColdDefectMassZero
#print axioms L3.bankTrialRenewalColdEarlyMassAfterCensor
#print axioms L3.bankTrialRenewalColdCleanMaskedWord
#print axioms L3.bankTrialRenewalColdSuccessMassLower_ofClearedWindow
#print axioms L3.bankTrialRenewalColdJointFirstStopCost
#print axioms L3.bankTrialRenewalColdJointFirstStopReserve
#print axioms L3.bankTrialRenewalColdJointIndexCharge
#print axioms L3.bankTrialRenewalColdLateIndexWeight

#print axioms L3.bankTrialColdEarlyRewardCutWindow
#print axioms L3.bankTrialRenewalColdGlobalMaskedWindow
#print axioms L3.bankTrialColdEarlyRewardFirstStopFactor
#print axioms L3.bankTrialColdEarlyMaskedCostFirstStopFactor
#print axioms L3.bankTrialRenewalColdGeometricCoefficientSumBound
#print axioms L3.bankTrialRenewalColdGrantDefectSingleCredit

#print axioms L3.bankTrialColdEarlyRewardMassBridge
#print axioms L3.bankTrialColdEarlyMaskedCostMassBridge
#print axioms L3.bankTrialColdMassConvolution
#print axioms L3.bankTrialColdLateConvolution
#print axioms L3.bankTrialColdMaskedCostConvolution
#print axioms L3.bankTrialRenewalColdClearedWindowAnyH
#print axioms L3.bankTrialRenewalColdSuccessMassLower
