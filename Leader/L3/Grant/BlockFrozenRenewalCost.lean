import Leader.L3.Grant.BlockFrozenRenewalInstance
import Leader.L3.Grant.BlockFrozenLatch
import Leader.L3.Grant.BlockFrozenRecovery
import Leader.L3.RenewalGrantStage

/-!
The stopped cost of the frozen chain, split into its C.3 phase (derived
here from `grantBlockFrozenLatchCanonicalBellman`) and its C.2 recovery
(an explicit hypothesis on the frozen chain).  Consumer:
`GrantBlockFrozenRenewal.lean`.
-/

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- Generic strong-Markov reserve: if from every reachable phase target
the terminal cost is at most `n ^ T * R`, then the terminal cost is at
most the phase cost plus `n ^ T * R`. -/
theorem grantBlockFrozenStageReserve {X : Type} {n : Nat}
    (next : X → Fin n → X) (Term P I : X → Prop) (R : Nat)
    (hTP : ∀ z, Term z → P z)
    (hclosed : ∀ z, I z → ¬ P z → ∀ e : Fin n, I (next z e))
    (hrec : ∀ z, I z → P z → ∀ T,
      costNumerator next Term z T ≤ n ^ T * R) :
    ∀ T z, I z →
      costNumerator next Term z T ≤
        costNumerator next P z T + n ^ T * R := by
  intro T
  induction T with
  | zero =>
      intro z _
      simp only [costNumerator_zero, Nat.zero_add]
      exact Nat.zero_le _
  | succ T ih =>
      intro z hz
      by_cases ha : P z
      · rw [costNumerator_terminal next P z ha (T + 1)]
        simpa only [Nat.zero_add] using hrec z hz ha (T + 1)
      · have hp : ¬ Term z := fun ht => ha (hTP z ht)
        rw [costNumerator_succ next Term z hp T,
          costNumerator_succ next P z ha T]
        have hs :
            (List.ofFn (fun e : Fin n =>
              costNumerator next Term (next z e) T)).sum ≤
            (List.ofFn (fun e : Fin n =>
              costNumerator next P (next z e) T)).sum +
              n * (n ^ T * R) := by
          calc
            _ ≤ (List.ofFn (fun e : Fin n =>
                costNumerator next P (next z e) T +
                n ^ T * R)).sum :=
              ofFn_sum_le _ _ (fun e =>
                ih (next z e) (hclosed z hz ha e))
            _ = _ := by rw [ofFn_sum_add, ofFn_sum_const]
        calc
          _ ≤ n ^ (T + 1) +
              ((List.ofFn (fun e : Fin n =>
                costNumerator next P (next z e) T)).sum +
              n * (n ^ T * R)) := Nat.add_le_add_left hs _
          _ = (n ^ (T + 1) +
              (List.ofFn (fun e : Fin n =>
                costNumerator next P (next z e) T)).sum) +
              n ^ (T + 1) * R := by
            rw [Nat.pow_succ]
            ac_rfl

/-- Phase target of the frozen chain: a terminal reference or a RESET
root. -/
def GrantBlockFrozenPhaseTarget {n : Nat} (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring)
    (S : GrantBlockFrozenRef n) : Prop :=
  (grantBlockFrozenKernel ring member).Terminal S ∨
    (S.fields (0 : Fin ((compileAdvice (ceilLogTwo n)).b + 1))).1 = .RESET

/-- References reached from the member's frozen start. -/
def GrantBlockFrozenReached {n : Nat} (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring)
    (S : GrantBlockFrozenRef n) : Prop :=
  ∃ w : List (Fin n), S =
    GrantBankReference.bankLocalReferenceWordClamped ring member.1 w
      (GrantBankReference.bankLocalReferenceStart ring member.1
        member.2.val)

theorem grantBlockFrozenReachedStep {n : Nat} (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring)
    (S : GrantBlockFrozenRef n) (hS : GrantBlockFrozenReached ring member S)
    (e : Fin n) :
    GrantBlockFrozenReached ring member
      (GrantBankReference.bankLocalReferenceStepClamped ring member.1
        S e) := by
  obtain ⟨w, hw⟩ := hS
  refine ⟨w ++ [e], ?_⟩
  rw [GrantBankReference.bankLocalReferenceWordAppendClamped, ← hw]
  rfl

/-- The C.2 recovery cost of the frozen chain: from every reached
unlatched RESET reference, the expected time to a latched or Clean
reference is at most `(4 b + 6) n`.  This is the one fact about the
frozen chain that is not proved here. -/
def GrantBlockFrozenRecoveryCost {n : Nat} (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring) : Prop :=
  ∀ S : GrantBlockFrozenRef n, GrantBlockFrozenReached ring member S →
    S.success = false →
    (S.fields (0 : Fin ((compileAdvice (ceilLogTwo n)).b + 1))).1 =
      .RESET →
    ∀ T : Nat,
      costNumerator (grantBlockFrozenKernel ring member).next
          (grantBlockFrozenKernel ring member).Terminal S T ≤
        n ^ T * (((4 * (compileAdvice (ceilLogTwo n)).b + 6) * n))

/-- C.3 on the frozen chain: the expected time to a phase target, from
the canonical frozen Bellman inequality at a buffered entrance.

Consumer: `grantBlockFrozenStoppedCostOfRecovery`. -/
theorem grantBlockFrozenPhaseCost {n : Nat} (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring) (radius : Nat)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hbuffered : HeadlineGrantBufferedCounter ring member.2.val radius
      member.1) (T : Nat) :
    costNumerator (grantBlockFrozenKernel ring member).next
        (GrantBlockFrozenPhaseTarget ring member)
        (grantBlockFrozenKernel ring member).start T ≤
      n ^ T * ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
        (compileAdvice (ceilLogTwo n)).b + 7) * n) := by
  have hmain := Prob.costNumerator_le_of_potential_on
    (grantBlockFrozenKernel ring member).next
    (GrantBlockFrozenPhaseTarget ring member)
    (GrantBlockFrozenReached ring member)
    (fun S => grantBlockFrozenColdLocalStoppedCredit n (ceilLogTwo n) S)
    (by
      intro x hx _ e
      exact grantBlockFrozenReachedStep ring member x hx e)
    (by
      intro x hx hnp
      have hnt : ¬ (grantBlockFrozenKernel ring member).Terminal x :=
        fun h => hnp (Or.inl h)
      have hnr : (x.fields (0 : Fin
          ((compileAdvice (ceilLogTwo n)).b + 1))).1 ≠ .RESET :=
        fun h => hnp (Or.inr h)
      have hfalse : x.success = false := by
        cases hs : x.success with
        | false => rfl
        | true =>
            exfalso
            apply hnt
            simp [GrantBlockFrozenKernel.Terminal, grantBlockFrozenKernel,
              hs]
      obtain ⟨w, hw⟩ := hx
      have hbound : GrantBlockFrozenColdLeaseBound (ceilLogTwo n) x := by
        rw [hw]
        exact grantBlockFrozenColdLeaseBoundWord ring member.1 w _
          (grantBlockFrozenColdLeaseBoundStart ring member.2.val
            member.1)
      have hb := grantBlockFrozenLatchCanonicalBellman ring member.2.val
        member.1 radius hsp hbuffered x hbound hfalse hnr
      have hcr : grantBlockFrozenColdLocalStoppedCredit n
          (ceilLogTwo n) x =
          grantBlockFrozenColdLocalActiveCredit n (ceilLogTwo n) x := by
        simp [grantBlockFrozenColdLocalStoppedCredit, hfalse, hnr]
      rw [hcr]
      exact hb)
    (grantBlockFrozenKernel ring member).start ⟨[], rfl⟩ T
  refine Nat.le_trans hmain (Nat.mul_le_mul_left _ ?_)
  -- the stopped credit of the start
  obtain ⟨S0, hS0⟩ : ∃ S0 : GrantBlockFrozenRef n, S0 =
      GrantBankReference.bankLocalReferenceStart ring member.1
        member.2.val := ⟨_, rfl⟩
  have hstart : (grantBlockFrozenKernel ring member).start = S0 :=
    hS0.symm
  rw [hstart]
  have hbound0 : GrantBlockFrozenColdLeaseBound (ceilLogTwo n) S0 := by
    rw [hS0]
    exact grantBlockFrozenColdLeaseBoundStart ring member.2.val member.1
  have hfields := grantBlockFrozenColdEmbedFields ring member.2.val
    member.1 member.2.property.1 S0 hbound0
  have hlarge := Counter.resetColdLargeAtSpatialCutoff n hsp
  have hphys := Counter.resetColdUncappedCredit_start_le_of_large ring
    member.1 hlarge (grantBlockFrozenColdEmbedCarrier ring member.2.val
      member.1 member.2.property.1 S0)
  by_cases hreset : (S0.fields (0 : Fin
      ((compileAdvice (ceilLogTwo n)).b + 1))).1 = .RESET
  · have h := grantBlockFrozenColdRecoveryStartCredit ring member.1
      (grantBlockFrozenColdEmbedCarrier ring member.2.val
        member.1 member.2.property.1 S0) S0 hfields (by rw [hS0]; rfl) hreset
    exact h ▸ hphys
  · have h := grantBlockFrozenColdActiveStartCredit ring member.1
      (grantBlockFrozenColdEmbedCarrier ring member.2.val
        member.1 member.2.property.1 S0) S0 hfields (by rw [hS0]; rfl) hreset
    exact h ▸ hphys

/-- The frozen stopped cost from the C.3 Bellman inequality and the
C.2 recovery cost.

Consumer: `grantBlockFrozenLocalColdClockOfRecovery`. -/
theorem grantBlockFrozenStoppedCostOfRecovery {n : Nat}
    (ring : DirectedRing n) (member : GrantBlockFamilyMember ring)
    (radius : Nat)
    (hsp : (compileAdvice (ceilLogTwo n)).useSmall = false)
    (hbuffered : HeadlineGrantBufferedCounter ring member.2.val radius
      member.1)
    (hrec : GrantBlockFrozenRecoveryCost ring member) (T : Nat) :
    costNumerator (grantBlockFrozenKernel ring member).next
        (grantBlockFrozenKernel ring member).Terminal
        (grantBlockFrozenKernel ring member).start T ≤
      n ^ T * ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
        5 * (compileAdvice (ceilLogTwo n)).b + 13) * n) := by
  have hres := grantBlockFrozenStageReserve
    (grantBlockFrozenKernel ring member).next
    (grantBlockFrozenKernel ring member).Terminal
    (GrantBlockFrozenPhaseTarget ring member)
    (GrantBlockFrozenReached ring member)
    (((4 * (compileAdvice (ceilLogTwo n)).b + 6) * n))
    (fun z h => Or.inl h)
    (fun z hz _ e => grantBlockFrozenReachedStep ring member z hz e)
    (by
      intro z hz hp T'
      rcases hp with ht | hr
      · rw [costNumerator_terminal _ _ z ht T']
        exact Nat.zero_le _
      · by_cases hs : z.success = true
        · have ht : (grantBlockFrozenKernel ring member).Terminal z := by
            simp [GrantBlockFrozenKernel.Terminal, grantBlockFrozenKernel,
              hs]
          rw [costNumerator_terminal _ _ z ht T']
          exact Nat.zero_le _
        · have hs' : z.success = false := by simpa using hs
          exact hrec z hz hs' hr T')
    T _ ⟨[], rfl⟩
  have hph := grantBlockFrozenPhaseCost ring member radius hsp hbuffered T
  have hcoef := Counter.resetClockBankColdCompositionCoefficient n
    (compileAdvice (ceilLogTwo n)).bankLeaseCap
    (compileAdvice (ceilLogTwo n)).b
  calc
    _ ≤ _ := hres
    _ ≤ n ^ T * ((2 * (compileAdvice (ceilLogTwo n)).bankLeaseCap +
          (compileAdvice (ceilLogTwo n)).b + 7) * n) +
        n ^ T * (((4 * (compileAdvice (ceilLogTwo n)).b + 6) * n)) :=
      Nat.add_le_add_right hph _
    _ = _ := by
      rw [← Nat.mul_add, hcoef]

end L3
#print axioms L3.grantBlockFrozenStageReserve
#print axioms L3.grantBlockFrozenPhaseCost
#print axioms L3.grantBlockFrozenStoppedCostOfRecovery
