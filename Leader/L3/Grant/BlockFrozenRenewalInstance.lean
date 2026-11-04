import Leader.L3.Grant.BlockFrozenRenewalBridge
import Leader.L3.Grant.BlockFrozenAmplification
import Leader.L3.Grant.BlockFrozenColdClock
import Leader.L3.Grant.BlockNegCorr

/-!
The frozen chain as a CLEAN / GRANT kernel, and the comparison of its
proxy mass with the frozen proxy mass.  Consumer:
`GrantBlockFrozenRenewal.lean`.
-/

namespace L3

open Classical
open FiniteUniformStoppingTree
open K2ArbitraryElimination.FiniteAccounting

set_option autoImplicit false
set_option Elab.async false

/-- A stopped word is zero or the weight of its unique first-stop leaf. -/
theorem grantBlockFrozenStoppedWordLeaf {X : Type} {n : Nat}
    (next : X → Fin n → X) (stop : List (Fin n) → X → Bool)
    (F : List (Fin n) → X → List (Fin n) → Nat) :
    ∀ (word : List (Fin n)) (t : Nat) (pre : List (Fin n)) (z : X),
      bankTrialSuccessNatStoppedWord next stop
        (fun cut z _ suffix => F cut z suffix) t pre z word = 0 ∨
      ∃ u v : List (Fin n), word = u ++ v ∧
        bankTrialSuccessNatStoppedWord next stop
          (fun cut z _ suffix => F cut z suffix) t pre z word =
          F (pre ++ u) (Prob.stoppedTapeRun next u z) v := by
  intro word
  induction word with
  | nil =>
      intro t pre z
      cases hs : stop pre z with
      | true =>
          right
          exact ⟨[], [], rfl, by
            simp [bankTrialSuccessNatStoppedWord, hs,
              Prob.stoppedTapeRun]⟩
      | false =>
          left
          simp [bankTrialSuccessNatStoppedWord, hs]
  | cons e tail ih =>
      intro t pre z
      cases hs : stop pre z with
      | true =>
          right
          exact ⟨[], e :: tail, rfl, by
            simp [bankTrialSuccessNatStoppedWord, hs,
              Prob.stoppedTapeRun]⟩
      | false =>
          have hrec : bankTrialSuccessNatStoppedWord next stop
              (fun cut z _ suffix => F cut z suffix) t pre z
              (e :: tail) =
            bankTrialSuccessNatStoppedWord next stop
              (fun cut z _ suffix => F cut z suffix) (t - 1)
              (pre ++ [e]) (next z e) tail := by
            simp [bankTrialSuccessNatStoppedWord, hs]
          rw [hrec]
          rcases ih (t - 1) (pre ++ [e]) (next z e) with h | ⟨u, v, hw, hv⟩
          · exact Or.inl h
          · right
            refine ⟨e :: u, v, by simp [hw], ?_⟩
            rw [hv]
            simp [Prob.stoppedTapeRun]

/-- The frozen chain as a CLEAN / GRANT kernel: states are clamped local
references, stepped by the clamped BANK row, stopped at the first latched
success (GRANT) or Clean reference (CLEAN). -/
noncomputable def grantBlockFrozenKernel {n : Nat} (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring) : GrantBlockFrozenKernel n where
  X := GrantBlockFrozenRef n
  next := fun S e =>
    GrantBankReference.bankLocalReferenceStepClamped ring member.1 S e
  start := GrantBankReference.bankLocalReferenceStart ring member.1
    member.2.val
  kind := fun S =>
    if S.success = true then .grant
    else if BankTrialLocalClean (ceilLogTwo n) S then .clean S
    else .live

theorem grantBlockFrozenKernelRun {n : Nat} (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring) :
    ∀ (w : List (Fin n)) (S : GrantBlockFrozenRef n),
      Prob.stoppedTapeRun (grantBlockFrozenKernel ring member).next w S =
        GrantBankReference.bankLocalReferenceWordClamped ring member.1
          w S := by
  intro w
  induction w with
  | nil => intro S; rfl
  | cons e es ih => intro S; exact ih _

/-- Every CLEAN label of the frozen kernel carries a Clean reference. -/
theorem grantBlockFrozenKernelCleanSound {n : Nat} (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring) :
    (grantBlockFrozenKernel ring member).CleanSound := by
  intro cut S hk
  change (if (Prob.stoppedTapeRun (grantBlockFrozenKernel ring member).next
      cut _).success = true then _ else _) = _ at hk
  generalize Prob.stoppedTapeRun (grantBlockFrozenKernel ring member).next
    cut (grantBlockFrozenKernel ring member).start = R at hk
  by_cases h1 : R.success = true
  · simp [h1] at hk
  · by_cases h2 : BankTrialLocalClean (ceilLogTwo n) R
    · simp only [h1, h2, if_true, if_false] at hk
      cases hk
      exact h2
    · simp [h1, h2] at hk

theorem grantBlockFrozenProxyHitClamped {n : Nat} (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring) (w : List (Fin n)) :
    grantBlockFrozenProxyHit ring member w =
      (GrantBankReference.bankLocalReferenceWordClamped ring member.1 w
        (GrantBankReference.bankLocalReferenceStart ring member.1
          member.2.val)).success := by
  unfold grantBlockFrozenProxyHit
  rw [GrantBankReference.bankLocalReferenceWordLocalityClamped]

/-- Pathwise: a positive proxy weight of the frozen kernel is a frozen
hit on the W-prefix of the same word. -/
theorem grantBlockFrozenKernelProxyWord {n : Nat} (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring) (T W : Nat)
    (word : List (Fin n)) :
    bankTrialSuccessNatStoppedWord
        (grantBlockFrozenKernel ring member).next
        (grantBlockFrozenKernel ring member).stop
        (fun cut z _ suffix =>
          (grantBlockFrozenKernel ring member).proxyWeight ring member.1
            W cut z suffix) T []
        (grantBlockFrozenKernel ring member).start word ≤
      (if grantBlockFrozenProxyHit ring member (word.take W)
        then 1 else 0) := by
  rcases grantBlockFrozenStoppedWordLeaf
      (grantBlockFrozenKernel ring member).next
      (grantBlockFrozenKernel ring member).stop
      (fun cut z suffix =>
        (grantBlockFrozenKernel ring member).proxyWeight ring member.1
          W cut z suffix) word T []
      (grantBlockFrozenKernel ring member).start with h | ⟨u, v, hw, hv⟩
  · rw [h]; exact Nat.zero_le _
  · rw [hv]
    obtain ⟨R, hR⟩ : ∃ R : GrantBlockFrozenRef n, R =
        GrantBankReference.bankLocalReferenceWordClamped ring member.1 u
          (GrantBankReference.bankLocalReferenceStart ring member.1
            member.2.val) := ⟨_, rfl⟩
    have hrun : Prob.stoppedTapeRun
        (grantBlockFrozenKernel ring member).next u
        (grantBlockFrozenKernel ring member).start = R := by
      rw [hR]
      exact grantBlockFrozenKernelRun ring member u _
    rw [hrun, List.nil_append]
    by_cases hc : u.length ≤ W
    · have htake : word.take W = u ++ v.take (W - u.length) := by
        rw [hw, List.take_append]
        simp [List.take_of_length_le hc] 
      have hhit : grantBlockFrozenProxyHit ring member (word.take W) =
          (GrantBankReference.bankLocalReferenceWordClamped ring
            member.1 (v.take (W - u.length)) R).success := by
        rw [grantBlockFrozenProxyHitClamped, htake,
          GrantBankReference.bankLocalReferenceWordAppendClamped, hR]
      unfold GrantBlockFrozenKernel.proxyWeight
      rw [if_pos hc]
      cases hk : (grantBlockFrozenKernel ring member).kind R with
      | live => exact Nat.zero_le _
      | grant =>
          have hs : R.success = true := by
            change (if R.success = true then _ else _) = _ at hk
            by_cases h1 : R.success = true
            · exact h1
            · by_cases h2 : BankTrialLocalClean (ceilLogTwo n) R <;>
                simp [h1, h2] at hk
          rw [hhit, GrantBankReference.bankLocalReferenceLatchedWordClamped
            ring member.1 _ R hs, hs]
          simp
      | clean S =>
          have hS : S = R := by
            change (if R.success = true then _ else _) = _ at hk
            by_cases h1 : R.success = true
            · simp [h1] at hk
            · by_cases h2 : BankTrialLocalClean (ceilLogTwo n) R
              · simp [h1, h2] at hk
                exact hk.symm
              · simp [h1, h2] at hk
          subst hS
          by_cases hb : bankTrialRenewalSuccessBy ring member.1 S
              (W - u.length) v = true
          · have hl := grantBlockFrozenSuccessByLatched ring member.1 S
              (W - u.length) v hb
            rw [hhit, hl]
            simp [Prob.indicator, hb]
          · have hb' : bankTrialRenewalSuccessBy ring member.1 S
                (W - u.length) v = false := by
              cases h : bankTrialRenewalSuccessBy ring member.1 S
                (W - u.length) v with
              | false => rfl
              | true => exact absurd h hb
            simp [Prob.indicator, hb']
    · unfold GrantBlockFrozenKernel.proxyWeight
      rw [if_neg hc]
      exact Nat.zero_le _

/-- The proxy mass of the frozen kernel is at most the frozen proxy mass.

Consumer: `grantBlockFrozenLocalColdClockOfStoppedCost`. -/
theorem grantBlockFrozenKernelProxyMassLe {n : Nat} (ring : DirectedRing n)
    (member : GrantBlockFamilyMember ring) (T W : Nat) :
    (grantBlockFrozenKernel ring member).proxyMass ring member.1 T W ≤
      grantBlockFrozenProxyMass ring member T W := by
  unfold GrantBlockFrozenKernel.proxyMass grantBlockFrozenProxyMass
  exact Density.schedule_sum_mono T _ _
    (fun word => grantBlockFrozenKernelProxyWord ring member T W word)

end L3
#print axioms L3.grantBlockFrozenStoppedWordLeaf
#print axioms L3.grantBlockFrozenKernelCleanSound
#print axioms L3.grantBlockFrozenKernelProxyWord
#print axioms L3.grantBlockFrozenKernelProxyMassLe
