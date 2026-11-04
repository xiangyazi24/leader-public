import Leader.L3.Grant.BlockFrozenRenewalKernel

/-!
The local trial/renewal machine of the G13 chain is the clamped frozen
chain itself: its bank is the clamped word image and a won phase is a
latched success.  Consumer: `GrantBlockFrozenRenewal.lean`.
-/

namespace L3

open Classical

set_option autoImplicit false
set_option Elab.async false

/-- One local trial step from a live or recovering trial moves the bank
by the clamped step. -/
theorem grantBlockFrozenLocalNextBank {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankTrialLocalState q)
    (hz : z.phase ≠ .won ∧ z.phase ≠ .lost) :
    (bankTrialLocalNext ring root z e).bank =
      GrantBankReference.bankLocalReferenceStepClamped ring root
        z.bank e := by
  obtain ⟨bank, phase⟩ := z
  cases phase with
  | won => exact absurd rfl hz.1
  | lost => exact absurd rfl hz.2
  | recovery =>
      unfold bankTrialLocalNext
      by_cases h1 : (GrantBankReference.bankLocalReferenceStepClamped
        ring root bank e).success = true
      · simp [h1]
      · by_cases h2 : BankTrialLocalClean q
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root bank e)
        · simp [h1, h2]
        · simp [h1, h2]
  | live begun =>
      unfold bankTrialLocalNext
      by_cases h1 : (GrantBankReference.bankLocalReferenceStepClamped
        ring root bank e).success = true
      · simp [h1]
      · by_cases h2 : BankTrialLocalClean q
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root bank e) ∧
            (begun = true ∨ e = root ∨ ring.rightNeighbor e = root)
        · simp [h1, h2]
        · by_cases h3 : ((GrantBankReference.bankLocalReferenceStepClamped
            ring root bank e).fields 0).1 = .RESET
          · simp [h1, h2, h3]
          · simp [h1, h2, h3]

/-- A won phase after one local step carries a latched bank. -/
theorem grantBlockFrozenLocalNextWon {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankTrialLocalState q)
    (hz : z.phase ≠ .won ∧ z.phase ≠ .lost)
    (hwon : (bankTrialLocalNext ring root z e).phase = .won) :
    (bankTrialLocalNext ring root z e).bank.success = true := by
  obtain ⟨bank, phase⟩ := z
  cases phase with
  | won => exact absurd rfl hz.1
  | lost => exact absurd rfl hz.2
  | recovery =>
      unfold bankTrialLocalNext at hwon ⊢
      by_cases h1 : (GrantBankReference.bankLocalReferenceStepClamped
        ring root bank e).success = true
      · simpa [h1] using h1
      · by_cases h2 : BankTrialLocalClean q
          (GrantBankReference.bankLocalReferenceStepClamped
            ring root bank e)
        · simp [h1, h2] at hwon
        · simp [h1, h2] at hwon
  | live begun =>
      unfold bankTrialLocalNext at hwon ⊢
      by_cases h1 : (GrantBankReference.bankLocalReferenceStepClamped
        ring root bank e).success = true
      · simpa [h1] using h1
      · by_cases h2 : BankTrialLocalClean q
            (GrantBankReference.bankLocalReferenceStepClamped
              ring root bank e) ∧
            (begun = true ∨ e = root ∨ ring.rightNeighbor e = root)
        · simp [h1, h2] at hwon
        · by_cases h3 : ((GrantBankReference.bankLocalReferenceStepClamped
            ring root bank e).fields 0).1 = .RESET
          · simp [h1, h2, h3] at hwon
          · simp [h1, h2, h3] at hwon

/-- Won implies latched, preserved by the renewal step. -/
def GrantBlockFrozenRenewalInv {q : Nat} (z : BankTrialRenewalState q) :
    Prop :=
  z.observer.phase = .won → z.observer.bank.success = true

theorem grantBlockFrozenRenewalNextInv {n q : Nat}
    (ring : DirectedRing n) (root e : Fin n)
    (z : BankTrialRenewalState q) (hz : GrantBlockFrozenRenewalInv z) :
    GrantBlockFrozenRenewalInv (bankTrialRenewalNext ring root z e) ∧
    (bankTrialRenewalNext ring root z e).observer.bank =
      GrantBankReference.bankLocalReferenceStepClamped ring root
        z.observer.bank e := by
  cases hphase : z.observer.phase with
  | won =>
      have hs := hz hphase
      rw [bankTrialRenewalNextWon ring root e z hphase]
      exact ⟨hz, (GrantBankReference.bankLocalReferenceLatchedStepClamped
        ring root e _ hs).symm⟩
  | lost =>
      have hl : ((bankTrialLocalStart z.observer.bank :
          BankTrialLocalState q).phase ≠ .won ∧
          (bankTrialLocalStart z.observer.bank :
            BankTrialLocalState q).phase ≠ .lost) := by
        simp [bankTrialLocalStart]
      have hb := grantBlockFrozenLocalNextBank ring root e
        (bankTrialLocalStart z.observer.bank) hl
      have hw := grantBlockFrozenLocalNextWon ring root e
        (bankTrialLocalStart z.observer.bank) hl
      simp only [bankTrialRenewalNext, hphase, bankTrialRenewalAdvance]
      split
      · exact ⟨fun h => hw h, hb⟩
      · exact ⟨fun h => hw h, hb⟩
  | recovery =>
      have hl : (z.observer.phase ≠ .won ∧ z.observer.phase ≠ .lost) := by
        simp [hphase]
      have hb := grantBlockFrozenLocalNextBank ring root e z.observer hl
      have hw := grantBlockFrozenLocalNextWon ring root e z.observer hl
      simp only [bankTrialRenewalNext, hphase, bankTrialRenewalAdvance]
      split
      · exact ⟨fun h => hw h, hb⟩
      · exact ⟨fun h => hw h, hb⟩
  | live begun =>
      have hl : (z.observer.phase ≠ .won ∧ z.observer.phase ≠ .lost) := by
        simp [hphase]
      have hb := grantBlockFrozenLocalNextBank ring root e z.observer hl
      have hw := grantBlockFrozenLocalNextWon ring root e z.observer hl
      simp only [bankTrialRenewalNext, hphase, bankTrialRenewalAdvance]
      split
      · exact ⟨fun h => hw h, hb⟩
      · exact ⟨fun h => hw h, hb⟩

/-- The renewal machine's bank is the clamped word image, and a won
phase is a latched success. -/
theorem grantBlockFrozenRenewalRunBank {n q : Nat}
    (ring : DirectedRing n) (root : Fin n) :
    ∀ (w : List (Fin n)) (z : BankTrialRenewalState q),
      GrantBlockFrozenRenewalInv z →
      GrantBlockFrozenRenewalInv
        (bankTrialRenewalRunFrom ring root w z) ∧
      (bankTrialRenewalRunFrom ring root w z).observer.bank =
        GrantBankReference.bankLocalReferenceWordClamped ring root w
          z.observer.bank := by
  intro w
  induction w with
  | nil => intro z hz; exact ⟨hz, rfl⟩
  | cons e es ih =>
      intro z hz
      obtain ⟨h1, h2⟩ := grantBlockFrozenRenewalNextInv ring root e z hz
      obtain ⟨h3, h4⟩ := ih _ h1
      refine ⟨h3, ?_⟩
      change (bankTrialRenewalRunFrom ring root es
        (bankTrialRenewalNext ring root z e)).observer.bank =
        GrantBankReference.bankLocalReferenceWordClamped ring root es
          (GrantBankReference.bankLocalReferenceStepClamped ring root
            z.observer.bank e)
      rw [h4, h2]

/-- Success by `k` letters of the renewal machine is a latched clamped
reference after those letters. -/
theorem grantBlockFrozenSuccessByLatched {n q : Nat}
    (ring : DirectedRing n) (root : Fin n)
    (S : GrantBankReference.BankLocalReference (compileAdvice q).b)
    (k : Nat) (suffix : List (Fin n))
    (h : bankTrialRenewalSuccessBy ring root S k suffix = true) :
    (GrantBankReference.bankLocalReferenceWordClamped ring root
      (suffix.take k) S).success = true := by
  have hrun := grantBlockFrozenRenewalRunBank ring root (suffix.take k)
    (bankTrialRenewalStart S) (by
      intro hw
      simp [bankTrialRenewalStart, bankTrialLocalStart] at hw)
  have hwon : (bankTrialRenewalRun ring root S (suffix.take k)).observer.phase
      = .won := by
    simpa [bankTrialRenewalSuccessBy, bankTrialRenewalHitWord] using h
  have hs := hrun.1 hwon
  unfold bankTrialRenewalRun at hs
  rw [hrun.2] at hs
  simpa [bankTrialRenewalStart, bankTrialLocalStart] using hs

end L3
#print axioms L3.grantBlockFrozenRenewalRunBank
#print axioms L3.grantBlockFrozenSuccessByLatched
