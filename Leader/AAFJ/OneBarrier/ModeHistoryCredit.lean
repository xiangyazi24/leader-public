import Leader.AAFJ.OneBarrier.ModeRank

set_option autoImplicit false
set_option Elab.async false

namespace AAFJPK.OneBarrierModeHistoryCredit

open AAFJPK
open AAFJPK.BarrierAlgebra
open AAFJPK.SingleBarrierSanitation
open AAFJPK.SingleBarrierSanitation.DirtyTailBellman
open AAFJPK.OriginalNonbarrierWord
open AAFJPK.OriginalUniqueLeaderCleanup
open AAFJPK.OriginalDangerousProbeChase
open AAFJPK.OriginalMultipleLeaderOneBarrier
open AAFJPK.SelectedMultipleUniqueSafe
open AAFJPK.OddZeroPhiFamily
open AAFJPK.OddZeroModeDebt
open AAFJPK.CenteredRenewal.OneBarrierCleanup
open AAFJPK.OriginalPhaseAwareMacroRank
open AAFJPK.OneBarrierModeRankConsumer

/-!
The state-only rank in `ZZAAFJOneBarrierModeRankConsumer` stops at the actual
word `[2,0,0,2]`: `PhiAt` is unchanged and `zeroModeDebt` rises when the
unique leader disappears.  The smallest source-visible quantity which pays
that edge is one bit recording whether a live bullet remains.  The safe
cleanup consumes its sole bullet, while the odd zero birth is paid first by
`zeroModeDebt`; hence the credit must precede the mode coordinate, and
`zeroModeDebt` must remain after it.

This file only instantiates the resulting finite lexicographic certificate on
the literal producer endpoints.  It does not introduce an abstract
transition relation.
-/

/-- One unit for each currently live bullet.  It is the compensating credit
    carried across the safe-Unique-to-zero mode change. -/
def bulletCredit {n k : Nat} (C : Fin n → State k) : Nat :=
  (List.ofFn (fun i : Fin n => if (C i).bullet then 1 else 0)).sum

/-- Minimal compensating history credit: zero means no live bullet remains,
    and one means that the endpoint still carries at least one bullet. -/
def historyCredit {n k : Nat} (C : Fin n → State k) : Nat :=
  if bulletCredit C = 0 then 0 else 1

/-- The finite endpoint payload with the new credit in the only position that
    can pay the unchanged-`PhiAt` safe cleanup edge. -/
def historyModeTuple {n k : Nat} (ring : DirectedRing n) (b : Fin n)
    (C : Fin n → State k) : Nat × Nat × Nat × Nat × Nat :=
  (PhiAt ring b C, historyCredit C, zeroModeDebt C,
    finiteModeRank ring b C, dirtyCtl C b)

/-- Explicit list representation of `historyModeTuple`, used for a closed
    kernel reduction rather than an imported order instance. -/
def historyModeList {n k : Nat} (ring : DirectedRing n) (b : Fin n)
    (C : Fin n → State k) : List Nat :=
  [PhiAt ring b C, historyCredit C, zeroModeDebt C,
    finiteModeRank ring b C, dirtyCtl C b]

def lexNat : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => false
  | _ :: _, [] => false
  | a :: as, b :: bs =>
      if a < b then true else if a = b then lexNat as bs else false

/-- `x` is below `y` in the displayed five-coordinate endpoint order. -/
def HistoryModeDrop {n k : Nat} (ring : DirectedRing n)
    (b : Fin n) (C : Fin n → State k)
    (b' : Fin n) (D : Fin n → State k) : Prop :=
  lexNat (historyModeList ring b' D) (historyModeList ring b C) = true

/-! ## The actual cycle seen after forgetting the credit -/

/-- The coarse mode seen by a state-only mode rank.  Safe Unique is `0`, and
    both Zero and Multiple are `1`; this is deliberately independent of the
    barrier cut, so the two actual producer families can be compared. -/
def coarseMode {n k : Nat} (C : Fin n → State k) : Nat :=
  if leaderCount C = 1 then 0 else 1

def oddZero3 : Fin 3 → State 2 := oddZero 1

def oddZero3BirthWord : List (Fin 3) := [2, 0, 1, 2]

def oddZero3BirthEnd : Fin 3 → State 2 :=
  rawRun OddZeroPhiFamily.hk2 (oddRing 1) oddZero3 oddZero3BirthWord

/-! The cycle uses two independently selected actual words: the safe unique
cleanup word from the candidate and the odd-family selected birth word. -/

theorem safe_cleanup_mode_edge_actual :
    SafeEndpoint = rawRun OriginalPhaseAwareMacroRank.hk2 ring3 SafeUnique
        [2, 0, 0, 2] ∧
      coarseMode SafeUnique = 0 ∧
      coarseMode SafeEndpoint = 1 ∧
      PhiAt ring3 0 SafeEndpoint = PhiAt ring3 2 SafeUnique ∧
      bulletCredit SafeEndpoint < bulletCredit SafeUnique := by
  have h := safe_branch_mode_loss
  refine ⟨rfl, ?_, ?_, h.2.2.2.2.2.2.2.2, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem safe_cleanup_consumes_one_history_bit :
    historyCredit SafeUnique = 1 ∧ historyCredit SafeEndpoint = 0 := by
  decide +kernel

theorem odd_zero_birth_mode_edge_actual :
    OneBarrierAt OddZeroPhiFamily.hk2 (oddRing 1) oddZero3 (oddTail 1) ∧
      oddZero3BirthWord.length ≤ 5 ∧
      OneBarrierAt OddZeroPhiFamily.hk2 (oddRing 1) oddZero3BirthEnd 0 ∧
      PhiAt (oddRing 1) 0 oddZero3BirthEnd = 1 ∧
      (∃ ell, UniqueLeaderAt oddZero3BirthEnd ell) ∧
      coarseMode oddZero3 = 1 ∧
      coarseMode oddZero3BirthEnd = 0 ∧
      bulletCredit oddZero3BirthEnd = bulletCredit oddZero3 ∧
      zeroModeDebt oddZero3BirthEnd < zeroModeDebt oddZero3 := by
  have h := oddZero3_selected_word_decreases
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem odd_zero_birth_debt_exact :
    zeroModeDebt oddZero3 = 1 ∧
      zeroModeDebt oddZero3BirthEnd = 0 := by
  decide +kernel

/-! The quotient cycle is an actual two-edge cycle on the finite mode key:
`SafeUnique -> Zero -> UniqueSafe`.  A rank whose only input is this mode
key cannot strictly decrease on both selected words. -/
theorem cleanup_birth_coarse_cycle :
    coarseMode SafeUnique = coarseMode oddZero3BirthEnd ∧
      coarseMode SafeEndpoint = coarseMode oddZero3 ∧
      coarseMode SafeUnique = 0 ∧
      coarseMode SafeEndpoint = 1 := by
  decide +kernel

theorem no_state_only_mode_rank_on_cleanup_birth :
    ¬ ∃ r : Nat → Nat,
      r (coarseMode SafeEndpoint) < r (coarseMode SafeUnique) ∧
      r (coarseMode oddZero3BirthEnd) < r (coarseMode oddZero3) := by
  intro h
  obtain ⟨r, hcleanup, hbirth⟩ := h
  have hc := cleanup_birth_coarse_cycle
  have hlt : r (coarseMode SafeUnique) < r (coarseMode SafeUnique) := by
    rw [← hc.1, ← hc.2.1] at hbirth
    omega
  exact Nat.lt_irrefl _ hlt

/-! ## The minimal positive certificate on actual endpoints -/

theorem safe_cleanup_history_mode_drop :
    HistoryModeDrop ring3 2 SafeUnique 0 SafeEndpoint := by
  unfold HistoryModeDrop historyModeList historyCredit bulletCredit lexNat
  decide +kernel

theorem odd_zero_birth_history_mode_drop :
    HistoryModeDrop (oddRing 1) (oddTail 1) oddZero3
        0 oddZero3BirthEnd := by
  unfold HistoryModeDrop historyModeList historyCredit bulletCredit lexNat
  decide +kernel

def U1EndBarrier : Fin 3 :=
  endpointDischargeBarrier ring3 U1S (2 : Fin 3)

theorem dangerous_chase_history_mode_drop :
    HistoryModeDrop ring3 2 U0 2 U1 := by
  unfold HistoryModeDrop historyModeList historyCredit bulletCredit lexNat
  decide +kernel

theorem selected_multiple_unique_safe_history_mode_drop :
    HistoryModeDrop ring3 2 U1 U1EndBarrier U1D := by
  unfold HistoryModeDrop historyModeList historyCredit bulletCredit U1EndBarrier lexNat
  decide +kernel

theorem selected_multiple_endpoint_is_unique_safe :
    OneBarrierAt OriginalPhaseAwareMacroRank.hk2 ring3 U1D U1EndBarrier ∧
      (∃ ell, UniqueLeaderAt U1D ell) ∧
      ¬ Dangerous (cutView ring3 U1EndBarrier U1D) ∧
      PhiAt ring3 U1EndBarrier U1D < PhiAt ring3 2 U1 := by
  have h := multiple_macro_U1_endpoint
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  decide +kernel

/-! A concrete dirty-tail instance keeps `PhiAt`, zero debt, and finite mode
fixed while the existing two-incoming service lowers the local `dirtyCtl`.
The credit coordinate is therefore compatible with this local edge: it is
allowed to remain unchanged while the final local coordinate pays. -/

def DirtyZero (i : Fin 3) : State 2 :=
  if i = 0 then q false false 0 false false
  else if i = 1 then q false false 1 false false
  else q true false 0 false false

def DirtyZeroEnd : Fin 3 → State 2 :=
  rawRun OriginalPhaseAwareMacroRank.hk2 ring3 DirtyZero [1, 1]

theorem dirty_tail_history_mode_drop :
    OneBarrierAt OriginalPhaseAwareMacroRank.hk2 ring3 DirtyZero 2 ∧
      PhiAt ring3 2 DirtyZero = 1 ∧
      (DirtyZero 2).bullet = true ∧
      DirtyZeroEnd = rawRun OriginalPhaseAwareMacroRank.hk2 ring3 DirtyZero [1, 1] ∧
      HistoryModeDrop ring3 2 DirtyZero 2 DirtyZeroEnd := by
  refine ⟨?_, ?_, ?_, rfl, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · unfold HistoryModeDrop historyModeList historyCredit bulletCredit DirtyZeroEnd lexNat
    decide +kernel

/-! The cycle proves that at least one bit of additional information is needed
if the outer mode is retained as the only coarse state summary.  `Fin 1` has
one history value, so it cannot orient the two actual edges; the positive
certificate above uses the live-bullet bit as that one-unit credit. -/

theorem zero_history_has_one_value :
    ∀ h : Fin 1, h = 0 := by
  intro h
  apply Fin.ext
  omega

theorem history_credit_is_one_bit {n k : Nat} (C : Fin n → State k) :
    historyCredit C = 0 ∨ historyCredit C = 1 := by
  unfold historyCredit
  split <;> omega

theorem minimum_history_cardinality_for_cleanup_birth :
    ¬ ∃ r : (Nat × Fin 1) → Nat,
      r (coarseMode SafeEndpoint, 0) <
        r (coarseMode SafeUnique, 0) ∧
      r (coarseMode oddZero3BirthEnd, 0) <
        r (coarseMode oddZero3, 0) := by
  intro h
  obtain ⟨r, hc, hb⟩ := h
  have hmode := cleanup_birth_coarse_cycle
  have hlt : r (coarseMode SafeUnique, 0) <
      r (coarseMode SafeUnique, 0) := by
    rw [← hmode.1, ← hmode.2.1] at hb
    omega
  exact Nat.lt_irrefl _ hlt

#print axioms safe_cleanup_mode_edge_actual
#print axioms safe_cleanup_consumes_one_history_bit
#print axioms odd_zero_birth_mode_edge_actual
#print axioms odd_zero_birth_debt_exact
#print axioms no_state_only_mode_rank_on_cleanup_birth
#print axioms safe_cleanup_history_mode_drop
#print axioms odd_zero_birth_history_mode_drop
#print axioms dangerous_chase_history_mode_drop
#print axioms selected_multiple_unique_safe_history_mode_drop
#print axioms selected_multiple_endpoint_is_unique_safe
#print axioms dirty_tail_history_mode_drop
#print axioms history_credit_is_one_bit
#print axioms minimum_history_cardinality_for_cleanup_birth

end AAFJPK.OneBarrierModeHistoryCredit
