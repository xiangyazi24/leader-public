import Leader.Wu.Elimination.SinkTwoGapEntrance
import Leader.Wu.Elimination.SinkTwoGapSuccessorFootprint

namespace LDSinkTwoGapEntranceBellman

open LDSinkTwoGapEntrance LDSinkTwoGapNoResetKernel LDSinkTwoGapAttemptResidual
open LDSinkGapCleanup LDTwoGapFrame PPLLRepair
open FiniteUniformStoppingTree
open Classical

set_option autoImplicit false

variable {n ψ : Nat}

/-- The raw/global form of the two Attempt2 rank facts.  The checked theorems
`raw_nonincrease` and `raw_strictDrop` provide these facts on `AActive`; the
exact `EntranceBellman`, however, quantifies over raw `AState`. -/
def RawAttemptRankLaws (hψ : ψ > 0) (F : TwoGapFrame n) : Prop :=
  (∀ (x : AState n ψ) (e : Fin n),
      rawStoppedR F (attemptStepRaw hψ F x e) ≤ R F x) ∧
  ∀ x : AState n ψ, ∃ e : Fin n,
      rawStoppedR F (attemptStepRaw hψ F x e) < R F x

/-- This is the single genuinely new physical seam.  Attempt2 made this child
`.failure`, so its old stopped rank was zero.  Entrance reactivates exactly the
same child, hence we must pay for its positive rank explicitly.

Strict `<` rather than merely `≤` is the useful minimal form: the strict raw
Attempt2 edge may itself be the old failure edge, so a non-strict escrow would
not necessarily leave any edge that pays the unit Bellman cost. -/
structure EntranceAbsorptionResidual (hψ : ψ > 0)
    (F : TwoGapFrame n) : Prop where
  reactivated_lt :
    ∀ (x : AState n ψ) (e : Fin n),
      attemptStepRaw hψ F x e = .failure →
      R F (advanceAState F x (attemptStepConf hψ F x e)) < R F x

/-- The implementation does not reset a parked phase on absorption (or on any
other post-configuration passed to `advanceAState`). -/
theorem advanceAState_phase_eq_parked (F : TwoGapFrame n)
    (x : AState n ψ) (C : Fin n → AgentState ψ)
    (hp : x.phase = .parked) :
    (advanceAState F x C).phase = .parked := by
  simp [advanceAState, advanceAPhase, hp]

/-- Consequently, for a parked state the desired absorption rank drop follows
from a strict physical `W` drop; the phase machinery itself contributes no
reset credit.  What is missing from the pasted API is precisely the theorem
that `NoResetAbsorbedAt` forces this `W` inequality. -/
theorem R_advance_lt_of_parked_of_W_lt (F : TwoGapFrame n)
    (x : AState n ψ) (C : Fin n → AgentState ψ)
    (hp : x.phase = .parked) (hw : W F C < W F x.conf) :
    R F (advanceAState F x C) < R F x := by
  unfold R phaseDebtA
  simp [advanceAState, advanceAPhase, hp]
  omega

/-- The checked AttemptResidual laws give exactly the two raw-rank facts at an
invariant active state. -/
theorem attempt_rank_laws_at_active (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AActive hψ F) :
    (∀ e : Fin n,
      rawStoppedR F (attemptStepRaw hψ F x.1 e) ≤ R F x.1) ∧
    ∃ e : Fin n,
      rawStoppedR F (attemptStepRaw hψ F x.1 e) < R F x.1 := by
  exact ⟨raw_nonincrease hψ F x, raw_strictDrop hψ F x⟩

private theorem attemptStepRaw_success_implies_success2
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (x : AState n ψ) (e : Fin n)
    (hsucc : attemptStepRaw hψ F x e = .success) :
    NoResetSuccess F (attemptStepConf hψ F x e) := by
  classical
  by_cases hs : NoResetSuccess F (attemptStepConf hψ F x e)
  · exact hs
  · by_cases ha : NoResetAbsorbedAt F x e (attemptStepConf hψ F x e)
    · simp [attemptStepRaw, hs, ha] at hsucc
    · simp [attemptStepRaw, hs, ha] at hsucc

private theorem entrance_rawStoppedR_le
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (hRaw : RawAttemptRankLaws hψ F)
    (hAbs : EntranceAbsorptionResidual hψ F)
    (x : AState n ψ) (e : Fin n) :
    rawStoppedR F (entranceStep hψ F x e) ≤ R F x := by
  classical
  by_cases hE : EntranceSuccess F (attemptStepConf hψ F x e)
  · simp [entranceStep, hE, rawStoppedR]
  · cases hA : attemptStepRaw hψ F x e with
    | active y =>
        have hle := hRaw.1 x e
        simpa [entranceStep, hE, reactivateFailure, hA, rawStoppedR] using hle
    | success =>
        have hs := attemptStepRaw_success_implies_success2 hψ F x e hA
        exact (hE (Or.inr hs)).elim
    | failure =>
        have hlt := hAbs.reactivated_lt x e hA
        have hle := Nat.le_of_lt hlt
        simpa [entranceStep, hE, reactivateFailure, hA, rawStoppedR] using hle

private theorem exists_entrance_rawStoppedR_lt
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (hRaw : RawAttemptRankLaws hψ F)
    (hAbs : EntranceAbsorptionResidual hψ F)
    (x : AState n ψ) :
    ∃ e : Fin n, rawStoppedR F (entranceStep hψ F x e) < R F x := by
  obtain ⟨e, hlt⟩ := hRaw.2 x
  refine ⟨e, ?_⟩
  classical
  by_cases hE : EntranceSuccess F (attemptStepConf hψ F x e)
  · have hp := R_pos F x
    simpa [entranceStep, hE, rawStoppedR] using hp
  · cases hA : attemptStepRaw hψ F x e with
    | active y =>
        simpa [entranceStep, hE, reactivateFailure, hA, rawStoppedR] using hlt
    | success =>
        have hs := attemptStepRaw_success_implies_success2 hψ F x e hA
        exact (hE (Or.inr hs)).elim
    | failure =>
        have ha := hAbs.reactivated_lt x e hA
        simpa [entranceStep, hE, reactivateFailure, hA, rawStoppedR] using ha

private theorem entrancePotential_eq_mul_rawStoppedR
    (F : TwoGapFrame n) (z : StopNode (AState n ψ)) :
    entrancePotential F z = n * rawStoppedR F z := by
  cases z <;> rfl

/-- Once the global/raw Attempt2 rank laws are available, the one-field
absorption escrow is sufficient to prove the exact Bellman seam. -/
theorem entranceBellman_of_raw_rank_laws
    (hψ : ψ > 0) (F : TwoGapFrame n)
    (hRaw : RawAttemptRankLaws hψ F)
    (hAbs : EntranceAbsorptionResidual hψ F) :
    EntranceBellman hψ F := by
  unfold EntranceBellman NatBellmanSuperSolution
  refine ⟨rfl, rfl, ?_⟩
  intro x
  obtain ⟨e0, hstrict⟩ :=
    exists_entrance_rawStoppedR_lt hψ F hRaw hAbs x
  let c := entrancePotential F (.active x)
  let a := entrancePotential F (entranceStep hψ F x e0)
  let bound : Fin n → Nat := fun e => if e = e0 then a else c
  have hpoint : ∀ e : Fin n,
      entrancePotential F (entranceStep hψ F x e) ≤ bound e := by
    intro e
    have hr := entrance_rawStoppedR_le hψ F hRaw hAbs x e
    have hp : entrancePotential F (entranceStep hψ F x e) ≤ c := by
      dsimp [c]
      rw [entrancePotential_eq_mul_rawStoppedR]
      exact Nat.mul_le_mul_left n hr
    by_cases he : e = e0
    · subst e
      simp [bound, a]
    · simpa [bound, he] using hp
  have hsumle := ofFn_sum_le
    (fun e : Fin n => entrancePotential F (entranceStep hψ F x e))
    bound hpoint
  have hsumbound :=
    PredictableTwoTargetFiniteTree.ofFn_sum_one_value_else_const
      e0 bound c (by
        intro e he
        simp [bound, he])
  have he0 : bound e0 = a := by simp [bound]
  rw [he0] at hsumbound
  rw [hsumbound] at hsumle
  have hn : 0 < n := by
    have := e0.isLt
    omega
  have hpred : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have hsucc : rawStoppedR F (entranceStep hψ F x e0) + 1 ≤ R F x := by
    omega
  have hmul := Nat.mul_le_mul_left n hsucc
  have hpay : n + a ≤ c := by
    dsimp [a, c]
    rw [entrancePotential_eq_mul_rawStoppedR]
    have hact : entrancePotential F (StopNode.active x) = n * R F x := rfl
    simp only [Nat.mul_add, Nat.mul_one] at hmul
    omega
  calc
    1 * n + (List.ofFn (fun e : Fin n =>
        entrancePotential F (entranceStep hψ F x e))).sum ≤
        n + (a + (n - 1) * c) := by
      simpa [Nat.one_mul] using Nat.add_le_add_left hsumle n
    _ = (n + a) + (n - 1) * c := by omega
    _ ≤ c + (n - 1) * c := Nat.add_le_add_right hpay _
    _ = (n - 1 + 1) * c := by
      rw [Nat.add_mul]
      omega
    _ = n * c := by rw [hpred]
    _ = n * entrancePotential F (.active x) := by rfl

#print axioms advanceAState_phase_eq_parked
#print axioms R_advance_lt_of_parked_of_W_lt
#print axioms attempt_rank_laws_at_active
#print axioms entranceBellman_of_raw_rank_laws

end LDSinkTwoGapEntranceBellman
