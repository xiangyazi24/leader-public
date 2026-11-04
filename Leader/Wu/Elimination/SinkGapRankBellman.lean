import Leader.Wu.Elimination.SinkGapServiceRank

open LDSinkGapCleanup LDSinkKernelC LDSinkProtectedAbsorption
  LDSinkGapDoneInvariant LDSinkGapBlockedPreStep LDSinkGapServiceRank
  FiniteUniformStoppingTree PPLLRepair
open Classical

namespace LDSinkGapRankBellman

set_option autoImplicit false

variable {n ψ : Nat}

/-!
C4: Bellman and bounded-word corollaries of C3.
The quantitative results retain a uniform `hR7land` hypothesis. Neither the
residual itself nor its propagation is assumed silently. No kernel unfolds.
The stopped transition needs only C2b closure, not the rank residual.
-/

/-- The rank vanishes on the K2 stopping set, including arbitrary inputs. -/
theorem gapWC_doneC (F : GapFrame n) (C : Fin n → AgentState ψ)
    (hd : GapDoneC F C) : gapWC F C = 0 := by
  classical
  unfold gapWC
  rw [if_pos hd]

/-- Apply the generic service-rank-to-Bellman theorem without changing its
scheduler: there are still exactly `n` raw edges. -/
private theorem rankCertificate (hψ : ψ > 0) (F : GapFrame n)
    (hR7land : ∀ D : Fin n → AgentState ψ,
      GapInvariant hψ F D → ¬ GapDoneC F D → CRankResidual hψ F D)
    (C : Fin n → AgentState ψ) (hi : GapInvariant hψ F C) :
    n * gapWC F C ≤ n * (2 * F.d) ∧
    (∀ D : Fin n → AgentState ψ, GapDoneC F D → n * gapWC F D = 0) ∧
    ∀ D : Fin n → AgentState ψ, GapInvariant hψ F D → ¬ GapDoneC F D →
      n + (List.ofFn (fun e : Fin n =>
        n * gapWC F (sinkStepC hψ F D e))).sum ≤
          n * (n * gapWC F D) := by
  exact rank_to_bellman
    (sinkStepC hψ F) (GapInvariant hψ F) (GapDoneC F)
    (gapWC F) (2 * F.d)
    (gapWC_le_two_d hψ F)
    (gapWC_doneC F)
    (fun D e hD hn =>
      gapWC_step_le hψ F D e hD hn (hR7land D hD hn))
    (by
      intro D hD hn
      obtain ⟨e, he⟩ :=
        exists_gapWC_step_lt hψ F D hD hn (hR7land D hD hn)
      exact ⟨e, by omega⟩)
    C hi

/-- B1: `V D = n * gapWC F D` is the division-free `2nd` certificate. -/
theorem sinkC_gap_cleanup_2nd (hψ : ψ > 0) (F : GapFrame n)
    (hR7land : ∀ D : Fin n → AgentState ψ,
      GapInvariant hψ F D → ¬ GapDoneC F D → CRankResidual hψ F D)
    (C : Fin n → AgentState ψ) (hi : GapInvariant hψ F C) :
    ∃ V : (Fin n → AgentState ψ) → Nat,
      V C ≤ 2 * n * F.d ∧
      (∀ D, GapDoneC F D → V D = 0) ∧
      ∀ D, GapInvariant hψ F D → ¬ GapDoneC F D →
        n + (List.ofFn (fun e : Fin n =>
          V (sinkStepC hψ F D e))).sum ≤ n * V D := by
  obtain ⟨hle, hzero, hbell⟩ := rankCertificate hψ F hR7land C hi
  refine ⟨(fun D => n * gapWC F D), ?_, hzero, hbell⟩
  calc
    n * gapWC F C ≤ n * (2 * F.d) := hle
    _ = 2 * n * F.d := by ac_rfl

/-- Execute a finite word of raw K2 scheduler edges. -/
def gapRunC (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (w : List (Fin n)) :
    Fin n → AgentState ψ :=
  w.foldl (fun D e => sinkStepC hψ F D e) C

theorem gapRunC_nil (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) : gapRunC hψ F C [] = C := rfl

theorem gapRunC_cons (hψ : ψ > 0) (F : GapFrame n)
    (C : Fin n → AgentState ψ) (e : Fin n) (w : List (Fin n)) :
    gapRunC hψ F C (e :: w) =
      gapRunC hψ F (sinkStepC hψ F C e) w := rfl

/-- A rank budget pays for a finite successful scheduler word. The induction
uses the uniform residual again at each active successor. -/
theorem gapC_reaches_done (hψ : ψ > 0) (F : GapFrame n)
    (hR7land : ∀ D : Fin n → AgentState ψ,
      GapInvariant hψ F D → ¬ GapDoneC F D → CRankResidual hψ F D) :
    ∀ (m : Nat) (C : Fin n → AgentState ψ),
      GapInvariant hψ F C → gapWC F C ≤ m →
      ∃ w : List (Fin n),
        w.length ≤ m ∧ GapDoneC F (gapRunC hψ F C w) := by
  intro m
  induction m with
  | zero =>
      intro C hi hm
      by_cases hd : GapDoneC F C
      · exact ⟨[], Nat.le_refl 0, hd⟩
      · exfalso
        obtain ⟨e, he⟩ :=
          exists_gapWC_step_lt hψ F C hi hd (hR7land C hi hd)
        omega
  | succ m ih =>
      intro C hi hm
      by_cases hd : GapDoneC F C
      · exact ⟨[], Nat.zero_le _, hd⟩
      · obtain ⟨e, he⟩ :=
          exists_gapWC_step_lt hψ F C hi hd (hR7land C hi hd)
        rcases sinkStepC_invariant_or_done' hψ F C e hi hd with
          hdone | hi'
        · refine ⟨[e], ?_, hdone⟩
          change 1 ≤ m + 1
          omega
        · have hnext : gapWC F (sinkStepC hψ F C e) ≤ m := by omega
          obtain ⟨w, hw, hdone⟩ := ih (sinkStepC hψ F C e) hi' hnext
          refine ⟨e :: w, ?_, ?_⟩
          · simpa only [List.length_cons] using Nat.succ_le_succ hw
          · simpa only [gapRunC_cons] using hdone

/-- B2: existence of a successful word, not a bound for every word. -/
theorem gapC_cleanup_within_two_d (hψ : ψ > 0) (F : GapFrame n)
    (hR7land : ∀ D : Fin n → AgentState ψ,
      GapInvariant hψ F D → ¬ GapDoneC F D → CRankResidual hψ F D)
    (C : Fin n → AgentState ψ) (hi : GapInvariant hψ F C) :
    ∃ w : List (Fin n), w.length ≤ 2 * F.d ∧
      GapDoneC F (gapRunC hψ F C w) :=
  gapC_reaches_done hψ F hR7land (2 * F.d) C hi
    (gapWC_le_two_d hψ F C hi)

/-- Active configurations have exactly C2b's invariant and are not done. -/
abbrev ActiveC (hψ : ψ > 0) (F : GapFrame n) :=
  {C : Fin n → AgentState ψ // GapInvariant hψ F C ∧ ¬ GapDoneC F C}

/-- B3 transition. Success means `GapDoneC`; otherwise C2b certifies the
actual successor as active. There is no failure branch or fallback state. -/
noncomputable def stepC (hψ : ψ > 0) (F : GapFrame n)
    (x : ActiveC hψ F) (e : Fin n) : StopNode (ActiveC hψ F) :=
  if hd : GapDoneC F (sinkStepC hψ F x.1 e) then .success
  else .active ⟨sinkStepC hψ F x.1 e, by
    refine ⟨?_, hd⟩
    rcases sinkStepC_invariant_or_done' hψ F x.1 e x.2.1 x.2.2 with
      hdone | hi
    · exact False.elim (hd hdone)
    · exact hi⟩

/-- Extend `n * gapWC` by zero at both terminal constructors. -/
noncomputable def potentialC (hψ : ψ > 0) (F : GapFrame n) :
    StopNode (ActiveC hψ F) → Nat
  | .active x => n * gapWC F x.1
  | .success => 0
  | .failure => 0

/-- Stopping changes no child potential: a done successor already has rank 0. -/
theorem potentialC_step_eq (hψ : ψ > 0) (F : GapFrame n)
    (x : ActiveC hψ F) (e : Fin n) :
    potentialC hψ F (stepC hψ F x e) =
      n * gapWC F (sinkStepC hψ F x.1 e) := by
  classical
  unfold stepC
  split
  · rename_i hd
    change 0 = n * gapWC F (sinkStepC hψ F x.1 e)
    rw [gapWC_doneC F _ hd, Nat.mul_zero]
  · rfl

/-- The stopped process pays one unit per active raw interaction. -/
theorem stepC_natBellmanSuperSolution (hψ : ψ > 0) (F : GapFrame n)
    (hR7land : ∀ D : Fin n → AgentState ψ,
      GapInvariant hψ F D → ¬ GapDoneC F D → CRankResidual hψ F D) :
    NatBellmanSuperSolution (stepC hψ F) 1 (potentialC hψ F) := by
  refine ⟨rfl, rfl, ?_⟩
  intro x
  have hsum := FiniteUniformStoppingTree.ofFn_sum_eq
    (fun e : Fin n => potentialC hψ F (stepC hψ F x e))
    (fun e : Fin n => n * gapWC F (sinkStepC hψ F x.1 e))
    (fun e => potentialC_step_eq hψ F x e)
  change 1 * n + (List.ofFn (fun e : Fin n =>
    potentialC hψ F (stepC hψ F x e))).sum ≤ n * (n * gapWC F x.1)
  rw [Nat.one_mul, hsum]
  exact (rankCertificate hψ F hR7land x.1 x.2.1).2.2 x.1 x.2.1 x.2.2

/-- The uniform `2nd` potential bound also covers terminal starting nodes. -/
theorem potentialC_le (hψ : ψ > 0) (F : GapFrame n)
    (x : StopNode (ActiveC hψ F)) :
    potentialC hψ F x ≤ n * 2 * F.d := by
  cases x with
  | success => exact Nat.zero_le _
  | failure => exact Nat.zero_le _
  | active s =>
      change n * gapWC F s.1 ≤ n * 2 * F.d
      calc
        n * gapWC F s.1 ≤ n * (2 * F.d) :=
          Nat.mul_le_mul_left n (gapWC_le_two_d hψ F s.1 s.2.1)
        _ = n * 2 * F.d := (Nat.mul_assoc n 2 F.d).symm

/-- B3 finite-horizon bound, for every stopped starting node and horizon. -/
theorem sinkC_gap_cleanup_truncated (hψ : ψ > 0) (F : GapFrame n)
    (hR7land : ∀ D : Fin n → AgentState ψ,
      GapInvariant hψ F D → ¬ GapDoneC F D → CRankResidual hψ F D)
    (x : StopNode (ActiveC hψ F)) (T : Nat) :
    truncatedActiveCostNumerator (stepC hψ F) x T ≤
      n ^ T * (n * 2 * F.d) := by
  have h := truncatedActiveCostNumerator_mul_le_of_natSuperSolution
    (stepC hψ F) 1 (potentialC hψ F)
    (stepC_natBellmanSuperSolution hψ F hR7land) x T
  have hcost : truncatedActiveCostNumerator (stepC hψ F) x T ≤
      n ^ T * potentialC hψ F x := by
    simpa only [Nat.one_mul] using h
  exact Nat.le_trans hcost (Nat.mul_le_mul_left (n ^ T) (potentialC_le hψ F x))

end LDSinkGapRankBellman

#print axioms LDSinkGapRankBellman.gapWC_doneC
#print axioms LDSinkGapRankBellman.sinkC_gap_cleanup_2nd
#print axioms LDSinkGapRankBellman.gapRunC_nil
#print axioms LDSinkGapRankBellman.gapRunC_cons
#print axioms LDSinkGapRankBellman.gapC_reaches_done
#print axioms LDSinkGapRankBellman.gapC_cleanup_within_two_d
#print axioms LDSinkGapRankBellman.potentialC_step_eq
#print axioms LDSinkGapRankBellman.stepC_natBellmanSuperSolution
#print axioms LDSinkGapRankBellman.potentialC_le
#print axioms LDSinkGapRankBellman.sinkC_gap_cleanup_truncated
