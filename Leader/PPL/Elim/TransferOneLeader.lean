import Leader.PPL.Elim.TransferScale

/-!
# LD(c) to one-leader convergence

The finite-word first-hit cost to a final target is composed across geometric
leader-count scales. Every suffix starts at its literal physical endpoint;
the proof only uses the all-horizon scale costs and the finite scale budget.
-/

namespace PPL.Convergence.LDTransfer

open PPL.Convergence.LDLocal
open PPL.Convergence.LDTransferArith
open K2ArbitraryElimination.FiniteAccounting
open LeaderCountDyadicTail

set_option autoImplicit false
set_option Elab.async false

/-- First-hit costs compose across an intermediate target. If `P` has been
reached, the residual cost to `Q` is bounded uniformly by `R`; before `P`,
the two raw recursions advance together from the same physical successor. -/
private theorem costNumerator_intermediate
    {S : Type} {n : Nat}
    (next : S → Fin n → S) (I P Q : S → Prop)
    (hI : ∀ x e, I x → I (next x e))
    (hQP : ∀ x, I x → Q x → P x)
    (R : Nat)
    (hR : ∀ x, I x → P x → ∀ T,
      costNumerator next Q x T ≤ n ^ T * R) :
    ∀ T x, I x →
      costNumerator next Q x T ≤
        costNumerator next P x T + n ^ T * R := by
  intro T
  induction T with
  | zero =>
      intro x hx
      simp
  | succ T ih =>
      intro x hx
      by_cases hp : P x
      · have hcost := hR x hx hp (T + 1)
        rw [costNumerator_terminal next P x hp] at *
        simpa using hcost
      · have hq : ¬ Q x := by
          intro hqx
          exact hp (hQP x hx hqx)
        rw [costNumerator_succ next Q x hq T,
          costNumerator_succ next P x hp T]
        have hsum := FiniteUniformStoppingTree.ofFn_sum_le
          (fun e : Fin n => costNumerator next Q (next x e) T)
          (fun e : Fin n =>
            costNumerator next P (next x e) T + n ^ T * R)
          (fun e => ih (next x e) (hI x e hx))
        rw [FiniteUniformStoppingTree.ofFn_sum_add,
          FiniteUniformStoppingTree.ofFn_sum_const] at hsum
        have hpow : n * (n ^ T * R) = n ^ (T + 1) * R := by
          rw [Nat.pow_succ]
          ac_rfl
        rw [hpow] at hsum
        omega

/-- PB states always contain a leader, hence a count at most one is exactly
one. This follows directly from the first field of the physical PB invariant. -/
private theorem pb_leaderCount_pos
    {n : Nat} (ring : DirectedRing n) (C : Config n)
    (hPB : PPL.Elim.PB ring C) :
    0 < PPL.Elim.leaderCount C := by
  obtain ⟨i, hi⟩ := hPB.1
  change 0 < (List.ofFn
    (fun j : Fin n => if (C j).leader then 1 else 0)).sum
  have hmem : 1 ∈ (List.ofFn
      (fun j : Fin n => if (C j).leader then 1 else 0)) := by
    rw [List.mem_ofFn]
    exact ⟨i, by simp [hi]⟩
  by_cases hpos : 0 < (List.ofFn
      (fun j : Fin n => if (C j).leader then 1 else 0)).sum
  · exact hpos
  · have hz : (List.ofFn
        (fun j : Fin n => if (C j).leader then 1 else 0)).sum = 0 := by
      omega
    have hall := List.sum_eq_zero_iff_forall_eq_nat.mp hz
    have hone := hall 1 hmem
    omega

#print axioms costNumerator_intermediate
#print axioms pb_leaderCount_pos

/-- Every single-leader state lies below every geometric threshold. -/
private theorem one_atOrBelowScale
    {n : Nat} (h : Nat) (C : Config n)
    (hone : PPL.Elim.leaderCount C = 1) :
    atOrBelowScale h C := by
  unfold atOrBelowScale
  rw [hone, Nat.one_mul]
  exact Nat.pow_le_pow_left (by decide) h

/-! ## Scale induction and arithmetic closure -/

private theorem cost_to_one_at_scale
    {c n : Nat} (hPBStep : PBStepClosure)
    (hLD : LDStatement c) (hc : 1 ≤ c)
    (hn : 2 ≤ n) (ring : DirectedRing n) :
    ∀ h T (C : Config n),
      PPL.Elim.PB ring C → atOrBelowScale h C →
      costNumerator (stepE ring)
        (fun D => PPL.Elim.leaderCount D = 1) C T ≤
        n ^ T * scaleBudgetSum (16 * c * n ^ 2) h := by
  intro h
  induction h with
  | zero =>
      intro T C hPB hscale
      have hpos := pb_leaderCount_pos ring C hPB
      have hone : PPL.Elim.leaderCount C = 1 := by
        have hle : PPL.Elim.leaderCount C ≤ 1 := by
          simpa [atOrBelowScale] using hscale
        omega
      rw [costNumerator_terminal (stepE ring)
        (fun D => PPL.Elim.leaderCount D = 1) C hone T]
      simp [scaleBudgetSum]
  | succ h ih =>
      intro T C hPB hscale
      let P : Config n → Prop := atOrBelowScale h
      let Q : Config n → Prop := fun D => PPL.Elim.leaderCount D = 1
      have hstage := scale_cost hPBStep hLD hc hn ring h C hPB hscale T
      have hcompose := costNumerator_intermediate
        (stepE ring) (PPL.Elim.PB ring) P Q
        (fun D e hD => hPBStep ring D e hD)
        (fun D _ hD => one_atOrBelowScale h D hD)
        (scaleBudgetSum (16 * c * n ^ 2) h)
        (fun D hD hPD U => ih U D hD hPD)
        T C hPB
      change costNumerator (stepE ring) Q C T ≤
        costNumerator (stepE ring) P C T +
          n ^ T * scaleBudgetSum (16 * c * n ^ 2) h at hcompose
      have hscaleBlock : scaleBlock c n h =
          scaleCeil (16 * c * n ^ 2) h + 1 := by
        simp only [scaleBlock, scaleCeil, Nat.pow_two]
        ac_rfl
      calc
        costNumerator (stepE ring) Q C T ≤
            costNumerator (stepE ring) P C T +
              n ^ T * scaleBudgetSum (16 * c * n ^ 2) h := hcompose
        _ ≤ n ^ T * (3 * scaleBlock c n h) +
              n ^ T * scaleBudgetSum (16 * c * n ^ 2) h :=
          Nat.add_le_add_right hstage _
        _ = n ^ T * scaleBudgetSum (16 * c * n ^ 2) (h + 1) := by
          change n ^ T * (3 * scaleBlock c n h) +
              n ^ T * scaleBudgetSum (16 * c * n ^ 2) h =
            n ^ T * (scaleBudgetSum (16 * c * n ^ 2) h +
              3 * (scaleCeil (16 * c * n ^ 2) h + 1))
          rw [← hscaleBlock]
          rw [Nat.mul_add]
          ac_rfl

/-- The finite-word LD(c) transfer: every PB start reaches its unique
remaining leader with cost numerator at most `1172*c*n²` on every horizon. -/
theorem ld_transfer_costNumerator
    {c : Nat}
    (hPBStep : PBStepClosure)
    (hLast : LastLeaderSurvival)
    (hLD : LDStatement c) (hc : 1 ≤ c)
    {n : Nat} (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : Config n) (hPB : PPL.Elim.PB ring C) :
    ∀ T : Nat,
      costNumerator (stepE ring)
        (fun D => PPL.Elim.leaderCount D = 1) C T ≤
      n ^ T * (1172 * c * n * n) := by
  obtain ⟨H, hHit, hLeast⟩ :=
    least_scale_height_exists n hn
  have hcount : PPL.Elim.leaderCount C ≤ n := by
    change (List.ofFn
      (fun i : Fin n => if (C i).leader then 1 else 0)).sum ≤ n
    have hh := FiniteUniformStoppingTree.ofFn_sum_le
      (fun i : Fin n => if (C i).leader then 1 else 0)
      (fun _ : Fin n => 1)
      (fun i => by split <;> omega)
    simpa only [FiniteUniformStoppingTree.ofFn_sum_const, Nat.mul_one] using hh
  have hscale : atOrBelowScale H C := by
    unfold atOrBelowScale
    exact Nat.le_trans (Nat.mul_le_mul_right _ hcount) hHit
  intro T
  have hmain := cost_to_one_at_scale hPBStep hLD hc hn ring H T C hPB hscale
  have hbudget := scale_budget_sum_le n c H hn hc hHit hLeast
  have hmono : scaleBudgetSum (16 * c * n ^ 2) H ≤
      scaleBudgetSum (16 * c * n ^ 2) (H + 1) := by
    simp [scaleBudgetSum]
  have hfinal := Nat.le_trans hmain
    (Nat.mul_le_mul_left (n ^ T) (Nat.le_trans hmono hbudget))
  simpa only [Nat.pow_two, Nat.mul_assoc] using hfinal

/-- The LD(736) specialization uses the exact paper constant
`1172 * 736 = 862592`. -/
theorem ld736_transfer_costNumerator
    (hPBStep : PBStepClosure)
    (hLast : LastLeaderSurvival)
    (hLD : LD736Statement)
    {n : Nat} (hn : 2 ≤ n) (ring : DirectedRing n)
    (C : Config n) (hPB : PPL.Elim.PB ring C) :
    ∀ T : Nat,
      costNumerator (stepE ring)
        (fun D => PPL.Elim.leaderCount D = 1) C T ≤
      n ^ T * (862592 * n * n) := by
  have hLD' : LDStatement 736 := hLD
  intro T
  have hmain :=
    ld_transfer_costNumerator hPBStep hLast hLD' (by decide)
      hn ring C hPB T
  simpa only [show 1172 * 736 = 862592 by decide] using hmain

#print axioms ld_transfer_costNumerator
#print axioms ld736_transfer_costNumerator

end PPL.Convergence.LDTransfer
