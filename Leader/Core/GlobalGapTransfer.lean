import Leader.Core.GlobalGapComposition

namespace GlobalGapTransfer

open GlobalGapComposition
open FiniteUniformStoppingTree

set_option autoImplicit false

/-- The ordinary composition hypotheses, guarded to rows with no transfers,
plus a reserve and the ordinary/unique-transfer row dichotomy.

On a transfer edge, an increase of at most `M s e` in the gap sum is paid by
a reserve decrease of at least `M s e + n`. Thus that single edge pays the
whole denominator-cleared cost `n` of one uniform interaction.

`rowCases` makes the transfer edge unique and requires every other edge to
be pointwise off-pay for every component. Reserve monotonicity on those
other edges follows from `reserveNonincrease`.
-/
structure TransferBellmanHyp (n k : Nat) (G : Type) where
  next : G → Fin n → G
  enabled : Fin k → G → Prop
  φ : Fin k → G → Nat
  terminal : G → Prop
  ρ : G → Nat
  transfer : G → Fin n → Prop
  M : G → Fin n → Nat
  localPay : ∀ g s, (∀ e, ¬ transfer s e) → enabled g s →
    n + (List.ofFn (fun e => φ g (next s e))).sum ≤ n * φ g s
  offPay : ∀ g s, (∀ e, ¬ transfer s e) → ¬ enabled g s →
    (List.ofFn (fun e => φ g (next s e))).sum ≤ n * φ g s
  somePay : ∀ s, ¬ terminal s → (∀ e, ¬ transfer s e) →
    ∃ g, enabled g s
  terminal_zero : ∀ s, terminal s →
    sumPot φ s = 0 ∧ ρ s = 0
  transferRise : ∀ s e, transfer s e →
    sumPot φ (next s e) ≤ sumPot φ s + M s e
  transferDrop : ∀ s e, transfer s e →
    ρ (next s e) + M s e + n ≤ ρ s
  reserveNonincrease : ∀ s e, ¬ transfer s e →
    ρ (next s e) ≤ ρ s
  rowCases : ∀ s, ¬ terminal s →
    (∀ e, ¬ transfer s e) ∨
      ∃ e₀ : Fin n, transfer s e₀ ∧
        ∀ e : Fin n, e ≠ e₀ →
          ¬ transfer s e ∧ ∀ g : Fin k, φ g (next s e) ≤ φ g s

/-- The original composition interface is the zero-reserve, no-transfer
special case. In particular, the new hypotheses do not strengthen the old
ordinary-row obligations. -/
def ofSumBellmanHyp {n k : Nat} {G : Type}
    (H : SumBellmanHyp n k G) : TransferBellmanHyp n k G where
  next := H.next
  enabled := H.enabled
  φ := H.φ
  terminal := H.terminal
  ρ := fun _ => 0
  transfer := fun _ _ => False
  M := fun _ _ => 0
  localPay := fun g s _ hg => H.localPay g s hg
  offPay := fun g s _ hg => H.offPay g s hg
  somePay := fun s hs _ => H.somePay s hs
  terminal_zero := fun s hs => ⟨H.terminal_zero s hs, rfl⟩
  transferRise := fun _ _ he => False.elim he
  transferDrop := fun _ _ he => False.elim he
  reserveNonincrease := fun _ _ _ => Nat.le_refl 0
  rowCases := fun _ _ => Or.inl (fun _ he => he)

/-- A transfer edge pays `n` in the combined potential, even when the gap
sum rises. The proof only adds inequalities and rearranges additions. -/
theorem transfer_edge_pay
    {n k : Nat} {G : Type} (H : TransferBellmanHyp n k G)
    (s : G) (e : Fin n) (he : H.transfer s e) :
    n + (sumPot H.φ (H.next s e) + H.ρ (H.next s e)) ≤
      sumPot H.φ s + H.ρ s := by
  have hgap := H.transferRise s e he
  have hreserve := H.transferDrop s e he
  calc
    n + (sumPot H.φ (H.next s e) + H.ρ (H.next s e)) =
        sumPot H.φ (H.next s e) + (H.ρ (H.next s e) + n) := by
      simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    _ ≤ (sumPot H.φ s + H.M s e) + (H.ρ (H.next s e) + n) :=
      Nat.add_le_add_right hgap (H.ρ (H.next s e) + n)
    _ = sumPot H.φ s + (H.ρ (H.next s e) + H.M s e + n) := by
      simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    _ ≤ sumPot H.φ s + H.ρ s :=
      Nat.add_le_add_left hreserve (sumPot H.φ s)

/-- Finite-sum argument on an ordinary row. Local and off-pay
bounds are only used at this row, not at possible transfer successors. -/
theorem ordinary_gap_supersolution
    {n k : Nat} {G : Type} (H : TransferBellmanHyp n k G)
    (s : G) (hs : ¬ H.terminal s)
    (hordinary : ∀ e, ¬ H.transfer s e) :
    n + (List.ofFn (fun e : Fin n =>
      sumPot H.φ (H.next s e))).sum ≤ n * sumPot H.φ s := by
  classical
  obtain ⟨g₀, hg₀⟩ := H.somePay s hs hordinary
  have hcomponent : ∀ g : Fin k,
      (List.ofFn (fun e : Fin n => H.φ g (H.next s e))).sum ≤
        n * H.φ g s := by
    intro g
    by_cases hg : H.enabled g s
    · exact Nat.le_of_add_left_le (H.localPay g s hordinary hg)
    · exact H.offPay g s hordinary hg
  have hsum :
      n + (List.ofFn (fun g : Fin k =>
        (List.ofFn (fun e : Fin n => H.φ g (H.next s e))).sum)).sum ≤
      (List.ofFn (fun g : Fin k => n * H.φ g s)).sum :=
    ofFn_sum_le_of_one_pay n
      (fun g : Fin k =>
        (List.ofFn (fun e : Fin n => H.φ g (H.next s e))).sum)
      (fun g : Fin k => n * H.φ g s) g₀
      (H.localPay g₀ s hordinary hg₀) hcomponent
  calc
    n + (List.ofFn (fun e : Fin n =>
        sumPot H.φ (H.next s e))).sum =
      n + (List.ofFn (fun g : Fin k =>
        (List.ofFn (fun e : Fin n => H.φ g (H.next s e))).sum)).sum := by
      unfold sumPot
      exact congrArg (fun t : Nat => n + t)
        (ofFn_sum_comm
          (fun e : Fin n => fun g : Fin k => H.φ g (H.next s e)))
    _ ≤ (List.ofFn (fun g : Fin k => n * H.φ g s)).sum := hsum
    _ = n * sumPot H.φ s := by
      unfold sumPot
      exact ofFn_sum_mul_left n (fun g : Fin k => H.φ g s)

/-- Case (a): an ordinary paying row, plus a nonincreasing reserve. -/
theorem ordinary_supersolution
    {n k : Nat} {G : Type} (H : TransferBellmanHyp n k G)
    (s : G) (hs : ¬ H.terminal s)
    (hordinary : ∀ e, ¬ H.transfer s e) :
    n + (List.ofFn (fun e : Fin n =>
      sumPot H.φ (H.next s e) + H.ρ (H.next s e))).sum ≤
        n * (sumPot H.φ s + H.ρ s) := by
  have hgap := ordinary_gap_supersolution H s hs hordinary
  have hreserve :
      (List.ofFn (fun e : Fin n => H.ρ (H.next s e))).sum ≤
        n * H.ρ s := by
    calc
      (List.ofFn (fun e : Fin n => H.ρ (H.next s e))).sum ≤
          (List.ofFn (fun _ : Fin n => H.ρ s)).sum :=
        ofFn_sum_le _ _
          (fun e => H.reserveNonincrease s e (hordinary e))
      _ = n * H.ρ s := ofFn_sum_const n (H.ρ s)
  calc
    n + (List.ofFn (fun e : Fin n =>
        sumPot H.φ (H.next s e) + H.ρ (H.next s e))).sum =
      (n + (List.ofFn (fun e : Fin n =>
        sumPot H.φ (H.next s e))).sum) +
        (List.ofFn (fun e : Fin n => H.ρ (H.next s e))).sum := by
      rw [ofFn_sum_add]
      exact (Nat.add_assoc n _ _).symm
    _ ≤ n * sumPot H.φ s + n * H.ρ s := Nat.add_le_add hgap hreserve
    _ = n * (sumPot H.φ s + H.ρ s) :=
      (Nat.mul_add n (sumPot H.φ s) (H.ρ s)).symm

/-- Case (b): one transfer edge pays `n`; all other edges are nonincreasing
in the combined potential. This proof sums over edges, not components. -/
theorem unique_transfer_supersolution
    {n k : Nat} {G : Type} (H : TransferBellmanHyp n k G)
    (s : G) (e₀ : Fin n) (he₀ : H.transfer s e₀)
    (hoff : ∀ e : Fin n, e ≠ e₀ →
      ¬ H.transfer s e ∧
        ∀ g : Fin k, H.φ g (H.next s e) ≤ H.φ g s) :
    n + (List.ofFn (fun e : Fin n =>
      sumPot H.φ (H.next s e) + H.ρ (H.next s e))).sum ≤
        n * (sumPot H.φ s + H.ρ s) := by
  have hchosen := transfer_edge_pay H s e₀ he₀
  have hle : ∀ e : Fin n,
      sumPot H.φ (H.next s e) + H.ρ (H.next s e) ≤
        sumPot H.φ s + H.ρ s := by
    intro e
    by_cases he : e = e₀
    · subst e
      exact Nat.le_of_add_left_le hchosen
    · have hother := hoff e he
      have hgap : sumPot H.φ (H.next s e) ≤ sumPot H.φ s := by
        unfold sumPot
        exact ofFn_sum_le _ _ hother.2
      exact Nat.add_le_add hgap
        (H.reserveNonincrease s e hother.1)
  have hsum := ofFn_sum_le_of_one_pay n
    (fun e : Fin n => sumPot H.φ (H.next s e) + H.ρ (H.next s e))
    (fun _ : Fin n => sumPot H.φ s + H.ρ s)
    e₀ hchosen hle
  simpa only [ofFn_sum_const] using hsum

/-- The combined gap-plus-reserve potential is a denominator-cleared
unit-cost Bellman supersolution at every nonterminal state. -/
theorem transfer_supersolution
    {n k : Nat} {G : Type} (H : TransferBellmanHyp n k G) :
    ∀ s, ¬ H.terminal s →
      n + (List.ofFn (fun e : Fin n =>
        sumPot H.φ (H.next s e) + H.ρ (H.next s e))).sum ≤
          n * (sumPot H.φ s + H.ρ s) := by
  intro s hs
  rcases H.rowCases s hs with hordinary | htransfer
  · exact ordinary_supersolution H s hs hordinary
  · rcases htransfer with ⟨e₀, he₀, hoff⟩
    exact unique_transfer_supersolution H s e₀ he₀ hoff

/-- The subtype construction: terminal successors become success,
and only nonterminal successors enter the active-state subtype. -/
noncomputable def nonterminalStep
    {n k : Nat} {G : Type} (H : TransferBellmanHyp n k G) :
    {s : G // ¬ H.terminal s} → Fin n →
      StopNode {s : G // ¬ H.terminal s} := by
  classical
  exact fun state edge =>
    if hnext : H.terminal (H.next state.1 edge) then
      .success
    else
      .active ⟨H.next state.1 edge, hnext⟩

/-- The combined potential on active states, extended by zero at both
stopped outcomes. -/
def nonterminalPotential
    {n k : Nat} {G : Type} (H : TransferBellmanHyp n k G) :
    StopNode {s : G // ¬ H.terminal s} → Nat
  | .active state => sumPot H.φ state.1 + H.ρ state.1
  | .success => 0
  | .failure => 0

/-- Stopping at a terminal successor preserves the raw successor potential
exactly because both summands vanish there. -/
theorem nonterminalPotential_step
    {n k : Nat} {G : Type} (H : TransferBellmanHyp n k G)
    (state : {s : G // ¬ H.terminal s}) (e : Fin n) :
    nonterminalPotential H (nonterminalStep H state e) =
      sumPot H.φ (H.next state.1 e) + H.ρ (H.next state.1 e) := by
  classical
  by_cases ht : H.terminal (H.next state.1 e)
  · obtain ⟨hgap, hreserve⟩ := H.terminal_zero (H.next state.1 e) ht
    simp [nonterminalStep, nonterminalPotential, ht, hgap, hreserve]
  · simp [nonterminalStep, nonterminalPotential, ht]

/-- Repository-interface wrapper, with unit interaction scale. -/
theorem transfer_natBellmanSuperSolution
    {n k : Nat} {G : Type} (H : TransferBellmanHyp n k G) :
    NatBellmanSuperSolution (nonterminalStep H) 1
      (nonterminalPotential H) := by
  refine ⟨rfl, rfl, ?_⟩
  intro state
  have hactive := transfer_supersolution H state.1 state.2
  have hchildren :
      (List.ofFn (fun e : Fin n =>
        nonterminalPotential H (nonterminalStep H state e))).sum =
      (List.ofFn (fun e : Fin n =>
        sumPot H.φ (H.next state.1 e) + H.ρ (H.next state.1 e))).sum :=
    ofFn_sum_eq _ _ (fun e => nonterminalPotential_step H state e)
  change 1 * n +
      (List.ofFn (fun e : Fin n =>
        nonterminalPotential H (nonterminalStep H state e))).sum ≤
      n * (sumPot H.φ state.1 + H.ρ state.1)
  rw [hchildren]
  simpa only [Nat.one_mul] using hactive

end GlobalGapTransfer

#print axioms GlobalGapTransfer.transfer_edge_pay
#print axioms GlobalGapTransfer.ordinary_gap_supersolution
#print axioms GlobalGapTransfer.ordinary_supersolution
#print axioms GlobalGapTransfer.unique_transfer_supersolution
#print axioms GlobalGapTransfer.transfer_supersolution
#print axioms GlobalGapTransfer.nonterminalPotential_step
#print axioms GlobalGapTransfer.transfer_natBellmanSuperSolution
