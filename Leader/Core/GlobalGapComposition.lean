import Leader.Core.FiniteUniformStoppingTree

namespace GlobalGapComposition

open FiniteUniformStoppingTree

set_option autoImplicit false

-- `next` is the whole-ring raw-edge transition.  Local records remain
-- allocated after deletion; their potential is then zero.

def sumPot {k : Nat} {G : Type}
    (φ : Fin k → G → Nat) (s : G) : Nat :=
  (List.ofFn (fun g => φ g s)).sum

structure SumBellmanHyp (n k : Nat) (G : Type) where
  next      : G → Fin n → G
  enabled   : Fin k → G → Prop
  φ         : Fin k → G → Nat
  -- An enabled component, viewed against the whole `Fin n` scheduler,
  -- pays one raw interaction.
  localPay  : ∀ g s, enabled g s →
    n + (List.ofFn (fun e => φ g (next s e))).sum ≤ n * φ g s
  -- Disabled/off-gap records are stutters or, more generally, nonincreasing.
  offPay    : ∀ g s, ¬ enabled g s →
    (List.ofFn (fun e => φ g (next s e))).sum ≤ n * φ g s
  -- Every nonterminal global state exposes at least one paying component.
  terminal  : G → Prop
  somePay   : ∀ s, ¬ terminal s → ∃ g, enabled g s
  terminal_zero : ∀ s, terminal s → sumPot φ s = 0

private theorem ofFn_sum_zero {n : Nat} :
    (List.ofFn (fun _ : Fin n => 0)).sum = 0 := by
  induction n <;> simp [List.ofFn_succ, *]

/-- Exchange the two finite uniform sums over `Fin n` and `Fin k`. -/
theorem ofFn_sum_comm {n k : Nat} (f : Fin n → Fin k → Nat) :
    (List.ofFn (fun e : Fin n =>
      (List.ofFn (fun g : Fin k => f e g)).sum)).sum =
    (List.ofFn (fun g : Fin k =>
      (List.ofFn (fun e : Fin n => f e g)).sum)).sum := by
  induction k with
  | zero => simpa using (ofFn_sum_zero (n := n))
  | succ k ih =>
      calc
        (List.ofFn (fun e : Fin n =>
            (List.ofFn (fun g : Fin (k + 1) => f e g)).sum)).sum =
          (List.ofFn (fun e : Fin n =>
            f e 0 +
              (List.ofFn (fun g : Fin k => f e g.succ)).sum)).sum := by
                apply ofFn_sum_eq
                intro e
                rw [List.ofFn_succ, List.sum_cons]
        _ =
          (List.ofFn (fun e : Fin n => f e 0)).sum +
            (List.ofFn (fun e : Fin n =>
              (List.ofFn (fun g : Fin k => f e g.succ)).sum)).sum :=
          ofFn_sum_add _ _
        _ =
          (List.ofFn (fun e : Fin n => f e 0)).sum +
            (List.ofFn (fun g : Fin k =>
              (List.ofFn (fun e : Fin n => f e g.succ)).sum)).sum := by
                rw [ih (fun e g => f e g.succ)]
        _ =
          (List.ofFn (fun g : Fin (k + 1) =>
            (List.ofFn (fun e : Fin n => f e g)).sum)).sum := by
              rw [List.ofFn_succ, List.sum_cons]

/-- If every summand is nonincreasing and one distinguished summand pays an
additional `bonus`, then the whole finite sum pays that bonus. -/
theorem ofFn_sum_le_of_one_pay
    {k : Nat} (bonus : Nat) (a b : Fin k → Nat) (chosen : Fin k)
    (hpay : bonus + a chosen ≤ b chosen)
    (hle : ∀ i, a i ≤ b i) :
    bonus + (List.ofFn a).sum ≤ (List.ofFn b).sum := by
  induction k with
  | zero => exact Fin.elim0 chosen
  | succ k ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons]
      by_cases hzero : chosen = 0
      · subst chosen
        have htail := ofFn_sum_le
          (fun i : Fin k => a i.succ) (fun i => b i.succ)
          (fun i => hle i.succ)
        omega
      · have hpos : 0 < chosen.val := by
          have hne : chosen.val ≠ 0 :=
            fun h => hzero (Fin.ext (by simpa using h))
          omega
        let previous : Fin k := ⟨chosen.val - 1, by omega⟩
        have hsucc : previous.succ = chosen :=
          Fin.ext (by simp [previous]; omega)
        have htail := ih
          (fun i : Fin k => a i.succ) (fun i => b i.succ) previous
          (by simpa only [hsucc] using hpay)
          (fun i => hle i.succ)
        have hhead := hle 0
        omega

/-- Summing per-gap Bellman potentials yields a Bellman supersolution for the
whole raw scheduler whenever every nonterminal state has a paying component. -/
theorem sum_perGap_supersolution
    {n k : Nat} {G : Type} (H : SumBellmanHyp n k G) :
    ∀ s, ¬ H.terminal s →
      n + (List.ofFn (fun e : Fin n =>
        sumPot H.φ (H.next s e))).sum ≤
          n * sumPot H.φ s := by
  classical
  intro s hs
  obtain ⟨g0, hg0⟩ := H.somePay s hs
  have hcomponent : ∀ g : Fin k,
      (List.ofFn (fun e : Fin n => H.φ g (H.next s e))).sum ≤
        n * H.φ g s := by
    intro g
    by_cases hg : H.enabled g s
    · have hp := H.localPay g s hg
      omega
    · exact H.offPay g s hg
  have hsum :
      n + (List.ofFn (fun g : Fin k =>
        (List.ofFn (fun e : Fin n => H.φ g (H.next s e))).sum)).sum ≤
          (List.ofFn (fun g : Fin k => n * H.φ g s)).sum :=
    ofFn_sum_le_of_one_pay n
      (fun g : Fin k =>
        (List.ofFn (fun e : Fin n => H.φ g (H.next s e))).sum)
      (fun g : Fin k => n * H.φ g s) g0
      (H.localPay g0 s hg0) hcomponent
  calc
    n + (List.ofFn (fun e : Fin n =>
        sumPot H.φ (H.next s e))).sum =
      n + (List.ofFn (fun g : Fin k =>
        (List.ofFn (fun e : Fin n => H.φ g (H.next s e))).sum)).sum := by
          unfold sumPot
          exact congrArg (n + ·)
            (ofFn_sum_comm
              (fun e : Fin n => fun g : Fin k => H.φ g (H.next s e)))
    _ ≤ (List.ofFn (fun g : Fin k => n * H.φ g s)).sum := hsum
    _ = n * sumPot H.φ s := by
      unfold sumPot
      exact ofFn_sum_mul_left n (fun g : Fin k => H.φ g s)

/-- Active states are exactly the nonterminal global states.  A transition
stops before a terminal global state is inserted into the active-state type. -/
noncomputable def nonterminalStep
    {n k : Nat} {G : Type} (H : SumBellmanHyp n k G) :
    {s : G // ¬ H.terminal s} → Fin n →
      StopNode {s : G // ¬ H.terminal s} := by
  classical
  exact fun state edge =>
    if hnext : H.terminal (H.next state.1 edge) then
      .success
    else
      .active ⟨H.next state.1 edge, hnext⟩

/-- The summed gap potential on nonterminal active states, extended by zero at
both stopped outcomes. -/
def nonterminalPotential
    {n k : Nat} {G : Type} (H : SumBellmanHyp n k G) :
    StopNode {s : G // ¬ H.terminal s} → Nat
  | .active state => sumPot H.φ state.1
  | .success => 0
  | .failure => 0

/-- Repository-interface wrapper for the global per-gap composition theorem. -/
theorem sum_perGap_natBellmanSuperSolution
    {n k : Nat} {G : Type} (H : SumBellmanHyp n k G) :
    NatBellmanSuperSolution (nonterminalStep H) 1
      (nonterminalPotential H) := by
  classical
  refine ⟨rfl, rfl, ?_⟩
  intro state
  rcases state with ⟨s, hs⟩
  have hactive := sum_perGap_supersolution H s hs
  have hchildren :
      (List.ofFn (fun e : Fin n =>
        nonterminalPotential H (nonterminalStep H ⟨s, hs⟩ e))).sum =
      (List.ofFn (fun e : Fin n =>
        sumPot H.φ (H.next s e))).sum := by
    apply ofFn_sum_eq
    intro e
    by_cases hterminal : H.terminal (H.next s e)
    · have hz := H.terminal_zero (H.next s e) hterminal
      simp [nonterminalStep, nonterminalPotential, hterminal, hz]
    · simp [nonterminalStep, nonterminalPotential, hterminal]
  change 1 * n +
      (List.ofFn (fun e : Fin n =>
        nonterminalPotential H (nonterminalStep H ⟨s, hs⟩ e))).sum ≤
      n * sumPot H.φ s
  rw [hchildren]
  simpa using hactive

end GlobalGapComposition

#print axioms GlobalGapComposition.ofFn_sum_comm
#print axioms GlobalGapComposition.ofFn_sum_le_of_one_pay
#print axioms GlobalGapComposition.sum_perGap_supersolution
#print axioms GlobalGapComposition.sum_perGap_natBellmanSuperSolution
