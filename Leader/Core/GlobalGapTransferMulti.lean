import Leader.Core.GlobalGapTransfer

open FiniteUniformStoppingTree
open GlobalGapComposition

namespace GlobalGapTransfer

private theorem sum_ofFn_mono {m : Nat} (a b : Fin m → Nat)
    (h : ∀ i, a i ≤ b i) :
    (List.ofFn a).sum ≤ (List.ofFn b).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp only [List.ofFn_succ, List.sum_cons]
      apply Nat.add_le_add
      · exact h 0
      · exact ih (fun i => a i.succ) (fun i => b i.succ) (fun i => h i.succ)

private theorem sum_ofFn_add {m : Nat} (a b : Fin m → Nat) :
    (List.ofFn (fun i => a i + b i)).sum =
      (List.ofFn a).sum + (List.ofFn b).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp only [List.ofFn_succ, List.sum_cons]
      have ht := ih (fun i => a i.succ) (fun i => b i.succ)
      omega

private theorem sum_ofFn_mul_left {m : Nat} (c : Nat) (a : Fin m → Nat) :
    (List.ofFn (fun i => c * a i)).sum = c * (List.ofFn a).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp only [List.ofFn_succ, List.sum_cons]
      rw [ih (fun i => a i.succ)]
      exact (Nat.mul_add c (a 0)
        (List.ofFn (fun i : Fin m => a i.succ)).sum).symm

private theorem sum_ofFn_const (m B : Nat) :
    (List.ofFn (fun _ : Fin m => B)).sum = m * B := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp only [List.ofFn_succ, List.sum_cons]
      rw [ih, Nat.succ_mul]
      omega

private theorem credit_add_sum_ofFn_le
    {m : Nat} (a b : Fin m → Nat) (credit : Nat) (i₀ : Fin m)
    (hall : ∀ i, a i ≤ b i)
    (hone : credit + a i₀ ≤ b i₀) :
    credit + (List.ofFn a).sum ≤ (List.ofFn b).sum := by
  induction m generalizing credit with
  | zero => exact Fin.elim0 i₀
  | succ m ih =>
      cases i₀ using Fin.cases with
      | zero =>
          simp only [List.ofFn_succ, List.sum_cons]
          have htail := sum_ofFn_mono
            (fun i : Fin m => a i.succ)
            (fun i : Fin m => b i.succ)
            (fun i => hall i.succ)
          omega
      | succ i₀ =>
          simp only [List.ofFn_succ, List.sum_cons]
          have hhead := hall (0 : Fin (m + 1))
          have htail := ih
            (fun i : Fin m => a i.succ)
            (fun i : Fin m => b i.succ)
            credit i₀ (fun i => hall i.succ) hone
          omega

private theorem sum_ofFn_swap {m r : Nat} (f : Fin m → Fin r → Nat) :
    (List.ofFn (fun i : Fin m => (List.ofFn (fun j : Fin r => f i j)).sum)).sum =
      (List.ofFn (fun j : Fin r => (List.ofFn (fun i : Fin m => f i j)).sum)).sum := by
  induction m with
  | zero =>
      simp only [List.ofFn_zero, List.sum_nil]
      rw [FiniteUniformStoppingTree.ofFn_sum_const]
      simp
  | succ m ih =>
      simp only [List.ofFn_succ, List.sum_cons]
      have htail := ih (fun i j => f i.succ j)
      have hadd := sum_ofFn_add
        (fun j : Fin r => f 0 j)
        (fun j : Fin r => (List.ofFn (fun i : Fin m => f i.succ j)).sum)
      omega

private theorem sumPot_le_of_pointwise
    {k : Nat} {G : Type} (φ : Fin k → G → Nat) {s t : G}
    (h : ∀ g, φ g t ≤ φ g s) :
    sumPot φ t ≤ sumPot φ s := by
  unfold sumPot
  exact sum_ofFn_mono (fun g => φ g t) (fun g => φ g s) h

/--
Multi-transfer version of `TransferBellmanHyp`.

For a fixed nonterminal row `s`, the predicate `transfer s : Fin n → Prop`
*is* the transfer set `T ⊆ Fin n`.  The second branch of `rowCases` says
only that `T` is nonempty and that every edge outside `T` is pointwise
off-pay for every component.  It deliberately does **not** say that the
witness `e₀` is the unique transfer edge.  `reserveNonincrease` supplies the
reserve law outside `T`; `transferRise` and `transferDrop` supply the two laws
on every edge in `T`.

The reserve accounting with several simultaneous transfers is sound.  Put

  `C e = sumPot φ (next s e) + ρ (next s e)` and
  `P   = sumPot φ s + ρ s`.

For every `e ∈ T`, `transferRise` plus the per-edge hypothesis

  `ρ (next s e) + M s e + n ≤ ρ s`

gives `n + C e ≤ P`.  For every `e ∉ T`, pointwise off-pay plus
`reserveNonincrease` gives `C e ≤ P`.  Thus, if `T` has `q > 0` edges, summing
the branch inequalities gives the stronger bookkeeping inequality

  `q * n + Σ_e C e ≤ n * P`,

and hence `n + Σ_e C e ≤ n * P`.  There is no sequential consumption of one
reserve value along a single execution: the Bellman sum evaluates the `n`
children independently, each against the same parent potential `P`.  The
formal proof below does not even need to count `q`; it selects one transfer
edge to pay the single leading `n` and uses the plain `C e ≤ P` bound for all
other children.  When `T` is empty, the ordinary `localPay`/`somePay` argument
pays that leading `n` instead.
-/
structure TransferBellmanHypMulti (n k : Nat) (G : Type) where
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
        ∀ e : Fin n, ¬ transfer s e →
          ∀ g : Fin k, φ g (next s e) ≤ φ g s

/--
Transfer-count `0` special case (the `k` in `TransferBellmanHypMulti n k G`
still counts components, not transfer edges): this is exactly the ordinary
row argument.  One enabled component pays the leading `n`; every component
pays its scheduler-row sum, and the reserve is nonincreasing on every edge.
-/
theorem transfer_multi_zero_supersolution
    {n k : Nat} {G : Type} (H : TransferBellmanHypMulti n k G)
    (s : G) (hs : ¬ H.terminal s) (hzero : ∀ e, ¬ H.transfer s e) :
    n + (List.ofFn (fun e : Fin n =>
      sumPot H.φ (H.next s e) + H.ρ (H.next s e))).sum ≤
        n * (sumPot H.φ s + H.ρ s) := by
  classical
  obtain ⟨g₀, hg₀⟩ := H.somePay s hs hzero
  let compChild : Fin k → Nat := fun g =>
    (List.ofFn (fun e : Fin n => H.φ g (H.next s e))).sum
  have hallComp : ∀ g, compChild g ≤ n * H.φ g s := by
    intro g
    by_cases hg : H.enabled g s
    · have hp := H.localPay g s hzero hg
      dsimp [compChild]
      omega
    · simpa [compChild] using H.offPay g s hzero hg
  have hpayComp : n + compChild g₀ ≤ n * H.φ g₀ s := by
    simpa [compChild] using H.localPay g₀ s hzero hg₀
  have hcompSum :
      n + (List.ofFn compChild).sum ≤
        (List.ofFn (fun g : Fin k => n * H.φ g s)).sum :=
    credit_add_sum_ofFn_le compChild
      (fun g : Fin k => n * H.φ g s) n g₀ hallComp hpayComp
  have hswap :
      (List.ofFn (fun e : Fin n => sumPot H.φ (H.next s e))).sum =
        (List.ofFn (fun g : Fin k =>
          (List.ofFn (fun e : Fin n => H.φ g (H.next s e))).sum)).sum := by
    unfold sumPot
    exact sum_ofFn_swap (fun e g => H.φ g (H.next s e))
  have hscale :
      (List.ofFn (fun g : Fin k => n * H.φ g s)).sum =
        n * sumPot H.φ s := by
    unfold sumPot
    exact sum_ofFn_mul_left n (fun g : Fin k => H.φ g s)
  have hφ :
      n + (List.ofFn (fun e : Fin n => sumPot H.φ (H.next s e))).sum ≤
        n * sumPot H.φ s := by
    calc
      n + (List.ofFn (fun e : Fin n => sumPot H.φ (H.next s e))).sum
          = n + (List.ofFn compChild).sum := by
              rw [hswap]
      _ ≤ (List.ofFn (fun g : Fin k => n * H.φ g s)).sum := hcompSum
      _ = n * sumPot H.φ s := hscale
  have hρ :
      (List.ofFn (fun e : Fin n => H.ρ (H.next s e))).sum ≤
        n * H.ρ s := by
    calc
      (List.ofFn (fun e : Fin n => H.ρ (H.next s e))).sum
          ≤ (List.ofFn (fun _ : Fin n => H.ρ s)).sum :=
            sum_ofFn_mono
              (fun e : Fin n => H.ρ (H.next s e))
              (fun _ : Fin n => H.ρ s)
              (fun e => H.reserveNonincrease s e (hzero e))
      _ = n * H.ρ s := sum_ofFn_const n (H.ρ s)
  have hsplit :
      (List.ofFn (fun e : Fin n =>
        sumPot H.φ (H.next s e) + H.ρ (H.next s e))).sum =
        (List.ofFn (fun e : Fin n => sumPot H.φ (H.next s e))).sum +
        (List.ofFn (fun e : Fin n => H.ρ (H.next s e))).sum :=
    sum_ofFn_add
      (fun e : Fin n => sumPot H.φ (H.next s e))
      (fun e : Fin n => H.ρ (H.next s e))
  rw [hsplit, Nat.mul_add]
  omega

/--
Bellman supersolution inequality with an arbitrary nonempty set of simultaneous
transfer edges.  On a transfer row, one selected transfer edge supplies the
single external `n`; every transfer edge, including any additional ones, is
independently bounded by the parent potential via its own rise/drop law.
-/
theorem transfer_multi_supersolution
    {n k : Nat} {G : Type} (H : TransferBellmanHypMulti n k G) :
    ∀ s, ¬ H.terminal s →
      n + (List.ofFn (fun e : Fin n =>
        sumPot H.φ (H.next s e) + H.ρ (H.next s e))).sum ≤
          n * (sumPot H.φ s + H.ρ s) := by
  intro s hs
  classical
  rcases H.rowCases s hs with hzero | ⟨e₀, he₀, hoff⟩
  · exact transfer_multi_zero_supersolution H s hs hzero
  · let child : Fin n → Nat := fun e =>
      sumPot H.φ (H.next s e) + H.ρ (H.next s e)
    let parent : Nat := sumPot H.φ s + H.ρ s
    have hstrong : ∀ e, H.transfer s e → n + child e ≤ parent := by
      intro e he
      have hrise := H.transferRise s e he
      have hdrop := H.transferDrop s e he
      dsimp [child, parent]
      omega
    have hall : ∀ e, child e ≤ parent := by
      intro e
      by_cases he : H.transfer s e
      · have h := hstrong e he
        omega
      · have hpot := sumPot_le_of_pointwise H.φ (hoff e he)
        have hreserve := H.reserveNonincrease s e he
        dsimp [child, parent]
        omega
    have hcredit :
        n + (List.ofFn child).sum ≤
          (List.ofFn (fun _ : Fin n => parent)).sum :=
      credit_add_sum_ofFn_le child (fun _ : Fin n => parent)
        n e₀ hall (hstrong e₀ he₀)
    calc
      n + (List.ofFn (fun e : Fin n =>
        sumPot H.φ (H.next s e) + H.ρ (H.next s e))).sum
          = n + (List.ofFn child).sum := by rfl
      _ ≤ (List.ofFn (fun _ : Fin n => parent)).sum := hcredit
      _ = n * parent := sum_ofFn_const n parent
      _ = n * (sumPot H.φ s + H.ρ s) := by rfl

/--
Transfer-count `1` special case.  The uniqueness hypothesis is deliberately
stronger than what `transfer_multi_supersolution` needs; this theorem records
that an exactly-one-transfer row is included unchanged in the multi interface.
Here again, `1` counts transfer edges, not the component parameter `k`.
-/
theorem transfer_multi_one_supersolution
    {n k : Nat} {G : Type} (H : TransferBellmanHypMulti n k G)
    (s : G) (hs : ¬ H.terminal s) (e₀ : Fin n)
    (hone : ∀ e : Fin n, H.transfer s e ↔ e = e₀) :
    n + (List.ofFn (fun e : Fin n =>
      sumPot H.φ (H.next s e) + H.ρ (H.next s e))).sum ≤
        n * (sumPot H.φ s + H.ρ s) := by
  have he₀ : H.transfer s e₀ := (hone e₀).2 rfl
  rcases H.rowCases s hs with hzero | hmixed
  · exact False.elim (hzero e₀ he₀)
  · exact transfer_multi_supersolution H s hs

/-- Every old single-transfer-row hypothesis is a multi-transfer hypothesis. -/
def TransferBellmanHyp.toMulti
    {n k : Nat} {G : Type} (H : TransferBellmanHyp n k G) :
    TransferBellmanHypMulti n k G where
  next := H.next
  enabled := H.enabled
  φ := H.φ
  terminal := H.terminal
  ρ := H.ρ
  transfer := H.transfer
  M := H.M
  localPay := H.localPay
  offPay := H.offPay
  somePay := H.somePay
  terminal_zero := H.terminal_zero
  transferRise := H.transferRise
  transferDrop := H.transferDrop
  reserveNonincrease := H.reserveNonincrease
  rowCases := by
    intro s hs
    rcases H.rowCases s hs with hzero | ⟨e₀, he₀, hrest⟩
    · exact Or.inl hzero
    · refine Or.inr ⟨e₀, he₀, ?_⟩
      intro e hnot g
      by_cases heq : e = e₀
      · subst e
        exact False.elim (hnot he₀)
      · exact (hrest e heq).2 g

/-- Corollary in implication form requested by the compatibility interface. -/
def transferBellmanHyp_implies_multi
    {n k : Nat} {G : Type} (H : TransferBellmanHyp n k G) :
    TransferBellmanHypMulti n k G :=
  H.toMulti

/--
The old zero-or-one-transfer theorem is recovered by passing its hypothesis
through `TransferBellmanHyp.toMulti`.  Thus the multi theorem is a genuine
conservative generalization of `transfer_supersolution`.
-/
theorem transfer_supersolution_recovered
    {n k : Nat} {G : Type} (H : TransferBellmanHyp n k G) :
    ∀ s, ¬ H.terminal s →
      n + (List.ofFn (fun e : Fin n =>
        sumPot H.φ (H.next s e) + H.ρ (H.next s e))).sum ≤
          n * (sumPot H.φ s + H.ρ s) := by
  simpa [TransferBellmanHyp.toMulti] using
    (transfer_multi_supersolution (H := H.toMulti))

#print axioms transfer_multi_zero_supersolution
#print axioms transfer_multi_supersolution
#print axioms transfer_multi_one_supersolution
#print axioms TransferBellmanHyp.toMulti
#print axioms transferBellmanHyp_implies_multi
#print axioms transfer_supersolution_recovered

end GlobalGapTransfer
