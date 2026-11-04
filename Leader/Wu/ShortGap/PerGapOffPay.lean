-- core only
/-!
# Per-gap off-pay: abstract separation and ordinary-row locality

This file is standalone: there are no repository imports and no Mathlib.

The tiny definitions mirror the distinction between the already-proved
whole-ring `global_offPay` and the desired component `perGap_offPay`.

`OrdinaryLocality` mirrors the concrete `NoTransfer` ordinary-row split:
* `frame` says a row outside gap `g` does ¬ change `Phi g`;
* `quiet` says a row touching disabled gap `g` cannot raise `Phi g`.

The final theorem proves the exact finite-uniform child-sum inequality from
those two physical facts.
-/

namespace PerGapOffPay

set_option autoImplicit false

/-! ## A minimal abstract counterexample: n = 2, m = 2 -/

abbrev TinyGap := Fin 2
abbrev TinyEdge := Fin 2
abbrev TinyState := Bool

def tinyNext (_ : TinyState) (_ : TinyEdge) : TinyState := true

def tinyPhi (g : TinyGap) : TinyState -> Nat
  | false => 1
  | true => if g = (0 : TinyGap) then 2 else 0

def tinyRootPot (_ : TinyState) : Nat := 0

def tinyPsi (s : TinyState) : Nat :=
  (List.ofFn (fun g : TinyGap => tinyPhi g s)).sum + tinyRootPot s

def TinyNoTransfer (_ : TinyState) : Prop := True

def TinyEnabled (_ : TinyGap) (_ : TinyState) : Prop := False

def TinyEnabledGlobal (_ : TinyState) : Prop := False

def TinyGlobalOffPay : Prop :=
  forall s : TinyState,
    TinyNoTransfer s -> ¬ TinyEnabledGlobal s ->
      (List.ofFn (fun e : TinyEdge => tinyPsi (tinyNext s e))).sum <=
        2 * tinyPsi s

def TinyPerGapOffPay : Prop :=
  forall g : TinyGap, forall s : TinyState,
    TinyNoTransfer s -> ¬ TinyEnabled g s ->
      (List.ofFn (fun e : TinyEdge =>
        tinyPhi g (tinyNext s e))).sum <=
        2 * tinyPhi g s

/-- The whole-ring inequality holds at both tiny states. -/
theorem tiny_global_offPay : TinyGlobalOffPay := by
  intro s _ _
  cases s <;> decide

/-- Gap 0 at `false` is disabled and violates its component inequality. -/
theorem tiny_perGap_counterexample :
    TinyNoTransfer false  ∧
    ¬ TinyEnabled (0 : TinyGap) false  ∧
    ¬ ((List.ofFn (fun e : TinyEdge =>
      tinyPhi (0 : TinyGap) (tinyNext false e))).sum <=
        2 * tinyPhi (0 : TinyGap) false) := by
  refine ⟨trivial, ?_, ?_⟩
  · intro h
    exact h
  · decide

/-- Therefore the naive component statement is false for the tiny system. -/
theorem tiny_not_perGap_offPay : ¬ TinyPerGapOffPay := by
  intro h
  have hbad := h (0 : TinyGap) false
    tiny_perGap_counterexample.1
    tiny_perGap_counterexample.2.1
  exact tiny_perGap_counterexample.2.2 hbad

/-- One explicit model has global off-pay but ¬ per-gap off-pay. -/
theorem global_offPay_does_not_force_perGap :
    TinyGlobalOffPay  ∧  ¬ TinyPerGapOffPay := by
  exact ⟨tiny_global_offPay, tiny_not_perGap_offPay⟩

/-! ## Finite uniform sums -/

/-- Pointwise domination lifts to domination of `List.ofFn` sums. -/
theorem ofFn_sum_le {n : Nat} (f g : Fin n -> Nat)
    (hfg : forall i, f i <= g i) :
    (List.ofFn f).sum <= (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, List.ofFn_succ, List.sum_cons]
      exact Nat.add_le_add (hfg 0)
        (ih (fun i => f i.succ) (fun i => g i.succ)
          (fun i => hfg i.succ))

/-- The sum of a constant over `Fin n` is exactly `n * c`. -/
theorem ofFn_sum_const (n c : Nat) :
    (List.ofFn (fun _ : Fin n => c)).sum = n * c := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, ih, Nat.succ_mul]
      exact Nat.add_comm _ _

/-! ## Ordinary-row locality -/

structure OrdinaryLocality
    {State Gap : Type} {n : Nat}
    (next : State -> Fin n -> State)
    (Phi : Gap -> State -> Nat)
    (NoTransfer : State -> Prop)
    (enabled : Gap -> State -> Prop)
    (touches : Gap -> State -> Fin n -> Prop) where
  frame :
    forall g s e, NoTransfer s -> ¬ touches g s e ->
      Phi g (next s e) = Phi g s
  quiet :
    forall g s e, NoTransfer s -> ¬ enabled g s ->
      touches g s e -> Phi g (next s e) <= Phi g s

/-- `perGap_offPay` follows from the two ordinary-row physical facts.
Every scheduler child is bounded by the same constant `Phi g s`, so summing
all `n` children gives exactly `n * Phi g s`. -/
theorem perGap_offPay_of_ordinaryLocality
    {State Gap : Type} {n : Nat}
    (next : State -> Fin n -> State)
    (Phi : Gap -> State -> Nat)
    (NoTransfer : State -> Prop)
    (enabled : Gap -> State -> Prop)
    (touches : Gap -> State -> Fin n -> Prop)
    (L : OrdinaryLocality next Phi NoTransfer enabled touches) :
    forall g s, NoTransfer s -> ¬ enabled g s ->
      (List.ofFn (fun e : Fin n => Phi g (next s e))).sum <=
        n * Phi g s := by
  intro g s hNoTransfer hOff
  calc
    (List.ofFn (fun e : Fin n => Phi g (next s e))).sum <=
        (List.ofFn (fun _ : Fin n => Phi g s)).sum := by
      apply ofFn_sum_le
      intro e
      by_cases hTouches : touches g s e
      · exact L.quiet g s e hNoTransfer hOff hTouches
      · rw [L.frame g s e hNoTransfer hTouches]
        exact Nat.le_refl _
    _ = n * Phi g s := ofFn_sum_const n (Phi g s)

#print axioms tiny_global_offPay
#print axioms tiny_perGap_counterexample
#print axioms tiny_not_perGap_offPay
#print axioms global_offPay_does_not_force_perGap
#print axioms ofFn_sum_le
#print axioms ofFn_sum_const
#print axioms perGap_offPay_of_ordinaryLocality

end PerGapOffPay
