import Leader.Core.FiniteUniformStoppingTree
import Leader.Core.BellmanGeometricTailReachable


namespace PhaseComposition


open FiniteUniformStoppingTree


set_option autoImplicit false


inductive TwoPhase where
  | p1
  | p2
  deriving DecidableEq


structure MonotonePhaseIndicator {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) where
  phase : S → TwoPhase
  noBack : ∀ s e t, phase s = .p2 →
    step s e = .active t → phase t = .p2


/-- Sequentially compose two phases on one stopped transition system.


At a phase-1 node, `Φ₁` is charged only to children that remain in phase 1.
Every scheduler child also receives a reserve `C₂`; this reserve covers
phase-1-to-phase-2 crossings by `henter` and `hC₂`, and trivially covers
terminal children.  At a phase-2 node, monotonicity (`noBack`) reduces the
composite Bellman inequality to `h₂`. -/
theorem phase_compose_bellman
    {S : Type} {n : Nat} (step : S → Fin n → StopNode S)
    (I : MonotonePhaseIndicator step)
    (Φ₁ Φ₂ : StopNode S → Nat) (C₂ : Nat) (E₂ : S → Prop)
    (h₁ : ∀ s, I.phase s = .p1 →
      n + (List.ofFn (fun e : Fin n => match step s e with
        | .active t => if I.phase t = .p1 then Φ₁ (.active t) else 0
        | .success => 0 | .failure => 0)).sum ≤ n * Φ₁ (.active s))
    (h₂ : ∀ s, I.phase s = .p2 →
      n + (List.ofFn (fun e : Fin n => match step s e with
        | .active t => Φ₂ (.active t)
        | .success => 0 | .failure => 0)).sum ≤ n * Φ₂ (.active s))
    (henter : ∀ s e t, I.phase s = .p1 → step s e = .active t →
      I.phase t = .p2 → E₂ t)
    (hC₂ : ∀ t, E₂ t → Φ₂ (.active t) ≤ C₂) :
    NatBellmanSuperSolution step 1
      (fun x => match x with
        | .active s => if I.phase s = .p1 then Φ₁ (.active s) + C₂
                       else Φ₂ (.active s)
        | .success => 0 | .failure => 0) := by
  let Φ : StopNode S → Nat := fun x =>
    match x with
    | .active s =>
        if I.phase s = .p1 then Φ₁ (.active s) + C₂ else Φ₂ (.active s)
    | .success => 0
    | .failure => 0
  change NatBellmanSuperSolution step 1 Φ
  refine ⟨rfl, rfl, ?_⟩
  intro s
  cases hs : I.phase s with
  | p1 =>
      have hself : Φ (.active s) = Φ₁ (.active s) + C₂ := by
        simp [Φ, hs]
      rw [hself]
      simp only [Nat.one_mul]
      have hchild :
          ∀ e : Fin n,
            Φ (step s e) ≤
              (match step s e with
               | .active t =>
                   if I.phase t = .p1 then Φ₁ (.active t) else 0
               | .success => 0
               | .failure => 0) + C₂ := by
        intro e
        cases hstep : step s e with
        | active t =>
            cases ht : I.phase t with
            | p1 =>
                simp [Φ, hstep, ht]
            | p2 =>
                have hE : E₂ t := henter s e t hs hstep ht
                have hbound := hC₂ t hE
                simpa [Φ, hstep, ht] using hbound
        | success =>
            simp [Φ, hstep]
        | failure =>
            simp [Φ, hstep]
      have hsum :
          (List.ofFn (fun e : Fin n => Φ (step s e))).sum ≤
            (List.ofFn (fun e : Fin n =>
              (match step s e with
               | .active t =>
                   if I.phase t = .p1 then Φ₁ (.active t) else 0
               | .success => 0
               | .failure => 0) + C₂)).sum :=
        ofFn_sum_le _ _ hchild
      calc
        n + (List.ofFn (fun e : Fin n => Φ (step s e))).sum ≤
            n + (List.ofFn (fun e : Fin n =>
              (match step s e with
               | .active t =>
                   if I.phase t = .p1 then Φ₁ (.active t) else 0
               | .success => 0
               | .failure => 0) + C₂)).sum :=
          Nat.add_le_add_left hsum n
        _ =
            (n + (List.ofFn (fun e : Fin n => match step s e with
              | .active t =>
                  if I.phase t = .p1 then Φ₁ (.active t) else 0
              | .success => 0
              | .failure => 0)).sum) + n * C₂ := by
          rw [ofFn_sum_add, ofFn_sum_const, ← Nat.add_assoc]
        _ ≤ n * Φ₁ (.active s) + n * C₂ :=
          Nat.add_le_add_right (h₁ s hs) (n * C₂)
        _ = n * (Φ₁ (.active s) + C₂) :=
          (Nat.mul_add n (Φ₁ (.active s)) C₂).symm
  | p2 =>
      have hself : Φ (.active s) = Φ₂ (.active s) := by
        simp [Φ, hs]
      rw [hself]
      simp only [Nat.one_mul]
      have hchild :
          ∀ e : Fin n,
            Φ (step s e) =
              match step s e with
              | .active t => Φ₂ (.active t)
              | .success => 0
              | .failure => 0 := by
        intro e
        cases hstep : step s e with
        | active t =>
            have ht : I.phase t = .p2 := I.noBack s e t hs hstep
            simpa [Φ, hstep, ht]
        | success =>
            simp [Φ, hstep]
        | failure =>
            simp [Φ, hstep]
      have hsum := ofFn_sum_eq
        (fun e : Fin n => Φ (step s e))
        (fun e : Fin n => match step s e with
          | .active t => Φ₂ (.active t)
          | .success => 0
          | .failure => 0)
        hchild
      calc
        n + (List.ofFn (fun e : Fin n => Φ (step s e))).sum =
            n + (List.ofFn (fun e : Fin n => match step s e with
              | .active t => Φ₂ (.active t)
              | .success => 0
              | .failure => 0)).sum :=
          congrArg (fun z => n + z) hsum
        _ ≤ n * Φ₂ (.active s) := h₂ s hs


/-- Closure of a predicate along the finite-tree reachability relation. -/
private theorem reach_closed
    {S : Type} {n : Nat}
    {step : S → Fin n → StopNode S}
    (P : StopNode S → Prop)
    (hstep : ∀ {y : StopNode S}, P y → ∀ e : Fin n,
      P (stepNode step y e))
    {x y : StopNode S}
    (hx : P x)
    (hxy : BellmanGeometricTailReachable.Reach step x y) :
    P y := by
  induction hxy with
  | refl =>
      exact hx
  | next hxy edge ih =>
      exact hstep ih edge


/-- Reachable-state version of the composed geometric tail.  This retains the
interface: the caller may supply an arbitrary active-state invariant
`Reach`; closure lifts it to `BellmanGeometricTailReachable.Reach`. -/
theorem phase_compose_tail
    {S : Type} {n : Nat} (step : S → Fin n → StopNode S)
    (Φ : StopNode S → Nat) (Reach : S → Prop) (x : S) (B r : Nat)
    (hB : 0 < B) (hsuper : NatBellmanSuperSolution step 1 Φ)
    (hx : Reach x)
    (hclosed : ∀ s, Reach s → ∀ e t, step s e = .active t → Reach t)
    (hbound : ∀ s, Reach s → Φ (.active s) ≤ B) :
    2 ^ r * activeCount step (.active x) (2 * B * r) ≤
      n ^ (2 * B * r) := by
  cases n with
  | zero =>
      cases r with
      | zero =>
          simp [activeCount, treeWeight, activeWeight]
      | succ r =>
          have hTpos : 0 < 2 * B * Nat.succ r :=
            Nat.mul_pos
              (Nat.mul_pos (Nat.succ_pos 1) hB)
              (Nat.succ_pos r)
          obtain ⟨T, hT⟩ :=
            Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hTpos)
          rw [hT]
          simp [activeCount, treeWeight, activeWeight]
  | succ n =>
      let Good : StopNode S → Prop := fun y =>
        match y with
        | .active s => Reach s
        | .success => True
        | .failure => True
      have hGoodStep :
          ∀ {y : StopNode S}, Good y →
            ∀ e : Fin (Nat.succ n), Good (stepNode step y e) := by
        intro y hy e
        cases y with
        | active s =>
            change Reach s at hy
            cases hstep : step s e with
            | active t =>
                have ht : Reach t := hclosed s hy e t hstep
                simpa [Good, stepNode, hstep] using ht
            | success =>
                simp [Good, stepNode, hstep]
            | failure =>
                simp [Good, stepNode, hstep]
        | success =>
            simp [Good, stepNode]
        | failure =>
            simp [Good, stepNode]
      have hGoodStart : Good (.active x) := by
        change Reach x
        exact hx
      have hGoodReach :
          ∀ y : StopNode S,
            BellmanGeometricTailReachable.Reach step (.active x) y → Good y := by
        intro y hy
        exact reach_closed Good hGoodStep hGoodStart hy
      have htreeBound :
          ∀ y : StopNode S,
            BellmanGeometricTailReachable.Reach step (.active x) y → Φ y ≤ B := by
        intro y hy
        have hGood := hGoodReach y hy
        cases y with
        | active s =>
            change Reach s at hGood
            exact hbound s hGood
        | success =>
            rw [hsuper.1]
            exact Nat.zero_le B
        | failure =>
            rw [hsuper.2.1]
            exact Nat.zero_le B
      have htail :=
        BellmanGeometricTailReachable.geometric_tail_reach
          (B := B) step Φ hsuper (.active x) htreeBound
            (Nat.succ_pos n) r
      have hhor : r * (2 * B) = 2 * B * r := Nat.mul_comm _ _
      simpa only [hhor] using htail


/-- Prepend one phase to an already-composed residual supersolution.


Use `Ψ` as the result of a previous `phase_compose_bellman` application.
Applying this corollary repeatedly is the four-phase construction without a
separate four-way finite-sum proof. -/
theorem compose_twice
    {S : Type} {n : Nat} (step : S → Fin n → StopNode S)
    (I : MonotonePhaseIndicator step)
    (Φ₁ Ψ : StopNode S → Nat) (C : Nat) (E : S → Prop)
    (h₁ : ∀ s, I.phase s = .p1 →
      n + (List.ofFn (fun e : Fin n => match step s e with
        | .active t => if I.phase t = .p1 then Φ₁ (.active t) else 0
        | .success => 0 | .failure => 0)).sum ≤ n * Φ₁ (.active s))
    (hΨ : NatBellmanSuperSolution step 1 Ψ)
    (henter : ∀ s e t, I.phase s = .p1 → step s e = .active t →
      I.phase t = .p2 → E t)
    (hC : ∀ t, E t → Ψ (.active t) ≤ C) :
    NatBellmanSuperSolution step 1
      (fun x => match x with
        | .active s => if I.phase s = .p1 then Φ₁ (.active s) + C
                       else Ψ (.active s)
        | .success => 0 | .failure => 0) := by
  have h₂ : ∀ s, I.phase s = .p2 →
      n + (List.ofFn (fun e : Fin n => match step s e with
        | .active t => Ψ (.active t)
        | .success => 0 | .failure => 0)).sum ≤ n * Ψ (.active s) := by
    intro s _
    have hbell :
        n + (List.ofFn (fun e : Fin n => Ψ (step s e))).sum ≤
          n * Ψ (.active s) := by
      simpa only [Nat.one_mul] using hΨ.2.2 s
    have hchild :
        ∀ e : Fin n,
          Ψ (step s e) =
            match step s e with
            | .active t => Ψ (.active t)
            | .success => 0
            | .failure => 0 := by
      intro e
      cases hstep : step s e with
      | active t =>
          simp [hstep]
      | success =>
          simpa [hstep] using hΨ.1
      | failure =>
          simpa [hstep] using hΨ.2.1
    have hsum := ofFn_sum_eq
      (fun e : Fin n => Ψ (step s e))
      (fun e : Fin n => match step s e with
        | .active t => Ψ (.active t)
        | .success => 0
        | .failure => 0)
      hchild
    rw [← hsum]
    exact hbell
  exact phase_compose_bellman step I Φ₁ Ψ C E h₁ h₂ henter hC


end PhaseComposition


#print axioms PhaseComposition.phase_compose_bellman
#print axioms PhaseComposition.phase_compose_tail
#print axioms PhaseComposition.compose_twice
