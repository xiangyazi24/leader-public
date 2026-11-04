import Leader.Wu.ShortGap.ChoiceStopping


namespace ShortGapIncidenceReward


set_option autoImplicit false


open PeriodHIncidenceChoice FiniteUniformStoppingTree


/-!
# Multiplicity reward for bare incidence resolution


The cyclic subharmonicity theorem requires `1 < m` and `1 < n`.
The logical singleton must be excluded: its only gap has the same root at
both ends, and resolving that root changes its all-Race reward from one to
zero. No cyclic-order assumption on `Placement` is otherwise required.


`raceDrainStep` in `ShortGapChoiceStopping` discards the final configuration
at its payload-free `.success` constructor. The reward wrapper below instead
retains configurations, with every frozen configuration an absorbing state.
Its outer `.active` constructor is a payload container, not a claim that a
frozen configuration still pays active-interaction cost. Do not use this
wrapper as the active-cost kernel.


At a finite horizon, unresolved leaves can still carry reward. The final
candidate-count corollary therefore has an explicit zero-unresolved-mass
hypothesis; the preceding residual bound is unconditional.


These proofs use the imported bare kernel, not the literal capture adapter.
No Lean compiler was run while preparing this file.
-/


/-! ## Rewards and masked candidate counts -/


def wOut : Choice → Nat
  | .out1 => 2
  | .race => 1
  | .in0 => 0


def wIn : Choice → Nat
  | .in0 => 2
  | .race => 1
  | .out1 => 0


def maskCount {m : Nat} (short : Fin m → Bool) : Nat :=
  (List.ofFn (fun g : Fin m => if short g then 1 else 0)).sum


def gapReward {m : Nat} (ring : DirectedRing m)
    (short : Fin m → Bool) (C : Configuration m) (g : Fin m) : Nat :=
  if short g then wOut (C g) * wIn (C (ring.rightNeighbor g)) else 0


def W {m : Nat} (ring : DirectedRing m)
    (short : Fin m → Bool) (C : Configuration m) : Nat :=
  (List.ofFn (fun g : Fin m => gapReward ring short C g)).sum


local instance candidate10Decidable {m : Nat} (ring : DirectedRing m)
    (C : Configuration m) (g : Fin m) : Decidable (Candidate10 ring C g) := by
  unfold Candidate10
  infer_instance


def candidateCount {m : Nat} (ring : DirectedRing m)
    (short : Fin m → Bool) (C : Configuration m) : Nat :=
  (List.ofFn (fun g : Fin m =>
    if short g then (if Candidate10 ring C g then 1 else 0) else 0)).sum


theorem maskCount_all_true (m : Nat) :
    maskCount (fun _ : Fin m => true) = m := by
  simp [maskCount, ofFn_sum_const]


/-! ## Elementary finite-sum and physical-port facts -/


private def edgeHit {n : Nat} (a e : Fin n) : Nat :=
  if e = a then 1 else 0


private theorem edgeHit_sum : ∀ (n : Nat) (a : Fin n),
    (List.ofFn (fun e : Fin n => edgeHit a e)).sum = 1 := by
  intro n
  induction n with
  | zero =>
      intro a
      exact Fin.elim0 a
  | succ n ih =>
      intro a
      refine Fin.cases ?_ (fun k => ?_) a
      · have hhead : edgeHit (0 : Fin (n + 1)) 0 = 1 := by
          simp [edgeHit]
        have htail :
            (List.ofFn (fun i : Fin n =>
              edgeHit (0 : Fin (n + 1)) i.succ)).sum = 0 := by
          calc
            _ = (List.ofFn (fun _ : Fin n => 0)).sum := by
              apply ofFn_sum_eq
              intro i
              have hne : i.succ ≠ (0 : Fin (n + 1)) := by
                intro h
                have hv := congrArg Fin.val h
                change i.val + 1 = 0 at hv
                omega
              simp only [edgeHit, if_neg hne]
            _ = 0 := by
              rw [ofFn_sum_const, Nat.mul_zero]
        rw [List.ofFn_succ, List.sum_cons, hhead, htail]
      · have hne : (0 : Fin (n + 1)) ≠ k.succ := by
          intro h
          have hv := congrArg Fin.val h
          change 0 = k.val + 1 at hv
          omega
        have hhead : edgeHit k.succ (0 : Fin (n + 1)) = 0 := by
          simp only [edgeHit, if_neg hne]
        have htail :
            (List.ofFn (fun i : Fin n => edgeHit k.succ i.succ)).sum =
              (List.ofFn (fun i : Fin n => edgeHit k i)).sum := by
          apply ofFn_sum_eq
          intro i
          have heq : i.succ = k.succ ↔ i = k := by
            constructor
            · intro h
              apply Fin.ext
              have hv := congrArg Fin.val h
              change i.val + 1 = k.val + 1 at hv
              omega
            · intro h
              exact congrArg Fin.succ h
          simp only [edgeHit, heq]
        rw [List.ofFn_succ, List.sum_cons, hhead, htail, Nat.zero_add]
        exact ih k


private theorem swap_ofFn_sums :
    ∀ (p q : Nat) (f : Fin p → Fin q → Nat),
      (List.ofFn (fun i : Fin p =>
        (List.ofFn (fun j : Fin q => f i j)).sum)).sum =
      (List.ofFn (fun j : Fin q =>
        (List.ofFn (fun i : Fin p => f i j)).sum)).sum := by
  intro p
  induction p with
  | zero =>
      intro q f
      simp [ofFn_sum_const]
  | succ p ih =>
      intro q f
      simp only [List.ofFn_succ, List.sum_cons]
      rw [ih q (fun i j => f i.succ j), ofFn_sum_add]


private theorem left_right_id {n : Nat} (ring : DirectedRing n)
    (i : Fin n) : ring.leftNeighbor (ring.rightNeighbor i) = i := by
  have hn : 0 < n := ring.hn
  have hi_lt : i.val < n := i.isLt
  apply Fin.ext
  simp only [DirectedRing.leftNeighbor, DirectedRing.rightNeighbor]
  by_cases hi : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hi]
    have heq : i.val + 1 + n - 1 = n + i.val := by omega
    rw [heq, add_self_mod, Nat.mod_eq_of_lt i.isLt]
  · have hieq : i.val + 1 = n := by omega
    rw [hieq, Nat.mod_self]
    have hlt : n - 1 < n := by omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    omega


private theorem right_left_id {n : Nat} (ring : DirectedRing n)
    (i : Fin n) : ring.rightNeighbor (ring.leftNeighbor i) = i := by
  have hn : 0 < n := ring.hn
  have hi_lt : i.val < n := i.isLt
  apply Fin.ext
  simp only [DirectedRing.rightNeighbor, DirectedRing.leftNeighbor]
  by_cases hi : i.val = 0
  · rw [hi]
    have hlt : n - 1 < n := by omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hlt]
    have hs : n - 1 + 1 = n := by omega
    rw [hs, Nat.mod_self]
  · have heq : i.val + n - 1 = n + (i.val - 1) := by omega
    rw [heq, add_self_mod, Nat.mod_eq_of_lt (by omega : i.val - 1 < n)]
    have hs : i.val - 1 + 1 = i.val := by omega
    rw [hs, Nat.mod_eq_of_lt i.isLt]


private def incomingEdge {n m : Nat} (P : Placement n m)
    (i : Fin m) : Fin n :=
  P.physicalRing.leftNeighbor (P.root i)


private theorem root_eq_right_iff {n m : Nat} (P : Placement n m)
    (i : Fin m) (e : Fin n) :
    P.root i = P.physicalRing.rightNeighbor e ↔ e = incomingEdge P i := by
  constructor
  · intro h
    have hh := congrArg P.physicalRing.leftNeighbor h
    rw [left_right_id] at hh
    exact hh.symm
  · intro h
    rw [h]
    exact (right_left_id P.physicalRing (P.root i)).symm


private theorem incidenceStep_race_eq {n m : Nat} (P : Placement n m)
    (C : Configuration m) (i : Fin m) (e : Fin n) (hr : C i = .race) :
    incidenceStep P C e i =
      (if e = P.root i then .out1
       else if e = incomingEdge P i then .in0 else .race) := by
  have hnot : ¬ (C i ≠ .race) := fun hne => hne hr
  change
    (if C i ≠ .race then C i
     else if P.root i = e then Choice.out1
     else if P.root i = P.physicalRing.rightNeighbor e then Choice.in0
     else Choice.race) =
    (if e = P.root i then Choice.out1
     else if e = incomingEdge P i then Choice.in0 else Choice.race)
  simp only [if_neg hnot]
  by_cases hout : P.root i = e
  · have hout' : e = P.root i := hout.symm
    simp only [if_pos hout, if_pos hout']
  · have hout' : e ≠ P.root i := fun h => hout h.symm
    simp only [if_neg hout, if_neg hout', root_eq_right_iff P i e]


/-- Exact one-root balances, with no subtraction in the natural numbers. -/
private theorem race_step_balances {n m : Nat} (P : Placement n m)
    (hn : 1 < n) (C : Configuration m) (i : Fin m) (e : Fin n)
    (hr : C i = .race) :
    (wOut (incidenceStep P C e i) + edgeHit (incomingEdge P i) e =
      1 + edgeHit (P.root i) e) ∧
    (wIn (incidenceStep P C e i) + edgeHit (P.root i) e =
      1 + edgeHit (incomingEdge P i) e) := by
  have hports : P.root i ≠ incomingEdge P i :=
    Placement.root_ne_incomingEdge P hn i
  simp only [incidenceStep_race_eq P C i e hr]
  by_cases hout : e = P.root i
  · have hin : e ≠ incomingEdge P i := by
      intro heq
      exact hports (hout.symm.trans heq)
    simp only [if_pos hout, if_neg hin, wOut, wIn, edgeHit] <;> decide
  · by_cases hin : e = incomingEdge P i
    · simp only [if_neg hout, if_pos hin, wOut, wIn, edgeHit] <;> decide
    · simp only [if_neg hout, if_neg hin, wOut, wIn, edgeHit] <;> decide


/-- Each individual endpoint weight is harmonic under the uniform scheduler. -/
theorem incidence_weight_sums {n m : Nat} (P : Placement n m)
    (hn : 1 < n) (C : Configuration m) (i : Fin m) :
    ((List.ofFn (fun e : Fin n => wOut (incidenceStep P C e i))).sum =
      n * wOut (C i)) ∧
    ((List.ofFn (fun e : Fin n => wIn (incidenceStep P C e i))).sum =
      n * wIn (C i)) := by
  cases hc : C i with
  | race =>
      have ho := ofFn_sum_eq
        (fun e : Fin n =>
          wOut (incidenceStep P C e i) + edgeHit (incomingEdge P i) e)
        (fun e : Fin n => 1 + edgeHit (P.root i) e)
        (fun e => (race_step_balances P hn C i e hc).1)
      have hi := ofFn_sum_eq
        (fun e : Fin n =>
          wIn (incidenceStep P C e i) + edgeHit (P.root i) e)
        (fun e : Fin n => 1 + edgeHit (incomingEdge P i) e)
        (fun e => (race_step_balances P hn C i e hc).2)
      simp only [ofFn_sum_add, edgeHit_sum, ofFn_sum_const, Nat.mul_one] at ho hi
      have hso :
          (List.ofFn (fun e : Fin n => wOut (incidenceStep P C e i))).sum = n := by
        omega
      have hsi :
          (List.ofFn (fun e : Fin n => wIn (incidenceStep P C e i))).sum = n := by
        omega
      constructor
      · simpa only [hc, wOut, Nat.mul_one] using hso
      · simpa only [hc, wIn, Nat.mul_one] using hsi
  | in0 =>
      simp [incidenceStep, hc, wOut, wIn, ofFn_sum_const]
  | out1 =>
      simp [incidenceStep, hc, wOut, wIn, ofFn_sum_const]


/-! ## The two-root inequality, including shared physical edges -/


private theorem weights_product_bound (x y : Choice)
    (hout : ¬ (x = .out1 ∧ y = .out1))
    (hin : ¬ (x = .in0 ∧ y = .in0)) :
    wOut x + wIn y ≤ wOut x * wIn y + 1 := by
  cases x <;> cases y <;> simp_all [wOut, wIn]


/-- Distinct Race roots cannot both become initiators or both become responders
in one physical interaction. Both possible shared-edge orientations are allowed. -/
private theorem race_pair_pointwise {n m : Nat} (P : Placement n m)
    (C : Configuration m) (i j : Fin m) (hij : i ≠ j)
    (hi : C i = .race) (hj : C j = .race) (e : Fin n) :
    wOut (incidenceStep P C e i) + wIn (incidenceStep P C e j) ≤
      wOut (incidenceStep P C e i) * wIn (incidenceStep P C e j) + 1 := by
  have hnoOut : ¬ (incidenceStep P C e i = .out1 ∧
      incidenceStep P C e j = .out1) := by
    rintro ⟨hio, hjo⟩
    have hie : P.root i = e := by grind [incidenceStep]
    have hje : P.root j = e := by grind [incidenceStep]
    exact hij (P.root_injective (hie.trans hje.symm))
  have hnoIn : ¬ (incidenceStep P C e i = .in0 ∧
      incidenceStep P C e j = .in0) := by
    rintro ⟨hii, hji⟩
    have hie : P.root i = P.physicalRing.rightNeighbor e := by
      grind [incidenceStep]
    have hje : P.root j = P.physicalRing.rightNeighbor e := by
      grind [incidenceStep]
    exact hij (P.root_injective (hie.trans hje.symm))
  exact weights_product_bound
    (incidenceStep P C e i) (incidenceStep P C e j) hnoOut hnoIn


/-- The unmasked contribution of any two distinct roots is subharmonic. -/
theorem gap_term_subharmonic {n m : Nat} (P : Placement n m)
    (hn : 1 < n) (C : Configuration m) (i j : Fin m) (hij : i ≠ j) :
    n * (wOut (C i) * wIn (C j)) ≤
      (List.ofFn (fun e : Fin n =>
        wOut (incidenceStep P C e i) * wIn (incidenceStep P C e j))).sum := by
  cases hi : C i with
  | in0 =>
      simp [hi, wOut]
  | out1 =>
      have hfixed (e : Fin n) : wOut (incidenceStep P C e i) = 2 := by
        simp [incidenceStep, hi, wOut]
      have hmean := (incidence_weight_sums P hn C j).2
      apply Nat.le_of_eq
      calc
        n * (wOut Choice.out1 * wIn (C j)) = 2 * (n * wIn (C j)) := by
          change n * (2 * wIn (C j)) = 2 * (n * wIn (C j))
          ac_rfl
        _ = 2 * (List.ofFn (fun e : Fin n =>
            wIn (incidenceStep P C e j))).sum := by rw [hmean]
        _ = (List.ofFn (fun e : Fin n =>
            2 * wIn (incidenceStep P C e j))).sum :=
          (ofFn_sum_mul_left 2 _).symm
        _ = (List.ofFn (fun e : Fin n =>
            wOut (incidenceStep P C e i) *
              wIn (incidenceStep P C e j))).sum := by
          apply ofFn_sum_eq
          intro e
          rw [hfixed e]
  | race =>
      cases hj : C j with
      | out1 =>
          simp [hj, wIn]
      | in0 =>
          have hfixed (e : Fin n) : wIn (incidenceStep P C e j) = 2 := by
            simp [incidenceStep, hj, wIn]
          have hmean := (incidence_weight_sums P hn C i).1
          apply Nat.le_of_eq
          calc
            n * (wOut Choice.race * wIn Choice.in0) =
                2 * (n * wOut (C i)) := by
              simpa only [hi, wOut, wIn, Nat.one_mul, Nat.mul_one] using
                (Nat.mul_comm n 2)
            _ = 2 * (List.ofFn (fun e : Fin n =>
                wOut (incidenceStep P C e i))).sum := by rw [hmean]
            _ = (List.ofFn (fun e : Fin n =>
                2 * wOut (incidenceStep P C e i))).sum :=
              (ofFn_sum_mul_left 2 _).symm
            _ = (List.ofFn (fun e : Fin n =>
                wOut (incidenceStep P C e i) *
                  wIn (incidenceStep P C e j))).sum := by
              apply ofFn_sum_eq
              intro e
              rw [hfixed e]
              exact Nat.mul_comm _ _
      | race =>
          have ho :
              (List.ofFn (fun e : Fin n => wOut (incidenceStep P C e i))).sum = n := by
            simpa only [hi, wOut, Nat.mul_one] using
              (incidence_weight_sums P hn C i).1
          have ht :
              (List.ofFn (fun e : Fin n => wIn (incidenceStep P C e j))).sum = n := by
            simpa only [hj, wIn, Nat.mul_one] using
              (incidence_weight_sums P hn C j).2
          have hs := ofFn_sum_le
            (fun e : Fin n =>
              wOut (incidenceStep P C e i) + wIn (incidenceStep P C e j))
            (fun e : Fin n =>
              wOut (incidenceStep P C e i) * wIn (incidenceStep P C e j) + 1)
            (fun e => race_pair_pointwise P C i j hij hi hj e)
          simp only [ofFn_sum_add, ofFn_sum_const, ho, ht, Nat.mul_one] at hs
          have hbound : n ≤
              (List.ofFn (fun e : Fin n =>
                wOut (incidenceStep P C e i) *
                  wIn (incidenceStep P C e j))).sum := by
            omega
          simpa only [hi, hj, wOut, wIn, Nat.mul_one] using hbound


/-- Sum the per-gap inequalities, then interchange the two finite sums. -/
theorem reward_subharmonic {n m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (hn : 1 < n) (hm : 1 < m)
    (short : Fin m → Bool) (C : Configuration m) :
    n * W ring short C ≤
      (List.ofFn (fun e : Fin n => W ring short (incidenceStep P C e))).sum := by
  calc
    n * W ring short C =
        (List.ofFn (fun g : Fin m => n * gapReward ring short C g)).sum :=
      (ofFn_sum_mul_left n _).symm
    _ ≤ (List.ofFn (fun g : Fin m =>
        (List.ofFn (fun e : Fin n =>
          gapReward ring short (incidenceStep P C e) g)).sum)).sum := by
      apply ofFn_sum_le
      intro g
      have hneq : g ≠ ring.rightNeighbor g := by
        intro heq
        exact (rightNeighbor_ne ring hm g) heq.symm
      have hgap := gap_term_subharmonic P hn C g (ring.rightNeighbor g) hneq
      cases hs : short g with
      | false => simp [gapReward, hs, ofFn_sum_const]
      | true => simpa [gapReward, hs] using hgap
    _ = (List.ofFn (fun e : Fin n =>
        (List.ofFn (fun g : Fin m =>
          gapReward ring short (incidenceStep P C e) g)).sum)).sum :=
      swap_ofFn_sums m n
        (fun g e => gapReward ring short (incidenceStep P C e) g)
    _ = (List.ofFn (fun e : Fin n =>
        W ring short (incidenceStep P C e))).sum := rfl


/-! ## Initial, frozen, and bounded rewards -/


theorem reward_start_masked {m : Nat} (ring : DirectedRing m)
    (short : Fin m → Bool) :
    W ring short (fun _ => .race) = maskCount short := by
  unfold W maskCount
  apply ofFn_sum_eq
  intro g
  cases hs : short g <;> simp [gapReward, hs, wOut, wIn]


theorem reward_start {m : Nat} (ring : DirectedRing m) :
    W ring (fun _ => true) (fun _ => .race) = m := by
  rw [reward_start_masked, maskCount_all_true]


theorem reward_frozen {m : Nat} (ring : DirectedRing m)
    (short : Fin m → Bool) (C : Configuration m) (hf : Frozen C) :
    W ring short C = 4 * candidateCount ring short C := by
  calc
    W ring short C =
        (List.ofFn (fun g : Fin m =>
          4 * (if short g then (if Candidate10 ring C g then 1 else 0)
            else 0))).sum := by
      apply ofFn_sum_eq
      intro g
      have hi : C g ≠ .race := hf g
      have hj : C (ring.rightNeighbor g) ≠ .race := hf (ring.rightNeighbor g)
      cases hs : short g <;>
        cases hc : C g <;> cases hd : C (ring.rightNeighbor g) <;>
        simp_all [gapReward, Candidate10, wOut, wIn]
    _ = 4 * candidateCount ring short C := ofFn_sum_mul_left 4 _


theorem reward_le_four_maskCount {m : Nat} (ring : DirectedRing m)
    (short : Fin m → Bool) (C : Configuration m) :
    W ring short C ≤ 4 * maskCount short := by
  calc
    W ring short C ≤
        (List.ofFn (fun g : Fin m => 4 * (if short g then 1 else 0))).sum := by
      apply ofFn_sum_le
      intro g
      cases hs : short g <;>
        cases hc : C g <;> cases hd : C (ring.rightNeighbor g) <;>
        simp [gapReward, hs, hc, hd, wOut, wIn]
    _ = 4 * maskCount short := ofFn_sum_mul_left 4 _


/-! ## Generic tree lifting for a subharmonic reward -/


/-- Terminal rewards need not vanish: terminal nodes are absorbing. -/
theorem treeWeight_ge_of_subharmonic {S : Type} {n : Nat}
    (step : S → Fin n → StopNode S) (weight : StopNode S → Nat)
    (hstep : ∀ s,
      n * weight (.active s) ≤
        (List.ofFn (fun e : Fin n => weight (step s e))).sum) :
    ∀ x T, n ^ T * weight x ≤ treeWeight step weight x T := by
  intro x T
  induction T generalizing x with
  | zero => simp [treeWeight]
  | succ T ih =>
      have hnode : n * weight x ≤
          (List.ofFn (fun e : Fin n => weight (stepNode step x e))).sum := by
        cases x with
        | active s => exact hstep s
        | success =>
            simpa only [stepNode, ofFn_sum_const] using
              (Nat.le_refl (n * weight .success))
        | failure =>
            simpa only [stepNode, ofFn_sum_const] using
              (Nat.le_refl (n * weight .failure))
      calc
        n ^ (T + 1) * weight x = n ^ T * (n * weight x) := by
          rw [Nat.pow_succ, Nat.mul_assoc]
        _ ≤ n ^ T *
            (List.ofFn (fun e : Fin n => weight (stepNode step x e))).sum :=
          Nat.mul_le_mul_left (n ^ T) hnode
        _ = (List.ofFn (fun e : Fin n =>
            n ^ T * weight (stepNode step x e))).sum :=
          (ofFn_sum_mul_left (n ^ T) _).symm
        _ ≤ (List.ofFn (fun e : Fin n =>
            treeWeight step weight (stepNode step x e) T)).sum :=
          ofFn_sum_le _ _ (fun e => ih (stepNode step x e))
        _ = treeWeight step weight x (T + 1) := rfl


/-! ## Configuration-retaining absorbing race drain -/


/-- Frozen configurations stutter, retaining their terminal candidate reward.
The payload-free terminal constructors of `StopNode` are not reached here. -/
def rewardDrainStep {n m : Nat} (P : Placement n m)
    (C : Configuration m) (e : Fin n) : StopNode (Configuration m) :=
  .active (incidenceStep P C e)


theorem incidenceStep_eq_self_of_frozen {n m : Nat} (P : Placement n m)
    (C : Configuration m) (hf : Frozen C) (e : Fin n) :
    incidenceStep P C e = C := by
  funext i
  simp [incidenceStep, hf i]


theorem rewardDrainStep_of_frozen {n m : Nat} (P : Placement n m)
    (C : Configuration m) (hf : Frozen C) (e : Fin n) :
    rewardDrainStep P C e = .active C := by
  exact congrArg StopNode.active (incidenceStep_eq_self_of_frozen P C hf e)


def nodeReward {m : Nat} (ring : DirectedRing m) (short : Fin m → Bool) :
    StopNode (Configuration m) → Nat
  | .active C => W ring short C
  | .success => 0
  | .failure => 0


def nodeCandidateCount {m : Nat} (ring : DirectedRing m)
    (short : Fin m → Bool) : StopNode (Configuration m) → Nat
  | .active C => candidateCount ring short C
  | .success => 0
  | .failure => 0


/-- Indicator of a genuinely unresolved payload, not of the outer constructor. -/
noncomputable def nodeUnresolved {m : Nat}
    (x : StopNode (Configuration m)) : Nat := by
  classical
  exact match x with
    | .active C => if Frozen C then 0 else 1
    | .success => 0
    | .failure => 0


theorem nodeUnresolved_of_frozen {m : Nat}
    (C : Configuration m) (hf : Frozen C) :
    nodeUnresolved (.active C) = 0 := by
  classical
  simp [nodeUnresolved, hf]


theorem reward_tree_ge_start {n m : Nat} (ring : DirectedRing m)
    (P : Placement n m) (hn : 1 < n) (hm : 1 < m)
    (short : Fin m → Bool) (C : Configuration m) (T : Nat) :
    n ^ T * W ring short C ≤
      treeWeight (rewardDrainStep P) (nodeReward ring short) (.active C) T := by
  have hstep : ∀ D : Configuration m,
      n * nodeReward ring short (.active D) ≤
        (List.ofFn (fun e : Fin n =>
          nodeReward ring short (rewardDrainStep P D e))).sum := by
    intro D
    change n * W ring short D ≤
      (List.ofFn (fun e : Fin n =>
        W ring short (incidenceStep P D e))).sum
    exact reward_subharmonic ring P hn hm short D
  exact @treeWeight_ge_of_subharmonic (Configuration m) n
    (rewardDrainStep P) (nodeReward ring short) hstep (.active C) T


/-- The masked finite-horizon reward inequality. This includes unresolved credit. -/
theorem expected_candidates_ge_quarter_masked {n m : Nat}
    (ring : DirectedRing m) (P : Placement n m) (hn : 1 < n) (hm : 1 < m)
    (short : Fin m → Bool) (T : Nat) :
    n ^ T * maskCount short ≤
      treeWeight (rewardDrainStep P) (nodeReward ring short)
        (.active (fun _ => .race)) T := by
  have h := reward_tree_ge_start ring P hn hm short (fun _ => .race) T
  rw [reward_start_masked] at h
  exact h


/-- All gaps counted: the depth-T reward sum is at least `n^T*m`. -/
theorem expected_candidates_ge_quarter {n m : Nat}
    (ring : DirectedRing m) (P : Placement n m) (hn : 1 < n) (hm : 1 < m)
    (T : Nat) :
    n ^ T * m ≤
      treeWeight (rewardDrainStep P) (nodeReward ring (fun _ => true))
        (.active (fun _ => .race)) T := by
  have h := expected_candidates_ge_quarter_masked
    ring P hn hm (fun _ => true) T
  rw [maskCount_all_true] at h
  exact h


/-! ## Actual candidate counts, with the unfinished-leaf correction -/


private theorem nodeReward_le_candidates_add_unresolved {m : Nat}
    (ring : DirectedRing m) (short : Fin m → Bool)
    (x : StopNode (Configuration m)) :
    nodeReward ring short x ≤
      4 * nodeCandidateCount ring short x +
        (4 * maskCount short) * nodeUnresolved x := by
  classical
  cases x with
  | active C =>
      by_cases hf : Frozen C
      · simp only [nodeReward, nodeCandidateCount, nodeUnresolved, if_pos hf,
          Nat.mul_zero, Nat.add_zero]
        exact Nat.le_of_eq (reward_frozen ring short C hf)
      · have hcap := reward_le_four_maskCount ring short C
        simp only [nodeReward, nodeCandidateCount, nodeUnresolved, if_neg hf,
          Nat.mul_one]
        omega
  | success => simp [nodeReward, nodeCandidateCount, nodeUnresolved]
  | failure => simp [nodeReward, nodeCandidateCount, nodeUnresolved]


/-- A genuine finite-horizon candidate inequality: unresolved words pay an
explicit residual of at most four times the number of masked gaps each. -/
theorem candidates_bound_with_residual {n m : Nat}
    (ring : DirectedRing m) (P : Placement n m) (hn : 1 < n) (hm : 1 < m)
    (short : Fin m → Bool) (T : Nat) :
    n ^ T * maskCount short ≤
      4 * treeWeight (rewardDrainStep P) (nodeCandidateCount ring short)
        (.active (fun _ => .race)) T +
      (4 * maskCount short) *
        treeWeight (rewardDrainStep P) nodeUnresolved
          (.active (fun _ => .race)) T := by
  have hlower := expected_candidates_ge_quarter_masked ring P hn hm short T
  have hupper := treeWeight_mono
    (rewardDrainStep P)
    (nodeReward ring short)
    (fun x => 4 * nodeCandidateCount ring short x +
      (4 * maskCount short) * nodeUnresolved x)
    (nodeReward_le_candidates_add_unresolved ring short)
    (.active (fun _ => .race)) T
  simp only [treeWeight_add, treeWeight_mul_left] at hupper
  exact Nat.le_trans hlower hupper


/-- Full-resolution specialization, written without division.
No finite deterministic horizon is asserted to resolve every scheduler word. -/
theorem candidates_ge_quarter_of_full_resolution {n m : Nat}
    (ring : DirectedRing m) (P : Placement n m) (hn : 1 < n) (hm : 1 < m)
    (short : Fin m → Bool) (T : Nat)
    (hresolved : treeWeight (rewardDrainStep P) nodeUnresolved
      (.active (fun _ => .race)) T = 0) :
    n ^ T * maskCount short ≤
      4 * treeWeight (rewardDrainStep P) (nodeCandidateCount ring short)
        (.active (fun _ => .race)) T := by
  have h := candidates_bound_with_residual ring P hn hm short T
  simpa only [hresolved, Nat.mul_zero, Nat.add_zero] using h


/-- All-gap form: at a fully resolved tree the candidate numerator is at least
one quarter of `n^T*m`, with multiplication clearing the denominator. -/
theorem expected_candidates_ge_quarter_frozen {n m : Nat}
    (ring : DirectedRing m) (P : Placement n m) (hn : 1 < n) (hm : 1 < m)
    (T : Nat)
    (hresolved : treeWeight (rewardDrainStep P) nodeUnresolved
      (.active (fun _ => .race)) T = 0) :
    n ^ T * m ≤
      4 * treeWeight (rewardDrainStep P)
        (nodeCandidateCount ring (fun _ => true))
        (.active (fun _ => .race)) T := by
  have h := candidates_ge_quarter_of_full_resolution
    ring P hn hm (fun _ => true) T hresolved
  rw [maskCount_all_true] at h
  exact h


#print axioms gap_term_subharmonic
#print axioms reward_subharmonic
#print axioms reward_start_masked
#print axioms reward_start
#print axioms reward_frozen
#print axioms treeWeight_ge_of_subharmonic
#print axioms incidenceStep_eq_self_of_frozen
#print axioms rewardDrainStep_of_frozen
#print axioms nodeUnresolved_of_frozen
#print axioms reward_tree_ge_start
#print axioms expected_candidates_ge_quarter_masked
#print axioms expected_candidates_ge_quarter
#print axioms candidates_ge_quarter_of_full_resolution
#print axioms expected_candidates_ge_quarter_frozen

end ShortGapIncidenceReward
