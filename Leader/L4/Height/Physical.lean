import Leader.L4.Height.Trial
import Leader.L4.Height.Constants

/-!
# Post-custody physical time bound

This file combines the clock-repair mean, the two quarter-failure trial,
and the restart theorem.  The only probabilistic composition needed below is
proved directly on the finite-horizon `iidHitCost` recurrence.
-/

namespace L4.Height

open Classical

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- The fixed physical trial deadline from the paper. -/
def physicalDeadline (L m : Nat) : Nat :=
  2 ^ 29 * L * m

/-- Twice the physical trial deadline is the advertised logical mean bound. -/
theorem twice_physicalDeadline (L m : Nat) :
    2 * physicalDeadline L m = 2 ^ 30 * L * m := by
  unfold physicalDeadline
  have hp : (2 : Nat) ^ 30 = 2 ^ 29 * 2 := by
    simpa using (Nat.pow_succ 2 29)
  rw [hp]
  ac_rfl

/-- Horizon-wise composition inequality.  If every state in `B` has
truncated mean at most `b` to `C`, then from any state the cost to `C` is at
most the cost to `B` plus `b`.  This statement is stronger than the closed-
intermediate-set form used below. -/
theorem iidHitCost_then_le {α : Type} {N b : Nat}
    (next : α → Fin N → α) (B C : α → Prop)
    (hBC : ∀ y, B y →
      IIDExpectedHittingTimeAtMost next C y b) :
    ∀ t x,
      iidHitCost next C t x ≤
        iidHitCost next B t x + b * N ^ t := by
  intro t
  induction t with
  | zero =>
      intro x
      simp [iidHitCost]
  | succ t ih =>
      intro x
      by_cases hC : C x
      · rw [iidHitCost_of_target next C x hC (t + 1)]
        exact Nat.zero_le _
      · by_cases hB : B x
        · have hbound := hBC x hB (t + 1)
          rw [iidHitCost_of_target next B x hB (t + 1)]
          simpa using hbound
        · simp only [iidHitCost, hC, hB, if_false]
          have hsum :
              (List.ofFn (fun e : Fin N =>
                iidHitCost next C t (next x e))).sum ≤
              (List.ofFn (fun e : Fin N =>
                iidHitCost next B t (next x e) +
                  b * N ^ t)).sum := by
            apply sum_ofFn_le
            intro e
            exact ih (next x e)
          rw [sum_ofFn_add] at hsum
          rw [sum_ofFn_const N (b * N ^ t)] at hsum
          calc
            N ^ (t + 1) +
                (List.ofFn (fun e : Fin N =>
                  iidHitCost next C t (next x e))).sum ≤
              N ^ (t + 1) +
                ((List.ofFn (fun e : Fin N =>
                  iidHitCost next B t (next x e))).sum +
                    N * (b * N ^ t)) :=
              Nat.add_le_add_left hsum _
            _ =
              (N ^ (t + 1) +
                (List.ofFn (fun e : Fin N =>
                  iidHitCost next B t (next x e))).sum) +
                    b * N ^ (t + 1) := by
              rw [Nat.pow_succ]
              ac_rfl

/-- Composition through a forward-closed intermediate predicate.  The direct
horizon inequality above in fact does not need closure, but the premise is
kept here because this is the physical interface consumed by the paper. -/
theorem expected_then_closed {α : Type} {N a b : Nat}
    (next : α → Fin N → α) (A B C : α → Prop)
    (hAB : ∀ x, A x →
      IIDExpectedHittingTimeAtMost next B x a)
    (_hBclosed : ∀ x e, B x → B (next x e))
    (hBC : ∀ y, B y →
      IIDExpectedHittingTimeAtMost next C y b)
    (x : α) (hxA : A x) :
    IIDExpectedHittingTimeAtMost next C x (a + b) := by
  unfold IIDExpectedHittingTimeAtMost
  intro t
  have hthen := iidHitCost_then_le next B C hBC t x
  have hfirst := hAB x hxA t
  calc
    iidHitCost next C t x ≤
        iidHitCost next B t x + b * N ^ t := hthen
    _ ≤ a * N ^ t + b * N ^ t :=
      Nat.add_le_add_right hfirst _
    _ = (a + b) * N ^ t :=
      (Nat.add_mul a b (N ^ t)).symm

/-- Increasing a numerical mean bound preserves the expected-hitting-time
assertion. -/
theorem expected_bound_mono {α : Type} {N a b : Nat}
    (next : α → Fin N → α) (target : α → Prop) (x : α)
    (h : IIDExpectedHittingTimeAtMost next target x a)
    (hab : a ≤ b) :
    IIDExpectedHittingTimeAtMost next target x b := by
  unfold IIDExpectedHittingTimeAtMost at h ⊢
  intro t
  exact Nat.le_trans (h t)
    (Nat.mul_le_mul_right (N ^ t) hab)

/-- From custody, repair the clocks, run independent half-success trials from
legitimacy, and compose the two expected costs. -/
theorem post_custody_time {α : Type} {N : Nat}
    (next : α → Fin N → α)
    (R Leg Cust : α → Prop)
    (L m : Nat)
    (FailLog FailOver : α → List (Fin N) → Prop)
    (hR : ∀ x e, R x → R (next x e))
    (hLeg : ∀ x e, Leg x → Leg (next x e))
    (_hCust : ∀ x e, Cust x → Cust (next x e))
    (_hLegCust : ∀ x, Leg x → Cust x)
    (hRepair : ∀ x, Cust x →
      IIDExpectedHittingTimeAtMost next Leg x (8 * L * m))
    (hLogical : ∀ x, Leg x → ¬ R x →
      4 * wordSum
          (fun u => if FailLog x u then 1 else 0)
          (physicalDeadline L m) ≤
        N ^ (physicalDeadline L m))
    (hOverrun : ∀ x, Leg x → ¬ R x →
      4 * wordSum
          (fun u => if FailOver x u then 1 else 0)
          (physicalDeadline L m) ≤
        N ^ (physicalDeadline L m))
    (hCover : ∀ x, Leg x →
      ∀ u, u.length = physicalDeadline L m →
        ¬ FailLog x u → ¬ FailOver x u →
          R (runWord next x u))
    (x : α) (hxCust : Cust x) :
    IIDExpectedHittingTimeAtMost next R x
      ((8 + 2 ^ 30) * L * m) := by
  have hfail :
      ∀ y, Leg y → ¬ R y →
        2 * wordSum
            (fun u => if R (runWord next y u) then 0 else 1)
            (physicalDeadline L m) ≤
          N ^ (physicalDeadline L m) := by
    intro y hyLeg hyR
    exact trial_from_two next R y
      (FailLog y) (FailOver y)
      (hLogical y hyLeg hyR)
      (hOverrun y hyLeg hyR)
      (hCover y hyLeg)
  have hRestart :
      ∀ y, Leg y →
        IIDExpectedHittingTimeAtMost next R y
          (2 ^ 30 * L * m) := by
    intro y hyLeg
    have h := restart_mean next R Leg hR hLeg hfail y hyLeg
    rw [twice_physicalDeadline L m] at h
    exact h
  have hComposed :
      IIDExpectedHittingTimeAtMost next R x
        (8 * L * m + 2 ^ 30 * L * m) := by
    exact expected_then_closed
      (next := next) (A := Cust) (B := Leg) (C := R)
      (a := 8 * L * m) (b := 2 ^ 30 * L * m)
      hRepair hLeg hRestart x hxCust
  have hsum :
      8 * L * m + 2 ^ 30 * L * m =
        (8 + 2 ^ 30) * L * m := by
    calc
      8 * L * m + 2 ^ 30 * L * m =
          (8 * L + 2 ^ 30 * L) * m :=
        (Nat.add_mul (8 * L) (2 ^ 30 * L) m).symm
      _ = ((8 + 2 ^ 30) * L) * m := by
        apply congrArg (fun q : Nat => q * m)
        exact (Nat.add_mul 8 (2 ^ 30) L).symm
      _ = (8 + 2 ^ 30) * L * m := rfl
  rw [← hsum]
  exact hComposed

/-- Substitute the paper's physical scale and use `anchor_physical` to obtain
the final quadratic post-custody bound. -/
theorem post_custody_quadratic {α : Type} {N : Nat}
    (next : α → Fin N → α)
    (R Leg Cust : α → Prop)
    (L m bL ringN r : Nat)
    (FailLog FailOver : α → List (Fin N) → Prop)
    (hL : L = 2 ^ (5 * bL + 34) * ringN * r)
    (hmr : m * r ≤ ringN)
    (hR : ∀ x e, R x → R (next x e))
    (hLeg : ∀ x e, Leg x → Leg (next x e))
    (hCust : ∀ x e, Cust x → Cust (next x e))
    (hLegCust : ∀ x, Leg x → Cust x)
    (hRepair : ∀ x, Cust x →
      IIDExpectedHittingTimeAtMost next Leg x (8 * L * m))
    (hLogical : ∀ x, Leg x → ¬ R x →
      4 * wordSum
          (fun u => if FailLog x u then 1 else 0)
          (physicalDeadline L m) ≤
        N ^ (physicalDeadline L m))
    (hOverrun : ∀ x, Leg x → ¬ R x →
      4 * wordSum
          (fun u => if FailOver x u then 1 else 0)
          (physicalDeadline L m) ≤
        N ^ (physicalDeadline L m))
    (hCover : ∀ x, Leg x →
      ∀ u, u.length = physicalDeadline L m →
        ¬ FailLog x u → ¬ FailOver x u →
          R (runWord next x u))
    (x : α) (hxCust : Cust x) :
    IIDExpectedHittingTimeAtMost next R x
      (2 ^ (5 * bL + 65) * ringN ^ 2) := by
  have htime :
      IIDExpectedHittingTimeAtMost next R x
        ((8 + 2 ^ 30) * L * m) := by
    exact post_custody_time
      (next := next) (R := R) (Leg := Leg) (Cust := Cust)
      (L := L) (m := m)
      (FailLog := FailLog) (FailOver := FailOver)
      hR hLeg hCust hLegCust hRepair hLogical hOverrun hCover
      x hxCust
  have hbound :
      (8 + 2 ^ 30) * L * m ≤
        2 ^ (5 * bL + 65) * ringN ^ 2 := by
    rw [hL]
    exact anchor_physical bL ringN r m hmr
  exact expected_bound_mono
    (next := next) (target := R) (x := x) htime hbound

#print axioms L4.Height.iidHitCost_then_le
#print axioms L4.Height.expected_then_closed
#print axioms L4.Height.post_custody_time
#print axioms L4.Height.post_custody_quadratic

end L4.Height
