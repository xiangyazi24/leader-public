import Leader.L4.Height.ClockRepair
import Leader.L4.Height.PhysicalGen

namespace L4.Height

open Classical

set_option maxRecDepth 8192
set_option maxHeartbeats 12000000

/-- The post-custody quadratic estimate with the accepted `17 * L * m`
clock-repair budget.  The same `+66` exponent as the sixteen-unit version is
sufficient because `17 + 2 * 2^30` is still at most `2^32`. -/
theorem post_custody_quadratic_rep {α : Type} {N : Nat}
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
      IIDExpectedHittingTimeAtMost next Leg x (17 * L * m))
    (hLogical : ∀ x, Leg x → ¬ R x →
      4 * wordSum
        (fun u => if FailLog x u then 1 else 0)
        (2 ^ 30 * L * m) ≤ N ^ (2 ^ 30 * L * m))
    (hOverrun : ∀ x, Leg x → ¬ R x →
      4 * wordSum
        (fun u => if FailOver x u then 1 else 0)
        (2 ^ 30 * L * m) ≤ N ^ (2 ^ 30 * L * m))
    (hCover : ∀ x, Leg x →
      ∀ u, u.length = 2 ^ 30 * L * m →
        ¬ FailLog x u → ¬ FailOver x u →
          R (runWord next x u))
    (x : α) (hxCust : Cust x) :
    IIDExpectedHittingTimeAtMost next R x
      (2 ^ (5 * bL + 66) * ringN ^ 2) := by
  have htime := post_custody_time_gen
    (next := next) (R := R) (Leg := Leg) (Cust := Cust)
    (rep := 17 * L * m) (d := 2 ^ 30 * L * m)
    (FailLog := FailLog) (FailOver := FailOver)
    hR hLeg hCust hLegCust hRepair hLogical hOverrun hCover x hxCust
  have hcoefficient : 17 + 2 * 2 ^ 30 ≤ 2 ^ 32 := by decide
  have hfactor :
      17 * L * m + 2 * (2 ^ 30 * L * m) =
        (17 + 2 * 2 ^ 30) * L * m := by
    simp only [Nat.add_mul]
    ac_rfl
  have hsmall :
      17 * L * m + 2 * (2 ^ 30 * L * m) ≤
      2 ^ 32 * L * m := by
    rw [hfactor]
    exact Nat.mul_le_mul_right m
      (Nat.mul_le_mul_right L hcoefficient)
  have hscale :
      2 ^ 32 * L * m ≤ 2 ^ (5 * bL + 66) * ringN ^ 2 := by
    rw [hL]
    have hexp :
        2 ^ 32 * 2 ^ (5 * bL + 34) = 2 ^ (5 * bL + 66) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hrbound :
        ringN * (m * r) ≤ ringN * ringN :=
      Nat.mul_le_mul_left ringN hmr
    have hsq : ringN ^ 2 = ringN * ringN := by
      simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    calc
      2 ^ 32 * (2 ^ (5 * bL + 34) * ringN * r) * m
          = (2 ^ 32 * 2 ^ (5 * bL + 34)) *
              (ringN * (m * r)) := by ac_rfl
      _ = 2 ^ (5 * bL + 66) * (ringN * (m * r)) := by
        rw [hexp]
      _ ≤ 2 ^ (5 * bL + 66) * (ringN * ringN) :=
        Nat.mul_le_mul_left _ hrbound
      _ = 2 ^ (5 * bL + 66) * ringN ^ 2 := by
        rw [hsq]
  exact expected_bound_mono (next := next) (target := R) (x := x)
    htime (Nat.le_trans hsmall hscale)

/-- Assemble the accepted clock repair with the generic post-custody trial.
The only clock-specific hypotheses left exposed are the path-cap interface and
the per-site service moments; the logical, overrun, and deterministic-cover
interfaces are passed through verbatim. -/
theorem post_custody_chain
    {α : Type} {N m B M : Nat} {hm : 0 < m}
    (C : Recover.Chain.ClockChain α N m B M hm)
    (R : α → Prop)
    (L bL ringN r : Nat)
    (FailLog FailOver : α → List (Fin N) → Prop)
    (hcap : Recover.ChainTwo.CapInterface B M (m / 2) hm)
    (hM : Recover.StageTwo.ClockParams M)
    (hLpos : 1 ≤ L) (hmOne : 1 ≤ m)
    (hMom : ∀ i y, Thru.MomentAt C.next (C.served i) L y)
    (hL : L = 2 ^ (5 * bL + 34) * ringN * r)
    (hmr : m * r ≤ ringN)
    (hR : ∀ x e, R x → R (C.next x e))
    (hLogical : ∀ x, Recover.Chain.LgSet C x → ¬ R x →
      4 * wordSum
        (fun u => if FailLog x u then 1 else 0)
        (2 ^ 30 * L * m) ≤ N ^ (2 ^ 30 * L * m))
    (hOverrun : ∀ x, Recover.Chain.LgSet C x → ¬ R x →
      4 * wordSum
        (fun u => if FailOver x u then 1 else 0)
        (2 ^ 30 * L * m) ≤ N ^ (2 ^ 30 * L * m))
    (hCover : ∀ x, Recover.Chain.LgSet C x →
      ∀ u, u.length = 2 ^ 30 * L * m →
        ¬ FailLog x u → ¬ FailOver x u →
          R (runWord C.next x u))
    (x : α) (hxCust : Recover.StageTwo.WellFormed M (C.cfg x)) :
    IIDExpectedHittingTimeAtMost C.next R x
      (2 ^ (5 * bL + 66) * ringN ^ 2) := by
  have hCust :
      ∀ y e, Recover.StageTwo.WellFormed M (C.cfg y) →
        Recover.StageTwo.WellFormed M (C.cfg (C.next y e)) := by
    intro y e hy
    cases hact : C.act y e with
    | none =>
        have hcfg := C.cfg_next y e
        simp only [hact] at hcfg
        rw [hcfg]
        exact hy
    | some p =>
        rcases p with ⟨i, delta⟩
        have hcfg := C.cfg_next y e
        simp only [hact] at hcfg
        rw [hcfg]
        exact Recover.Chain.wellFormed_activate
          hM hm (C.cfg y) hy i delta
  have hLeg :
      ∀ y e, Recover.Chain.LgSet C y →
        Recover.Chain.LgSet C (C.next y e) :=
    Recover.Chain.lg_closed C hM
  have hLegCust :
      ∀ y, Recover.Chain.LgSet C y →
        Recover.StageTwo.WellFormed M (C.cfg y) := by
    intro y hy
    unfold Recover.Chain.LgSet at hy
    exact hy.2.2
  have hRepair :
      ∀ y, Recover.StageTwo.WellFormed M (C.cfg y) →
        IIDExpectedHittingTimeAtMost C.next
          (Recover.Chain.LgSet C) y (17 * L * m) := by
    exact Recover.clock_repair_of_cap
      C hcap hM hLpos hmOne hMom
  exact post_custody_quadratic_rep
    (next := C.next)
    (R := R)
    (Leg := Recover.Chain.LgSet C)
    (Cust := fun y => Recover.StageTwo.WellFormed M (C.cfg y))
    (L := L) (m := m) (bL := bL) (ringN := ringN) (r := r)
    (FailLog := FailLog) (FailOver := FailOver)
    hL hmr hR hLeg hCust hLegCust hRepair
    hLogical hOverrun hCover x hxCust

#print axioms L4.Height.post_custody_quadratic_rep
#print axioms L4.Height.post_custody_chain

end L4.Height

