import Leader.L4.Height.CapRepair
import Leader.L4.Height.LogicalAssembly
import Leader.L4.Height.HeightLemma

namespace L4.Height

open Classical
open L4.Compiler.Native

/-- The remaining interfaces for the all-size headline theorem.

The scheduler, its physical clock projection, and the permanent output set are
shared throughout. Custody is the first proof cut: it is reached from every
Cartesian state in quadratic expected time, is forward closed, and lies inside
the well-formed clock domain. The remaining fields are exactly the hypotheses
consumed by `post_custody_chain_capfree`. -/
structure HeadlineInterfaces
    {α : Type} {N m B M : Nat} {hm : 0 < m} where
  C : Recover.Chain.ClockChain α N m B M hm
  R : α → Prop
  Cust : α → Prop
  K1 : Nat
  bL : Nat
  r : Nat
  L : Nat
  FailLog : α → List (Fin N) → Prop
  FailOver : α → List (Fin N) → Prop

  /-- The custody cut is reached from every Cartesian starting state. -/
  custody_reached :
    ∀ x, IIDExpectedHittingTimeAtMost C.next Cust x (K1 * N ^ 2)

  /-- Custody is preserved by every scheduler letter. -/
  custody_closed :
    ∀ x e, Cust x → Cust (C.next x e)

  /-- Every custody state is in the well-formed clock domain. -/
  custody_wellFormed :
    ∀ x, Cust x → Recover.StageTwo.WellFormed M (C.cfg x)

  /-- Permanent one-leader states remain permanent. -/
  R_closed :
    ∀ x e, R x → R (C.next x e)

  /-- Clock parameters and the strict half-period diameter condition. -/
  clockParams : Recover.StageTwo.ClockParams M
  diameter : m / 2 < M / 2

  /-- Positivity assumptions used by the accepted clock-repair theorem. -/
  L_positive : 1 ≤ L
  m_positive : 1 ≤ m

  /-- Per-site truncated service moments, in the exact accepted form. -/
  serviceMoments :
    ∀ i y, Thru.MomentAt C.next (C.served i) L y

  /-- The long-client service scale. -/
  serviceScale :
    L = 2 ^ (5 * bL + 34) * N * r

  /-- The packing-width inequality. -/
  widthBound : m * r ≤ N

  /-- Logical failure-count bound, exactly as consumed post-custody. -/
  logicalBound :
    ∀ x, Recover.Chain.LgSet C x → ¬ R x →
      4 * wordSum
        (fun u => if FailLog x u then 1 else 0)
        (2 ^ 30 * L * m) ≤ N ^ (2 ^ 30 * L * m)

  /-- Overrun failure-count bound, exactly as consumed post-custody. -/
  overrunBound :
    ∀ x, Recover.Chain.LgSet C x → ¬ R x →
      4 * wordSum
        (fun u => if FailOver x u then 1 else 0)
        (2 ^ 30 * L * m) ≤ N ^ (2 ^ 30 * L * m)

  /-- Deterministic cover after excluding the two failure events. -/
  cover :
    ∀ x, Recover.Chain.LgSet C x →
      ∀ u, u.length = 2 ^ 30 * L * m →
        ¬ FailLog x u → ¬ FailOver x u →
          R (runWord C.next x u)

/-- Conditional all-size headline: quadratic expected time from every
Cartesian starting state to the forward-closed permanent one-leader set.

The first stage reaches Cust in K1*N^2 expected time. Cust is contained in
WellFormed, so CapRepair supplies the post-custody bound. The two bounds are
composed on the same IID scheduler by Physical.expected_then_closed. -/
theorem headline_of_interfaces
    {α : Type} {N m B M : Nat} {hm : 0 < m}
    (H : HeadlineInterfaces (α := α) (N := N) (m := m)
      (B := B) (M := M) (hm := hm))
    (x : α) :
    IIDExpectedHittingTimeAtMost H.C.next H.R x
      ((H.K1 + 2 ^ (5 * H.bL + 66)) * N ^ 2) := by
  have hPost : ∀ y, H.Cust y →
      IIDExpectedHittingTimeAtMost H.C.next H.R y
        (2 ^ (5 * H.bL + 66) * N ^ 2) := by
    intro y hy
    exact post_custody_chain_capfree
      H.C H.R H.L H.bL N H.r H.FailLog H.FailOver
      H.clockParams H.diameter H.L_positive H.m_positive
      H.serviceMoments H.serviceScale H.widthBound H.R_closed
      H.logicalBound H.overrunBound H.cover y
      (H.custody_wellFormed y hy)
  have hComposed :
      IIDExpectedHittingTimeAtMost H.C.next H.R x
        (H.K1 * N ^ 2 + 2 ^ (5 * H.bL + 66) * N ^ 2) := by
    exact expected_then_closed
      (next := H.C.next)
      (A := fun _ : α => True)
      (B := H.Cust)
      (C := H.R)
      (a := H.K1 * N ^ 2)
      (b := 2 ^ (5 * H.bL + 66) * N ^ 2)
      (by
        intro y hy
        exact H.custody_reached y)
      H.custody_closed
      hPost
      x
      True.intro
  have hArithmetic :
      H.K1 * N ^ 2 + 2 ^ (5 * H.bL + 66) * N ^ 2 =
        (H.K1 + 2 ^ (5 * H.bL + 66)) * N ^ 2 := by
    exact (Nat.add_mul H.K1 (2 ^ (5 * H.bL + 66)) (N ^ 2)).symm
  rw [← hArithmetic]
  exact hComposed

end L4.Height

