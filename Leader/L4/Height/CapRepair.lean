import Leader.L4.Height.CapCoverAlt
import Leader.L4.Height.Assembly

/-!
# Clock repair and the post-custody bound without the CapInterface hypothesis

`cap_interface` (CapCoverAlt) discharges `ChainTwo.CapInterface B M (m / 2) hm`
under `ClockParams M` and the diameter condition `m / 2 < M / 2`.
-/

namespace L4.Height

open Classical
open L4.Compiler.Native

/-- Local clock repair: from every well-formed configuration the chain reaches
the legitimate set within expected time `17 L m`, given the per-site service
moments. -/
theorem clock_repair {α : Type} {n m B M L : Nat} {hm : 0 < m}
    (C : Recover.Chain.ClockChain α n m B M hm)
    (hM : Recover.StageTwo.ClockParams M) (hdiam : m / 2 < M / 2)
    (hL : 1 ≤ L) (hmOne : 1 ≤ m)
    (hMom : ∀ i y, Thru.MomentAt C.next (C.served i) L y) :
    ∀ x, Recover.StageTwo.WellFormed M (C.cfg x) →
      IIDExpectedHittingTimeAtMost C.next (Recover.Chain.LgSet C) x (17 * L * m) :=
  Recover.clock_repair_of_cap C
    (Recover.StageTwo.cap_interface (B := B) hM hdiam hm) hM hL hmOne hMom

/-- The post-custody quadratic bound on a clock chain, with the path-cap
interface discharged. -/
theorem post_custody_chain_capfree
    {α : Type} {N m B M : Nat} {hm : 0 < m}
    (C : Recover.Chain.ClockChain α N m B M hm)
    (R : α → Prop)
    (L bL ringN r : Nat)
    (FailLog FailOver : α → List (Fin N) → Prop)
    (hM : Recover.StageTwo.ClockParams M) (hdiam : m / 2 < M / 2)
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
      (2 ^ (5 * bL + 66) * ringN ^ 2) :=
  post_custody_chain C R L bL ringN r FailLog FailOver
    (Recover.StageTwo.cap_interface (B := B) hM hdiam hm)
    hM hLpos hmOne hMom hL hmr hR hLogical hOverrun hCover x hxCust

end L4.Height

