import Leader.L4.Height.ChainBridge
import Leader.L4.Height.ChainClear
import Leader.L4.Height.FrozenCover

/-!
# lem:clock, first clause, on any clock-driving chain

From any well-formed native clock configuration, the expected time until all
clocks are correct and quiet (`LgSet`) is at most `17 L m`, provided every site's
strict service time has the exponential moment `MomentAt ... L` and the stage-2
cap theorem holds in its path-service form (`ChainTwo.CapInterface`).
-/

namespace L4.Height.Recover

open L4.Compiler.Native

theorem clock_repair_of_cap
    {α : Type} {n m B M L : Nat} {hm : 0 < m}
    (C : Chain.ClockChain α n m B M hm)
    (hcap : ChainTwo.CapInterface B M (m / 2) hm)
    (hM : StageTwo.ClockParams M)
    (hL : 1 ≤ L) (hmOne : 1 ≤ m)
    (hMom : ∀ i y, Thru.MomentAt C.next (C.served i) L y) :
    ∀ x, StageTwo.WellFormed M (C.cfg x) →
      IIDExpectedHittingTimeAtMost C.next (Chain.LgSet C) x (17 * L * m) := by
  have hhalf : 2 * (m / 2) ≤ m := by
    have h := Nat.div_mul_le_self m 2
    omega
  exact Chain.chain_repair_two_covers (D := m / 2) C hM hL hmOne hhalf hMom
    (ChainTwo.frozen_stage_cover hm C hcap hM hMom)
    (ChainThree.clear_stage_cover hm C hM rfl hMom)

end L4.Height.Recover

