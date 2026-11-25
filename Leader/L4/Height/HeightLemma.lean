import Leader.L4.Height.FillLoss
import Leader.L4.Height.Contraction

/-!
# Lemma lem:height (anchor contraction), unconditional

From any bounded snapshot on the m-cycle (m < B), the expected number of full
synchronous logical rounds until exactly one anchor remains is at most 122880 m,
for independent fair bits per site per round (letters of `Fin (2^m)`).
-/

namespace L4.Height

open L4.Compiler.Native

theorem anchor_contraction
    {m : Nat} (B : Nat) (hm : 0 < m) (hB : m < B)
    (s : Fin m → Snapshot) (hs : Bounded B s) :
    IIDExpectedHittingTimeAtMost
      (heightChain B hm)
      (fun x => anchorCount hm x = 1)
      s (122880 * m) :=
  height_contraction_of_fill B hm hB (fill_loss_interface B hm hB) s hs

end L4.Height

