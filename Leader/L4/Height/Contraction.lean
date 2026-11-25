import Leader.L4.Height.LossAlt

/-!
# lem:height from the four-bit interface

`height_contraction_of_fill` is Lemma lem:height (expected logical rounds to a single
anchor at most 122880 m from any bounded snapshot), conditional only on
`FillLossInterface` (the four-bit event lemma) at every bounded state with at least
two anchors. All other hypotheses of `height_contraction_mid` are discharged.
-/

namespace L4.Height

open L4.Compiler.Native

theorem height_contraction_of_fill
    {m : Nat} (B : Nat) (hm : 0 < m) (hB : m < B)
    (hfill : ∀ x : HeightBoundedState m B,
      2 ≤ boundedAnchorCount (B := B) hm x →
      FillLossInterface B hm hB x)
    (s : Fin m → Snapshot) (hs : Bounded B s) :
    IIDExpectedHittingTimeAtMost
      (heightChain B hm)
      (fun x => anchorCount hm x = 1)
      s (122880 * m) :=
  height_contraction_mid B hm hB s hs
    (drift_step_of_fill B hm hB hfill)
    (fun k h2 hk => gap_len_bound m k h2 hk)
    (window_step_interface m)
    (potential_bound_interface m)

end L4.Height
