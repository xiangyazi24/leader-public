import Leader.L3.Base
import Leader.L3.ParamsFacts

/-!
# The SMALL `RUN (j+1)` fallback of `smallRun` is never taken in production

`smallRun v` (`Base.lean`) saturates at `RUN (kStar-1)` when `v ≥ kStar`.  `smallPair` calls
`smallRun (j + 1)` only under `j + 1 < k` where `k = c.K = 2q + kappa`; on the production SMALL band
(`useSmall`, `q ≥ 3`) `K ≤ 175 < 199 = kStar` (`compileAdvice_K_le_smallCap`), so `j + 1 < kStar` and
the saturating branch is dead.
-/

namespace L3

set_option autoImplicit false

/-- Below `kStar`, `smallRun` is the exact `RUN v`. -/
theorem smallRun_of_lt (v : Nat) (h : v < kStar) : smallRun v = Small.RUN ⟨v, h⟩ := by
  unfold smallRun
  rw [dif_pos h]

/-- Production SMALL band: the `RUN (j+1)` built under `j + 1 < K` is exact (no saturation). -/
theorem smallRun_succ_production (q : Nat) (h3 : 3 ≤ q)
    (hs : (compileAdvice q).useSmall = true) (j : Nat) (hj : j + 1 < (compileAdvice q).K) :
    smallRun (j + 1) = Small.RUN ⟨j + 1, small_run_succ_lt q h3 hs j hj⟩ :=
  smallRun_of_lt (j + 1) (small_run_succ_lt q h3 hs j hj)

end L3
