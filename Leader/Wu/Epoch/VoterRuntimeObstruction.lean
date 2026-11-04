import Leader.Wu.Epoch.VoterFiniteTree

/-!
# Finite-horizon cubic obstruction for the current epoch dynamics

The unique Bellman residual value can be combined with an exact finite action
tree.  Summing truncated doubled costs over all `n^t` scheduler words preserves
the Bellman value.  A missed word can carry at most the global cubic residual;
a word that has already absorbed carries none.  Therefore a midpoint
contiguous domain cannot have failure at most `1/8` before a cubic horizon.

This is a finite count theorem, not an asymptotic heuristic.  Since the
P_PLL-derived epoch colors project exactly to this directed voter process and
protected entry requires color consensus, the present slot rule cannot supply
the thesis-order WHP route; a faster physical epoch rule is required.
-/

namespace PPLLEpochVoterRuntimeObstruction

open PPLLEpochVoterBellman PPLLEpochVoterFiniteTree
  PPLLEpochVoterTwoDomain

/-! ## Bellman residual summed over finite action trees -/

/-- Total doubled truncated-cost numerator over all length-`t` lazy action
words.  At horizon zero the residual Bellman value remains.  At each interior
step every one of the `n^(t+1)` words pays doubled cost two, followed by the
`n-2` stutter, shrink, and grow subtrees. -/
def lazyDoubledCostTotal (n x : Nat) : Nat → Nat
  | 0 => doubledLazyConsensusTime n x
  | t + 1 => if x = 0 ∨ x = n then 0
    else 2 * n ^ (t + 1) +
      (n - 2) * lazyDoubledCostTotal n x t +
      lazyDoubledCostTotal n (x - 1) t +
      lazyDoubledCostTotal n (x + 1) t

/-- Exact finite-tree Bellman conservation: total truncated cost equals the
number of scheduler words times the initial residual value. -/
theorem lazyDoubledCostTotal_eq
    (n x t : Nat) (hx : x ≤ n) :
    lazyDoubledCostTotal n x t =
      n ^ t * doubledLazyConsensusTime n x := by
  induction t generalizing x with
  | zero => simp [lazyDoubledCostTotal]
  | succ t ih =>
      rw [lazyDoubledCostTotal]
      by_cases hboundary : x = 0 ∨ x = n
      · rcases hboundary with rfl | rfl <;>
          simp [doubledLazyConsensusTime]
      · have hxpos : 0 < x := by omega
        have hxlt : x < n := by omega
        rw [if_neg hboundary, ih x hx, ih (x - 1) (by omega),
          ih (x + 1) (by omega)]
        have hbell := doubledLazyConsensusTime_bellman n x hxpos hxlt
        rw [Nat.pow_succ]
        grind

/-- The doubled Bellman residual is bounded by `n^3` at every legal domain
length. -/
theorem doubledLazyConsensusTime_le_cube
    (n x : Nat) (hx : x ≤ n) :
    doubledLazyConsensusTime n x ≤ n ^ 3 := by
  unfold doubledLazyConsensusTime
  have hs : n - x ≤ n := by omega
  have h1 : n * x ≤ n * n := Nat.mul_le_mul_left n hx
  have h2 : (n * x) * (n - x) ≤ (n * n) * n :=
    Nat.mul_le_mul h1 hs
  simpa [Nat.pow_succ, Nat.mul_assoc] using h2

private theorem truncated_cost_step_bound
    (n t p M C0 Cm Cp m0 mm mp : Nat) (hn : 2 ≤ n)
    (h0 : C0 ≤ 2 * t * p + m0 * M)
    (hm : Cm ≤ 2 * t * p + mm * M)
    (hp : Cp ≤ 2 * t * p + mp * M) :
    2 * (p * n) + (n - 2) * C0 + Cm + Cp ≤
      2 * (t + 1) * (p * n) + ((n - 2) * m0 + mm + mp) * M := by
  have hw : (n - 2) * C0 ≤ (n - 2) * (2 * t * p + m0 * M) :=
    Nat.mul_le_mul_left _ h0
  have hs : (n - 2) * C0 + Cm + Cp ≤
      (n - 2) * (2 * t * p + m0 * M) +
        (2 * t * p + mm * M) + (2 * t * p + mp * M) :=
    Nat.add_le_add (Nat.add_le_add hw hm) hp
  calc
    2 * (p * n) + (n - 2) * C0 + Cm + Cp ≤
        2 * (p * n) + ((n - 2) * (2 * t * p + m0 * M) +
          (2 * t * p + mm * M) + (2 * t * p + mp * M)) := by
            simpa [Nat.add_assoc] using Nat.add_le_add_left hs (2 * (p * n))
    _ = 2 * (t + 1) * (p * n) +
        ((n - 2) * m0 + mm + mp) * M := by
          have heq : n - 2 + 2 = n := by omega
          grind

/-- Every finite action-tree cost is bounded by elapsed doubled time on all
words plus one cubic residual for each word that still misses absorption. -/
theorem lazyDoubledCostTotal_le_elapsed_add_misses
    (n x t : Nat) (hn : 2 ≤ n) (hx : x ≤ n) :
    lazyDoubledCostTotal n x t ≤
      2 * t * n ^ t + lazyDomainMissCount n x t * n ^ 3 := by
  induction t generalizing x with
  | zero =>
      rw [lazyDoubledCostTotal, lazyDomainMissCount]
      by_cases hboundary : x = 0 ∨ x = n
      · rcases hboundary with rfl | rfl <;>
          simp [doubledLazyConsensusTime]
      · rw [if_neg hboundary]
        simp
        exact doubledLazyConsensusTime_le_cube n x hx
  | succ t ih =>
      rw [lazyDoubledCostTotal, lazyDomainMissCount]
      by_cases hboundary : x = 0 ∨ x = n
      · simp [hboundary]
      · rw [if_neg hboundary, if_neg hboundary]
        have h0 := ih x hx
        have hm := ih (x - 1) (by omega : x - 1 ≤ n)
        have hp := ih (x + 1) (by omega : x + 1 ≤ n)
        rw [Nat.pow_succ]
        exact truncated_cost_step_bound n t (n ^ t) (n ^ 3)
          (lazyDoubledCostTotal n x t)
          (lazyDoubledCostTotal n (x - 1) t)
          (lazyDoubledCostTotal n (x + 1) t)
          (lazyDomainMissCount n x t)
          (lazyDomainMissCount n (x - 1) t)
          (lazyDomainMissCount n (x + 1) t)
          hn h0 hm hp

/-- Renewal inequality obtained by combining exact Bellman conservation with
the finite miss-count upper decomposition. -/
theorem lazyDomain_renewal_inequality
    (n x t : Nat) (hn : 2 ≤ n) (hx : x ≤ n) :
    n ^ t * doubledLazyConsensusTime n x ≤
      2 * t * n ^ t + lazyDomainMissCount n x t * n ^ 3 := by
  rw [← lazyDoubledCostTotal_eq n x t hx]
  exact lazyDoubledCostTotal_le_elapsed_add_misses n x t hn hx

/-! ## Cubic finite-horizon lower bound -/

/-- On an even ring `n=2m`, if at most one eighth of exact length-`t` action
words miss consensus from the midpoint two-domain state, then `t` is already
at least cubic up to the explicit factor two. -/
theorem lazy_midpoint_failure_eighth_forces_cubic_horizon
    (m t : Nat) (hm : 4 ≤ m)
    (hfail : 8 * lazyDomainMissCount (2 * m) m t ≤ (2 * m) ^ t) :
    m ^ 3 ≤ 2 * t := by
  have hr := lazyDomain_renewal_inequality
    (2 * m) m t (by omega) (by omega)
  rw [doubledLazyConsensusTime_even_midpoint] at hr
  have hres : lazyDomainMissCount (2 * m) m t * (2 * m) ^ 3 ≤
      (2 * m) ^ t * m ^ 3 := by
    have hp := Nat.mul_le_mul_right (m ^ 3) hfail
    have heq : (2 * m) ^ 3 = 8 * m ^ 3 := by grind
    rw [heq]
    calc
      lazyDomainMissCount (2 * m) m t * (8 * m ^ 3) =
          (8 * lazyDomainMissCount (2 * m) m t) * m ^ 3 := by grind
      _ ≤ (2 * m) ^ t * m ^ 3 := hp
  have hmain : (2 * m) ^ t * (2 * m ^ 3) ≤
      2 * t * (2 * m) ^ t + (2 * m) ^ t * m ^ 3 :=
    Nat.le_trans hr (Nat.add_le_add_left hres _)
  have hsplit : (2 * m) ^ t * (2 * m ^ 3) =
      (2 * m) ^ t * m ^ 3 + (2 * m) ^ t * m ^ 3 := by grind
  rw [hsplit, Nat.add_comm (2 * t * (2 * m) ^ t)] at hmain
  have hc0 : (2 * m) ^ t * m ^ 3 ≤ 2 * t * (2 * m) ^ t :=
    Nat.le_of_add_le_add_left hmain
  have hc : (2 * m) ^ t * m ^ 3 ≤ (2 * m) ^ t * (2 * t) := by
    simpa [Nat.mul_comm] using hc0
  have hpos : 0 < (2 * m) ^ t := Nat.pow_pos (by omega)
  exact Nat.le_of_mul_le_mul_left hc hpos

/-- The same cubic horizon obstruction holds for the actual directed-voter
scheduler tree on a canonical midpoint contiguous domain. -/
theorem voter_midpoint_failure_eighth_forces_cubic_horizon
    (m t : Nat) (hm : 4 ≤ m) (ring : DirectedRing (2 * m))
    (hfail : 8 * voterMissTree ring
        (canonicalTwoDomain (by omega : 1 < 2 * m) m (by omega)) t ≤
      (2 * m) ^ t) :
    m ^ 3 ≤ 2 * t := by
  rw [voterMissTree_canonicalTwoDomain
    (by omega : 1 < 2 * m) ring t m (by omega)] at hfail
  exact lazy_midpoint_failure_eighth_forces_cubic_horizon m t hm hfail

end PPLLEpochVoterRuntimeObstruction
