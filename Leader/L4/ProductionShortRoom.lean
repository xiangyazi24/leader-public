import Leader.L4.ProductionH6Count

namespace L4.ProductionShortRoom
open AllSizeProtocol ShortLayerGeometry ShortResetCycle

/-- Production advice already leaves room for seven consecutive gaps
of every supported short-sheet cap (and even B=81). -/
theorem seven_gaps_fit {s n B : Nat} (S : 6≤s) (advice : s=ell (ell n))
    (b : B≤81) : 7*B<n := by
  have P := ProductionH6Count.advice_lower (by omega) advice
  have E : 32≤2^(s-1) := Nat.pow_le_pow_right (by decide : 0<2) (by omega : 5≤s-1)
  have F := Nat.pow_le_pow_right (by decide : 0<2) E
  change 4294967296≤2^(2^(s-1)) at F
  omega

/-- Instantiate physical charts directly from the current sheet's
frozen-header successor law. No MIS stabilization is assumed. -/
theorem chart_cap {s n B : Nat} {h : Fin n → Bool}
    (S : 6≤s) (advice : s=ell (ell n)) (bound : B≤81)
    (next : ∀ q, h q=true → ∃ d≤B, Gap h q d)
    (r : Fin n) (root : h r=true) :
    ∃ C : Chart h, C.root=r ∧ C.L≤3*B := by
  have N := seven_gaps_fit S advice bound
  exact chart_of_successor_law (by omega) next r root

theorem chart_cap_nine {s n : Nat} {h : Fin n → Bool}
    (S : 6≤s) (advice : s=ell (ell n))
    (next : ∀ q, h q=true → ∃ d≤3, Gap h q d)
    (r : Fin n) (root : h r=true) :
    ∃ C : Chart h, C.root=r ∧ C.L≤9 :=
  chart_cap S advice (by decide) next r root

theorem chart_cap_twentySeven {s n : Nat} {h : Fin n → Bool}
    (S : 6≤s) (advice : s=ell (ell n))
    (next : ∀ q, h q=true → ∃ d≤9, Gap h q d)
    (r : Fin n) (root : h r=true) :
    ∃ C : Chart h, C.root=r ∧ C.L≤27 :=
  chart_cap S advice (by decide) next r root

theorem chart_cap_eightyOne {s n : Nat} {h : Fin n → Bool}
    (S : 6≤s) (advice : s=ell (ell n))
    (next : ∀ q, h q=true → ∃ d≤27, Gap h q d)
    (r : Fin n) (root : h r=true) :
    ∃ C : Chart h, C.root=r ∧ C.L≤81 :=
  chart_cap S advice (by decide) next r root

end L4.ProductionShortRoom
