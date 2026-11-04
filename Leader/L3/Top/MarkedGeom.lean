import Leader.L3.Top.MarkedSite

/-!
# Q7: geometry of the target window on the ring

Offsets of `certSite`, the predecessor of a window site, the span bound
`r < n`, the marker pattern of a complete block pair, and the frozen public
fields along a reached fixed trace.

Consumer: `Leader/L3/Top/MarkedLink.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false

/-- The right neighbour of an offset site.

Consumer: `link_window`. -/
theorem rn_certSite {n : Nat} (ring : DirectedRing n) (s : Fin n) (k : Nat) :
    ring.rightNeighbor (certSite s k) = certSite s (k + 1) := by
  apply Fin.ext
  change ((s.val + k) % n + 1) % n = (s.val + (k + 1)) % n
  rw [Nat.mod_add_mod, ← Nat.add_assoc]

/-- The right neighbour map is injective.

Consumer: `link_window`. -/
theorem rightNeighbor_inj {n : Nat} (ring : DirectedRing n) (a b : Fin n)
    (h : ring.rightNeighbor a = ring.rightNeighbor b) : a = b := by
  apply Fin.ext
  have h1 := congrArg Fin.val h
  simp only [DirectedRing.rightNeighbor] at h1
  have ha := a.isLt
  have hb := b.isLt
  rcases Nat.lt_or_ge (a.val + 1) n with h2 | h2 <;>
  rcases Nat.lt_or_ge (b.val + 1) n with h3 | h3
  · rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3] at h1; omega
  · have h4 : b.val + 1 = n := by omega
    rw [Nat.mod_eq_of_lt h2, h4, Nat.mod_self] at h1; omega
  · have h4 : a.val + 1 = n := by omega
    rw [h4, Nat.mod_self, Nat.mod_eq_of_lt h3] at h1; omega
  · have h4 : a.val + 1 = n := by omega
    have h5 : b.val + 1 = n := by omega
    omega

/-- The predecessor of an offset site.

Consumer: `link_window`. -/
theorem certSite_pred {n : Nat} (ring : DirectedRing n) (s e : Fin n) (k : Nat)
    (h : ring.rightNeighbor e = certSite s (k + 1)) : e = certSite s k := by
  apply rightNeighbor_inj ring
  rw [h, rn_certSite]

/-- Close offsets give distinct sites.

Consumer: `link_window`. -/
theorem certSite_inj_close {n : Nat} (s : Fin n) (a b : Nat) (hab : a ≤ b)
    (hlt : b - a < n) (h : certSite s a = certSite s b) : a = b := by
  have h1 := congrArg Fin.val h
  change (s.val + a) % n = (s.val + b) % n at h1
  have h2 := Nat.sub_mod_eq_zero_of_mod_eq h1.symm
  have h3 : s.val + b - (s.val + a) = b - a := by omega
  rw [h3] at h2
  rcases Nat.eq_zero_or_pos (b - a) with h4 | h4
  · omega
  · rw [Nat.mod_eq_of_lt hlt] at h2; omega

/-- `r < n` at every eligible entrance.

Consumer: `link_window`. -/
theorem span_lt_n {n : Nat} (hn : 5 ≤ n) : topClockSpan n < n := by
  have h1 := cert_n_ge_t_add_r n hn
  have h2 := compileAdvice_t_ge_two (ceilLogTwo n) (ringQ_facts n hn).1
  unfold topClockSpan
  omega

/-- The span is at least three.

Consumer: `link_window`. -/
theorem span_ge_three {n : Nat} (hn : 5 ≤ n) : 3 ≤ topClockSpan n :=
  cert_rho_ge_three n hn

/-! ### Marker and leader pattern of a bad complete pair -/

theorem geom_border {n : Nat} (C : HeadlineConfiguration n) (s : Fin n)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    (C (certSite s (topClockSpan n))).beta = true :=
  topPortEligibleTargetMarker C s hbad

/-- Interior target registers are not markers.

Consumer: `link_window`. -/
theorem geom_interior {n : Nat} (C : HeadlineConfiguration n) (s : Fin n)
    (hbad : HeadlineDigit.BadCompletePair C s) (j : Nat) (h0 : 0 < j)
    (h1 : j < topClockSpan n) :
    (C (certSite s (topClockSpan n + j))).beta = false :=
  topPortEligibleTargetInteriorMarker C s hbad ⟨j, h1⟩ h0

/-- The register after the window is a marker.

Consumer: `link_window`. -/
theorem geom_terminal {n : Nat} (C : HeadlineConfiguration n) (s : Fin n)
    (hbad : HeadlineDigit.BadCompletePair C s) :
    (C (certSite s (topClockSpan n + topClockSpan n))).beta = true := by
  have h := hbad.1.2.2.1
  have e : 2 * (compileAdvice (ceilLogTwo n)).rho = topClockSpan n + topClockSpan n := by
    unfold topClockSpan; omega
  rw [e] at h
  exact h

/-! ### The frozen public fields -/

def PublicFrozen {n : Nat} (C : HeadlineConfiguration n) (Z : TopFixedTraceState n) : Prop :=
  ∀ v, (Z.1.1 v).l = (C v).l ∧ (Z.1.1 v).beta = (C v).beta

/-- Frozen public fields along a word.

Consumer: `link_window`. -/
theorem publicFrozen_word {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n) :
    ∀ (w : List (Fin n)) (Z : TopFixedTraceState n), PublicFrozen C Z →
      PublicFrozen C (w.foldl (topFixedTraceNext ring C) Z) := by
  intro w
  induction w with
  | nil => intro Z h; exact h
  | cons e rest ih =>
      intro Z _
      exact ih _ (fun v => ⟨rfl, rfl⟩)

/-- Frozen public fields at a reached cut.

Consumer: `link_window`. -/
theorem publicFrozen_reached {n : Nat} (ring : DirectedRing n) (C : HeadlineConfiguration n)
    (Z : TopFixedTraceState n) (h : topClockReached ring C Z) : PublicFrozen C Z := by
  unfold topClockReached at h
  rw [h]
  unfold topFixedTraceRun
  exact publicFrozen_word ring C Z.2 _ (fun v => ⟨rfl, rfl⟩)

end MarkedCells
end L3

#print axioms L3.MarkedCells.span_lt_n
#print axioms L3.MarkedCells.publicFrozen_reached
