import Leader.Wu.Splice.PhysicalHoldProjectionLetter
import Leader.Wu.Splice.PhysicalHoldGlobalProgress

set_option autoImplicit false

/-! # The potential drop of same-edge services is a drop of the served pair's weight

Consecutive services of one edge change only the two served cells, so the global
`controllerPotentialV6` drop certified by the global progress theorem is a strict drop of the
pair weight.  The pair weight is local, so it transfers through far services between hits:
the potential-drop alternative of global progress becomes a pair-weight drop for the hit word. -/

namespace B9SpliceV10ePairWeight

open Q11593SpliceControllerDesign B9SpliceControllerR1Table B9SpliceControllerR1TableV6
  B9SpliceControllerR1TableV7 B9SpliceTableV10d B9SpliceTableV10e B9SpliceV10eTransparency
  B9SpliceV10eWordProjection B9SpliceV10eProjectionLetter B9SpliceV10eGlobalProgress
  B9SpliceV10eGlobalProgressFinal

variable {n psi width kappa tau : Nat}

/-- Exact one-index exchange of `List.ofFn` sums. -/
theorem ofFn_sum_exchange (f g : Fin n → Nat) (a : Fin n) (h : ∀ i, i ≠ a → f i = g i) :
    (List.ofFn f).sum + g a = (List.ofFn g).sum + f a := by
  have h1 := ofFn_sum_split f g a (fun i hi => Nat.le_of_eq (h i hi))
  have h2 := ofFn_sum_split g f a (fun i hi => Nat.le_of_eq (h i hi).symm)
  omega

/-- Weight of the served pair. -/
def pairWeight (ring : DirectedRing n) (C : R1ConfigV6 n psi kappa tau) (e : Fin n) : Nat :=
  controllerWeightV6 (C e) + controllerWeightV6 (C (ring.rightNeighbor e))

/-- Two cells change: the potential and the pair weight move together. -/
theorem potential_pair_identity (ring : DirectedRing n) (C D : R1ConfigV6 n psi kappa tau)
    (e : Fin n) (hne : ring.rightNeighbor e ≠ e)
    (hother : ∀ i, i ≠ e → i ≠ ring.rightNeighbor e → D i = C i) :
    controllerPotentialV6 D + pairWeight ring C e = controllerPotentialV6 C + pairWeight ring D e := by
  let M : R1ConfigV6 n psi kappa tau := fun i => if i = e then D e else C i
  have hs1 := ofFn_sum_exchange (fun i => controllerWeightV6 (M i)) (fun i => controllerWeightV6 (C i)) e
    (fun i hi => by simp [M, hi])
  have hs2 := ofFn_sum_exchange (fun i => controllerWeightV6 (D i)) (fun i => controllerWeightV6 (M i))
    (ring.rightNeighbor e) (fun i hi => by
      by_cases hie : i = e
      · subst hie; simp [M]
      · simp [M, hie, hother i hie hi])
  have hMe : M e = D e := by simp [M]
  have hMj : M (ring.rightNeighbor e) = C (ring.rightNeighbor e) := by simp [M, hne]
  unfold controllerPotentialV6 pairWeight
  simp only [hMe, hMj] at hs1 hs2
  omega

theorem serveIter_other (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (e : Fin n) (m : Nat) (C : R1ConfigV6 n psi kappa tau) (i : Fin n)
    (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) :
    serveIter hpsi hwidth hle ring e m C i = C i := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show stepV10e hpsi hwidth hle ring (serveIter hpsi hwidth hle ring e m C) e i = C i
    rw [stepV10e_other hpsi hwidth hle ring _ e i hi hj, ih]

/-- Along consecutive services of one edge, a potential drop is a pair-weight drop. -/
theorem serveIter_potential_drop_iff (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (e : Fin n) (hne : ring.rightNeighbor e ≠ e) (m : Nat)
    (C : R1ConfigV6 n psi kappa tau) :
    controllerPotentialV6 (serveIter hpsi hwidth hle ring e m C) < controllerPotentialV6 C ↔
      pairWeight ring (serveIter hpsi hwidth hle ring e m C) e < pairWeight ring C e := by
  have h := potential_pair_identity ring C (serveIter hpsi hwidth hle ring e m C) e hne
    (fun i hi hj => serveIter_other hpsi hwidth hle ring e m C i hi hj)
  omega

/-- Global progress in local form: some edge's next three consecutive services contain a
physical service or end with a strictly lower pair weight. -/
theorem globalProgress_local (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (hn : 2 ≤ n) (C : R1ConfigV6 n psi kappa tau)
    (hlead : ∀ i, (C i).carrier.splice.base.core.core.leader = false)
    (hS : SpliceSafeV7 hpsi ring C) (hclear : ¬ RolesClearV7 C) :
    ∃ e : Fin n, ∃ m, m < 3 ∧
      (PhysicalServiceAt hpsi hwidth hle ring
          (serveIter hpsi hwidth hle ring e m C) (serveIter hpsi hwidth hle ring e (m + 1) C) e ∨
        pairWeight ring (serveIter hpsi hwidth hle ring e (m + 1) C) e < pairWeight ring C e) := by
  obtain ⟨e, m, hm, h⟩ := globalProgressWithin3 hpsi hwidth hle ring hn C hlead hS hclear
  refine ⟨e, m, hm, ?_⟩
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr ((serveIter_potential_drop_iff hpsi hwidth hle ring e
      (rightNeighbor_ne_self ring hn e) (m + 1) C).1 h)

/-- The pair weight after `k` hits with far words between equals the pair weight after `k`
consecutive services. -/
theorem hitWord_pairWeight (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (e : Fin n) (hne : ring.rightNeighbor e ≠ e)
    (us : List (List (Fin n))) (hus : ∀ u ∈ us, ∀ f ∈ u, Far ring e f)
    (C : R1ConfigV6 n psi kappa tau) :
    pairWeight ring (serveWord hpsi hwidth hle ring (hitWord e us) C) e =
      pairWeight ring (serveIter hpsi hwidth hle ring e us.length C) e := by
  obtain ⟨h1, h2⟩ := hitWord_pair hpsi hwidth hle ring e hne us hus C
  unfold pairWeight
  rw [h1, h2]

/-- Window form of global progress: for the chosen edge, any three hits with far words between
either contain a physical service (a host letter of the projected word) or, at some hit, leave
the pair weight strictly below its value at the window start. -/
theorem window_progress (hpsi : 0 < psi) (hwidth : 0 < width) (hle : width <= psi)
    (ring : DirectedRing n) (hn : 2 ≤ n) (C : R1ConfigV6 n psi kappa tau)
    (hlead : ∀ i, (C i).carrier.splice.base.core.core.leader = false)
    (hS : SpliceSafeV7 hpsi ring C) (hclear : ¬ RolesClearV7 C) :
    ∃ e : Fin n, ∀ us : List (List (Fin n)), us.length = 3 →
      (∀ u ∈ us, ∀ f ∈ u, Far ring e f) →
      1 ≤ physCount hpsi hwidth hle ring (hitWord e us) C ∨
      ∃ k, k ≤ 3 ∧
        pairWeight ring (serveWord hpsi hwidth hle ring (hitWord e (us.take k)) C) e <
          pairWeight ring C e := by
  obtain ⟨e, m, hm, h⟩ := globalProgress_local hpsi hwidth hle ring hn C hlead hS hclear
  have hne := rightNeighbor_ne_self ring hn e
  refine ⟨e, fun us hlen hus => ?_⟩
  rcases h with h | h
  · left
    exact physCount_hitWord_pos hpsi hwidth hle ring e hne us hus C m (by omega) h
  · right
    refine ⟨m + 1, by omega, ?_⟩
    have htake : ∀ u ∈ us.take (m + 1), ∀ f ∈ u, Far ring e f :=
      fun u hu => hus u (List.mem_of_mem_take hu)
    rw [hitWord_pairWeight hpsi hwidth hle ring e hne _ htake C]
    have hl : (us.take (m + 1)).length = m + 1 := by
      rw [List.length_take]; omega
    rw [hl]
    exact h

end B9SpliceV10ePairWeight
