import Leader.L4.BStarBitGateGeometry

namespace L4.BStarBitLabelSwap

open BStarLongClaims BStarH6Ordinal BStarClearanceRaceMark BStarBitGateGeometry

def other : Side → Side
  | .left => .right
  | .right => .left

theorem other_other (s : Side) : other (other s) = s := by cases s <;> rfl
theorem other_ne (s : Side) : other s ≠ s := by cases s <;> decide

variable {n : Nat} {h : Fin n → Bool} (hh : ∃ i, h i = true)
variable (ready : Fin n → Prop) (ordinal4 : ∀ i, ready i → ordinal h hh i = 4)

def Witness (ready : Fin n → Prop) (e : Fin n) (p : Fin n × Side) : Prop :=
  ready p.1 ∧ incident p.1 p.2 = e

/-- A chart-dependent single-label map. Swap each ready BIT gate's two
incident marks; leave every other raw mark fixed. Here readiness is an
input from the old state, not a predicate about future publication. -/
noncomputable def swap (e : Fin n) : Fin n := by
  classical
  exact if H : ∃ p, Witness ready e p then
    incident (Classical.choose H).1 (other (Classical.choose H).2)
  else e

include hh ordinal4 in
theorem witness_unique {e : Fin n} {p q : Fin n × Side}
    (P : Witness ready e p) (Q : Witness ready e q) : p = q := by
  obtain ⟨l,r⟩ := incident_injective h hh p.1 q.1
    (ordinal4 _ P.1) (ordinal4 _ Q.1) p.2 q.2 (P.2.trans Q.2.symm)
  exact Prod.ext l r

include hh ordinal4 in
theorem swap_incident {i : Fin n} (H : ready i) (s : Side) :
    swap ready (incident i s) = incident i (other s) := by
  classical
  have W : Witness ready (incident i s) (i,s) := ⟨H,rfl⟩
  have E : ∃ p, Witness ready (incident i s) p := ⟨(i,s),W⟩
  unfold swap
  rw [dif_pos E]
  have C := witness_unique hh ready ordinal4 (Classical.choose_spec E) W
  rw [C]

theorem swap_fixed {e : Fin n} (no : ¬ ∃ p, Witness ready e p) :
    swap ready e = e := by
  classical
  simp only [swap,dif_neg no]

include hh ordinal4 in
/-- The exact physical labels admit a state-indexed permutation even
when the raw alphabet has odd size. Any unrevealing mark is fixed. -/
theorem swap_twice (e : Fin n) : swap ready (swap ready e) = e := by
  classical
  by_cases E : ∃ p, Witness ready e p
  · obtain ⟨⟨i,s⟩,H,R⟩ := E
    change incident i s = e at R
    rw [←R,swap_incident hh ready ordinal4 H,swap_incident hh ready ordinal4 H,other_other]
  · rw [swap_fixed ready E,swap_fixed ready E]

include hh ordinal4 in
theorem swap_nonfixed_iff (e : Fin n) :
    swap ready e ≠ e ↔ ∃ p, Witness ready e p := by
  constructor
  · intro N
    by_cases H : ∃ p, Witness ready e p
    · exact H
    · exact (N (swap_fixed ready H)).elim
  · rintro ⟨⟨i,s⟩,H,R⟩
    change incident i s = e at R
    rw [←R,swap_incident hh ready ordinal4 H]
    intro E
    have S := (incident_injective h hh i i (ordinal4 _ H) (ordinal4 _ H)
      (other s) s E).2
    exact other_ne s S

#print axioms swap_incident
#print axioms swap_twice
#print axioms swap_nonfixed_iff
end L4.BStarBitLabelSwap
