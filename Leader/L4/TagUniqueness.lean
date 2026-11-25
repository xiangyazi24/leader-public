import Leader.L4.EntranceQuiet

namespace L4.TaggedTrace

private theorem move_ne_resident {p c1 n : Nat} (x : Config p c1 n)
    (e j b : Fin n) (hje : j ≠ e)
    (hmove : carrierStep x e (some e) = some b)
    (hkeep : carrierStep x e (some j) = some b) : False := by
  obtain ⟨hb,ht⟩ := carrierStep_selected_survives x e b hmove
  have hbj := carrierStep_not_selected_stays x e j b hje hkeep
  have hj : j = rightNeighbor e := hbj.symm.trans hb
  have hno := tagTransfer_excludes_resident (x e) (x (rightNeighbor e)) ht
  simp only [carrierStep, if_neg hje, if_pos hj, hno, Bool.false_eq_true, if_false] at hkeep
  contradiction

/-- Distinct surviving pre-mark carriers never claim the same output byte.
The moving-tag and resident-tag claims on the selected responder are
exclusive, even before the peacefulness invariant holds. -/
theorem carrierStep_inj_survives {p c1 n : Nat} (x : Config p c1 n)
    (e i j b : Fin n)
    (hi : carrierStep x e (some i) = some b)
    (hj : carrierStep x e (some j) = some b) : i = j := by
  by_cases hie : i = e
  · subst i
    by_cases hje : j = e
    · exact hje.symm
    · exact (move_ne_resident x e j b hje hi hj).elim
  · by_cases hje : j = e
    · subst j
      exact (move_ne_resident x e i b hie hj hi).elim
    · exact (carrierStep_not_selected_stays x e i b hie hi).symm.trans
        (carrierStep_not_selected_stays x e j b hje hj)

private theorem advance_carrier {p c1 n : Nat} (s : Obs p c1 n) (e : Fin n) :
    (advance s e).carrier = carrierStep s.config e s.carrier := by
  cases h : s.carrier <;> simp [advance,h,carrierStep]

private theorem list_snoc_induction {α : Type} {P : List α → Prop}
    (hNil : P []) (hStep : ∀ w a, P w → P (w ++ [a])) (w : List α) : P w := by
  have h : ∀ v : List α, P v.reverse := by
    intro v
    induction v with
    | nil => exact hNil
    | cons a v ih => simpa only [List.reverse_cons] using hStep v.reverse a ih
  simpa only [List.reverse_reverse] using h w.reverse

/-- Product observer: live original IDs are disjoint on every finite word. -/
theorem original_carriers_injective {p c1 n : Nat} (x : Config p c1 n)
    (w : List (Fin n)) :
    ∀ i j b : Fin n,
      (trackAll (allInit x) w i).carrier = some b →
      (trackAll (allInit x) w j).carrier = some b → i = j := by
  induction w using list_snoc_induction with
  | hNil =>
    intro i j b hi hj
    change (init x i).carrier = some b at hi
    change (init x j).carrier = some b at hj
    unfold init at hi hj
    split at hi
    · split at hj
      · exact (Option.some.inj hi).trans (Option.some.inj hj).symm
      · contradiction
    · contradiction
  | hStep w e ih =>
    intro i j b hi hj
    rw [trackAll_append] at hi hj
    change (advance (trackAll (allInit x) w i) e).carrier = some b at hi
    change (advance (trackAll (allInit x) w j) e).carrier = some b at hj
    rw [advance_carrier, allTrack_config] at hi hj
    have hi' : (allInit x i).config = x := rfl
    have hj' : (allInit x j).config = x := rfl
    rw [hi'] at hi
    rw [hj'] at hj
    cases hci : (trackAll (allInit x) w i).carrier with
    | none => simp [hci,carrierStep] at hi
    | some a =>
      cases hcj : (trackAll (allInit x) w j).carrier with
      | none => simp [hcj,carrierStep] at hj
      | some c =>
        rw [hci] at hi
        rw [hcj] at hj
        have h := carrierStep_inj_survives (run x w) e a c b hi hj
        exact ih i j a hci (h.symm ▸ hcj)

end L4.TaggedTrace

