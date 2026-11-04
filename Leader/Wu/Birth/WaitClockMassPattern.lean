import Leader.Wu.Birth.WaitClockMassLine

/-!
# Finite internally interleaved WAIT service patterns

A pattern specifies an ordered subsequence, not the whole scheduler word.
Every inserted internal edge executes its real WAIT row.  Two lower-port
patterns followed by one real higher service force a higher consumption;
the recursive service length is exactly `3*2^j-1`.
-/

namespace BirthWaitClockMass.Line

set_option autoImplicit false
set_option Elab.async false

def rootPort {w : Nat} (hw : 2 ≤ w) : Fin (w - 1) := ⟨0, by omega⟩
def lastPort {w : Nat} (hw : 2 ≤ w) : Fin (w - 1) := ⟨w - 2, by omega⟩

variable {w : Nat} {hw : 2 ≤ w}

theorem root_bit_row (cap : Nat) (C : Line hw) (e : Fin (w - 1)) :
    ((step cap C e).cell (first hw)).h_field =
      if e = rootPort hw then !(C.cell (first hw)).h_field else (C.cell (first hw)).h_field := by
  by_cases he : e = rootPort hw
  · have hil : left e = first hw := Fin.ext (by simp [he, left, first, rootPort])
    have hb := congrArg (fun p : Registers × Registers => p.1.h) (row_registers cap C e)
    change (update cap C e (first hw)).h_field = _
    rw [← hil, update_left]
    simp only [registerPair, registers] at hb
    simp only [if_pos he]
    simpa [he, rootPort] using hb
  · have hil : first hw ≠ left e := by
      intro h
      apply he
      apply Fin.ext
      have := congrArg Fin.val h
      simpa [first, left, rootPort] using this.symm
    simp only [step, update_other cap C e _ hil (Ne.symm (right_ne_first hw e)), if_neg he]

theorem root_emit (C : Line hw) :
    emit C (rootPort hw) = (C.cell (first hw)).h_field := by rfl

/-- If no root carry was actually consumed, there was at most one root
outgoing toggle.  The equality tracks the current physical bit exactly. -/
theorem root_no_service (cap : Nat) (C : Line hw) (es : List (Fin (w - 1)))
    (hh : services cap (rootPort hw) C es = 0) :
    es.count (rootPort hw) + (if (C.cell (first hw)).h_field then 1 else 0) =
      (if ((run cap C es).cell (first hw)).h_field then 1 else 0) := by
  induction es generalizing C with
  | nil => simp only [List.count_nil, run, Nat.zero_add]; rfl
  | cons e es ih =>
    have ht : services cap (rootPort hw) (step cap C e) es = 0 := by
      simp only [services] at hh
      omega
    have h := ih (step cap C e) ht
    by_cases he : e = rootPort hw
    · subst e
      cases hb : (C.cell (first hw)).h_field
      · simp only [root_bit_row, if_true, hb, Bool.not_false, List.count_cons_self,
          run, Bool.false_eq_true, if_false, Nat.add_zero] at h ⊢
        exact h
      · simp only [services, root_emit, hb, and_self, if_true] at hh
        omega
    · rw [List.count_cons_of_ne he]
      simp only [root_bit_row, if_neg he] at h
      exact h

theorem root_two_letters (cap : Nat) (C : Line hw) (es : List (Fin (w - 1)))
    (he : 2 ≤ es.count (rootPort hw)) : 0 < services cap (rootPort hw) C es := by
  by_cases hh : services cap (rootPort hw) C es = 0
  · have h := root_no_service cap C es hh
    cases hb : (C.cell (first hw)).h_field <;>
      cases hf : ((run cap C es).cell (first hw)).h_field <;>
      simp [hb, hf] at h <;> omega
  · omega

def servicePattern : (j : Nat) → j < w - 1 → List (Fin (w - 1))
  | 0, h => [⟨0, h⟩, ⟨0, h⟩]
  | j + 1, h => servicePattern j (by omega) ++
      (servicePattern j (by omega) ++ [⟨j + 1, h⟩])

theorem servicePattern_length (j : Nat) (hj : j < w - 1) :
    (servicePattern j hj).length + 1 = 3 * 2 ^ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [servicePattern, List.length_append, List.length_cons, List.length_nil]
    have h := ih (by omega)
    rw [Nat.pow_succ]
    omega

/-- Any real internally interleaved word containing the service pattern
supplies an actual carry consumption at its target port. -/
theorem servicePattern_forces (cap : Nat) (j : Nat) (hj : j < w - 1)
    (C : Line hw) (es : List (Fin (w - 1)))
    (hsub : (servicePattern j hj).Sublist es) :
    0 < services cap ⟨j, hj⟩ C es := by
  induction j generalizing C es with
  | zero =>
    apply root_two_letters cap C es
    have h := hsub.count_le (rootPort hw)
    simpa [servicePattern, rootPort] using h
  | succ j ih =>
    change (servicePattern j _ ++
      (servicePattern j _ ++ [(⟨j + 1, hj⟩ : Fin (w - 1))])).Sublist es at hsub
    obtain ⟨a, bc, hes, ha, hbc⟩ := List.append_sublist_iff.mp hsub
    obtain ⟨b, c, hbc', hb, hc⟩ := List.append_sublist_iff.mp hbc
    have h1 := ih (by omega) C a ha
    have h2 := ih (by omega) (run cap C a) b hb
    have h12 : 2 ≤ services cap ⟨j, by omega⟩ C (a ++ b) := by
      rw [services_append]
      omega
    have hlast : (⟨j + 1, hj⟩ : Fin (w - 1)) ∈ c := hc.subset (by simp)
    have h := two_lower_then_real_service cap ⟨j, by omega⟩ ⟨j + 1, hj⟩ rfl
      C (a ++ b) c h12 hlast
    simpa only [hes, hbc', List.append_assoc] using h

end BirthWaitClockMass.Line

#print axioms BirthWaitClockMass.Line.root_two_letters
#print axioms BirthWaitClockMass.Line.servicePattern_length
#print axioms BirthWaitClockMass.Line.servicePattern_forces
