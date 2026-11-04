import Leader.Wu.Birth.WaitClockMassPattern

/-!
# A real saturated terminal count hit from a finite service pattern

The result is strict increase of the retained terminal count when it starts
below the cap.  It does not replace that cap by a leader-birth event.
-/

namespace BirthWaitClockMass.Line

set_option autoImplicit false
set_option Elab.async false

def hitPattern {w : Nat} (hw : 2 ≤ w) : List (Fin (w - 1)) :=
  servicePattern (w - 2) (by omega) ++ servicePattern (w - 2) (by omega)

variable {w : Nat} {hw : 2 ≤ w}

def terminalCount (C : Line hw) : Nat := (C.cell (last hw)).count
def terminalBit (C : Line hw) : Bool := (C.cell (last hw)).h_field

theorem terminal_rows (cap : Nat) (C : Line hw) (e : Fin (w - 1)) :
    terminalBit (step cap C e) =
        latchBit (if e = lastPort hw then emit C e else false) (terminalBit C) ∧
      terminalCount (step cap C e) =
        if e = lastPort hw ∧ emit C e = true ∧ terminalBit C = true
        then min (terminalCount C + 1) cap else terminalCount C := by
  have hh := congrArg (fun p : Registers × Registers => p.2.h) (row_registers cap C e)
  have hc := congrArg (fun p : Registers × Registers => p.2.count) (row_registers cap C e)
  by_cases he : e = lastPort hw
  · have hir : last hw = right e := Fin.ext (by
      have := e.isLt
      simp only [right, last, he, lastPort]
      omega)
    have hv : e.val + 1 = w - 1 := by have := congrArg Fin.val hir; exact this.symm
    simp only [terminalBit, terminalCount, step, hir, update_right, if_pos he]
    constructor
    · exact hh
    · simp only [registerPair, registers] at hc
      simp only [hv, and_true] at hc
      simp only [he, true_and] at hc ⊢
      exact hc
  · have hir : last hw ≠ right e := by
      intro h
      apply he
      apply Fin.ext
      have := congrArg Fin.val h
      have := e.isLt
      simp only [last, right, lastPort] at *
      omega
    simp only [terminalBit, terminalCount, step,
      update_other cap C e _ (Ne.symm (left_ne_last hw e)) hir,
      if_neg he, latchBit, Bool.false_eq_true, if_false]
    constructor
    · trivial
    · simp [he]

theorem terminal_step_le_cap (cap : Nat) (C : Line hw) (e : Fin (w - 1))
    (hc : terminalCount C ≤ cap) : terminalCount (step cap C e) ≤ cap := by
  rw [(terminal_rows cap C e).2]
  split
  · exact Nat.min_le_right _ _
  · exact hc

theorem terminal_step_mono (cap : Nat) (C : Line hw) (e : Fin (w - 1))
    (hc : terminalCount C ≤ cap) : terminalCount C ≤ terminalCount (step cap C e) := by
  rw [(terminal_rows cap C e).2]
  split
  · exact Nat.le_min.mpr ⟨by omega, hc⟩
  · exact Nat.le_refl _

theorem terminal_run_le_cap (cap : Nat) (C : Line hw) (es : List (Fin (w - 1)))
    (hc : terminalCount C ≤ cap) : terminalCount (run cap C es) ≤ cap := by
  induction es generalizing C with
  | nil => exact hc
  | cons e es ih => exact ih (step cap C e) (terminal_step_le_cap cap C e hc)

theorem terminal_run_mono (cap : Nat) (C : Line hw) (es : List (Fin (w - 1)))
    (hc : terminalCount C ≤ cap) : terminalCount C ≤ terminalCount (run cap C es) := by
  induction es generalizing C with
  | nil => exact Nat.le_refl _
  | cons e es ih =>
    exact Nat.le_trans (terminal_step_mono cap C e hc)
      (ih (step cap C e) (terminal_step_le_cap cap C e hc))

/-- With a subcap counter and no final count gain, the number of actual
incoming carry consumptions is paid by the one Boolean terminal bit. -/
theorem terminal_no_gain (cap : Nat) (C : Line hw) (es : List (Fin (w - 1)))
    (hc : terminalCount C < cap)
    (heq : terminalCount (run cap C es) = terminalCount C) :
    services cap (lastPort hw) C es + (if terminalBit C then 1 else 0) =
      (if terminalBit (run cap C es) then 1 else 0) := by
  induction es generalizing C with
  | nil => simp only [services, run, Nat.zero_add]; rfl
  | cons e es ih =>
    change services cap (lastPort hw) C (e :: es) + (if terminalBit C then 1 else 0) =
      (if terminalBit (run cap (step cap C e) es) then 1 else 0)
    have hmono := terminal_step_mono cap C e (by omega)
    have htail := terminal_run_mono cap (step cap C e) es
      (terminal_step_le_cap cap C e (by omega))
    have hstep : terminalCount (step cap C e) = terminalCount C := by
      change terminalCount (run cap (step cap C e) es) = terminalCount C at heq
      omega
    have h := ih (step cap C e) (by omega) (by simpa [run, hstep] using heq)
    have hb := (terminal_rows cap C e).1
    have hn : ¬ (e = lastPort hw ∧ emit C e = true ∧ terminalBit C = true) := by
      intro hit
      have hrow := (terminal_rows cap C e).2
      rw [if_pos hit, Nat.min_eq_left (by omega)] at hrow
      omega
    by_cases he : e = lastPort hw
    · subst e
      cases hp : emit C (lastPort hw) <;> cases hb0 : terminalBit C
      · simp only [services, hp, Bool.false_eq_true, and_false, if_false, Nat.zero_add,
          hb, if_true, latchBit, hb0] at h ⊢
        exact h
      · simp only [services, hp, Bool.false_eq_true, and_false, if_false, Nat.zero_add,
          hb, if_true, latchBit, hb0] at h ⊢
        exact h
      · simp only [services, hp, and_self, if_true, hb, latchBit, hb0, Bool.not_false,
          Bool.false_eq_true, if_false, Nat.add_zero] at h ⊢
        omega
      · exact False.elim (hn ⟨rfl, hp, hb0⟩)
    · simp only [services, he, false_and, if_false, Nat.zero_add, hb,
        latchBit, Bool.false_eq_true] at h ⊢
      exact h

theorem two_terminal_services_increase (cap : Nat) (C : Line hw)
    (es : List (Fin (w - 1))) (hc : terminalCount C < cap)
    (hs : 2 ≤ services cap (lastPort hw) C es) :
    terminalCount C < terminalCount (run cap C es) := by
  have hm := terminal_run_mono cap C es (by omega)
  by_cases he : terminalCount (run cap C es) = terminalCount C
  · have h := terminal_no_gain cap C es hc he
    cases hb : terminalBit C <;> cases hf : terminalBit (run cap C es) <;>
      simp [hb, hf] at h <;> omega
  · omega

theorem hitPattern_length : (hitPattern hw).length + 2 = 3 * 2 ^ (w - 1) := by
  have h := servicePattern_length (w := w) (w - 2) (by omega)
  have he : w - 1 = (w - 2) + 1 := by omega
  have hp : 2 ^ (w - 1) = 2 ^ (w - 2) * 2 := by rw [he, Nat.pow_succ]
  simp only [hitPattern, List.length_append]
  rw [hp]
  omega

/-- All inserted internal edges execute their actual rows.  The old bit and
carry contents are arbitrary; only actual reset flags are initially clear. -/
theorem hitPattern_forces_increase (cap : Nat) (C : Line hw)
    (es : List (Fin (w - 1))) (hc : terminalCount C < cap)
    (hsub : (hitPattern hw).Sublist es) :
    terminalCount C < terminalCount (run cap C es) := by
  obtain ⟨a, b, he, ha, hb⟩ := List.append_sublist_iff.mp hsub
  have h1 := servicePattern_forces cap (w - 2) (by omega) C a ha
  have h2 := servicePattern_forces cap (w - 2) (by omega) (run cap C a) b hb
  apply two_terminal_services_increase cap C es hc
  rw [he, services_append]
  change 2 ≤ services cap ⟨w - 2, by omega⟩ C a +
    services cap ⟨w - 2, by omega⟩ (run cap C a) b
  omega

end BirthWaitClockMass.Line

#print axioms BirthWaitClockMass.Line.terminal_run_mono
#print axioms BirthWaitClockMass.Line.two_terminal_services_increase
#print axioms BirthWaitClockMass.Line.hitPattern_length
#print axioms BirthWaitClockMass.Line.hitPattern_forces_increase
