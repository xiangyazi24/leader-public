import Leader.Wu.Birth.WaitClockMassLatch

/-!
# A lawful reset-free group, executing literal WAIT

The cells below are actual `AgentState` values.  The transition calls the
existing `waitSaturated` and retains its actual successor cells.  Only the
fixed labels, zero reset flags, and two boundary carry bits form the domain;
all other bits and internal pending carries are arbitrary.
-/

namespace BirthWaitClockMass

open PPLL PPLLRepair

set_option autoImplicit false
set_option Elab.async false

namespace Line

def first {w : Nat} (hw : 2 ≤ w) : Fin w := ⟨0, by omega⟩
def last {w : Nat} (hw : 2 ≤ w) : Fin w := ⟨w - 1, by omega⟩
def left {w : Nat} (j : Fin (w - 1)) : Fin w := ⟨j.val, by have := j.isLt; omega⟩
def right {w : Nat} (j : Fin (w - 1)) : Fin w := ⟨j.val + 1, by have := j.isLt; omega⟩

theorem left_ne_right {w : Nat} (j : Fin (w - 1)) : left j ≠ right j := by
  intro h
  have := congrArg Fin.val h
  simp only [left, right] at this
  omega

theorem right_ne_first {w : Nat} (hw : 2 ≤ w) (j : Fin (w - 1)) :
    right j ≠ first hw := by
  intro h
  have := congrArg Fin.val h
  simp only [right, first] at this
  omega

theorem left_ne_last {w : Nat} (hw : 2 ≤ w) (j : Fin (w - 1)) :
    left j ≠ last hw := by
  intro h
  have := congrArg Fin.val h
  have := j.isLt
  simp only [left, last] at *
  omega

end Line

structure Line {w : Nat} (hw : 2 ≤ w) where
  cell : Fin w → AgentState w
  label : ∀ i, (cell i).label = i
  reset_clear : ∀ i, (cell i).reset = false
  root_carry : (cell (Line.first hw)).carry = false
  terminal_carry : (cell (Line.last hw)).carry = false

namespace Line

variable {w : Nat} {hw : 2 ≤ w}

def row (cap : Nat) (C : Line hw) (j : Fin (w - 1)) : AgentState w × AgentState w :=
  waitSaturated (by omega : 0 < w) cap (C.cell (left j)) (C.cell (right j))

def emit (C : Line hw) (j : Fin (w - 1)) : Bool :=
  if j.val = 0 then (C.cell (left j)).h_field else (C.cell (left j)).carry

theorem row_registers (cap : Nat) (C : Line hw) (j : Fin (w - 1)) :
    registerPair (row cap C j) =
      (⟨if j.val = 0 then !(C.cell (left j)).h_field else (C.cell (left j)).h_field,
          false, false, (C.cell (left j)).count⟩,
       ⟨latchBit (emit C j) (C.cell (right j)).h_field,
          (C.cell (right j)).carry ||
            (emit C j && (C.cell (right j)).h_field && decide (j.val + 1 ≠ w - 1)),
          false,
          if emit C j = true ∧ (C.cell (right j)).h_field = true ∧ j.val + 1 = w - 1
          then min ((C.cell (right j)).count + 1) cap else (C.cell (right j)).count⟩) := by
  have h := internal_register_row (by omega : 0 < w) cap
    (C.cell (left j)) (C.cell (right j))
    (by rw [C.label]; exact right_ne_first hw j)
    (C.reset_clear _) (C.reset_clear _) (by
      intro hz
      have he : left j = first hw := by rw [C.label] at hz; exact hz
      rw [he]
      exact C.root_carry)
  simp only [row, C.label, left, right, pulse, emit, ne_eq, Fin.mk.injEq] at h ⊢
  exact h

def update (cap : Nat) (C : Line hw) (j : Fin (w - 1)) : Fin w → AgentState w :=
  fun i => if i = left j then (row cap C j).1
    else if i = right j then (row cap C j).2 else C.cell i

@[simp] theorem update_left (cap : Nat) (C : Line hw) (j : Fin (w - 1)) :
    update cap C j (left j) = (row cap C j).1 := by simp [update]

@[simp] theorem update_right (cap : Nat) (C : Line hw) (j : Fin (w - 1)) :
    update cap C j (right j) = (row cap C j).2 := by
  simp [update, Ne.symm (left_ne_right j)]

theorem update_other (cap : Nat) (C : Line hw) (j : Fin (w - 1)) (i : Fin w)
    (hl : i ≠ left j) (hr : i ≠ right j) : update cap C j i = C.cell i := by
  simp [update, hl, hr]

def step (cap : Nat) (C : Line hw) (j : Fin (w - 1)) : Line hw where
  cell := update cap C j
  label := by
    intro i
    have h := wait_label_frame (by omega : 0 < w) cap
      (C.cell (left j)) (C.cell (right j))
    by_cases hl : i = left j
    · subst i
      simpa only [update_left, row, C.label] using h.1
    · by_cases hr : i = right j
      · subst i
        simpa only [update_right, row, C.label] using h.2
      · rw [update_other cap C j i hl hr]
        exact C.label i
  reset_clear := by
    intro i
    have hl := congrArg (fun p : Registers × Registers => p.1.reset) (row_registers cap C j)
    have hr := congrArg (fun p : Registers × Registers => p.2.reset) (row_registers cap C j)
    by_cases hil : i = left j
    · subst i
      rw [update_left]
      exact hl
    · by_cases hir : i = right j
      · subst i
        simpa only [update_right, registerPair, registers] using hr
      · rw [update_other cap C j i hil hir]
        exact C.reset_clear i
  root_carry := by
    have h := congrArg (fun p : Registers × Registers => p.1.carry) (row_registers cap C j)
    by_cases he : first hw = left j
    · rw [he, update_left]
      exact h
    · rw [update_other cap C j _ he (Ne.symm (right_ne_first hw j))]
      exact C.root_carry
  terminal_carry := by
    have h := congrArg (fun p : Registers × Registers => p.2.carry) (row_registers cap C j)
    by_cases he : last hw = right j
    · have hv : j.val + 1 = w - 1 := by have := congrArg Fin.val he; exact this.symm
      rw [he, update_right]
      simp only [registerPair, registers, hv, ne_self_iff_false, decide_false,
        Bool.and_false, Bool.or_false] at h
      rw [h, ← he]
      exact C.terminal_carry
    · rw [update_other cap C j _ (Ne.symm (left_ne_last hw j)) he]
      exact C.terminal_carry

def run (cap : Nat) : Line hw → List (Fin (w - 1)) → Line hw
  | C, [] => C
  | C, e :: es => run cap (step cap C e) es

def services (cap : Nat) (j : Fin (w - 1)) : Line hw → List (Fin (w - 1)) → Nat
  | _, [] => 0
  | C, e :: es => (if e = j ∧ emit C e = true then 1 else 0) +
      services cap j (step cap C e) es

theorem run_append (cap : Nat) (C : Line hw) (a b : List (Fin (w - 1))) :
    run cap C (a ++ b) = run cap (run cap C a) b := by
  induction a generalizing C with
  | nil => rfl
  | cons e a ih => simpa only [List.cons_append, run] using ih (step cap C e)

theorem services_append (cap : Nat) (j : Fin (w - 1)) (C : Line hw)
    (a b : List (Fin (w - 1))) :
    services cap j C (a ++ b) = services cap j C a + services cap j (run cap C a) b := by
  induction a generalizing C with
  | nil => simp [services, run]
  | cons e a ih => simp only [List.cons_append, services, run, ih, Nat.add_assoc]

def latch (C : Line hw) (j : Fin (w - 1)) : Latch :=
  ⟨(C.cell (left j)).h_field, (C.cell (left j)).carry⟩

/-- The incoming pulse and outgoing service are disjoint actual edges. -/
def event (C : Line hw) (j e : Fin (w - 1)) : LatchEvent :=
  if e = j then .service
  else if e.val + 1 = j.val ∧ emit C e = true then .arrival else .idle

theorem latch_row (cap : Nat) (C : Line hw) (j e : Fin (w - 1)) (hj : j.val ≠ 0) :
    latch (step cap C e) j = (latch C j).step (event C j e) := by
  have h := row_registers cap C e
  by_cases he : e = j
  · subst e
    have hb := congrArg (fun p : Registers × Registers => Latch.mk p.1.h p.1.carry) h
    simpa only [latch, step, update_left, registerPair, registers, hj, if_false,
      event, if_true, Latch.step] using hb
  · have hil : left j ≠ left e := by
      intro hh
      exact he (Fin.ext (congrArg Fin.val hh).symm)
    by_cases hr : e.val + 1 = j.val
    · have hir : left j = right e := Fin.ext hr.symm
      have ht : j.val ≠ w - 1 := by have := j.isLt; omega
      have hb := congrArg (fun p : Registers × Registers => Latch.mk p.2.h p.2.carry) h
      change Latch.mk (update cap C e (left j)).h_field (update cap C e (left j)).carry = _
      rw [hir, update_right]
      simp only [registerPair, registers] at hb
      rw [hb]
      cases hp : emit C e <;>
        simp [latch, event, he, hr, hp, latchBit, Latch.step, hir, ht]
    · have hir : left j ≠ right e := by
        intro hh
        exact hr (congrArg Fin.val hh).symm
      simp only [latch, step, update_other cap C e (left j) hil hir,
        event, he, if_false, hr, false_and, Latch.step]

def trace (cap : Nat) (j : Fin (w - 1)) : Line hw → List (Fin (w - 1)) → List LatchEvent
  | _, [] => []
  | C, e :: es => event C j e :: trace cap j (step cap C e) es

theorem trace_append (cap : Nat) (j : Fin (w - 1)) (C : Line hw)
    (a b : List (Fin (w - 1))) :
    trace cap j C (a ++ b) = trace cap j C a ++ trace cap j (run cap C a) b := by
  induction a generalizing C with
  | nil => rfl
  | cons e a ih => simp only [List.cons_append, trace, run, ih]

theorem trace_run (cap : Nat) (j : Fin (w - 1)) (hj : j.val ≠ 0)
    (C : Line hw) (es : List (Fin (w - 1))) :
    (latch C j).run (trace cap j C es) = latch (run cap C es) j := by
  induction es generalizing C with
  | nil => rfl
  | cons e es ih =>
    simp only [trace, Latch.run, run]
    rw [← latch_row cap C j e hj]
    exact ih (step cap C e)

theorem event_mark (C : Line hw) (j e : Fin (w - 1)) (hj : j.val ≠ 0) :
    (latch C j).mark (event C j e) = if e = j ∧ emit C e = true then 1 else 0 := by
  by_cases he : e = j
  · subst e
    simp [latch, event, Latch.mark, emit, hj]
    rfl
  · by_cases hi : e.val + 1 = j.val ∧ emit C e = true <;>
      simp [event, he, hi, Latch.mark]

/-- The abstract latch's marks are exactly the actual higher-port carry
consumptions on this same physical internal-edge word. -/
theorem trace_hits (cap : Nat) (j : Fin (w - 1)) (hj : j.val ≠ 0)
    (C : Line hw) (es : List (Fin (w - 1))) :
    (latch C j).hits (trace cap j C es) = services cap j C es := by
  induction es generalizing C with
  | nil => rfl
  | cons e es ih =>
    simp only [trace, Latch.hits, services]
    rw [event_mark C j e hj, ← latch_row cap C j e hj, ih]

theorem event_arrival_iff (C : Line hw) (prev j e : Fin (w - 1))
    (hprev : prev.val + 1 = j.val) :
    event C j e = .arrival ↔ e = prev ∧ emit C e = true := by
  by_cases he : e = j
  · subst e
    have hp : j ≠ prev := by intro he; have := congrArg Fin.val he; omega
    simp [event, hp]
  · have heq : e.val + 1 = j.val ↔ e = prev := by
      constructor
      · intro h; exact Fin.ext (by omega)
      · intro h; subst e; exact hprev
    simp [event, he, heq]

/-- Every incoming latch arrival is the lower port's literal consumption.
No queued copies are inferred from a pending Boolean carry. -/
theorem trace_arrivals (cap : Nat) (prev j : Fin (w - 1))
    (hprev : prev.val + 1 = j.val) (C : Line hw) (es : List (Fin (w - 1))) :
    (trace cap j C es).count .arrival = services cap prev C es := by
  induction es generalizing C with
  | nil => rfl
  | cons e es ih =>
    simp only [trace, services]
    by_cases ha : event C j e = .arrival
    · have hp := (event_arrival_iff C prev j e hprev).mp ha
      rw [ha, List.count_cons_self, if_pos hp, ih]
      omega
    · have hp : ¬ (e = prev ∧ emit C e = true) := by
        intro h
        exact ha ((event_arrival_iff C prev j e hprev).mpr h)
      rw [List.count_cons_of_ne ha, if_neg hp, ih]
      simp

theorem trace_has_service (cap : Nat) (j : Fin (w - 1))
    (C : Line hw) (es : List (Fin (w - 1))) (hj : j ∈ es) :
    LatchEvent.service ∈ trace cap j C es := by
  induction es generalizing C with
  | nil => simp at hj
  | cons e es ih =>
    rcases List.mem_cons.mp hj with he | ht
    · subst e
      simp [trace, event]
    · exact List.mem_cons_of_mem _ (ih (step cap C e) ht)

/-- The source-faithful finite service lemma, with arbitrary interleaving in
both word segments and no assumption on old internal bits or carries. -/
theorem two_lower_then_real_service (cap : Nat) (prev j : Fin (w - 1))
    (hprev : prev.val + 1 = j.val) (C : Line hw)
    (before after : List (Fin (w - 1)))
    (hlower : 2 ≤ services cap prev C before) (hservice : j ∈ after) :
    0 < services cap j C (before ++ after) := by
  have hj : j.val ≠ 0 := by omega
  have h := (latch C j).two_arrivals_then_service
    (trace cap j C before) (trace cap j (run cap C before) after)
    (by rw [trace_arrivals cap prev j hprev]; exact hlower)
    (trace_has_service cap j (run cap C before) after hservice)
  rw [← trace_append, trace_hits cap j hj] at h
  exact h

end Line
end BirthWaitClockMass

#print axioms BirthWaitClockMass.Line.row_registers
#print axioms BirthWaitClockMass.Line.latch_row
#print axioms BirthWaitClockMass.Line.two_lower_then_real_service
