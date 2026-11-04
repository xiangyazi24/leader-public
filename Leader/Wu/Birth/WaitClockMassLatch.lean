import Leader.Wu.Birth.WaitClockMassRows

/-!
# Two arrivals and a real carry service

The latch retains Boolean coalescence.  Intervening arrivals and outgoing
services are arbitrary.  The finite-word lemma therefore permits every
internal-port interleaving; an outgoing service that consumes the carry early
already supplies the required event.
-/

namespace BirthWaitClockMass

set_option autoImplicit false
set_option Elab.async false

inductive LatchEvent where
  | arrival
  | service
  | idle
  deriving DecidableEq, Repr

structure Latch where
  h : Bool
  carry : Bool
  deriving DecidableEq, Repr

def Latch.step (s : Latch) : LatchEvent → Latch
  | .arrival => ⟨!s.h, s.carry || s.h⟩
  | .service => ⟨s.h, false⟩
  | .idle => s

def Latch.mark (s : Latch) : LatchEvent → Nat
  | .service => if s.carry then 1 else 0
  | _ => 0

def Latch.run : Latch → List LatchEvent → Latch
  | s, [] => s
  | s, e :: es => Latch.run (s.step e) es

def Latch.hits : Latch → List LatchEvent → Nat
  | _, [] => 0
  | s, e :: es => s.mark e + Latch.hits (s.step e) es

theorem Latch.run_append (s : Latch) (a b : List LatchEvent) :
    s.run (a ++ b) = (s.run a).run b := by
  induction a generalizing s with
  | nil => rfl
  | cons e a ih => simpa only [List.cons_append, Latch.run] using ih (s.step e)

theorem Latch.hits_append (s : Latch) (a b : List LatchEvent) :
    s.hits (a ++ b) = s.hits a + (s.run a).hits b := by
  induction a generalizing s with
  | nil => simp [Latch.hits, Latch.run]
  | cons e a ih =>
    simp only [List.cons_append, Latch.hits, Latch.run, ih, Nat.add_assoc]

/-- With no consumption and an empty final carry, at most one arrival could
have occurred.  This equality keeps the initial and final physical bit. -/
theorem Latch.no_hit_final_empty (s : Latch) (es : List LatchEvent)
    (hh : s.hits es = 0) (hc : (s.run es).carry = false) :
    s.carry = false ∧
      es.count .arrival + (if s.h then 1 else 0) =
        (if (s.run es).h then 1 else 0) := by
  induction es generalizing s with
  | nil => simp only [Latch.run, List.count_nil] at hc ⊢; exact ⟨hc, Nat.zero_add _⟩
  | cons e es ih =>
    have ht : (s.step e).hits es = 0 := by simp only [Latch.hits] at hh; omega
    have h := ih (s.step e) ht hc
    cases e with
    | idle =>
      simp [Latch.step, Latch.run] at h ⊢
      exact h
    | service =>
      have hs : s.carry = false := by
        cases he : s.carry
        · rfl
        · simp [Latch.hits, Latch.mark, he] at hh
      simp [Latch.step, Latch.run, hs] at h ⊢
      exact h
    | arrival =>
      have hs : s.carry = false ∧ s.h = false := by
        cases he : s.carry <;> cases hb : s.h <;>
          simp_all [Latch.step]
      have hb := h.2
      simp only [Latch.step, hs.2, Bool.not_false] at hb
      refine ⟨hs.1, ?_⟩
      simp only [List.count_cons_self, Latch.run, hs.2, Bool.false_eq_true, if_false,
        Nat.add_zero]
      simpa [Latch.step, hs.2] using hb

theorem Latch.two_arrivals_ready_or_hit (s : Latch) (es : List LatchEvent)
    (ha : 2 ≤ es.count .arrival) :
    (s.run es).carry = true ∨ 0 < s.hits es := by
  cases hc : (s.run es).carry
  · right
    by_cases hn : s.hits es = 0
    · have h := (s.no_hit_final_empty es hn hc).2
      cases hb : (s.run es).h <;> cases hb0 : s.h <;> simp [hb, hb0] at h <;> omega
    · omega
  · exact Or.inl rfl

theorem Latch.carry_survives_or_hit (s : Latch) (es : List LatchEvent)
    (hc : s.carry = true) : (s.run es).carry = true ∨ 0 < s.hits es := by
  cases hf : (s.run es).carry
  · right
    by_cases hn : s.hits es = 0
    · have h := (s.no_hit_final_empty es hn hf).1
      simp [hc] at h
    · omega
  · exact Or.inl rfl

theorem Latch.service_after_ready (s : Latch) (es : List LatchEvent)
    (hc : s.carry = true) (hs : LatchEvent.service ∈ es) : 0 < s.hits es := by
  induction es generalizing s with
  | nil => simp at hs
  | cons e es ih =>
    cases e with
    | service => simp only [Latch.hits, Latch.mark, hc, if_true]; omega
    | arrival =>
      apply Nat.lt_of_lt_of_le (ih (s.step .arrival) (by simp [Latch.step, hc])
        (by simpa using hs))
      simp [Latch.hits, Latch.mark]
    | idle =>
      simpa [Latch.hits, Latch.mark, Latch.step] using ih s hc (by simpa using hs)

/-- Both lower arrivals and the higher outgoing service are actual letters.
Extra arrivals may coalesce and extra services may consume early. -/
theorem Latch.two_arrivals_then_service (s : Latch) (first last : List LatchEvent)
    (ha : 2 ≤ first.count .arrival) (hs : LatchEvent.service ∈ last) :
    0 < s.hits (first ++ last) := by
  rw [Latch.hits_append]
  rcases s.two_arrivals_ready_or_hit first ha with hc | hh
  · have h := (s.run first).service_after_ready last hc hs
    omega
  · omega

end BirthWaitClockMass

#print axioms BirthWaitClockMass.Latch.no_hit_final_empty
#print axioms BirthWaitClockMass.Latch.two_arrivals_then_service
