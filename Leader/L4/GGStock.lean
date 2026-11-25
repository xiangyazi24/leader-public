import Init.Data.List.FinRange
import Lean.Elab.Tactic.Omega

namespace L4.GGStock

/-- Proof-side label class relative to the initial half-open arc of span s.
An exterior label covers both old exterior residents and later mints. -/
inductive Origin (s : Nat)
  | initial (offset : Fin s)
  | exterior
  deriving DecidableEq, Repr

/-- The moving right boundary may expose an exterior resident, but it is
quarantined immediately upstream of k. Natural coordinates are clockwise
lifts on a stopped interval, not protocol fields. -/
def Quarantined {s : Nat} (label : Origin s) (site k : Nat) : Prop :=
  label = .exterior → site + 1 = k

/-- A nonterminal paid advance of j consumes stock at its old predecessor.
The exact physical observer is required to prove the quarantine hypothesis. -/
structure PaidJ (s : Nat) where
  j : Nat
  k : Nat
  donor : Nat
  label : Origin s
  preceding : donor + 1 = j
  distinct : j < k
  quarantine : Quarantined label donor k

/-- An exterior label cannot be the donor for a nonterminal advance of j:
its only allowed in-arc position has successor k, not j. -/
theorem PaidJ.not_exterior {s : Nat} (v : PaidJ s) : v.label ≠ .exterior := by
  intro h
  have hk := v.quarantine h
  have hj := v.preceding
  have hlt := v.distinct
  omega

def PaidJ.initialLabel {s : Nat} (v : PaidJ s) : Fin s :=
  match hh : v.label with
  | .initial a => a
  | .exterior => False.elim (v.not_exterior hh)

theorem PaidJ.origin_eq_initial {s : Nat} (v : PaidJ s) :
    v.label = .initial v.initialLabel := by
  unfold PaidJ.initialLabel
  split
  · assumption
  · contradiction

/-- Logical proof-side stock credits: one original label per initially
occupied site, never reused. A physical proof needs to link distinct
literal consumptions to erasure in this list, not merely count bits in
the possibly growing current interval. -/
inductive CreditTrace {s : Nat} : List (Fin s) → List (PaidJ s) → Prop
  | nil (unused : List (Fin s)) : CreditTrace unused []
  | pay {unused : List (Fin s)} {tail : List (PaidJ s)}
      (v : PaidJ s) (available : v.initialLabel ∈ unused)
      (later : CreditTrace (unused.erase v.initialLabel) tail) :
      CreditTrace unused (v :: tail)

theorem credit_count {s : Nat} {unused : List (Fin s)} {payments : List (PaidJ s)}
    (h : CreditTrace unused payments) : payments.length ≤ unused.length := by
  induction h with
  | nil => simp
  | @pay unused tail v available _ ih =>
    have helen : (unused.erase v.initialLabel).length = unused.length - 1 := by
      rw [List.length_erase]
      simp [available]
    have hpos := List.length_pos_of_mem available
    simp only [List.length_cons]
    omega

theorem paid_j_le_initial_span {s : Nat} {payments : List (PaidJ s)}
    (h : CreditTrace (List.finRange s) payments) : payments.length ≤ s := by
  simpa using credit_count h

/-- The old head of k moves one site, while its old resident stays put.
This is the precise newly exposed exterior position that the physical
projection can allow, rather than forbidding all exterior stock in [i,k). -/
theorem newly_exposed_resident_quarantined {s k : Nat} (label : Origin s) :
    Quarantined label k (k+1) := fun _ => rfl

/-- The two metric envelopes needed for the fixed virtual sink b+s. -/
theorem displacement_envelope {a b c i j : Nat}
    {payments : List (PaidJ (c-a))}
    (h : CreditTrace (List.finRange (c-a)) payments)
    (ha : a ≤ i) (hab : a ≤ b) (hbc : b ≤ c)
    (hj : j = b + payments.length) :
    j ≤ b + (c-a) ∧ j-i ≤ 2*(c-a) := by
  have hlen := paid_j_le_initial_span h
  omega

end L4.GGStock
