import Leader.Wu.ZeroDivisible.CheckRepair

/-!
# Local counter laws for the actual DISAPPEAR stage

These laws concern `PPLL.disappear`, the stage called by the unchanged R5
pipeline. The initiator carry is consumed even on dirty input. On clean
destination carry, weighted counter mass is conserved, with one extra unit
for a head-toss tick, unless the responder becomes terminal E.

This module does not assert a full-pipeline frame or a sweep theorem. Those
consumers must establish that intervening stages retain the counter fields
and that their chosen schedule supplies the stated carry conditions.
-/
namespace PPLLAstraR5TossCounter

open PPLL
set_option autoImplicit false

/-- Numerical value of a lottery bit. -/
def bitVal (b : Bool) : Nat := if b then 1 else 0

/-- The actual initiator condition for starting a lottery increment. -/
def HeadTick {ψ : Nat} (u : AgentState ψ) : Prop :=
  u.state = .toss ∧ u.label.val = 0

instance {ψ : Nat} (u : AgentState ψ) : Decidable (HeadTick u) :=
  inferInstanceAs (Decidable (u.state = .toss ∧ u.label.val = 0))

/-- Two adjacent bit positions, including their pending carry weights.
The initiator bit has weight one; its carry has weight two. -/
def counterMass {ψ : Nat} (l r : AgentState ψ) : Nat :=
  bitVal l.p + 2 * bitVal r.p + 2 * bitVal l.p_carry + 4 * bitVal r.p_carry

/-- Exact source factorization when the responder is not a physical head.
Only the initiator head-toss preparation can precede carry consumption. -/
theorem disappear_internal_eq {ψ : Nat} (hp : 0 < ψ) (l r : AgentState ψ)
    (hr : r.label.val ≠ 0) :
    disappear hp l r = disappearCarry hp
      (if HeadTick l then
        if l.p = true then { l with p := false, p_carry := true }
        else { l with p := true }
       else l) r := by
  have hn : r.label ≠ ⟨0, hp⟩ := by
    intro he
    exact hr (congrArg Fin.val he)
  by_cases ht : l.state = .toss ∧ l.label.val = 0 <;>
    simp [disappear_eq_staged, disappearStaged, disappearStartR,
      disappearStartL, hn, HeadTick, Fin.ext_iff, ht]

private theorem carry_cleared {ψ : Nat} (hp : 0 < ψ) (l r : AgentState ψ) :
    (disappearCarry hp l r).1.p_carry = false := by
  cases hl : l.p_carry <;> cases hr : r.p <;>
    simp [disappearCarry, hl, hr]
  split <;> rfl

/-- Every actual DISAPPEAR row clears its initiator carry, with no cleanliness,
state, label, token, leader, or responder-field assumptions. This is the
local dirty-carry flush fact, not yet a whole-sweep assertion. -/
theorem disappear_initiator_carry_cleared {ψ : Nat} (hp : 0 < ψ)
    (l r : AgentState ψ) : (disappear hp l r).1.p_carry = false := by
  rw [disappear_eq_staged]
  exact carry_cleared hp _ _

/-- On an internal orientation, DISAPPEAR retains both labels, main paths and
tokens, and the initiator main state. Its sole possible responder state
change is terminal elimination. All lottery fields may initially be dirty. -/
theorem disappear_internal_frame {ψ : Nat} (hp : 0 < ψ) (l r : AgentState ψ)
    (hr : r.label.val ≠ 0) :
    let z := disappear hp l r
    z.1.label = l.label ∧ z.2.label = r.label ∧
    z.1.path = l.path ∧ z.2.path = r.path ∧
    z.1.path2 = l.path2 ∧ z.2.path2 = r.path2 ∧
    z.1.state = l.state ∧
    (z.2.state = r.state ∨
      (r.label.val + 1 = ψ ∧ z.2.state = .eliminate_signal)) := by
  rw [disappear_internal_eq hp l r hr]
  by_cases ht : HeadTick l <;> cases hl : l.p <;>
    cases hc : l.p_carry <;> cases hb : r.p <;>
    by_cases he : r.label = ⟨ψ-1, by omega⟩ <;>
    simp [ht, hl, hc, hb, disappearCarry, he]
  all_goals
    have hv := congrArg Fin.val he
    simp only at hv
    omega

/-- Exact weighted update of the actual stage. A head tick requires its old
carry clear; an ordinary initiator may have a pending carry. The responder
carry must be clear to exclude merging two pending carries. No other raw
fields are restricted. Terminal overflow is an explicit output alternative. -/
theorem disappear_counter_step {ψ : Nat} (hp : 0 < ψ) (l r : AgentState ψ)
    (hr : r.label.val ≠ 0) (hclean : HeadTick l → l.p_carry = false)
    (hrc : r.p_carry = false) :
    let z := disappear hp l r
    (r.label.val + 1 = ψ ∧ z.2.state = .eliminate_signal) ∨
      counterMass z.1 z.2 = counterMass l r + (if HeadTick l then 1 else 0) := by
  rw [disappear_internal_eq hp l r hr]
  by_cases ht : HeadTick l
  · have hc := hclean ht
    cases hl : l.p <;> cases hb : r.p <;>
      by_cases he : r.label = ⟨ψ-1, by omega⟩ <;>
      simp [ht, hl, hc, hb, hrc, disappearCarry, he, counterMass, bitVal]
    have hv := congrArg Fin.val he
    simp only at hv
    omega
  · cases hl : l.p <;> cases hc : l.p_carry <;> cases hb : r.p <;>
      by_cases he : r.label = ⟨ψ-1, by omega⟩ <;>
      simp [ht, hl, hc, hb, hrc, disappearCarry, he, counterMass, bitVal]
    all_goals
      have hv := congrArg Fin.val he
      simp only at hv
      omega

/-- At a non-head terminal, an arbitrary old terminal carry is retained and
does not participate in the bit update. Thus a forward sweep need not clear
that flag: the two bit positions absorb the incoming carry/tick, or the
actual responder state is elimination. Only a head tick requires a clean
initiator carry; ordinary incoming carries remain permitted. -/
theorem disappear_terminal_counter_step {ψ : Nat} (hp : 0 < ψ)
    (l r : AgentState ψ) (hr : r.label.val ≠ 0)
    (hrt : r.label.val + 1 = ψ) (hclean : HeadTick l → l.p_carry = false) :
    let z := disappear hp l r
    z.2.p_carry = r.p_carry ∧
      (z.2.state = .eliminate_signal ∨
        bitVal z.1.p + 2 * bitVal z.2.p =
          bitVal l.p + 2 * bitVal r.p + 2 * bitVal l.p_carry +
            (if HeadTick l then 1 else 0)) := by
  have he : r.label = ⟨ψ-1, by omega⟩ := by
    apply Fin.ext
    simp only
    omega
  rw [disappear_internal_eq hp l r hr]
  by_cases ht : HeadTick l
  · have hc := hclean ht
    cases hl : l.p <;> cases hb : r.p <;>
      simp [ht, hl, hc, hb, disappearCarry, he, bitVal]
  · cases hl : l.p <;> cases hc : l.p_carry <;> cases hb : r.p <;>
      simp [ht, hl, hc, hb, disappearCarry, he, bitVal]

#print axioms disappear_internal_eq
#print axioms disappear_initiator_carry_cleared
#print axioms disappear_internal_frame
#print axioms disappear_counter_step
#print axioms disappear_terminal_counter_step

end PPLLAstraR5TossCounter
