import Leader.Wu.Protocol.Repairs

/-!
# Actual reset-free WAIT latch rows

These equations use Prepare, Carry, Reset, and Finish in their source order.
The counted event is the carry consumed by the scheduled initiator.  Root
carry is prepared and consumed in the same row; higher carry requires its own
scheduled service.  No assertion here identifies a count hit with birth.
-/

namespace BirthWaitClockMass

open PPLL PPLLRepair

set_option autoImplicit false
set_option Elab.async false

structure Registers where
  h : Bool
  carry : Bool
  reset : Bool
  count : Nat
  deriving DecidableEq, Repr

def registers {w : Nat} (u : AgentState w) : Registers :=
  ⟨u.h_field, u.carry, u.reset, u.count⟩

def registerPair {w : Nat} (p : AgentState w × AgentState w) : Registers × Registers :=
  (registers p.1, registers p.2)

theorem finish_registers {w : Nat} (hw : 0 < w) (cap : Nat)
    (l r : AgentState w) :
    registerPair (waitSaturatedFinish hw cap l r) = (registers l, registers r) := by
  unfold waitSaturatedFinish
  split <;> dsimp only <;> split <;> rfl

theorem reset_registers_of_clear {w : Nat} (hw : 0 < w)
    (l r : AgentState w) (hl : l.reset = false) :
    registerPair (waitSaturatedReset hw l r) = (registers l, registers r) := by
  simp only [waitSaturatedReset, hl, Bool.false_eq_true, if_false]
  rfl

/-- The input pulse actually consumed by an internal WAIT edge.  For the
root, Prepare creates it exactly when the old root bit was one. -/
def pulse {w : Nat} (hw : 0 < w) (l : AgentState w) : Bool :=
  if l.label = ⟨0, hw⟩ then l.h_field else l.carry

def latchBit (a h : Bool) : Bool := if a then !h else h

/-- A complete literal internal-edge equation.  The responder is non-root,
both old reset flags are clear, and root carry is clear if this is a root
edge.  Arbitrary pre-existing responder carry is retained by Boolean OR. -/
theorem internal_register_row {w : Nat} (hw : 0 < w) (cap : Nat)
    (l r : AgentState w)
    (hr0 : r.label ≠ ⟨0, hw⟩)
    (hlz : l.reset = false) (hrz : r.reset = false)
    (hlc : l.label = ⟨0, hw⟩ → l.carry = false) :
    registerPair (waitSaturated hw cap l r) =
      (⟨if l.label = ⟨0, hw⟩ then !l.h_field else l.h_field,
          false, false, l.count⟩,
       ⟨latchBit (pulse hw l) r.h_field,
          r.carry || (pulse hw l && r.h_field &&
            decide (r.label ≠ ⟨w - 1, by omega⟩)),
          false,
          if pulse hw l = true ∧ r.h_field = true ∧
              r.label = ⟨w - 1, by omega⟩
          then min (r.count + 1) cap else r.count⟩) := by
  unfold waitSaturated
  rw [finish_registers]
  simp only [waitSaturatedPrepare, if_neg hr0]
  by_cases hl0 : l.label = ⟨0, hw⟩
  · have hcarry := hlc hl0
    cases hh : l.h_field <;> cases rh : r.h_field <;>
      cases rc : r.carry <;>
      by_cases ht : r.label = ⟨w - 1, by omega⟩ <;>
      simp [waitSaturatedCarry, waitSaturatedReset,
        pulse, latchBit, registers, satCountSucc,
        hl0, hlz, hrz, hcarry, hh, rh, rc, ht]
  · cases hh : l.h_field <;> cases lc : l.carry <;>
      cases rh : r.h_field <;> cases rc : r.carry <;>
      by_cases ht : r.label = ⟨w - 1, by omega⟩ <;>
      simp [waitSaturatedCarry, waitSaturatedReset,
        pulse, latchBit, registers, satCountSucc,
        hl0, hlz, hrz, hh, lc, rh, rc, ht]

theorem wait_label_frame {w : Nat} (hw : 0 < w) (cap : Nat)
    (l r : AgentState w) :
    (waitSaturated hw cap l r).1.label = l.label ∧
      (waitSaturated hw cap l r).2.label = r.label := by
  have finish (a b : AgentState w) :
      (waitSaturatedFinish hw cap a b).1.label = a.label ∧
        (waitSaturatedFinish hw cap a b).2.label = b.label := by
    unfold waitSaturatedFinish
    split <;> dsimp only <;> split <;> exact ⟨rfl, rfl⟩
  have reset (a b : AgentState w) :
      (waitSaturatedReset hw a b).1.label = a.label ∧
        (waitSaturatedReset hw a b).2.label = b.label := by
    unfold waitSaturatedReset
    split
    · split <;> exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  have carry (a b : AgentState w) :
      (waitSaturatedCarry hw cap a b).1.label = a.label ∧
        (waitSaturatedCarry hw cap a b).2.label = b.label := by
    unfold waitSaturatedCarry
    split
    · split
      · split <;> exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  have prep :
      (waitSaturatedPrepare hw l r).1.label = l.label ∧
        (waitSaturatedPrepare hw l r).2.label = r.label := by
    unfold waitSaturatedPrepare
    split <;> dsimp only <;> split
    all_goals first | exact ⟨rfl, rfl⟩ | split <;> exact ⟨rfl, rfl⟩
  unfold waitSaturated
  rw [(finish _ _).1, (finish _ _).2,
    (reset _ _).1, (reset _ _).2, (carry _ _).1, (carry _ _).2]
  exact prep

/-- A terminal exports no carry or reset.  Even Finish leaves its complete
initiator cell unchanged, for arbitrary state at the next group's root. -/
theorem terminal_outgoing_frame {w : Nat} (hw : 2 ≤ w) (cap : Nat)
    (l r : AgentState w) (hl : l.label = ⟨w - 1, by omega⟩)
    (hc : l.carry = false) (hz : l.reset = false) :
    (waitSaturated (by omega : 0 < w) cap l r).1 = l := by
  have hlval : l.label.val = w - 1 := by
    exact congrArg Fin.val hl
  have hl0 : l.label ≠ ⟨0, by omega⟩ := by
    intro he
    have hzval : l.label.val = 0 := by
      exact congrArg Fin.val he
    omega
  unfold waitSaturated
  simp only [waitSaturatedPrepare, if_neg hl0]
  generalize (if r.label = ⟨0, by omega⟩ then
    { r with reset := true, h_field := false } else r) = b
  simp only [waitSaturatedCarry, hc, Bool.false_eq_true, if_false,
    waitSaturatedReset, hz]
  unfold waitSaturatedFinish
  split <;> simp [hl]

end BirthWaitClockMass

#print axioms BirthWaitClockMass.internal_register_row
#print axioms BirthWaitClockMass.wait_label_frame
#print axioms BirthWaitClockMass.terminal_outgoing_frame
