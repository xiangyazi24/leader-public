import Leader.Wu.Protocol.Algorithm

set_option autoImplicit false
set_option Elab.async false

namespace ZZWaitStaged

open PPLL

/-- WAIT stage 1: the responder's label-zero initialization. -/
def waitR0 {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  (l,
   if r.label = ⟨0, hψ⟩ then
     { r with reset := true, h_field := false }
   else r)

/-- WAIT stage 2: the initiator's label-zero counter preparation. -/
def waitL0 {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  ((if l.label = ⟨0, hψ⟩ then
      if l.h_field = true then
        { l with h_field := false, carry := true }
      else
        { l with h_field := true }
    else l),
   r)

/-- WAIT stage 3: single-use carry movement. -/
def waitCarry {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  if l.carry = true then
    if r.h_field = true then
      if r.label = ⟨ψ - 1, by omega⟩ then
        ({ l with carry := false },
         { r with h_field := false, count := r.count + 1 })
      else
        ({ l with carry := false },
         { r with h_field := false, carry := true })
    else
      ({ l with carry := false }, { r with h_field := true })
  else
    (l, r)

/-- WAIT stage 4: reset movement and counter-bit clearing. -/
def waitReset {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  if l.reset = true then
    let r :=
      if r.label ≠ ⟨ψ - 1, by omega⟩ then
        { r with reset := true }
      else r
    ({ l with reset := false }, { r with h_field := false })
  else
    (l, r)

/-- WAIT stage 5: release the terminal responder at count κ. -/
def waitCount {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  (l,
   if r.label = ⟨ψ - 1, by omega⟩ ∧ r.count = κ then
     { r with wait := false }
   else r)

/-- WAIT stage 6: propagate the released wait marker. -/
def waitProp {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  if r.wait = false ∧ l.label ≠ ⟨ψ - 1, by omega⟩ then
    ({ l with wait := false }, { r with wait := true })
  else
    (l, r)

/-- Matcher-free staged presentation of Algorithm 3. -/
def waitStaged {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) : AgentState ψ × AgentState ψ :=
  let q := waitR0 hψ l r
  let q := waitL0 hψ q.1 q.2
  let q := waitCarry hψ q.1 q.2
  let q := waitReset hψ q.1 q.2
  let q := waitCount hψ κ q.1 q.2
  waitProp hψ q.1 q.2

/-- The staged presentation is definitionally equal to the literal WAIT. -/
theorem wait_eq_staged {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    wait hψ κ l r = waitStaged hψ κ l r := by
  rfl

/-- The eight protocol fields that WAIT frames on both endpoints. -/
abbrev trapProj {ψ : Nat} (u : AgentState ψ) :=
  (u.leader, u.label, u.bit, u.state,
   u.path, u.path2, u.path3, u.write)

theorem waitR0_proj {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (trapProj (waitR0 hψ l r).1, trapProj (waitR0 hψ l r).2) =
      (trapProj l, trapProj r) := by
  unfold waitR0
  repeat (first | rfl | split)

theorem waitL0_proj {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (trapProj (waitL0 hψ l r).1, trapProj (waitL0 hψ l r).2) =
      (trapProj l, trapProj r) := by
  unfold waitL0
  repeat (first | rfl | split)

theorem waitCarry_proj {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (trapProj (waitCarry hψ l r).1, trapProj (waitCarry hψ l r).2) =
      (trapProj l, trapProj r) := by
  unfold waitCarry
  repeat (first | rfl | split)

theorem waitReset_proj {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (trapProj (waitReset hψ l r).1, trapProj (waitReset hψ l r).2) =
      (trapProj l, trapProj r) := by
  unfold waitReset
  repeat (first | rfl | split)

theorem waitCount_proj {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    (trapProj (waitCount hψ κ l r).1,
     trapProj (waitCount hψ κ l r).2) =
      (trapProj l, trapProj r) := by
  unfold waitCount
  repeat (first | rfl | split)

theorem waitProp_proj {ψ : Nat} (hψ : ψ > 0)
    (l r : AgentState ψ) :
    (trapProj (waitProp hψ l r).1, trapProj (waitProp hψ l r).2) =
      (trapProj l, trapProj r) := by
  unfold waitProp
  repeat (first | rfl | split)

/-- WAIT frames all eight projected fields on both endpoints. -/
theorem wait_proj {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    (trapProj (wait hψ κ l r).1, trapProj (wait hψ κ l r).2) =
      (trapProj l, trapProj r) := by
  rw [wait_eq_staged]
  simp only [waitStaged]
  rw [waitProp_proj, waitCount_proj, waitReset_proj,
      waitCarry_proj, waitL0_proj, waitR0_proj]

theorem wait_leader {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    (wait hψ κ l r).1.leader = l.leader ∧
      (wait hψ κ l r).2.leader = r.leader := by
  have h := wait_proj hψ κ l r
  simp only [trapProj, Prod.mk.injEq] at h
  exact ⟨h.1.1, h.2.1⟩

theorem wait_label {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    (wait hψ κ l r).1.label = l.label ∧
      (wait hψ κ l r).2.label = r.label := by
  have h := wait_proj hψ κ l r
  simp only [trapProj, Prod.mk.injEq] at h
  exact ⟨h.1.2.1, h.2.2.1⟩

theorem wait_bit {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    (wait hψ κ l r).1.bit = l.bit ∧
      (wait hψ κ l r).2.bit = r.bit := by
  have h := wait_proj hψ κ l r
  simp only [trapProj, Prod.mk.injEq] at h
  exact ⟨h.1.2.2.1, h.2.2.2.1⟩

theorem wait_state {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    (wait hψ κ l r).1.state = l.state ∧
      (wait hψ κ l r).2.state = r.state := by
  have h := wait_proj hψ κ l r
  simp only [trapProj, Prod.mk.injEq] at h
  exact ⟨h.1.2.2.2.1, h.2.2.2.2.1⟩

theorem wait_path {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    (wait hψ κ l r).1.path = l.path ∧
      (wait hψ κ l r).2.path = r.path := by
  have h := wait_proj hψ κ l r
  simp only [trapProj, Prod.mk.injEq] at h
  exact ⟨h.1.2.2.2.2.1, h.2.2.2.2.2.1⟩

theorem wait_path2 {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    (wait hψ κ l r).1.path2 = l.path2 ∧
      (wait hψ κ l r).2.path2 = r.path2 := by
  have h := wait_proj hψ κ l r
  simp only [trapProj, Prod.mk.injEq] at h
  exact ⟨h.1.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

theorem wait_path3 {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    (wait hψ κ l r).1.path3 = l.path3 ∧
      (wait hψ κ l r).2.path3 = r.path3 := by
  have h := wait_proj hψ κ l r
  simp only [trapProj, Prod.mk.injEq] at h
  exact ⟨h.1.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩

theorem wait_write {ψ : Nat} (hψ : ψ > 0) (κ : Nat)
    (l r : AgentState ψ) :
    (wait hψ κ l r).1.write = l.write ∧
      (wait hψ κ l r).2.write = r.write := by
  have h := wait_proj hψ κ l r
  simp only [trapProj, Prod.mk.injEq] at h
  exact ⟨h.1.2.2.2.2.2.2.2, h.2.2.2.2.2.2.2.2⟩

end ZZWaitStaged

#print axioms ZZWaitStaged.wait_eq_staged
#print axioms ZZWaitStaged.waitR0_proj
#print axioms ZZWaitStaged.waitL0_proj
#print axioms ZZWaitStaged.waitCarry_proj
#print axioms ZZWaitStaged.waitReset_proj
#print axioms ZZWaitStaged.waitCount_proj
#print axioms ZZWaitStaged.waitProp_proj
#print axioms ZZWaitStaged.wait_proj
#print axioms ZZWaitStaged.wait_leader
#print axioms ZZWaitStaged.wait_label
#print axioms ZZWaitStaged.wait_bit
#print axioms ZZWaitStaged.wait_state
#print axioms ZZWaitStaged.wait_path
#print axioms ZZWaitStaged.wait_path2
#print axioms ZZWaitStaged.wait_path3
#print axioms ZZWaitStaged.wait_write
