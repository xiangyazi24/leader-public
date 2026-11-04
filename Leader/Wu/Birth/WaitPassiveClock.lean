import Leader.Wu.Birth.WaitClockRows
import Leader.Wu.Birth.WaitClockPotential

namespace BirthWaitPassive

open PPLL PPLLRepair BirthWaitClockAudit

set_option autoImplicit false
set_option Elab.async false

variable {psi : Nat}

/-- The complete WAIT projection, also retaining the unchanged ruler bit and phase. -/
structure Clock (psi : Nat) where
  label : Fin psi
  h : Bool
  carry : Bool
  reset : Bool
  count : Nat
  wait : Bool
  bit : Bool
  phase : Bool
  deriving DecidableEq, Repr

def clock (u : AgentState psi) : Clock psi :=
  ⟨u.label, u.h_field, u.carry, u.reset, u.count, u.wait, u.bit, u.phase⟩

def Boundary (hpsi : 0 < psi) (u : AgentState psi) : Prop :=
  ((u.label = ⟨0,hpsi⟩ ∨ u.label = ⟨psi-1,by omega⟩) → u.carry = false) ∧
  (u.label = ⟨psi-1,by omega⟩ → u.reset = false)

def Below (hpsi : 0 < psi) (kappa : Nat) (u : AgentState psi) : Prop :=
  u.label = ⟨psi-1,by omega⟩ → u.count < kappa

def Cap (hpsi : 0 < psi) (kappa : Nat) (u : AgentState psi) : Prop :=
  u.label = ⟨psi-1,by omega⟩ ∧ u.count = kappa

private theorem prepare_clock_congr (hpsi : 0 < psi)
    (l r l' r' : AgentState psi) (hl : clock l = clock l') (hr : clock r = clock r') :
    let q := waitSaturatedPrepare hpsi l r
    let q' := waitSaturatedPrepare hpsi l' r'
    clock q.1 = clock q'.1 ∧ clock q.2 = clock q'.2 := by
  cases l; cases r; cases l'; cases r'
  simp only [clock, Clock.mk.injEq] at hl hr
  rcases hl with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  rcases hr with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  unfold waitSaturatedPrepare
  repeat (first | exact ⟨rfl,rfl⟩ | split <;> try dsimp only)

private theorem carry_clock_congr (hpsi : 0 < psi) (kappa : Nat)
    (l r l' r' : AgentState psi) (hl : clock l = clock l') (hr : clock r = clock r') :
    let q := waitSaturatedCarry hpsi kappa l r
    let q' := waitSaturatedCarry hpsi kappa l' r'
    clock q.1 = clock q'.1 ∧ clock q.2 = clock q'.2 := by
  cases l; cases r; cases l'; cases r'
  simp only [clock, Clock.mk.injEq] at hl hr
  rcases hl with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  rcases hr with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  unfold waitSaturatedCarry
  repeat (first | exact ⟨rfl,rfl⟩ | split <;> try dsimp only)

private theorem reset_clock_congr (hpsi : 0 < psi)
    (l r l' r' : AgentState psi) (hl : clock l = clock l') (hr : clock r = clock r') :
    let q := waitSaturatedReset hpsi l r
    let q' := waitSaturatedReset hpsi l' r'
    clock q.1 = clock q'.1 ∧ clock q.2 = clock q'.2 := by
  cases l; cases r; cases l'; cases r'
  simp only [clock, Clock.mk.injEq] at hl hr
  rcases hl with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  rcases hr with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  unfold waitSaturatedReset
  repeat (first | exact ⟨rfl,rfl⟩ | split <;> try dsimp only)

private theorem finish_clock_congr (hpsi : 0 < psi) (kappa : Nat)
    (l r l' r' : AgentState psi) (hl : clock l = clock l') (hr : clock r = clock r') :
    let q := waitSaturatedFinish hpsi kappa l r
    let q' := waitSaturatedFinish hpsi kappa l' r'
    clock q.1 = clock q'.1 ∧ clock q.2 = clock q'.2 := by
  cases l; cases r; cases l'; cases r'
  simp only [clock, Clock.mk.injEq] at hl hr
  rcases hl with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  rcases hr with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  unfold waitSaturatedFinish
  repeat (first | exact ⟨rfl,rfl⟩ | split <;> try dsimp only)

/-- Literal WAIT depends only on the observed fields, for arbitrary raw cells. -/
theorem wait_clock_congr (hpsi : 0 < psi) (kappa : Nat)
    (l r l' r' : AgentState psi) (hl : clock l = clock l') (hr : clock r = clock r') :
    let q := waitSaturated hpsi kappa l r
    let q' := waitSaturated hpsi kappa l' r'
    clock q.1 = clock q'.1 ∧ clock q.2 = clock q'.2 := by
  have hp := prepare_clock_congr hpsi l r l' r' hl hr
  have hc := carry_clock_congr hpsi kappa _ _ _ _ hp.1 hp.2
  have hs := reset_clock_congr hpsi _ _ _ _ hc.1 hc.2
  exact finish_clock_congr hpsi kappa _ _ _ _ hs.1 hs.2

private theorem prepare_static (hpsi : 0 < psi) (l r : AgentState psi) :
    let q := waitSaturatedPrepare hpsi l r
    q.1.label = l.label ∧ q.2.label = r.label ∧
    q.1.wait = l.wait ∧ q.2.wait = r.wait ∧ q.1.count = l.count ∧ q.2.count = r.count := by
  unfold waitSaturatedPrepare
  repeat (first | exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ | split <;> try dsimp only)

private theorem carry_static (hpsi : 0 < psi) (kappa : Nat) (l r : AgentState psi) :
    let q := waitSaturatedCarry hpsi kappa l r
    q.1.label = l.label ∧ q.2.label = r.label ∧
    q.1.wait = l.wait ∧ q.2.wait = r.wait ∧ q.1.count = l.count := by
  unfold waitSaturatedCarry
  repeat (first | exact ⟨rfl,rfl,rfl,rfl,rfl⟩ | split <;> try dsimp only)

private theorem reset_static (hpsi : 0 < psi) (l r : AgentState psi) :
    let q := waitSaturatedReset hpsi l r
    q.1.label = l.label ∧ q.2.label = r.label ∧
    q.1.wait = l.wait ∧ q.2.wait = r.wait ∧ q.1.count = l.count ∧ q.2.count = r.count := by
  unfold waitSaturatedReset
  repeat (first | exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ | split <;> try dsimp only)

private theorem finish_static (hpsi : 0 < psi) (kappa : Nat) (l r : AgentState psi) :
    let q := waitSaturatedFinish hpsi kappa l r
    q.1.label = l.label ∧ q.2.label = r.label ∧
    q.1.count = l.count ∧ q.2.count = r.count := by
  unfold waitSaturatedFinish
  repeat (first | exact ⟨rfl,rfl,rfl,rfl⟩ | split <;> try dsimp only)

/-- Labels and the initiator count are fixed by every WAIT row. -/
theorem wait_static (hpsi : 0 < psi) (kappa : Nat) (l r : AgentState psi) :
    let q := waitSaturated hpsi kappa l r
    q.1.label = l.label ∧ q.2.label = r.label ∧ q.1.count = l.count := by
  have hp := prepare_static hpsi l r
  have hc := carry_static hpsi kappa (waitSaturatedPrepare hpsi l r).1
    (waitSaturatedPrepare hpsi l r).2
  have hr := reset_static hpsi
    (waitSaturatedCarry hpsi kappa (waitSaturatedPrepare hpsi l r).1
      (waitSaturatedPrepare hpsi l r).2).1
    (waitSaturatedCarry hpsi kappa (waitSaturatedPrepare hpsi l r).1
      (waitSaturatedPrepare hpsi l r).2).2
  have hf := finish_static hpsi kappa
    (waitSaturatedReset hpsi
      (waitSaturatedCarry hpsi kappa (waitSaturatedPrepare hpsi l r).1
        (waitSaturatedPrepare hpsi l r).2).1
      (waitSaturatedCarry hpsi kappa (waitSaturatedPrepare hpsi l r).1
        (waitSaturatedPrepare hpsi l r).2).2).1
    (waitSaturatedReset hpsi
      (waitSaturatedCarry hpsi kappa (waitSaturatedPrepare hpsi l r).1
        (waitSaturatedPrepare hpsi l r).2).1
      (waitSaturatedCarry hpsi kappa (waitSaturatedPrepare hpsi l r).1
        (waitSaturatedPrepare hpsi l r).2).2).2
  exact ⟨hf.1.trans (hr.1.trans (hc.1.trans hp.1)),
    hf.2.1.trans (hr.2.1.trans (hc.2.1.trans hp.2.1)),
    hf.2.2.1.trans (hr.2.2.2.2.1.trans (hc.2.2.2.2.trans hp.2.2.2.2.1))⟩

/-- All WAIT bits remain armed whenever the actual post-WAIT terminal is below cap. -/
theorem wait_armed (hpsi : 0 < psi) (kappa : Nat) (l r : AgentState psi)
    (hl : l.wait = true) (hr : r.wait = true)
    (hbelow : Below hpsi kappa (waitSaturated hpsi kappa l r).2) :
    let q := waitSaturated hpsi kappa l r
    q.1.wait = true ∧ q.2.wait = true := by
  let p := waitSaturatedPrepare hpsi l r
  let c := waitSaturatedCarry hpsi kappa p.1 p.2
  let s := waitSaturatedReset hpsi c.1 c.2
  have hp := prepare_static hpsi l r
  have hc := carry_static hpsi kappa p.1 p.2
  have hs := reset_static hpsi c.1 c.2
  have hf := finish_static hpsi kappa s.1 s.2
  have hwl : s.1.wait = true := hs.2.2.1.trans (hc.2.2.1.trans (hp.2.2.1.trans hl))
  have hwr : s.2.wait = true := hs.2.2.2.1.trans (hc.2.2.2.1.trans (hp.2.2.2.1.trans hr))
  have hnc : ¬ (s.2.label = ⟨psi-1,by omega⟩ ∧ s.2.count = kappa) := by
    rintro ⟨ht,hk⟩
    have he : (waitSaturated hpsi kappa l r).2.label = s.2.label := hf.2.1
    have hv : (waitSaturated hpsi kappa l r).2.count = s.2.count := hf.2.2.2
    have hb := hbelow (he.trans ht)
    rw [hv,hk] at hb
    omega
  change let q := waitSaturatedFinish hpsi kappa s.1 s.2
    q.1.wait = true ∧ q.2.wait = true
  simp [waitSaturatedFinish, hnc, hwl, hwr]

private theorem prepare_carry_boundary (hpsi : 0 < psi) (hsize : 2 ≤ psi)
    (kappa : Nat) (l r : AgentState psi)
    (hl : Boundary hpsi l) (hr : Boundary hpsi r) :
    let p := waitSaturatedPrepare hpsi l r
    let q := waitSaturatedCarry hpsi kappa p.1 p.2
    Boundary hpsi q.1 ∧ Boundary hpsi q.2 := by
  have ht0 : (⟨psi-1,by omega⟩ : Fin psi) ≠ ⟨0,hpsi⟩ := by
    intro h
    have hv : psi-1 = 0 := congrArg Fin.val h
    omega
  by_cases hl0 : l.label = ⟨0,hpsi⟩ <;>
    by_cases hr0 : r.label = ⟨0,hpsi⟩ <;>
    by_cases hlt : l.label = ⟨psi-1,by omega⟩ <;>
    by_cases hrt : r.label = ⟨psi-1,by omega⟩ <;>
    cases hh : l.h_field <;> cases hc : l.carry <;> cases rh : r.h_field <;>
    simp_all [Boundary, waitSaturatedPrepare, waitSaturatedCarry]

private theorem reset_boundary (hpsi : 0 < psi) (l r : AgentState psi)
    (hl : Boundary hpsi l) (hr : Boundary hpsi r) :
    let q := waitSaturatedReset hpsi l r
    Boundary hpsi q.1 ∧ Boundary hpsi q.2 := by
  unfold waitSaturatedReset
  split <;> try dsimp only
  · split <;> simp_all [Boundary]
  · exact ⟨hl,hr⟩

private theorem finish_boundary (hpsi : 0 < psi) (kappa : Nat)
    (l r : AgentState psi) (hl : Boundary hpsi l) (hr : Boundary hpsi r) :
    let q := waitSaturatedFinish hpsi kappa l r
    Boundary hpsi q.1 ∧ Boundary hpsi q.2 := by
  unfold waitSaturatedFinish
  split <;> try dsimp only
  all_goals split <;> simpa only [Boundary] using And.intro hl hr

/-- Root and terminal carries, and terminal reset, are preserved by the
actual composed WAIT row. No label-adjacency or count premise is used. -/
theorem wait_boundary (hpsi : 0 < psi) (hsize : 2 ≤ psi) (kappa : Nat)
    (l r : AgentState psi) (hl : Boundary hpsi l) (hr : Boundary hpsi r) :
    let q := waitSaturated hpsi kappa l r
    Boundary hpsi q.1 ∧ Boundary hpsi q.2 := by
  have hc := prepare_carry_boundary hpsi hsize kappa l r hl hr
  have hr := reset_boundary hpsi _ _ hc.1 hc.2
  exact finish_boundary hpsi kappa _ _ hr.1 hr.2

/-- At a bounded output either the actual terminal cap is present or its
strict pre-cap condition holds. This is a current row test. -/
theorem cap_or_below (hpsi : 0 < psi) (kappa : Nat) (u : AgentState psi)
    (hu : u.count ≤ kappa) : Cap hpsi kappa u ∨ Below hpsi kappa u := by
  by_cases ht : u.label = ⟨psi-1,by omega⟩
  · by_cases hv : u.count = kappa
    · exact Or.inl ⟨ht,hv⟩
    · exact Or.inr (fun _ => by omega)
  · exact Or.inr (fun h => (ht h).elim)

end BirthWaitPassive
