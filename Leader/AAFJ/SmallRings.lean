import Leader.Core.Basic

/-!
# Exact small-ring branches for the AAFJ family

The journal `P_k` protocol is intended for rings with at least three agents,
and its literal extension has a two-leader trap at `n = 2`.  These two small
protocols make the exact-size family total without changing the `n ≥ 3`
transition.
-/

namespace AAFJSmallRings

set_option autoImplicit false

/-! ## The one-agent branch -/

/-- The one-agent protocol has one local state, which always outputs leader. -/
inductive OneState where
  | leader
  deriving DecidableEq

def oneStateValues : List OneState := [.leader]

theorem oneStateValues_complete (q : OneState) : q ∈ oneStateValues := by
  cases q
  simp [oneStateValues]

theorem oneStateValues_nodup : oneStateValues.Nodup := by
  decide

theorem oneStateValues_length : oneStateValues.length = 1 := by
  rfl

/-- Exact protocol for a one-agent ring. -/
def oneProtocol : PopulationProtocol where
  Q := OneState
  Y := Bool
  transition := fun _ _ => (.leader, .leader)
  output := fun _ => true

/-- Every one-agent configuration is Definition-1 safe. -/
theorem oneProtocol_isSafe
    (ring : DirectedRing 1)
    (C : oneProtocol.Configuration 1) :
    oneProtocol.IsSafe ring C (fun y => y) := by
  constructor
  · refine ⟨⟨0, by omega⟩, rfl, ?_⟩
    intro j _
    apply Fin.ext
    omega
  · intro C' _ i
    cases C' i <;> cases C i <;> rfl

/-! ## The two-agent branch -/

/-- Equal endpoint bits are oriented as leader/follower; unequal bits stay. -/
def twoTransition (u v : Bool) : Bool × Bool :=
  if u = v then (true, false) else (u, v)

/-- Exact protocol for a two-agent directed ring. -/
def twoProtocol : PopulationProtocol where
  Q := Bool
  Y := Bool
  transition := twoTransition
  output := id

def twoStateValues : List Bool := [false, true]

theorem twoStateValues_complete (q : Bool) : q ∈ twoStateValues := by
  cases q <;> simp [twoStateValues]

theorem twoStateValues_nodup : twoStateValues.Nodup := by
  decide

theorem twoStateValues_length : twoStateValues.length = 2 := by
  rfl

/-- The two bits differ, hence exactly one of them is a leader. -/
def TwoStable (C : twoProtocol.Configuration 2) : Prop :=
  C ⟨0, by omega⟩ ≠ C ⟨1, by omega⟩

private theorem fin_two_cases (i : Fin 2) :
    i = ⟨0, by omega⟩ ∨ i = ⟨1, by omega⟩ := by
  rcases i with ⟨i, hi⟩
  have h : i = 0 ∨ i = 1 := by omega
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Every interaction maps an arbitrary two-agent configuration into the
stable unequal-bit region. -/
theorem twoProtocol_step_stable
    (ring : DirectedRing 2)
    (C : twoProtocol.Configuration 2)
    (e : Fin 2) :
    TwoStable (twoProtocol.step ring C e) := by
  rcases fin_two_cases e with rfl | rfl
  · cases h0 : C 0 <;>
      cases h1 : C 1 <;>
      simp [TwoStable, PopulationProtocol.step, twoProtocol,
        twoTransition, DirectedRing.rightNeighbor, h0, h1]
  · cases h0 : C 0 <;>
      cases h1 : C 1 <;>
      simp [TwoStable, PopulationProtocol.step, twoProtocol,
        twoTransition, DirectedRing.rightNeighbor, h0, h1]

/-- A stable two-agent configuration is a fixed point of every interaction. -/
theorem twoProtocol_step_eq_of_stable
    (ring : DirectedRing 2)
    (C : twoProtocol.Configuration 2)
    (hC : TwoStable C)
    (e : Fin 2) :
    twoProtocol.step ring C e = C := by
  funext i
  rcases fin_two_cases e with rfl | rfl <;>
    rcases fin_two_cases i with rfl | rfl <;>
    cases h0 : C 0 <;>
    cases h1 : C 1 <;>
    simp [TwoStable, PopulationProtocol.step, twoProtocol,
      twoTransition, DirectedRing.rightNeighbor, h0, h1] at hC ⊢

/-- Reachability from a stable configuration is equality. -/
theorem twoProtocol_reachable_eq_of_stable
    (ring : DirectedRing 2)
    (C C' : twoProtocol.Configuration 2)
    (hC : TwoStable C)
    (hreach : twoProtocol.Reachable ring C C') :
    C' = C := by
  induction hreach with
  | refl => rfl
  | step C1 C2 h01 h12 ih =>
      rcases h12 with ⟨e, rfl⟩
      rw [ih, twoProtocol_step_eq_of_stable ring C hC e]

/-- The stable unequal-bit region is Definition-1 safe. -/
theorem twoProtocol_isSafe_of_stable
    (ring : DirectedRing 2)
    (C : twoProtocol.Configuration 2)
    (hC : TwoStable C) :
    twoProtocol.IsSafe ring C (fun y => y) := by
  constructor
  · cases h0 : C 0 <;>
      cases h1 : C 1 <;>
      simp [TwoStable, twoProtocol, h0, h1] at hC ⊢
  · intro C' hreach i
    rw [twoProtocol_reachable_eq_of_stable ring C C' hC hreach]

/-- One arbitrary interaction reaches Definition-1 safety on a two-agent
ring, independently of which directed edge is selected. -/
theorem twoProtocol_one_step_isSafe
    (ring : DirectedRing 2)
    (C : twoProtocol.Configuration 2)
    (e : Fin 2) :
    twoProtocol.IsSafe ring (twoProtocol.step ring C e) (fun y => y) :=
  twoProtocol_isSafe_of_stable ring _
    (twoProtocol_step_stable ring C e)

end AAFJSmallRings
