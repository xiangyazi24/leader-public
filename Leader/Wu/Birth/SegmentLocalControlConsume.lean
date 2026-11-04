import Leader.Wu.Birth.CheckPermitRepairLeaf

set_option autoImplicit false

/-! # Candidate repair R3: segment-local control signals (definition only, not adopted)

ERRATA T29: SIGMOVE moves control signals across segment boundaries and applies them without clearing them.  R3
consumes a control signal at its boundary target before the interaction: a label-0 cell holding action 6 enters `toss`
and drops the signal, a label psi-1 cell holding action 3 or 4 enters `eliminate_signal` and drops it, a label psi-1
cell holding action 5 enters `depart` and drops it (`consume`).  The R3 row is the R1 row on consumed inputs
(`row`).  On a pair without such boundary signals R3 is the R1 row (`row_eq_of_clear`), so every R1 row lemma applies
to R3 rows whose cells carry no boundary control signal; the R3 step changes only the served pair and the new pair
depends only on the old one (`step_pairLocal`).  Probe evidence: run/verification/b6-r1-r3-episode-compare.txt.
-/

namespace BirthControlConsumeR3

open PPLL PPLLResearchFormulation PPLLExpiringComparisonRepair
open BirthCheckPermitRepairLeaf B6WindowLocality

variable {n ψ κ τ : Nat}

/-- The printed action (1..6) of a bounded path2 signal, 0 without a signal. -/
def action (c : ExpiringAgentState ψ κ τ) : Nat :=
  match c.core.core.path2 with
  | some q => q.action.val + 1
  | none => 0

/-- A control signal sitting at its boundary target. -/
def BoundarySignal (c : ExpiringAgentState ψ κ τ) : Prop :=
  (c.core.core.label.val = 0 ∧ action c = 6) ∨
    (c.core.core.label.val + 1 = ψ ∧ (action c = 3 ∨ action c = 4 ∨ action c = 5))

instance (c : ExpiringAgentState ψ κ τ) : Decidable (BoundarySignal c) := by
  unfold BoundarySignal; infer_instance

/-- Apply and drop a boundary control signal. -/
def consume (c : ExpiringAgentState ψ κ τ) : ExpiringAgentState ψ κ τ :=
  if c.core.core.label.val = 0 ∧ action c = 6 then
    ⟨⟨{ c.core.core with state := .toss, path2 := none }, c.core.path0Crossed⟩, c.stall⟩
  else if c.core.core.label.val + 1 = ψ ∧ (action c = 3 ∨ action c = 4) then
    ⟨⟨{ c.core.core with state := .eliminate_signal, path2 := none }, c.core.path0Crossed⟩, c.stall⟩
  else if c.core.core.label.val + 1 = ψ ∧ action c = 5 then
    ⟨⟨{ c.core.core with state := .depart, path2 := none }, c.core.path0Crossed⟩, c.stall⟩
  else c

theorem consume_of_clear (c : ExpiringAgentState ψ κ τ) (h : ¬ BoundarySignal c) : consume c = c := by
  unfold BoundarySignal at h
  have h1 : ¬ (c.core.core.label.val = 0 ∧ action c = 6) := fun h' => h (Or.inl h')
  have h2 : ¬ (c.core.core.label.val + 1 = ψ ∧ (action c = 3 ∨ action c = 4)) := by
    rintro ⟨ha, hb⟩; exact h (Or.inr ⟨ha, by omega⟩)
  have h3 : ¬ (c.core.core.label.val + 1 = ψ ∧ action c = 5) := by
    rintro ⟨ha, hb⟩; exact h (Or.inr ⟨ha, by omega⟩)
  unfold consume
  rw [if_neg h1, if_neg h2, if_neg h3]

/-- A cell without any path2 signal carries no boundary signal. -/
theorem clear_of_path2_none (c : ExpiringAgentState ψ κ τ) (h : c.core.core.path2 = none) : ¬ BoundarySignal c := by
  unfold BoundarySignal action
  rw [h]
  simp

/-- The R3 row: the R1 row on consumed inputs. -/
def row (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : ExpiringAgentState ψ κ τ) : ExpiringAgentState ψ κ τ × ExpiringAgentState ψ κ τ :=
  BirthCheckPermitRepair.row hψ (by decide : 0 < 2) h2 (consume l) (consume r)

theorem row_eq_of_clear (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (l r : ExpiringAgentState ψ κ τ)
    (hl : ¬ BoundarySignal l) (hr : ¬ BoundarySignal r) :
    row hψ h2 l r = BirthCheckPermitRepair.row hψ (by decide : 0 < 2) h2 l r := by
  unfold row; rw [consume_of_clear l hl, consume_of_clear r hr]

/-- The R3 protocol with the consumer state type and output. -/
def protocol (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (κ τ : Nat) : PopulationProtocol where
  Q := ExpiringAgentState ψ κ τ
  Y := Bool
  transition := row hψ h2
  output := fun q => q.core.core.leader

def step (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n) : FC n ψ κ τ :=
  (protocol hψ h2 κ τ).step ring C e

theorem step_other (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) (C : FC n ψ κ τ)
    (e i : Fin n) (hi : i ≠ e) (hj : i ≠ ring.rightNeighbor e) : step hψ h2 ring C e i = C i := by
  simp only [step, PopulationProtocol.step, if_neg hi]
  exact if_neg hj

theorem step_pairLocal (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) :
    PairLocal ring (step (κ := κ) (τ := τ) hψ h2 ring) := by
  refine ⟨fun C e i hi hj => step_other hψ h2 ring C e i hi hj, ?_⟩
  intro C D e hl hr
  simp only [step, PopulationProtocol.step, protocol, hl, hr]
  exact ⟨trivial, trivial⟩

/-- Where the served pair carries no boundary signal, the R3 step is the R1 step. -/
theorem step_eq_of_clear (hψ : 0 < ψ) (h2 : 2 ≤ ψ) (ring : DirectedRing n) (C : FC n ψ κ τ) (e : Fin n)
    (hl : ¬ BoundarySignal (C e)) (hr : ¬ BoundarySignal (C (ring.rightNeighbor e))) :
    step hψ h2 ring C e = step1 hψ h2 ring C e := by
  unfold step step1
  simp only [PopulationProtocol.step, protocol, BirthCheckPermitRepair.protocol]
  rw [row_eq_of_clear hψ h2 _ _ hl hr]

end BirthControlConsumeR3
