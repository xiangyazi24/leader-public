import Leader.Wu.Carrier.RootCarrierTable
import Leader.Wu.Carrier.HeldValidatorRankRepair

/-!
# Physical QMAT corridor semantics

This file gives the exact all-length single-corridor grammar and its owned
edge semantics over the complete literal 26-root/39-carrier table.  Edge `0`
is the source boundary, edge `ell` is the target boundary, and the remaining
edges are carrier-carrier interactions.

The active grammar is exactly

* `S, E^ell, target-hold`;
* `validate-S, P^j, F:query-S, E^(ell-j-1), target-hold`;
* `validate-S, P^j, F:deny-keep, E^(ell-j-1), target-hold`,

where each cell in `P` is independently `F:.` or `F:query-S`.  In particular,
the distinguished frontier is the rightmost query/denial; stale queries in
the prefix are allowed and are handled by the literal collision rows.
-/

namespace PPLLV2ValidatorPhysicalRefinement

open PPLLV2LiteralTable

set_option autoImplicit false
set_option warningAsError true

abbrev EmptyCell : CellMode := headless .empty
abbrev FrozenCell : CellMode := headless .frozen
abbrev QueryCell : CellMode := ⟨.frozen, .querySource⟩
abbrev DenyCell : CellMode := ⟨.frozen, .denyKeep⟩

abbrev ValidatorPhase (ell : Nat) :=
  PPLLV2ValidatorRankRepair.Phase ell

/-- Literal state of one owned positive corridor. -/
structure Corridor (ell : Nat) where
  left : RootMode
  lane : Fin ell → CellMode
  right : RootMode

/-- A prefix cell allowed behind the rightmost live frontier. -/
def PrefixCell (cell : CellMode) : Prop :=
  cell = FrozenCell ∨ cell = QueryCell

/-- Exact present-state grammar, indexed by the abstract phase it realizes.
The `exited` case records only the first physical `T` write; active coherence
contains all lane and endpoint constraints. -/
def Represents {ell : Nat} (physical : Corridor ell) : ValidatorPhase ell → Prop
  | .anchor =>
      physical.left = .stableSource ∧
      (∀ i, physical.lane i = EmptyCell) ∧
      physical.right = .targetHold
  | .query frontier =>
      physical.left = .validateSource ∧
      (∀ i, i.val < frontier.val → PrefixCell (physical.lane i)) ∧
      physical.lane frontier = QueryCell ∧
      (∀ i, frontier.val < i.val → physical.lane i = EmptyCell) ∧
      physical.right = .targetHold
  | .deny frontier =>
      physical.left = .validateSource ∧
      (∀ i, i.val < frontier.val → PrefixCell (physical.lane i)) ∧
      physical.lane frontier = DenyCell ∧
      (∀ i, frontier.val < i.val → physical.lane i = EmptyCell) ∧
      physical.right = .targetHold
  | .exited => physical.right = .stableTarget

/-- Active coherent physical corridor, excluding the stopped target. -/
def ActiveCoherent {ell : Nat} (physical : Corridor ell) : Prop :=
  ∃ phase, phase ≠ .exited ∧ Represents physical phase

/-- Every active phase has one of the two source-side root shapes used by the
literal validator grammar. -/
theorem active_left_root_shape {ell : Nat} {physical : Corridor ell}
    {phase : ValidatorPhase ell} (hrep : Represents physical phase)
    (hactive : phase ≠ .exited) :
    physical.left = .stableSource ∨ physical.left = .validateSource := by
  cases phase with
  | anchor => exact Or.inl hrep.1
  | query frontier => exact Or.inr hrep.1
  | deny frontier => exact Or.inr hrep.1
  | exited => exact False.elim (hactive rfl)

/-- Every active phase holds the target-side root. -/
theorem active_right_root_targetHold {ell : Nat} {physical : Corridor ell}
    {phase : ValidatorPhase ell} (hrep : Represents physical phase)
    (hactive : phase ≠ .exited) : physical.right = .targetHold := by
  cases phase with
  | anchor => exact hrep.2.2
  | query frontier => exact hrep.2.2.2.2
  | deny frontier => exact hrep.2.2.2.2
  | exited => exact False.elim (hactive rfl)

/-- Two active corridors cannot share the first corridor's target root as the
second corridor's source root: the required literal root constructors are
disjoint. -/
theorem adjacent_active_corridors_exclusive
    {leftLength rightLength : Nat}
    {left : Corridor leftLength} {right : Corridor rightLength}
    (hshared : left.right = right.left)
    (hleft : ActiveCoherent left) (hright : ActiveCoherent right) : False := by
  rcases hleft with ⟨leftPhase, hleftActive, hleftRep⟩
  rcases hright with ⟨rightPhase, hrightActive, hrightRep⟩
  have htarget := active_right_root_targetHold hleftRep hleftActive
  rcases active_left_root_shape hrightRep hrightActive with hsource | hsource
  · simp_all
  · simp_all

/-- The exact grammar assigns at most one phase to a physical corridor. -/
theorem represents_unique {ell : Nat} {physical : Corridor ell}
    {first second : ValidatorPhase ell}
    (hfirst : Represents physical first)
    (hsecond : Represents physical second) : first = second := by
  cases first <;> cases second <;> simp_all [Represents]
  case query.query f g =>
    rcases hfirst with ⟨_, _, hf, hfsuffix, _⟩
    rcases hsecond with ⟨_, hg, hgsuffix⟩
    rcases Nat.lt_trichotomy f.val g.val with hlt | heq | hgt
    · have hempty := hfsuffix g hlt
      rw [hg] at hempty
      simp [QueryCell, EmptyCell, headless] at hempty
    · exact Fin.ext heq
    · have hempty := hgsuffix f hgt
      rw [hf] at hempty
      simp [QueryCell, EmptyCell, headless] at hempty
  case query.deny f g =>
    rcases hfirst with ⟨_, _, hf, hfsuffix, _⟩
    rcases hsecond with ⟨_, hg, hgsuffix⟩
    rcases Nat.lt_trichotomy f.val g.val with hlt | heq | hgt
    · have hempty := hfsuffix g hlt
      rw [hg] at hempty
      simp [DenyCell, EmptyCell, headless] at hempty
    · have hfg : f = g := Fin.ext heq
      rw [hfg, hg] at hf
      simp [QueryCell, DenyCell] at hf
    · have hempty := hgsuffix f hgt
      rw [hf] at hempty
      simp [QueryCell, EmptyCell, headless] at hempty
  case deny.query f g =>
    rcases hfirst with ⟨_, _, hf, hfsuffix, _⟩
    rcases hsecond with ⟨_, hg, hgsuffix⟩
    rcases Nat.lt_trichotomy f.val g.val with hlt | heq | hgt
    · have hempty := hfsuffix g hlt
      rw [hg] at hempty
      simp [QueryCell, EmptyCell, headless] at hempty
    · have hfg : f = g := Fin.ext heq
      rw [hfg, hg] at hf
      simp [QueryCell, DenyCell] at hf
    · have hempty := hgsuffix f hgt
      rw [hf] at hempty
      simp [DenyCell, EmptyCell, headless] at hempty
  case deny.deny f g =>
    rcases hfirst with ⟨_, _, hf, hfsuffix, _⟩
    rcases hsecond with ⟨_, hg, hgsuffix⟩
    rcases Nat.lt_trichotomy f.val g.val with hlt | heq | hgt
    · have hempty := hfsuffix g hlt
      rw [hg] at hempty
      simp [DenyCell, EmptyCell, headless] at hempty
    · exact Fin.ext heq
    · have hempty := hgsuffix f hgt
      rw [hf] at hempty
      simp [DenyCell, EmptyCell, headless] at hempty

/-- Canonical present-state witness for every abstract phase.  Query/denial
prefixes use `F:.`; the grammar also permits stale `F:query-S` cells. -/
def canonicalCorridor {ell : Nat} : ValidatorPhase ell → Corridor ell
  | .anchor =>
      { left := .stableSource
        lane := fun _ => EmptyCell
        right := .targetHold }
  | .query frontier =>
      { left := .validateSource
        lane := fun i =>
          if i.val < frontier.val then FrozenCell
          else if i = frontier then QueryCell else EmptyCell
        right := .targetHold }
  | .deny frontier =>
      { left := .validateSource
        lane := fun i =>
          if i.val < frontier.val then FrozenCell
          else if i = frontier then DenyCell else EmptyCell
        right := .targetHold }
  | .exited =>
      { left := .stableSource
        lane := fun _ => EmptyCell
        right := .stableTarget }

/-- The phase-indexed grammar is nonvacuous at every constructor. -/
@[simp] theorem canonicalCorridor_represents {ell : Nat}
    (phase : ValidatorPhase ell) : Represents (canonicalCorridor phase) phase := by
  cases phase with
  | anchor => simp [canonicalCorridor, Represents]
  | query frontier =>
      simp only [canonicalCorridor, Represents]
      refine ⟨by trivial, ?_, ?_, ?_, by trivial⟩
      · intro i hi
        simp [hi, PrefixCell]
      · simp
      · intro i hi
        have hne : i ≠ frontier := by
          intro h
          subst i
          omega
        simp [show ¬i.val < frontier.val by omega, hne]
  | deny frontier =>
      simp only [canonicalCorridor, Represents]
      refine ⟨by trivial, ?_, ?_, ?_, by trivial⟩
      · intro i hi
        simp [hi, PrefixCell]
      · simp
      · intro i hi
        have hne : i ≠ frontier := by
          intro h
          subst i
          omega
        simp [show ¬i.val < frontier.val by omega, hne]
  | exited => simp [canonicalCorridor, Represents]

theorem represents_nonempty {ell : Nat} (phase : ValidatorPhase ell) :
    ∃ physical : Corridor ell, Represents physical phase :=
  ⟨canonicalCorridor phase, canonicalCorridor_represents phase⟩

def firstCell {ell : Nat} (hell : 0 < ell) : Fin ell := ⟨0, hell⟩

def lastCell {ell : Nat} (hell : 0 < ell) : Fin ell :=
  ⟨ell - 1, by omega⟩

def updateAt {ell : Nat} (lane : Fin ell → CellMode)
    (index : Fin ell) (value : CellMode) : Fin ell → CellMode :=
  fun i => if i = index then value else lane i

/-- Deterministic repaired-table interaction on an owned corridor edge. -/
def ownedStep {ell : Nat} (hell : 0 < ell) (physical : Corridor ell)
    (edge : Fin (ell + 1)) : Corridor ell := by
  by_cases hsource : edge.val = 0
  · let out := rootCellStep physical.left (physical.lane (firstCell hell))
    exact
      { left := out.1
        lane := updateAt physical.lane (firstCell hell) out.2
        right := physical.right }
  · by_cases htarget : edge.val = ell
    · let out := repairedCellRootStep (physical.lane (lastCell hell))
          physical.right
      exact
        { left := physical.left
          lane := updateAt physical.lane (lastCell hell) out.1
          right := out.2 }
    · have hleft : edge.val - 1 < ell := by omega
      have hright : edge.val < ell := by omega
      let leftIndex : Fin ell := ⟨edge.val - 1, hleft⟩
      let rightIndex : Fin ell := ⟨edge.val, hright⟩
      let out := cellCellStep (physical.lane leftIndex)
        (physical.lane rightIndex)
      exact
        { left := physical.left
          lane := updateAt
            (updateAt physical.lane leftIndex out.1) rightIndex out.2
          right := physical.right }

@[simp] theorem ownedStep_source {ell : Nat} (hell : 0 < ell)
    (physical : Corridor ell) :
    ownedStep hell physical ⟨0, by omega⟩ =
      let out := rootCellStep physical.left (physical.lane (firstCell hell))
      { left := out.1
        lane := updateAt physical.lane (firstCell hell) out.2
        right := physical.right } := by
  simp [ownedStep]

@[simp] theorem ownedStep_target {ell : Nat} (hell : 0 < ell)
    (physical : Corridor ell) :
    ownedStep hell physical ⟨ell, by omega⟩ =
      let out := repairedCellRootStep
        (physical.lane (lastCell hell)) physical.right
      { left := physical.left
        lane := updateAt physical.lane (lastCell hell) out.1
        right := out.2 } := by
  have hellne : ell ≠ 0 := Nat.ne_of_gt hell
  simp [ownedStep, hellne]

/-! ## Full-table row closure facts for the grammar -/

theorem rootCell_validate_prefix {cell : CellMode} (hcell : PrefixCell cell) :
    (rootCellStep .validateSource cell).1 = .validateSource ∧
      PrefixCell (rootCellStep .validateSource cell).2 := by
  rcases hcell with rfl | rfl <;>
    simp [PrefixCell, FrozenCell, QueryCell]

theorem cellCell_prefix_prefix {left right : CellMode}
    (hleft : PrefixCell left) (hright : PrefixCell right) :
    PrefixCell (cellCellStep left right).1 ∧
      PrefixCell (cellCellStep left right).2 := by
  rcases hleft with rfl | rfl <;> rcases hright with rfl | rfl <;>
    simp [PrefixCell, FrozenCell, QueryCell, cellCellStep, headless,
      isLeftHead, isRightHead]

theorem cellCell_prefix_query {left : CellMode} (hleft : PrefixCell left) :
    PrefixCell (cellCellStep left QueryCell).1 ∧
      (cellCellStep left QueryCell).2 = QueryCell := by
  rcases hleft with rfl | rfl <;>
    simp [PrefixCell, FrozenCell, QueryCell, cellCellStep, headless,
      isLeftHead, isRightHead]

theorem cellCell_prefix_deny {left : CellMode} (hleft : PrefixCell left) :
    cellCellStep left DenyCell = (DenyCell, EmptyCell) := by
  rcases hleft with rfl | rfl <;>
    simp [FrozenCell, QueryCell, DenyCell, EmptyCell]

@[simp] theorem cellCell_deny_empty :
    cellCellStep DenyCell EmptyCell = (DenyCell, EmptyCell) := by
  simp [DenyCell, EmptyCell, cellCellStep, headless, isLeftHead]

#print axioms rootCell_validate_prefix
#print axioms cellCell_prefix_prefix

end PPLLV2ValidatorPhysicalRefinement
