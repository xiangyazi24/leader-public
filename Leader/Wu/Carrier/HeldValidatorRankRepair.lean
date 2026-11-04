import Leader.Wu.Scheduler.FixedBlockStrongRankDescent

/-!
# One-row held-validator rank repair

This file formalizes the all-length rank interface for the private QMAT
overlay audited by `cold-audit/solmax_validator_*`:

`F:query-S | target-hold -> F:deny-keep | T`.

The literal row returns the same denial but leaves `target-hold` unchanged.
QMAT changes only that target output to the already-existing mature `T`
constructor.  The finite Python audit checks the complete 26-root/39-cell
table.  Here we isolate the parametric old SCC grammar: an anchor, a right
query frontier, a left denial frontier, and the one-way exit from held target.

The rank is

* `rho(A) = ell`,
* `rho(Q_j) = ell-j` for zero-based `j < ell`,
* `rho(D_j) = ell+j+1`, and
* `rho(exit) = 0`.

Every abstract physical child is nonincreasing, and every non-exit state has
a displayed strict child.  The final generic lemmas turn any deterministic
physical realization of this interface into one unit of one-edge block-drop
mass and the existing division-free Bellman cost bound.
-/

namespace PPLLV2ValidatorRankRepair

set_option autoImplicit false

/-! ## The exact critical row -/

inductive RootMode where
  | validateSource
  | stableSource
  | targetHold
  | stableTarget
  deriving DecidableEq, Repr

inductive CellMode where
  | empty
  | frozen
  | querySource
  | denyKeep
  deriving DecidableEq, Repr

abbrev CriticalPair := CellMode × RootMode

/-- Literal v2 behavior on the critical ordered pair, framed as identity away
from that pair in this abstract four-by-four view. -/
def literalCriticalRow : CriticalPair → CriticalPair
  | (.querySource, .targetHold) => (.denyKeep, .targetHold)
  | pair => pair

/-- QMAT differs from the literal critical view in exactly the target output
of `querySource | targetHold`. -/
def repairedCriticalRow : CriticalPair → CriticalPair
  | (.querySource, .targetHold) => (.denyKeep, .stableTarget)
  | pair => pair

@[simp] theorem literal_querySource_targetHold :
    literalCriticalRow (.querySource, .targetHold) =
      (.denyKeep, .targetHold) := rfl

@[simp] theorem repaired_querySource_targetHold :
    repairedCriticalRow (.querySource, .targetHold) =
      (.denyKeep, .stableTarget) := rfl

/-- Outside the one named input row, literal and repaired views coincide. -/
theorem repaired_eq_literal_of_ne (pair : CriticalPair)
    (hne : pair ≠ (.querySource, .targetHold)) :
    repairedCriticalRow pair = literalCriticalRow pair := by
  rcases pair with ⟨cell, root⟩
  cases cell <;> cases root <;> simp_all [repairedCriticalRow,
    literalCriticalRow]

/-! ## All-length held-sector rank -/

/-- Quotient of the old `A_ell/D_ell` SCC by its rightmost live frontier.
`exited` means that physical `target-hold` has matured to `T`. -/
inductive Phase (ell : Nat) where
  | anchor
  | query (frontier : Fin ell)
  | deny (frontier : Fin ell)
  | exited
  deriving DecidableEq, Repr

/-- Natural-valued all-length rank for the repaired held-validator sector. -/
def rank {ell : Nat} : Phase ell → Nat
  | .anchor => ell
  | .query frontier => ell - frontier.val
  | .deny frontier => ell + frontier.val + 1
  | .exited => 0

/-- Every possible quotient child of the repaired physical rows.  `frame`
collects scheduler edges that do not change the rightmost frontier.
`queryMatures` is the QMAT row at the last cell and the pre-existing headless
target maturation at earlier frontiers. -/
inductive Next {ell : Nat} : Phase ell → Phase ell → Prop where
  | frame (state : Phase ell) : Next state state
  | anchorLaunch (hell : 0 < ell) :
      Next .anchor (.query ⟨0, hell⟩)
  | anchorMatures : Next .anchor .exited
  | queryMoves (frontier : Fin ell) (hnext : frontier.val + 1 < ell) :
      Next (.query frontier) (.query ⟨frontier.val + 1, hnext⟩)
  | queryMatures (frontier : Fin ell) : Next (.query frontier) .exited
  | denyMoves (frontier : Fin ell) (hpos : 0 < frontier.val) :
      Next (.deny frontier)
        (.deny ⟨frontier.val - 1, by omega⟩)
  | denyReturns (hell : 0 < ell) :
      Next (.deny ⟨0, hell⟩) .anchor
  | denyMatures (frontier : Fin ell) (hsuffix : frontier.val + 1 < ell) :
      Next (.deny frontier) .exited

/-- QMAT makes the repaired held-sector rank nonincreasing on every physical
child schema. -/
theorem rank_next_le {ell : Nat} {before after : Phase ell}
    (hnext : Next before after) : rank after ≤ rank before := by
  cases hnext <;> simp [rank] <;> omega

/-- Every positive-length, non-exited held phase has a concrete strict child.
This is pointwise in the present frontier; it carries no history or owner ID. -/
theorem exists_rank_drop {ell : Nat} (hell : 0 < ell)
    (state : Phase ell) (hactive : state ≠ .exited) :
    ∃ child, Next state child ∧ rank child < rank state := by
  cases state with
  | anchor =>
      exact ⟨.exited, .anchorMatures, by simp [rank, hell]⟩
  | query frontier =>
      refine ⟨.exited, .queryMatures frontier, ?_⟩
      simp only [rank]
      exact Nat.sub_pos_of_lt frontier.isLt
  | deny frontier =>
      by_cases hzero : frontier.val = 0
      · have hfrontier : frontier = ⟨0, hell⟩ := Fin.ext hzero
        subst frontier
        exact ⟨.anchor, .denyReturns hell, by simp [rank]⟩
      · have hpos : 0 < frontier.val := Nat.pos_of_ne_zero hzero
        refine ⟨.deny ⟨frontier.val - 1, by omega⟩,
          .denyMoves frontier hpos, ?_⟩
        simp only [rank]
        omega
  | exited => exact False.elim (hactive rfl)

theorem rank_anchor (ell : Nat) : rank (Phase.anchor : Phase ell) = ell := rfl

theorem rank_query {ell : Nat} (frontier : Fin ell) :
    rank (.query frontier) = ell - frontier.val := rfl

theorem rank_deny {ell : Nat} (frontier : Fin ell) :
    rank (.deny frontier) = ell + frontier.val + 1 := rfl

/-! ## One-edge mass and Bellman consumer -/

open FixedBlockStrongRankDescent

private theorem one_le_sum_map_of_mem_eq_one {A : Type} (xs : List A)
    (value : A → Nat) (chosen : A) (hmem : chosen ∈ xs)
    (hone : value chosen = 1) :
    1 ≤ (xs.map value).sum := by
  induction xs with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [List.mem_cons] at hmem
      simp only [List.map_cons, List.sum_cons]
      rcases hmem with hchosen | htail
      · subst head
        omega
      · have hrec := ih htail
        omega

/-- One explicit strict physical edge contributes at least one literal word
to the exact-length-one block-drop mass. -/
theorem one_le_blockDropMass_one_of_edge
    {S : Type} {n : Nat} (step : S → Fin n → S) (rho : S → Nat)
    (state : S) (edge : Fin n)
    (hdrop : rho (step state edge) < rho state) :
    1 ≤ blockDropMass step rho 1 state := by
  unfold blockDropMass
  apply one_le_sum_map_of_mem_eq_one _ _ [edge]
  · exact mem_allSchedules_of_length n 1 [edge] (by simp)
  · simp [runWord, hdrop]

/-- Pointwise existence of a strict scheduler edge supplies the `H=1,d=n`
mass premise required by `truncatedRoundedCostNumerator_le_of_dropMass`. -/
theorem oneStep_dropMass_bridge
    {S : Type} {n : Nat} (step : S → Fin n → S) (rho : S → Nat)
    (hstrict : ∀ state, 0 < rho state →
      ∃ edge, rho (step state edge) < rho state) :
    ∀ state, 0 < rho state →
      n ^ 1 ≤ n * blockDropMass step rho 1 state := by
  intro state hpositive
  obtain ⟨edge, hedge⟩ := hstrict state hpositive
  have hone := one_le_blockDropMass_one_of_edge step rho state edge hedge
  simpa using Nat.mul_le_mul_left n hone

/-- Division-free one-edge Bellman bound.  A physical realization of `Next`
supplies `hstep` from `rank_next_le` and `hstrict` from
`exists_rank_drop` plus its concrete edge-surjectivity lemma. -/
theorem oneStep_truncatedCostNumerator_le
    {S : Type} {n : Nat} (step : S → Fin n → S) (rho : S → Nat)
    (hstep : ∀ state edge, rho (step state edge) ≤ rho state)
    (hstrict : ∀ state, 0 < rho state →
      ∃ edge, rho (step state edge) < rho state) :
    ∀ state J,
      truncatedRoundedCostNumerator step rho 1 state J ≤
        n ^ J * (n * rho state) := by
  have hmass := oneStep_dropMass_bridge step rho hstrict
  simpa using truncatedRoundedCostNumerator_le_of_dropMass
    step rho 1 n hstep hmass

#print axioms repaired_eq_literal_of_ne
#print axioms rank_next_le
#print axioms exists_rank_drop
#print axioms one_le_blockDropMass_one_of_edge
#print axioms oneStep_dropMass_bridge
#print axioms oneStep_truncatedCostNumerator_le

end PPLLV2ValidatorRankRepair
