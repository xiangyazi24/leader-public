import Leader.Wu.Carrier.ValidatorCorridor

/-!
# Edge classification for the physical QMAT corridor

Every owned physical edge out of an active coherent corridor realizes an
abstract `Phase.Next` step.  The proofs reduce the exact endpoint and carrier
rows from `PPLLV2LiteralTable`; no abstract transition is assumed here.
-/

namespace PPLLV2ValidatorPhysicalRefinement

open PPLLV2LiteralTable
open PPLLV2ValidatorRankRepair

set_option autoImplicit false
set_option warningAsError true

def internalLeft {ell : Nat} (edge : Fin (ell + 1))
    (hsource : edge.val ≠ 0) : Fin ell :=
  ⟨edge.val - 1, by omega⟩

def internalRight {ell : Nat} (edge : Fin (ell + 1))
    (htarget : edge.val ≠ ell) : Fin ell :=
  ⟨edge.val, by omega⟩

theorem ownedStep_internal {ell : Nat} (hell : 0 < ell)
    (physical : Corridor ell) (edge : Fin (ell + 1))
    (hsource : edge.val ≠ 0) (htarget : edge.val ≠ ell) :
    ownedStep hell physical edge =
      let li := internalLeft edge hsource
      let ri := internalRight edge htarget
      let out := cellCellStep (physical.lane li) (physical.lane ri)
      { left := physical.left
        lane := updateAt (updateAt physical.lane li out.1) ri out.2
        right := physical.right } := by
  simp [ownedStep, hsource, htarget, internalLeft, internalRight]

/-- Every owned edge from the anchor realizes a corresponding `Next` step. -/
theorem anchor_ownedStep_refines {ell : Nat} (hell : 0 < ell)
    (physical : Corridor ell)
    (hphysical : Represents physical (.anchor : ValidatorPhase ell))
    (edge : Fin (ell + 1)) :
    ∃ after : ValidatorPhase ell,
      Represents (ownedStep hell physical edge) after ∧ Next .anchor after := by
  rcases hphysical with ⟨hleft, hlane, hright⟩
  by_cases hsource : edge.val = 0
  · let zero : Fin ell := ⟨0, hell⟩
    refine ⟨.query zero, ?_, .anchorLaunch hell⟩
    simp only [Represents]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [ownedStep, hsource, hleft, hlane, firstCell, EmptyCell]
    · intro i hi
      simp [zero] at hi
    · simp [ownedStep, hsource, hleft, hlane, firstCell, zero,
        updateAt, EmptyCell]
    · intro i hi
      have hne : i ≠ zero := by
        intro hie
        subst i
        omega
      simp [ownedStep, hsource, hleft, hlane, firstCell, zero,
        updateAt, hne, EmptyCell]
    · simp [ownedStep, hsource, hright]
  · by_cases htarget : edge.val = ell
    · refine ⟨.exited, ?_, .anchorMatures⟩
      simp only [Represents]
      have hellne : ell ≠ 0 := Nat.ne_of_gt hell
      simp [ownedStep, htarget, hellne, hright, hlane, lastCell, EmptyCell]
    · refine ⟨.anchor, ?_, .frame .anchor⟩
      simp only [Represents]
      refine ⟨?_, ?_, ?_⟩
      · simp [ownedStep, hsource, htarget, hleft]
      · intro i
        simp [ownedStep, hsource, htarget, updateAt, hlane,
          EmptyCell, headless, cellCellStep]
      · simp [ownedStep, hsource, htarget, hright]

/-- The anchor's target boundary uses the headless-empty target maturation
row and writes `T`. -/
theorem anchor_target_ownedStep_exits {ell : Nat} (hell : 0 < ell)
    (physical : Corridor ell)
    (hphysical : Represents physical (.anchor : ValidatorPhase ell)) :
    Represents (ownedStep hell physical ⟨ell, by omega⟩)
      (.exited : ValidatorPhase ell) := by
  rcases hphysical with ⟨_left, hlane, hright⟩
  simp only [Represents]
  rw [ownedStep_target]
  dsimp only
  rw [hright, hlane (lastCell hell)]
  rfl

/-- The target edge of every query state writes `T`.  At the last frontier
this is exactly QMAT; at an earlier frontier it is the pre-existing
`E | target-hold -> E | T` row. -/
theorem query_target_ownedStep_exits {ell : Nat} (hell : 0 < ell)
    (physical : Corridor ell) (frontier : Fin ell)
    (hphysical : Represents physical (.query frontier)) :
    Represents (ownedStep hell physical ⟨ell, by omega⟩)
      (.exited : ValidatorPhase ell) := by
  rcases hphysical with ⟨_hleft, _hprefix, hfrontier, hsuffix, hright⟩
  let last : Fin ell := lastCell hell
  have hlast : physical.lane last = QueryCell ∨
      physical.lane last = EmptyCell := by
    by_cases hfinal : frontier.val = ell - 1
    · left
      have hfl : frontier = last := by
        apply Fin.ext
        simpa [last, lastCell] using hfinal
      simpa [hfl] using hfrontier
    · right
      apply hsuffix
      simp only [last, lastCell]
      omega
  simp only [Represents]
  rw [ownedStep_target]
  dsimp only
  rw [hright]
  rcases hlast with hlast | hlast
  · rw [show physical.lane (lastCell hell) = QueryCell by simpa [last]]
    rfl
  · rw [show physical.lane (lastCell hell) = EmptyCell by simpa [last]]
    rfl

/-- The source edge of a query state updates only the permitted prefix. -/
theorem query_source_ownedStep_frames {ell : Nat} (hell : 0 < ell)
    (physical : Corridor ell) (frontier : Fin ell)
    (hphysical : Represents physical (.query frontier)) :
    Represents (ownedStep hell physical ⟨0, by omega⟩)
      (.query frontier : ValidatorPhase ell) := by
  rcases hphysical with ⟨hleft, hprefix, hfrontier, hsuffix, hright⟩
  rw [ownedStep_source]
  dsimp only
  let zero : Fin ell := firstCell hell
  by_cases hzero : frontier.val = 0
  · have hfz : frontier = zero := by
      apply Fin.ext
      simpa [zero, firstCell] using hzero
    subst frontier
    have hfrontFirst : physical.lane (firstCell hell) = QueryCell := by
      simpa [zero] using hfrontier
    simp only [Represents]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hleft, hfrontFirst]
      rfl
    · intro i hi
      simp [zero, firstCell] at hi
    · rw [hfrontFirst]
      rfl
    · intro i hi
      have hne : i ≠ firstCell hell := by
        intro hie
        have hv := congrArg Fin.val hie
        simp [firstCell] at hv
        omega
      simp [updateAt, hne, hsuffix i (by simpa [zero] using hi)]
    · exact hright

  · have hzeroPrefix : PrefixCell (physical.lane zero) := by
      apply hprefix
      simp only [zero, firstCell]
      omega
    have hroot :
        (rootCellStep physical.left (physical.lane (firstCell hell))).1 =
            .validateSource ∧
          PrefixCell
            (rootCellStep physical.left (physical.lane (firstCell hell))).2 := by
      rw [hleft]
      exact rootCell_validate_prefix (by simpa [zero] using hzeroPrefix)
    simp only [Represents]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact hroot.1
    · intro i hi
      by_cases hiz : i = firstCell hell
      · subst i
        simpa [updateAt] using hroot.2
      · simpa [updateAt, hiz] using hprefix i hi
    · have hne : frontier ≠ firstCell hell := by
        intro heq
        have hv := congrArg Fin.val heq
        simp [firstCell] at hv
        exact hzero hv
      simp [updateAt, hne, hfrontier]
    · intro i hi
      have hne : i ≠ firstCell hell := by
        intro heq
        have hv := congrArg Fin.val heq
        simp [firstCell] at hv
        omega
      simp [updateAt, hne, hsuffix i hi]
    · exact hright

/-- Selecting the carrier edge immediately to the right of a query moves the
rightmost query frontier one cell right. -/
theorem query_frontier_ownedStep_moves {ell : Nat} (hell : 0 < ell)
    (physical : Corridor ell) (frontier : Fin ell)
    (hphysical : Represents physical (.query frontier))
    (hnext : frontier.val + 1 < ell) :
    Represents
      (ownedStep hell physical ⟨frontier.val + 1, by omega⟩)
      (.query ⟨frontier.val + 1, hnext⟩ : ValidatorPhase ell) := by
  rcases hphysical with ⟨hleft, hprefix, hfrontier, hsuffix, hright⟩
  let edge : Fin (ell + 1) := ⟨frontier.val + 1, by omega⟩
  have hsource : edge.val ≠ 0 := by simp [edge]
  have htarget : edge.val ≠ ell := by simp [edge]; omega
  rw [ownedStep_internal hell physical edge hsource htarget]
  dsimp only [internalLeft, internalRight]
  have hleftIndex : (⟨edge.val - 1, by omega⟩ : Fin ell) = frontier := by
    apply Fin.ext
    simp [edge]
  have hrightIndex :
      (⟨edge.val, by omega⟩ : Fin ell) =
        ⟨frontier.val + 1, hnext⟩ := by
    apply Fin.ext
    simp [edge]
  simp only [hleftIndex, hrightIndex]
  have hrightEmpty :
      physical.lane ⟨frontier.val + 1, hnext⟩ = EmptyCell :=
    hsuffix _ (by simp)
  rw [hfrontier, hrightEmpty]
  simp only [query_empty]
  change Represents
    { left := physical.left
      lane := updateAt (updateAt physical.lane frontier FrozenCell)
        ⟨frontier.val + 1, hnext⟩ QueryCell
      right := physical.right }
    (.query ⟨frontier.val + 1, hnext⟩ : ValidatorPhase ell)
  simp only [Represents]
  refine ⟨hleft, ?_, ?_, ?_, hright⟩
  · intro i hi
    by_cases hir : i = ⟨frontier.val + 1, hnext⟩
    · subst i
      simp at hi
    by_cases hil : i = frontier
    · subst i
      have hne : frontier ≠ ⟨frontier.val + 1, hnext⟩ := by
        intro h
        have hv := congrArg Fin.val h
        simp at hv
      simp [updateAt, hne, PrefixCell, FrozenCell]
    · simp [updateAt, hir, hil]
      exact hprefix i (by omega)
  · simp [updateAt]
  · intro i hi
    have hir : i ≠ ⟨frontier.val + 1, hnext⟩ := by
      intro hir
      subst i
      simp at hi
    have hil : i ≠ frontier := by
      intro hil
      subst i
      omega
    simp [updateAt, hir, hil, hsuffix i (by omega)]

/-- An internal edge weakly left of the query frontier preserves the phase.
This includes duplicate-query collisions at the frontier. -/
theorem query_internal_left_ownedStep_frames {ell : Nat} (hell : 0 < ell)
    (physical : Corridor ell) (frontier : Fin ell)
    (hphysical : Represents physical (.query frontier))
    (edge : Fin (ell + 1)) (hsource : edge.val ≠ 0)
    (hle : edge.val ≤ frontier.val) :
    Represents (ownedStep hell physical edge)
      (.query frontier : ValidatorPhase ell) := by
  rcases hphysical with ⟨hleft, hprefix, hfrontier, hsuffix, hright⟩
  have htarget : edge.val ≠ ell := by omega
  let li := internalLeft edge hsource
  let ri := internalRight edge htarget
  let out := cellCellStep (physical.lane li) (physical.lane ri)
  have hli : li.val < frontier.val := by
    simp only [li, internalLeft]
    omega
  have hliPrefix : PrefixCell (physical.lane li) := hprefix li hli
  have hout : PrefixCell out.1 ∧ PrefixCell out.2 ∧
      (ri = frontier → out.2 = QueryCell) := by
    by_cases heq : edge.val = frontier.val
    · have hri : ri = frontier := by
        apply Fin.ext
        simpa [ri, internalRight] using heq
      have hpair : PrefixCell out.1 ∧ out.2 = QueryCell := by
        simpa [out, hri, hfrontier] using
          cellCell_prefix_query hliPrefix
      exact ⟨hpair.1, Or.inr hpair.2, fun _ => hpair.2⟩
    · have hriLt : ri.val < frontier.val := by
        simp only [ri, internalRight]
        omega
      have hpair : PrefixCell out.1 ∧ PrefixCell out.2 :=
        cellCell_prefix_prefix hliPrefix (hprefix ri hriLt)
      refine ⟨hpair.1, hpair.2, ?_⟩
      intro hri
      have hv := congrArg Fin.val hri
      simp [ri, internalRight] at hv
      exact False.elim (heq hv)
  rw [ownedStep_internal hell physical edge hsource htarget]
  change Represents
    { left := physical.left
      lane := updateAt (updateAt physical.lane li out.1) ri out.2
      right := physical.right }
    (.query frontier : ValidatorPhase ell)
  simp only [Represents]
  refine ⟨hleft, ?_, ?_, ?_, hright⟩
  · intro i hi
    by_cases hir : i = ri
    · simpa [updateAt, hir] using hout.2.1
    by_cases hil : i = li
    · subst i
      simp [updateAt, hir, hout.1]
    · simpa [updateAt, hir, hil] using hprefix i hi
  · by_cases hfr : frontier = ri
    · simp [updateAt, hfr, hout.2.2 hfr.symm]
    · have hfl : frontier ≠ li := by
        intro h
        have hv := congrArg Fin.val h
        omega
      simp [updateAt, hfr, hfl, hfrontier]
  · intro i hi
    have hir : i ≠ ri := by
      intro h
      have hv := congrArg Fin.val h
      simp [ri, internalRight] at hv
      omega
    have hil : i ≠ li := by
      intro h
      have hv := congrArg Fin.val h
      omega
    simp [updateAt, hir, hil, hsuffix i hi]

/-- An internal edge strictly right of the query's advancing edge sees two
empty suffix cells and frames the physical state. -/
theorem query_internal_right_ownedStep_frames {ell : Nat} (hell : 0 < ell)
    (physical : Corridor ell) (frontier : Fin ell)
    (hphysical : Represents physical (.query frontier))
    (edge : Fin (ell + 1)) (htarget : edge.val ≠ ell)
    (hgt : frontier.val + 1 < edge.val) :
    Represents (ownedStep hell physical edge)
      (.query frontier : ValidatorPhase ell) := by
  rcases hphysical with ⟨hleft, hprefix, hfrontier, hsuffix, hright⟩
  have hsource : edge.val ≠ 0 := by omega
  let li := internalLeft edge hsource
  let ri := internalRight edge htarget
  have hliEmpty : physical.lane li = EmptyCell := by
    apply hsuffix
    simp only [li, internalLeft]
    omega
  have hriEmpty : physical.lane ri = EmptyCell := by
    apply hsuffix
    simp only [ri, internalRight]
    omega
  rw [ownedStep_internal hell physical edge hsource htarget]
  change Represents
    { left := physical.left
      lane := updateAt
        (updateAt physical.lane li
          (cellCellStep (physical.lane li) (physical.lane ri)).1)
        ri (cellCellStep (physical.lane li) (physical.lane ri)).2
      right := physical.right }
    (.query frontier : ValidatorPhase ell)
  rw [hliEmpty, hriEmpty]
  have hlane :
      updateAt (updateAt physical.lane li EmptyCell) ri EmptyCell =
        physical.lane := by
    funext i
    by_cases hir : i = ri
    · subst i
      simp [updateAt, hriEmpty]
    by_cases hil : i = li
    · subst i
      simp [updateAt, hir, hliEmpty]
    · simp [updateAt, hir, hil]
  change Represents
    { left := physical.left
      lane := updateAt (updateAt physical.lane li EmptyCell) ri EmptyCell
      right := physical.right }
    (.query frontier : ValidatorPhase ell)
  rw [hlane]
  exact ⟨hleft, hprefix, hfrontier, hsuffix, hright⟩

/-- Complete query-phase edge classification. -/
theorem query_ownedStep_refines {ell : Nat} (hell : 0 < ell)
    (physical : Corridor ell) (frontier : Fin ell)
    (hphysical : Represents physical (.query frontier))
    (edge : Fin (ell + 1)) :
    ∃ after : ValidatorPhase ell,
      Represents (ownedStep hell physical edge) after ∧
        Next (.query frontier) after := by
  by_cases hsource : edge.val = 0
  · have hedge : edge = ⟨0, by omega⟩ := Fin.ext hsource
    rw [hedge]
    exact ⟨.query frontier, query_source_ownedStep_frames hell physical
      frontier hphysical, .frame (.query frontier)⟩
  by_cases htarget : edge.val = ell
  · have hedge : edge = ⟨ell, by omega⟩ := Fin.ext htarget
    rw [hedge]
    exact ⟨.exited, query_target_ownedStep_exits hell physical frontier
      hphysical, .queryMatures frontier⟩
  by_cases hmove : edge.val = frontier.val + 1
  · have hnext : frontier.val + 1 < ell := by omega
    have hedge : edge = ⟨frontier.val + 1, by omega⟩ := Fin.ext hmove
    rw [hedge]
    exact ⟨.query ⟨frontier.val + 1, hnext⟩,
      query_frontier_ownedStep_moves hell physical frontier hphysical hnext,
      .queryMoves frontier hnext⟩
  by_cases hleftSide : edge.val < frontier.val + 1
  · exact ⟨.query frontier,
      query_internal_left_ownedStep_frames hell physical frontier hphysical
        edge hsource (by omega),
      .frame (.query frontier)⟩
  · exact ⟨.query frontier,
      query_internal_right_ownedStep_frames hell physical frontier hphysical
        edge htarget (by omega),
      .frame (.query frontier)⟩

#print axioms query_ownedStep_refines

end PPLLV2ValidatorPhysicalRefinement
