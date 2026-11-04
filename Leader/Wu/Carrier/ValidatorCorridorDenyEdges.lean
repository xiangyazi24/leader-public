import Leader.Wu.Carrier.ValidatorCorridorEdges

/-!
# Denial-edge classification for the physical QMAT corridor

The denial frontier moves left through the exact literal collision row, returns
to the anchor at the source, and matures the held target only when an empty
suffix reaches that target.  This module also packages the public all-phase
owned-edge refinement theorem.
-/

namespace PPLLV2ValidatorPhysicalRefinement

open PPLLV2LiteralTable
open PPLLV2ValidatorRankRepair

set_option autoImplicit false
set_option warningAsError true

/-! ## Denial phases -/

/-- The source edge consumes a denial at frontier zero and restores the
anchor. -/
theorem deny_zero_source_ownedStep_returns {ell : Nat} (hell : 0 < ell)
    (physical : Corridor ell) (frontier : Fin ell)
    (hphysical : Represents physical (.deny frontier))
    (hzero : frontier.val = 0) :
    Represents (ownedStep hell physical ⟨0, by omega⟩)
      (.anchor : ValidatorPhase ell) := by
  rcases hphysical with ⟨hleft, _hprefix, hfrontier, hsuffix, hright⟩
  have hf : frontier = firstCell hell := by
    apply Fin.ext
    simpa [firstCell] using hzero
  rw [ownedStep_source]
  dsimp only
  have hfirst : physical.lane (firstCell hell) = DenyCell := by
    simpa [hf] using hfrontier
  rw [hleft, hfirst]
  simp only [validateSource_deny, Represents]
  refine ⟨by trivial, ?_, hright⟩
  intro i
  by_cases hi : i = firstCell hell
  · simp [updateAt, hi]
  · simp [updateAt, hi]
    apply hsuffix
    have hv : i.val ≠ 0 := by
      intro hv
      apply hi
      apply Fin.ext
      simpa [firstCell] using hv
    omega

/-- With a positive denial frontier, the source edge changes only a permitted
prefix cell. -/
theorem deny_positive_source_ownedStep_frames {ell : Nat} (hell : 0 < ell)
    (physical : Corridor ell) (frontier : Fin ell)
    (hphysical : Represents physical (.deny frontier))
    (hpos : 0 < frontier.val) :
    Represents (ownedStep hell physical ⟨0, by omega⟩)
      (.deny frontier : ValidatorPhase ell) := by
  rcases hphysical with ⟨hleft, hprefix, hfrontier, hsuffix, hright⟩
  rw [ownedStep_source]
  dsimp only
  have hfirstPrefix : PrefixCell (physical.lane (firstCell hell)) := by
    apply hprefix
    simp [firstCell]
    exact hpos
  have hroot :
      (rootCellStep physical.left (physical.lane (firstCell hell))).1 =
          .validateSource ∧
        PrefixCell
          (rootCellStep physical.left (physical.lane (firstCell hell))).2 := by
    rw [hleft]
    exact rootCell_validate_prefix hfirstPrefix
  simp only [Represents]
  refine ⟨hroot.1, ?_, ?_, ?_, hright⟩
  · intro i hi
    by_cases hiz : i = firstCell hell
    · subst i
      simpa [updateAt] using hroot.2
    · simpa [updateAt, hiz] using hprefix i hi
  · have hne : frontier ≠ firstCell hell := by
      intro heq
      have hv := congrArg Fin.val heq
      simp [firstCell] at hv
      omega
    simp [updateAt, hne, hfrontier]
  · intro i hi
    have hne : i ≠ firstCell hell := by
      intro heq
      have hv := congrArg Fin.val heq
      simp [firstCell] at hv
      omega
    simp [updateAt, hne, hsuffix i hi]

/-- If the denial frontier has a nonempty suffix, the target edge sees the
headless empty last cell and performs the literal target maturation. -/
theorem deny_suffix_target_ownedStep_exits {ell : Nat} (hell : 0 < ell)
    (physical : Corridor ell) (frontier : Fin ell)
    (hphysical : Represents physical (.deny frontier))
    (hsuffixNonempty : frontier.val + 1 < ell) :
    Represents (ownedStep hell physical ⟨ell, by omega⟩)
      (.exited : ValidatorPhase ell) := by
  rcases hphysical with ⟨_hleft, _hprefix, _hfrontier, hsuffix, hright⟩
  have hlast : physical.lane (lastCell hell) = EmptyCell := by
    apply hsuffix
    simp [lastCell]
    omega
  simp only [Represents]
  rw [ownedStep_target]
  dsimp only
  rw [hright, hlast]
  rfl

/-- If the denial itself occupies the last carrier, its left-moving head does
not use the target edge; the literal row frames. -/
theorem deny_last_target_ownedStep_frames {ell : Nat} (hell : 0 < ell)
    (physical : Corridor ell) (frontier : Fin ell)
    (hphysical : Represents physical (.deny frontier))
    (hlast : frontier.val + 1 = ell) :
    Represents (ownedStep hell physical ⟨ell, by omega⟩)
      (.deny frontier : ValidatorPhase ell) := by
  rcases hphysical with ⟨hleft, hprefix, hfrontier, hsuffix, hright⟩
  have hfl : lastCell hell = frontier := by
    apply Fin.ext
    simp [lastCell]
    omega
  rw [ownedStep_target]
  dsimp only
  rw [hfl, hfrontier, hright]
  simp [repairedCellRootStep, literalCellRootStep, DenyCell]
  rw [← hright]
  change Represents
    { left := physical.left
      lane := updateAt physical.lane frontier DenyCell
      right := physical.right }
    (.deny frontier : ValidatorPhase ell)
  have hlane : updateAt physical.lane frontier DenyCell = physical.lane := by
    funext i
    by_cases hi : i = frontier
    · subst i
      simp [updateAt, hfrontier]
    · simp [updateAt, hi]
  rw [hlane]
  exact ⟨hleft, hprefix, hfrontier, hsuffix, hright⟩

/-- The carrier edge immediately left of a positive denial frontier moves the
denial one cell toward its source. -/
theorem deny_frontier_ownedStep_moves {ell : Nat} (hell : 0 < ell)
    (physical : Corridor ell) (frontier : Fin ell)
    (hphysical : Represents physical (.deny frontier))
    (hpos : 0 < frontier.val) :
    Represents
      (ownedStep hell physical ⟨frontier.val, by omega⟩)
      (.deny ⟨frontier.val - 1, by omega⟩ : ValidatorPhase ell) := by
  rcases hphysical with ⟨hleft, hprefix, hfrontier, hsuffix, hright⟩
  let edge : Fin (ell + 1) := ⟨frontier.val, by omega⟩
  have hsource : edge.val ≠ 0 := by simp [edge]; omega
  have htarget : edge.val ≠ ell := by simp [edge]; omega
  let previous : Fin ell := ⟨frontier.val - 1, by omega⟩
  have hli : internalLeft edge hsource = previous := by
    apply Fin.ext
    simp [edge, internalLeft, previous]
  have hri : internalRight edge htarget = frontier := by
    apply Fin.ext
    simp [edge, internalRight]
  have hpreviousPrefix : PrefixCell (physical.lane previous) := by
    apply hprefix
    simp [previous]
    omega
  rw [ownedStep_internal hell physical edge hsource htarget]
  dsimp only
  rw [hli, hri, hfrontier, cellCell_prefix_deny hpreviousPrefix]
  change Represents
    { left := physical.left
      lane := updateAt (updateAt physical.lane previous DenyCell)
        frontier EmptyCell
      right := physical.right }
    (.deny previous : ValidatorPhase ell)
  simp only [Represents]
  refine ⟨hleft, ?_, ?_, ?_, hright⟩
  · intro i hi
    have hir : i ≠ frontier := by
      intro hir
      subst i
      simp [previous] at hi
      omega
    have hil : i ≠ previous := by
      intro hil
      subst i
      omega
    simp [updateAt, hir, hil]
    exact hprefix i (by simp [previous] at hi ⊢; omega)
  · have hne : previous ≠ frontier := by
      intro h
      have hv := congrArg Fin.val h
      simp [previous] at hv
      omega
    simp [updateAt, hne]
  · intro i hi
    by_cases hir : i = frontier
    · simp [updateAt, hir]
    have hil : i ≠ previous := by
      intro hil
      subst i
      omega
    simp [updateAt, hir, hil]
    apply hsuffix
    simp [previous] at hi
    have hine : i.val ≠ frontier.val := by
      intro hval
      apply hir
      exact Fin.ext hval
    omega

/-- An internal edge strictly left of the denial frontier updates two prefix
cells within the permitted prefix language. -/
theorem deny_internal_left_ownedStep_frames {ell : Nat} (hell : 0 < ell)
    (physical : Corridor ell) (frontier : Fin ell)
    (hphysical : Represents physical (.deny frontier))
    (edge : Fin (ell + 1)) (hsource : edge.val ≠ 0)
    (hlt : edge.val < frontier.val) :
    Represents (ownedStep hell physical edge)
      (.deny frontier : ValidatorPhase ell) := by
  rcases hphysical with ⟨hleft, hprefix, hfrontier, hsuffix, hright⟩
  have htarget : edge.val ≠ ell := by omega
  let li := internalLeft edge hsource
  let ri := internalRight edge htarget
  let out := cellCellStep (physical.lane li) (physical.lane ri)
  have hliPrefix : PrefixCell (physical.lane li) := by
    apply hprefix
    simp only [li, internalLeft]
    omega
  have hriPrefix : PrefixCell (physical.lane ri) := by
    apply hprefix
    simp only [ri, internalRight]
    exact hlt
  have hout : PrefixCell out.1 ∧ PrefixCell out.2 :=
    cellCell_prefix_prefix hliPrefix hriPrefix
  rw [ownedStep_internal hell physical edge hsource htarget]
  change Represents
    { left := physical.left
      lane := updateAt (updateAt physical.lane li out.1) ri out.2
      right := physical.right }
    (.deny frontier : ValidatorPhase ell)
  simp only [Represents]
  refine ⟨hleft, ?_, ?_, ?_, hright⟩
  · intro i hi
    by_cases hir : i = ri
    · simpa [updateAt, hir] using hout.2
    by_cases hil : i = li
    · subst i
      simp [updateAt, hir, hout.1]
    · simpa [updateAt, hir, hil] using hprefix i hi
  · have hfr : frontier ≠ ri := by
      intro h
      have hv := congrArg Fin.val h
      simp [ri, internalRight] at hv
      omega
    have hfl : frontier ≠ li := by
      intro h
      have hv := congrArg Fin.val h
      simp [li, internalLeft] at hv
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
      simp [li, internalLeft] at hv
      omega
    simp [updateAt, hir, hil, hsuffix i hi]

/-- Every internal edge right of a denial frontier frames.  The adjacent edge
sees `deny-keep | E`; farther edges see `E | E`. -/
theorem deny_internal_right_ownedStep_frames {ell : Nat} (hell : 0 < ell)
    (physical : Corridor ell) (frontier : Fin ell)
    (hphysical : Represents physical (.deny frontier))
    (edge : Fin (ell + 1)) (htarget : edge.val ≠ ell)
    (hgt : frontier.val < edge.val) :
    Represents (ownedStep hell physical edge)
      (.deny frontier : ValidatorPhase ell) := by
  rcases hphysical with ⟨hleft, hprefix, hfrontier, hsuffix, hright⟩
  have hsource : edge.val ≠ 0 := by omega
  let li := internalLeft edge hsource
  let ri := internalRight edge htarget
  have hriEmpty : physical.lane ri = EmptyCell := by
    apply hsuffix
    simpa [ri, internalRight] using hgt
  have hout :
      cellCellStep (physical.lane li) (physical.lane ri) =
        (physical.lane li, physical.lane ri) := by
    by_cases hnear : edge.val = frontier.val + 1
    · have hli : li = frontier := by
        apply Fin.ext
        simp [li, internalLeft, hnear]
      rw [hli, hfrontier, hriEmpty]
      exact cellCell_deny_empty
    · have hliEmpty : physical.lane li = EmptyCell := by
        apply hsuffix
        simp only [li, internalLeft]
        omega
      rw [hliEmpty, hriEmpty]
      rfl
  rw [ownedStep_internal hell physical edge hsource htarget]
  change Represents
    { left := physical.left
      lane := updateAt
        (updateAt physical.lane li
          (cellCellStep (physical.lane li) (physical.lane ri)).1)
        ri (cellCellStep (physical.lane li) (physical.lane ri)).2
      right := physical.right }
    (.deny frontier : ValidatorPhase ell)
  rw [hout]
  have hlane :
      updateAt (updateAt physical.lane li (physical.lane li))
          ri (physical.lane ri) = physical.lane := by
    funext i
    by_cases hir : i = ri
    · subst i
      simp [updateAt]
    by_cases hil : i = li
    · subst i
      simp [updateAt, hir]
    · simp [updateAt, hir, hil]
  rw [hlane]
  exact ⟨hleft, hprefix, hfrontier, hsuffix, hright⟩

/-- Complete denial-phase edge classification. -/
theorem deny_ownedStep_refines {ell : Nat} (hell : 0 < ell)
    (physical : Corridor ell) (frontier : Fin ell)
    (hphysical : Represents physical (.deny frontier))
    (edge : Fin (ell + 1)) :
    ∃ after : ValidatorPhase ell,
      Represents (ownedStep hell physical edge) after ∧
        Next (.deny frontier) after := by
  by_cases hsource : edge.val = 0
  · have hedge : edge = ⟨0, by omega⟩ := Fin.ext hsource
    rw [hedge]
    by_cases hzero : frontier.val = 0
    · have hf : frontier = ⟨0, hell⟩ := Fin.ext hzero
      rw [hf]
      exact ⟨.anchor,
        deny_zero_source_ownedStep_returns hell physical ⟨0, hell⟩
          (by simpa [hf] using hphysical) rfl,
        .denyReturns hell⟩
    · exact ⟨.deny frontier,
        deny_positive_source_ownedStep_frames hell physical frontier hphysical
          (Nat.pos_of_ne_zero hzero),
        .frame (.deny frontier)⟩
  by_cases htarget : edge.val = ell
  · have hedge : edge = ⟨ell, by omega⟩ := Fin.ext htarget
    rw [hedge]
    by_cases hsuffix : frontier.val + 1 < ell
    · exact ⟨.exited,
        deny_suffix_target_ownedStep_exits hell physical frontier hphysical
          hsuffix,
        .denyMatures frontier hsuffix⟩
    · exact ⟨.deny frontier,
        deny_last_target_ownedStep_frames hell physical frontier hphysical
          (by omega),
        .frame (.deny frontier)⟩
  by_cases hmove : edge.val = frontier.val
  · have hpos : 0 < frontier.val := by omega
    have hedge : edge = ⟨frontier.val, by omega⟩ := Fin.ext hmove
    rw [hedge]
    exact ⟨.deny ⟨frontier.val - 1, by omega⟩,
      deny_frontier_ownedStep_moves hell physical frontier hphysical hpos,
      .denyMoves frontier hpos⟩
  by_cases hleftSide : edge.val < frontier.val
  · exact ⟨.deny frontier,
      deny_internal_left_ownedStep_frames hell physical frontier hphysical
        edge hsource hleftSide,
      .frame (.deny frontier)⟩
  · exact ⟨.deny frontier,
      deny_internal_right_ownedStep_frames hell physical frontier hphysical
        edge htarget (by omega),
      .frame (.deny frontier)⟩

/-- Literal physical-to-abstract refinement for every active coherent phase
and every owned edge, at every positive corridor length. -/
theorem active_ownedStep_refines {ell : Nat} (hell : 0 < ell)
    (physical : Corridor ell) (before : ValidatorPhase ell)
    (hphysical : Represents physical before) (hactive : before ≠ .exited)
    (edge : Fin (ell + 1)) :
    ∃ after : ValidatorPhase ell,
      Represents (ownedStep hell physical edge) after ∧ Next before after := by
  cases before with
  | anchor => exact anchor_ownedStep_refines hell physical hphysical edge
  | query frontier =>
      exact query_ownedStep_refines hell physical frontier hphysical edge
  | deny frontier =>
      exact deny_ownedStep_refines hell physical frontier hphysical edge
  | exited => exact False.elim (hactive rfl)

#print axioms deny_ownedStep_refines
#print axioms active_ownedStep_refines

end PPLLV2ValidatorPhysicalRefinement
