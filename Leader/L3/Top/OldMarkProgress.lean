import Leader.L3.Top.OldMark
import Leader.L3.Top.MarkedSelect

/-!
# Q7: the nominated edge lowers the marked rank

Consumer: `Leader/L3/Top/OldMarkStep.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false

/-- The registers whose real edge strictly lowers the marked rank.

Consumer: `pair_strict_old`. -/
def SelO (ob vb : Bool) (x : Cell) (ox : Bool) (y : Cell) : Prop :=
  (x.c ≠ .off ∧ (violC ob x = true ∨ vb = true)) ∨
  (x.i = .x ∧ x.c = .off ∧ vb = true) ∨
  (x.i.isP = true ∧ x.c = .off ∧ (ob = true ∨ ox = true) ∧
    (y = { i := .e, c := .off } ∨ (y.i.isS = true ∧ y.c = .off))) ∨
  x.c = .inh

/-- The same at the terminal register.

Consumer: `term_strict_old`. -/
def SelOT (ob vb : Bool) (x : Cell) (ox : Bool) : Prop :=
  (x.c ≠ .off ∧ (violC ob x = true ∨ vb = true)) ∨
  (x.i = .x ∧ x.c = .off ∧ vb = true) ∨
  (x.i.isP = true ∧ x.c = .off ∧ (ob = true ∨ ox = true)) ∨
  x.c = .inh

/-- `SelO` as a Boolean. -/
private def selOB (ob vb : Bool) (x : Cell) (ox : Bool) (y : Cell) : Bool :=
  decide ((x.c ≠ .off ∧ (violC ob x = true ∨ vb = true)) ∨
    (x.i = .x ∧ x.c = .off ∧ vb = true) ∨
    (x.i.isP = true ∧ x.c = .off ∧ (ob = true ∨ ox = true) ∧
      (y = { i := .e, c := .off } ∨ (y.i.isS = true ∧ y.c = .off))) ∨
    x.c = .inh)

private theorem selOB_of {ob vb : Bool} {x : Cell} {ox : Bool} {y : Cell}
    (h : SelO ob vb x ox y) : selOB ob vb x ox y = true :=
  decide_eq_true h

/-- The premises of the strict old-window edge, as a Boolean. -/
private def premStrictOld (x y : Cell) (ox oy ob vb : Bool) : Bool :=
  (!vb || ob) && (!ox || x.i.isP) && (!oy || y.i.isP) &&
    (!decide (x.c = .fresh) || decide (x.i = .e)) && (!decide (y.c = .fresh) || decide (y.i = .e)) &&
    selOB ob vb x ox y

open Forms in
/-- Strict decrease of a selected old-window edge `x y ↦ c1 c2`, as forms (`r = p + 2 + d`). -/
private def chkStrictOldAt (x y c1 c2 : Cell) (ox oy ob vb : Bool) : Bool :=
  !premStrictOld x y ox oy ob vb ||
    LF.le (((wtF 2 0 ob vb (mk c1 (oldX x c1 ox))).add
        (wtF 2 1 (nob ob (mk c1 (oldX x c1 ox))) (nvb ob vb (mk c1 (oldX x c1 ox))) (mk c2 (oldY x y c2 ox oy)))).add LF.one)
      ((wtF 2 0 ob vb (mk x ox)).add (wtF 2 1 (nob ob (mk x ox)) (nvb ob vb (mk x ox)) (mk y oy)))

open Forms in
/-- All flag patterns of one edge input; `pair` is evaluated once. -/
private def chkStrictOld (border : Bool) (x y : Cell) : Bool :=
  withCell (pair border false x y).1 fun c1 => withCell (pair border false x y).2 fun c2 =>
    allBool.all fun ox => allBool.all fun oy => allBool.all fun ob => allBool.all fun vb =>
      chkStrictOldAt x y c1 c2 ox oy ob vb

open Forms in
/-- The check on every edge input (648 evaluations of `pair`, 10368 flag patterns). -/
private theorem chkStrictOld_all :
    allBool.all (fun border => allCell.all fun x => allCell.all fun y => chkStrictOld border x y) =
      true := by
  decide +kernel

/-- `premStrictOld` from the hypotheses. -/
private theorem premStrictOld_of {x y : Cell} {ox oy ob vb : Bool} (hv : vb = true → ob = true)
    (hox : ox = true → x.i.isP = true) (hoy : oy = true → y.i.isP = true)
    (hfx : x.c = .fresh → x.i = .e) (hfy : y.c = .fresh → y.i = .e)
    (hsel : SelO ob vb x ox y) : premStrictOld x y ox oy ob vb = true := by
  unfold premStrictOld
  simp only [Forms.impI hv, Forms.impI hox, Forms.impI hoy, Forms.impD hfx, Forms.impD hfy,
    selOB_of hsel, Bool.and_self]

/-- The selected window edge strictly lowers the marked weight.

Consumer: `rank_edge_old_lt`. -/
theorem pair_strict_old (r p : Nat) (hp : p + 1 < r) (border : Bool)
    (x y : Cell) (ox oy : Bool) (ob vb : Bool) (hv : vb = true → ob = true)
    (hox : ox = true → x.i.isP = true) (hoy : oy = true → y.i.isP = true)
    (hfx : x.c = .fresh → x.i = .e) (hfy : y.c = .fresh → y.i = .e)
    (hsel : SelO ob vb x ox y) :
    wt r p ob vb (mk (pair border false x y).1 (oldX x (pair border false x y).1 ox)) +
      wt r (p + 1) (nob ob (mk (pair border false x y).1 (oldX x (pair border false x y).1 ox)))
        (nvb ob vb (mk (pair border false x y).1 (oldX x (pair border false x y).1 ox)))
        (mk (pair border false x y).2
          (oldY x y (pair border false x y).2 ox oy)) + 1 ≤
    wt r p ob vb (mk x ox) +
      wt r (p + 1) (nob ob (mk x ox)) (nvb ob vb (mk x ox)) (mk y oy) := by
  obtain ⟨d, rfl⟩ : ∃ d, r = p + 2 + d := ⟨r - (p + 2), by omega⟩
  have h1 := Forms.allB (Forms.allB (Forms.allB chkStrictOld_all (Forms.memB border))
    (Forms.memC x)) (Forms.memC y)
  simp only [chkStrictOld, Forms.withCell_eq] at h1
  have h2 := Forms.allB (Forms.allB (Forms.allB (Forms.allB h1 (Forms.memB ox))
    (Forms.memB oy)) (Forms.memB ob)) (Forms.memB vb)
  have h := Forms.LF.le_sound
    (Forms.impB h2 (premStrictOld_of hv hox hoy hfx hfy hsel)) p d
  simp only [Forms.LF.ev_add, Forms.LF.ev_one] at h
  rw [Forms.wt_eq _ _ p d 2 0 rfl (Nat.add_zero p).symm (by omega),
    Forms.wt_eq _ _ p d 2 0 rfl (Nat.add_zero p).symm (by omega),
    Forms.wt_eq _ (p + 1) p d 2 1 rfl rfl (by omega),
    Forms.wt_eq _ (p + 1) p d 2 1 rfl rfl (by omega)]
  exact h

/-- The selected terminal edge strictly lowers the marked weight.

Consumer: `rank_term_old_lt`. -/
theorem term_strict_old (r p : Nat) (hp : p + 1 = r) (x : Cell) (ox : Bool) (ob vb : Bool)
    (hv : vb = true → ob = true) (hox : ox = true → x.i.isP = true)
    (hfx : x.c = .fresh → x.i = .e) (hsel : SelOT ob vb x ox) :
    wt r p ob vb (mk (pair false true x { i := .e, c := .off }).1
      (oldX x (pair false true x { i := .e, c := .off }).1 ox)) + 1 ≤
      wt r p ob vb (mk x ox) := by
  rcases x with ⟨xi, xc⟩
  cases xi <;> cases xc <;> cases ox <;> cases ob <;> cases vb <;>
    simp (config := { decide := true })
      [SelOT, pair, inSlots, carries, wt, gateW, violC, mk, oldX, Inp.isP, Inp.isS]
      at hv hox hfx hsel ⊢ <;> omega

/-- Register `p` is selected in the marked window.

Consumer: `rank_progress_old`. -/
def SelOAt (r : Nat) (cells : Nat → Cell) (o : Nat → Bool) (p : Nat) : Prop :=
  if p + 1 < r then
    SelO (scanFlags (markCells cells o) p 0 false false).1
      (scanFlags (markCells cells o) p 0 false false).2 (cells p) (o p) (cells (p + 1))
  else
    SelOT (scanFlags (markCells cells o) p 0 false false).1
      (scanFlags (markCells cells o) p 0 false false).2 (cells p) (o p)

/-- The flags after the edge of register `p`.

Consumer: `rank_edge_old_lt`. -/
def flagsAt (r : Nat) (cells : Nat → Cell) (o : Nat → Bool) (p : Nat) : Nat → Bool :=
  if p + 1 < r then flagsEdge r cells o p else flagsTerm r cells o

/-- The edge of a selected register strictly lowers the marked rank.

Consumer: `rank_progress_old`. -/
theorem rank_edge_old_lt (r p : Nat) (hp : p < r) (cells : Nat → Cell) (o : Nat → Bool)
    (ho : ∀ j, j < r → o j = true → (cells j).i.isP = true)
    (hf : ∀ j, j < r → (cells j).c = .fresh → (cells j).i = .e)
    (hsel : SelOAt r cells o p) :
    rank r (markCells (edgeStep r cells p) (flagsAt r cells o p)) + 1 ≤
      rank r (markCells cells o) := by
  unfold edgeStep flagsAt
  unfold SelOAt at hsel
  by_cases h : p + 1 < r
  · rw [if_pos h] at hsel ⊢
    rw [if_pos h]
    apply patch_two_lt r p h (markCells cells o)
    · intro i h1 h2
      simp [markCells, setTwo, flagsEdge, h1, h2]
    · intro ob vb hfl hv
      rw [hfl] at hsel
      have h1 := pair_strict_old r p h (decide (p = 0)) (cells p) (cells (p + 1)) (o p)
        (o (p + 1)) ob vb hv (ho p hp) (ho (p + 1) h) (hf p hp) (hf (p + 1) h) hsel
      have h2 := pair_local_old r p h (decide (p = 0)) (cells p) (cells (p + 1)) (o p)
        (o (p + 1)) ob vb hv (ho p hp) (ho (p + 1) h) (hf p hp) (hf (p + 1) h)
      simpa [markCells, setTwo, flagsEdge] using ⟨h1, h2.2.1, h2.2.2⟩
  · rw [if_neg h] at hsel ⊢
    rw [if_neg h]
    have hpe : p = r - 1 := by omega
    subst hpe
    apply patch_last_lt r (r - 1) (by omega) (markCells cells o)
    · intro i h1
      simp [markCells, setOne, flagsTerm, h1]
    · intro ob vb hfl hv
      rw [hfl] at hsel
      have := term_strict_old r (r - 1) (by omega) (cells (r - 1)) (o (r - 1)) ob vb hv
        (ho (r - 1) hp) (hf (r - 1) hp) hsel
      simpa [markCells, setOne, flagsTerm] using this

end MarkedCells
end L3

#print axioms L3.MarkedCells.pair_strict_old
#print axioms L3.MarkedCells.rank_edge_old_lt
