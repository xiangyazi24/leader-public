import Leader.L3.Top.MarkedRank
import Leader.L3.Top.MarkedForms

/-!
# Q7: the rightmost-violator edge lowers the rank

Off rank zero there is a window edge that strictly lowers the rank: the edge of
the rightmost pending input with an obstacle at or before it (move, settle,
terminal row, or host cleanup), the edge of the obstacle ahead of it (front or
carry), or, with no violator, the edge of an inherited carry.

Consumer: `Leader/L3/Top/MarkedDebtRows.lean` (nominated-edge row).
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false

/-- The registers whose edge strictly lowers the rank.

Consumer: `rank_progress`. -/
def Sel (ob vb : Bool) (x y : Cell) : Prop :=
  (x.c ≠ .off ∧ (violC ob x = true ∨ vb = true)) ∨
  (x.i = .x ∧ x.c = .off ∧ vb = true) ∨
  (x.i.isP = true ∧ x.c = .off ∧ ob = true ∧
    (y = { i := .e, c := .off } ∨ (y.i.isS = true ∧ y.c = .off))) ∨
  x.c = .inh

/-- The same at the terminal register.

Consumer: `rank_progress`. -/
def SelT (ob vb : Bool) (x : Cell) : Prop :=
  (x.c ≠ .off ∧ (violC ob x = true ∨ vb = true)) ∨
  (x.i = .x ∧ x.c = .off ∧ vb = true) ∨
  (x.i.isP = true ∧ x.c = .off ∧ ob = true) ∨
  x.c = .inh

open Forms in
/-- `Sel` as a Boolean. -/
private def selB (ob vb : Bool) (x y : Cell) : Bool :=
  decide ((x.c ≠ .off ∧ (violC ob x = true ∨ vb = true)) ∨
    (x.i = .x ∧ x.c = .off ∧ vb = true) ∨
    (x.i.isP = true ∧ x.c = .off ∧ ob = true ∧
      (y = { i := .e, c := .off } ∨ (y.i.isS = true ∧ y.c = .off))) ∨
    x.c = .inh)

private theorem selB_of {ob vb : Bool} {x y : Cell} (h : Sel ob vb x y) :
    selB ob vb x y = true :=
  decide_eq_true h

open Forms in
/-- Strict decrease of a selected window edge `x y ↦ c1 c2`, as forms (`r = p + 2 + d`). -/
private def chkStrictAt (x y c1 c2 : Cell) (ob vb : Bool) : Bool :=
  !((!vb || ob) && selB ob vb x y) ||
    LF.le (((wtF 2 0 ob vb c1).add (wtF 2 1 (nob ob c1) (nvb ob vb c1) c2)).add LF.one)
      ((wtF 2 0 ob vb x).add (wtF 2 1 (nob ob x) (nvb ob vb x) y))

open Forms in
/-- All flag patterns of one edge input; `pair` is evaluated once. -/
private def chkStrict (border : Bool) (x y : Cell) : Bool :=
  withCell (pair border false x y).1 fun c1 => withCell (pair border false x y).2 fun c2 =>
    allBool.all fun ob => allBool.all fun vb => chkStrictAt x y c1 c2 ob vb

open Forms in
/-- The check on every edge input (648 evaluations of `pair`, 2592 flag patterns). -/
private theorem chkStrict_all :
    allBool.all (fun border => allCell.all fun x => allCell.all fun y => chkStrict border x y) =
      true := by
  decide +kernel

/-- The selected window edge strictly lowers the local weight.

Consumer: `rank_progress`. -/
theorem pair_strict (r p : Nat) (hp : p + 1 < r) (border : Bool)
    (x y : Cell) (ob vb : Bool) (hv : vb = true → ob = true)
    (hsel : Sel ob vb x y) :
    wt r p ob vb (pair border false x y).1 +
      wt r (p + 1) (nob ob (pair border false x y).1)
        (nvb ob vb (pair border false x y).1) (pair border false x y).2 + 1 ≤
    wt r p ob vb x +
      wt r (p + 1) (nob ob x) (nvb ob vb x) y := by
  obtain ⟨d, rfl⟩ : ∃ d, r = p + 2 + d := ⟨r - (p + 2), by omega⟩
  have h1 := Forms.allB (Forms.allB (Forms.allB chkStrict_all (Forms.memB border))
    (Forms.memC x)) (Forms.memC y)
  simp only [chkStrict, Forms.withCell_eq] at h1
  have h2 := Forms.allB (Forms.allB h1 (Forms.memB ob)) (Forms.memB vb)
  have h := Forms.LF.le_sound (Forms.impB h2 (by
    simp only [Forms.impI hv, selB_of hsel, Bool.and_self])) p d
  simp only [Forms.LF.ev_add, Forms.LF.ev_one] at h
  rw [Forms.wt_eq _ _ p d 2 0 rfl (Nat.add_zero p).symm (by omega),
    Forms.wt_eq _ _ p d 2 0 rfl (Nat.add_zero p).symm (by omega),
    Forms.wt_eq _ (p + 1) p d 2 1 rfl rfl (by omega),
    Forms.wt_eq _ (p + 1) p d 2 1 rfl rfl (by omega)]
  exact h

/-- The selected terminal edge strictly lowers the local weight.

Consumer: `rank_progress`. -/
theorem term_strict (r p : Nat) (hp : p + 1 = r) (x : Cell) (ob vb : Bool)
    (hv : vb = true → ob = true) (hsel : SelT ob vb x) :
    wt r p ob vb (pair false true x { i := .e, c := .off }).1 + 1 ≤ wt r p ob vb x := by
  rcases x with ⟨xi, xc⟩
  cases xi <;> cases xc <;> cases ob <;> cases vb <;>
    simp (config := { decide := true })
      [SelT, pair, inSlots, carries, wt, gateW, violC, Inp.isP, Inp.isS] at hv hsel ⊢ <;>
    omega

/-- Patch of two cells, with a strict local decrease.

Consumer: `rank_progress`. -/
theorem patch_two_lt (r p : Nat) (hp : p + 1 < r) (cells cells' : Nat → Cell)
    (hout : ∀ i, i ≠ p → i ≠ p + 1 → cells' i = cells i)
    (hloc : ∀ ob vb, scanFlags cells p 0 false false = (ob, vb) →
      (vb = true → ob = true) →
      wt r p ob vb (cells' p) +
        wt r (p + 1) (nob ob (cells' p)) (nvb ob vb (cells' p)) (cells' (p + 1)) + 1 ≤
      wt r p ob vb (cells p) +
        wt r (p + 1) (nob ob (cells p)) (nvb ob vb (cells p)) (cells (p + 1)) ∧
      (nob (nob ob (cells' p)) (cells' (p + 1)) = true →
        nob (nob ob (cells p)) (cells (p + 1)) = true) ∧
      (nvb (nob ob (cells' p)) (nvb ob vb (cells' p)) (cells' (p + 1)) = true →
        nvb (nob ob (cells p)) (nvb ob vb (cells p)) (cells (p + 1)) = true)) :
    rank r cells' + 1 ≤ rank r cells := by
  obtain ⟨m, hm⟩ : ∃ m, r = p + (m + 2) := ⟨r - p - 2, by omega⟩
  have hpre := scan_congr r cells cells' p 0 false false
    (fun i _ hi => hout i (by omega) (by omega))
  have hvalid := scanFlags_valid cells p 0 false false (fun h => by simp at h)
  have hrank : ∀ cs : Nat → Cell, rank r cs =
      scan r cs p 0 false false +
        scan r cs (m + 2) p (scanFlags cs p 0 false false).1
          (scanFlags cs p 0 false false).2 := by
    intro cs
    unfold rank
    have h := scan_add r cs p (m + 2) 0 false false
    rw [← hm, Nat.zero_add] at h
    exact h
  rw [hrank cells', hrank cells, hpre.1, hpre.2]
  generalize hf : scanFlags cells p 0 false false = f at *
  obtain ⟨ob, vb⟩ := f
  have hloc' := hloc ob vb rfl hvalid
  have hsuf := scan_congr r cells cells' m (p + 2) (nob (nob ob (cells' p)) (cells' (p + 1)))
    (nvb (nob ob (cells' p)) (nvb ob vb (cells' p)) (cells' (p + 1)))
    (fun i h1 h2 => hout i (by omega) (by omega))
  have hmono := scan_mono r cells m (p + 2)
    (nob (nob ob (cells' p)) (cells' (p + 1))) (nob (nob ob (cells p)) (cells (p + 1)))
    (nvb (nob ob (cells' p)) (nvb ob vb (cells' p)) (cells' (p + 1)))
    (nvb (nob ob (cells p)) (nvb ob vb (cells p)) (cells (p + 1)))
    hloc'.2.1 hloc'.2.2
  have e2 : ∀ cs : Nat → Cell, scan r cs (m + 2) p ob vb =
      wt r p ob vb (cs p) +
        (wt r (p + 1) (nob ob (cs p)) (nvb ob vb (cs p)) (cs (p + 1)) +
          scan r cs m (p + 2) (nob (nob ob (cs p)) (cs (p + 1)))
            (nvb (nob ob (cs p)) (nvb ob vb (cs p)) (cs (p + 1)))) := by
    intro cs
    rfl
  rw [e2 cells', e2 cells, hsuf.1]
  have := hloc'.1
  omega

/-- Patch of the last cell, with a strict local decrease.

Consumer: `rank_progress`. -/
theorem patch_last_lt (r p : Nat) (hp : p + 1 = r) (cells cells' : Nat → Cell)
    (hout : ∀ i, i ≠ p → cells' i = cells i)
    (hloc : ∀ ob vb, scanFlags cells p 0 false false = (ob, vb) →
      (vb = true → ob = true) →
      wt r p ob vb (cells' p) + 1 ≤ wt r p ob vb (cells p)) :
    rank r cells' + 1 ≤ rank r cells := by
  have hpre := scan_congr r cells cells' p 0 false false
    (fun i _ hi => hout i (by omega))
  have hvalid := scanFlags_valid cells p 0 false false (fun h => by simp at h)
  have hrank : ∀ cs : Nat → Cell, rank r cs =
      scan r cs p 0 false false +
        scan r cs 1 p (scanFlags cs p 0 false false).1
          (scanFlags cs p 0 false false).2 := by
    intro cs
    unfold rank
    have h := scan_add r cs p 1 0 false false
    rw [← hp, Nat.zero_add] at h
    rw [hp] at h
    exact h
  rw [hrank cells', hrank cells, hpre.1, hpre.2]
  generalize hf : scanFlags cells p 0 false false = f at *
  obtain ⟨ob, vb⟩ := f
  have hloc' := hloc ob vb rfl hvalid
  have e2 : ∀ cs : Nat → Cell, scan r cs 1 p ob vb = wt r p ob vb (cs p) := by
    intro cs
    simp [scan]
  rw [e2 cells', e2 cells]
  omega

/-- The window edge at register `p` (the terminal edge when `p` is last).

Consumer: `rank_progress`. -/
def edgeStep (r : Nat) (cells : Nat → Cell) (p : Nat) : Nat → Cell :=
  if p + 1 < r then
    setTwo cells p (pair (decide (p = 0)) false (cells p) (cells (p + 1))).1
      (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2
  else
    setOne cells (r - 1) (pair false true (cells (r - 1)) { i := .e, c := .off }).1

/-- The edge of register `p` is an abstract step.

Consumer: `rank_progress`. -/
theorem edgeStep_step (r : Nat) (cells : Nat → Cell) (p : Nat) (hp : p < r) :
    Step r cells (edgeStep r cells p) := by
  unfold edgeStep
  by_cases h : p + 1 < r
  · rw [if_pos h]
    exact Step.edge p h
  · rw [if_neg h]
    exact Step.term

/-- The register `p` is selected in the window.

Consumer: `rank_progress`. -/
def SelAt (r : Nat) (cells : Nat → Cell) (p : Nat) : Prop :=
  if p + 1 < r then
    Sel (scanFlags cells p 0 false false).1 (scanFlags cells p 0 false false).2
      (cells p) (cells (p + 1))
  else
    SelT (scanFlags cells p 0 false false).1 (scanFlags cells p 0 false false).2 (cells p)

/-- The edge of a selected register strictly lowers the rank.

Consumer: `rank_progress`. -/
theorem edge_lt (r p : Nat) (hp : p < r) (cells : Nat → Cell) (hsel : SelAt r cells p) :
    rank r (edgeStep r cells p) + 1 ≤ rank r cells := by
  unfold edgeStep
  unfold SelAt at hsel
  by_cases h : p + 1 < r
  · rw [if_pos h] at hsel ⊢
    apply patch_two_lt r p h
    · intro i h1 h2
      simp [setTwo, h1, h2]
    · intro ob vb hf hv
      rw [hf] at hsel
      have h1 := pair_strict r p h (decide (p = 0)) (cells p) (cells (p + 1)) ob vb hv hsel
      have h2 := pair_local r p h (decide (p = 0)) (cells p) (cells (p + 1)) ob vb hv
      simpa [setTwo] using ⟨h1, h2.2.1, h2.2.2⟩
  · rw [if_neg h] at hsel ⊢
    apply patch_last_lt r (r - 1) (by omega)
    · intro i h1
      simp [setOne, h1]
    · intro ob vb hf hv
      have hp' : p = r - 1 := by omega
      subst hp'
      rw [hf] at hsel
      have := term_strict r (r - 1) (by omega) (cells (r - 1)) ob vb hv hsel
      simpa [setOne] using this

end MarkedCells
end L3

#print axioms L3.MarkedCells.edge_lt
