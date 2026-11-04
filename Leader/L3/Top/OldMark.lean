import Leader.L3.Top.MarkedGood
import Leader.L3.Top.MarkedSelect

/-!
# Q7: the old-pending term of the marked-debt rank

An *old* pending input (its audit atom is not post-anchor) is read by the rank as a
pending input carrying an inherited carry: `mk c true = (c.i, inh)`.  The rank of the
marked window is still at most `r (4 r + 4)`, because the per-register bound already
covers a pending input on an inherited carry; the new term costs nothing in the budget.

The abstract window dynamics are unchanged; only the flags `o` ride along: a pending
input keeps its flag when it stays, hands it to the register it moves into, and never
gains one.  This module proves, for the marked rank:

* `pair_local_old` / `term_local_old` / `port_local_old` : no edge raises it;
* the mark monotonicity `rank_mark_mono` : clearing marks does not raise it.

Consumer: `Leader/L3/Top/OldMarkStep.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false

/-- Read an old pending input as a pending input with an inherited carry.

Consumer: `markCells`. -/
def mk (c : Cell) (o : Bool) : Cell := if o then { c with c := .inh } else c

/-- The marked window.

Consumer: `rank_mark_mono`. -/
def markCells (cells : Nat → Cell) (o : Nat → Bool) : Nat → Cell := fun j => mk (cells j) (o j)

/-- The largest flags after an edge: a staying pending input keeps its flag, a moved one
passes it on.

Consumer: `pair_local_old`. -/
def oldX (x x' : Cell) (ox : Bool) : Bool := ox && x'.i.isP

/-- The flag of the responder after an edge.

Consumer: `pair_local_old`. -/
def oldY (x y y' : Cell) (ox oy : Bool) : Bool :=
  (oy && y'.i.isP && y.i.isP) || (ox && x.i.isP && !y.i.isP && y'.i.isP)

open Forms in
/-- The premises of the old-window edge facts, as a Boolean. -/
private def premOld (x y : Cell) (ox oy ob vb : Bool) : Bool :=
  (!vb || ob) && (!ox || x.i.isP) && (!oy || y.i.isP) &&
    (!decide (x.c = .fresh) || decide (x.i = .e)) && (!decide (y.c = .fresh) || decide (y.i = .e))

open Forms in
/-- The three facts of an old-window edge `x y ↦ c1 c2` (weight, both scan flags), as forms
(`r = p + 2 + d`). -/
private def chkLocalOldAt (x y c1 c2 : Cell) (ox oy ob vb : Bool) : Bool :=
  !premOld x y ox oy ob vb ||
    (LF.le ((wtF 2 0 ob vb (mk c1 (oldX x c1 ox))).add
        (wtF 2 1 (nob ob (mk c1 (oldX x c1 ox))) (nvb ob vb (mk c1 (oldX x c1 ox))) (mk c2 (oldY x y c2 ox oy))))
      ((wtF 2 0 ob vb (mk x ox)).add (wtF 2 1 (nob ob (mk x ox)) (nvb ob vb (mk x ox)) (mk y oy))) &&
     (!(nob (nob ob (mk c1 (oldX x c1 ox))) (mk c2 (oldY x y c2 ox oy))) || nob (nob ob (mk x ox)) (mk y oy)) &&
     (!(nvb (nob ob (mk c1 (oldX x c1 ox))) (nvb ob vb (mk c1 (oldX x c1 ox))) (mk c2 (oldY x y c2 ox oy))) ||
        nvb (nob ob (mk x ox)) (nvb ob vb (mk x ox)) (mk y oy)))

open Forms in
/-- All flag patterns of one edge input; `pair` is evaluated once. -/
private def chkLocalOld (border : Bool) (x y : Cell) : Bool :=
  withCell (pair border false x y).1 fun c1 => withCell (pair border false x y).2 fun c2 =>
    allBool.all fun ox => allBool.all fun oy => allBool.all fun ob => allBool.all fun vb =>
      chkLocalOldAt x y c1 c2 ox oy ob vb

open Forms in
/-- The check on every edge input (648 evaluations of `pair`, 10368 flag patterns). -/
private theorem chkLocalOld_all :
    allBool.all (fun border => allCell.all fun x => allCell.all fun y => chkLocalOld border x y) =
      true := by
  decide +kernel

/-- `premOld` from the hypotheses. -/
private theorem premOld_of {x y : Cell} {ox oy ob vb : Bool} (hv : vb = true → ob = true)
    (hox : ox = true → x.i.isP = true) (hoy : oy = true → y.i.isP = true)
    (hfx : x.c = .fresh → x.i = .e) (hfy : y.c = .fresh → y.i = .e) :
    premOld x y ox oy ob vb = true := by
  unfold premOld
  simp only [Forms.impI hv, Forms.impI hox, Forms.impI hoy, Forms.impD hfx, Forms.impD hfy,
    Bool.and_self]

/-- No edge raises the marked rank (local weight and flags).

Consumer: `rank_step_old`. -/
theorem pair_local_old (r p : Nat) (hp : p + 1 < r) (border : Bool)
    (x y : Cell) (ox oy : Bool) (ob vb : Bool) (hv : vb = true → ob = true)
    (hox : ox = true → x.i.isP = true) (hoy : oy = true → y.i.isP = true)
    (hfx : x.c = .fresh → x.i = .e) (hfy : y.c = .fresh → y.i = .e) :
    wt r p ob vb (mk (pair border false x y).1 (oldX x (pair border false x y).1 ox)) +
      wt r (p + 1) (nob ob (mk (pair border false x y).1 (oldX x (pair border false x y).1 ox)))
        (nvb ob vb (mk (pair border false x y).1 (oldX x (pair border false x y).1 ox)))
        (mk (pair border false x y).2
          (oldY x y (pair border false x y).2 ox oy)) ≤
    wt r p ob vb (mk x ox) +
      wt r (p + 1) (nob ob (mk x ox)) (nvb ob vb (mk x ox)) (mk y oy) ∧
    (nob (nob ob (mk (pair border false x y).1 (oldX x (pair border false x y).1 ox)))
        (mk (pair border false x y).2 (oldY x y (pair border false x y).2 ox oy)) = true →
      nob (nob ob (mk x ox)) (mk y oy) = true) ∧
    (nvb (nob ob (mk (pair border false x y).1 (oldX x (pair border false x y).1 ox)))
        (nvb ob vb (mk (pair border false x y).1 (oldX x (pair border false x y).1 ox)))
        (mk (pair border false x y).2 (oldY x y (pair border false x y).2 ox oy)) = true →
      nvb (nob ob (mk x ox)) (nvb ob vb (mk x ox)) (mk y oy) = true) := by
  obtain ⟨d, rfl⟩ : ∃ d, r = p + 2 + d := ⟨r - (p + 2), by omega⟩
  have h1 := Forms.allB (Forms.allB (Forms.allB chkLocalOld_all (Forms.memB border))
    (Forms.memC x)) (Forms.memC y)
  simp only [chkLocalOld, Forms.withCell_eq] at h1
  have h2 := Forms.allB (Forms.allB (Forms.allB (Forms.allB h1 (Forms.memB ox))
    (Forms.memB oy)) (Forms.memB ob)) (Forms.memB vb)
  obtain ⟨hw, hn, hvv⟩ := Forms.and3B (Forms.impB h2 (premOld_of hv hox hoy hfx hfy))
  refine ⟨?_, Forms.impB hn, Forms.impB hvv⟩
  have h := Forms.LF.le_sound hw p d
  simp only [Forms.LF.ev_add] at h
  rw [Forms.wt_eq _ _ p d 2 0 rfl (Nat.add_zero p).symm (by omega),
    Forms.wt_eq _ _ p d 2 0 rfl (Nat.add_zero p).symm (by omega),
    Forms.wt_eq _ (p + 1) p d 2 1 rfl rfl (by omega),
    Forms.wt_eq _ (p + 1) p d 2 1 rfl rfl (by omega)]
  exact h

/-- The terminal edge does not raise the marked weight.

Consumer: `rank_term_old`. -/
theorem term_local_old (r p : Nat) (hp : p < r) (x y : Cell) (ox : Bool) (ob vb : Bool)
    (hv : vb = true → ob = true) (hox : ox = true → x.i.isP = true)
    (hfx : x.c = .fresh → x.i = .e) :
    wt r p ob vb (mk (pair false true x y).1 (oldX x (pair false true x y).1 ox)) ≤
      wt r p ob vb (mk x ox) := by
  rcases x with ⟨xi, xc⟩
  cases xi <;> cases xc <;> cases ox <;> cases ob <;> cases vb <;>
    simp (config := { decide := true })
      [pair, inSlots, carries, wt, gateW, violC, mk, oldX, Inp.isP, Inp.isS]
      at hv hox hfx ⊢ <;> omega

/-- The port cleanup and the port acceptance do not raise the marked weight.

Consumer: `rank_port_old`. -/
theorem port_local_old (r : Nat) (c c' : Cell) (o : Bool)
    (hc' : c' = portClean c ∨ ∃ t, c' = portAccept t c)
    (ho : o = true → c.i.isP = true) (hf : c.c = .fresh → c.i = .e) :
    wt r 0 false false (mk c' (oldX c c' o)) ≤ wt r 0 false false (mk c o) ∧
    (nob false (mk c' (oldX c c' o)) = true → nob false (mk c o) = true) ∧
    (nvb false false (mk c' (oldX c c' o)) = true → nvb false false (mk c o) = true) := by
  rcases c with ⟨ci, cc⟩
  rcases hc' with rfl | ⟨t, rfl⟩ <;>
  cases ci <;> cases cc <;> cases o <;>
    simp (config := { decide := true })
      [portClean, portAccept, wt, gateW, violC, obC, nob, nvb, mk, oldX, Inp.isP, Inp.isS]
      at ho hf ⊢ <;>
    (try cases t) <;>
    simp (config := { decide := true })
      [portClean, portAccept, wt, gateW, violC, obC, nob, nvb, mk, oldX, Inp.isP, Inp.isS]
      at ho hf ⊢ <;> omega

/-- The flags after the edge of register `p`.

Consumer: `rank_edge_old`. -/
def flagsEdge (r : Nat) (cells : Nat → Cell) (o : Nat → Bool) (p : Nat) : Nat → Bool :=
  fun j =>
    if j = p then oldX (cells p) (pair (decide (p = 0)) false (cells p) (cells (p + 1))).1 (o p)
    else if j = p + 1 then
      oldY (cells p) (cells (p + 1)) (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2
        (o p) (o (p + 1))
    else o j

/-- The marked rank does not rise along a window edge.

Consumer: `rank_step_old`. -/
theorem rank_edge_old (r p : Nat) (hp : p + 1 < r) (cells : Nat → Cell) (o : Nat → Bool)
    (ho : ∀ j, j < r → o j = true → (cells j).i.isP = true)
    (hf : ∀ j, j < r → (cells j).c = .fresh → (cells j).i = .e) :
    rank r (markCells
      (setTwo cells p (pair (decide (p = 0)) false (cells p) (cells (p + 1))).1
        (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2)
      (flagsEdge r cells o p)) ≤ rank r (markCells cells o) := by
  apply patch_two r p hp (markCells cells o)
  · intro i h1 h2
    simp [markCells, setTwo, flagsEdge, h1, h2]
  · intro ob vb _ hv
    have := pair_local_old r p hp (decide (p = 0)) (cells p) (cells (p + 1)) (o p) (o (p + 1))
      ob vb hv (ho p (by omega)) (ho (p + 1) hp) (hf p (by omega)) (hf (p + 1) hp)
    simpa [markCells, setTwo, flagsEdge] using this

/-- The flags after the terminal edge.

Consumer: `rank_term_old`. -/
def flagsTerm (r : Nat) (cells : Nat → Cell) (o : Nat → Bool) : Nat → Bool :=
  fun j =>
    if j = r - 1 then
      oldX (cells (r - 1)) (pair false true (cells (r - 1)) { i := .e, c := .off }).1 (o (r - 1))
    else o j

/-- The marked rank does not rise along the terminal edge.

Consumer: `rank_step_old`. -/
theorem rank_term_old (r : Nat) (hr : 2 ≤ r) (cells : Nat → Cell) (o : Nat → Bool)
    (ho : ∀ j, j < r → o j = true → (cells j).i.isP = true)
    (hf : ∀ j, j < r → (cells j).c = .fresh → (cells j).i = .e) :
    rank r (markCells
      (setOne cells (r - 1) (pair false true (cells (r - 1)) { i := .e, c := .off }).1)
      (flagsTerm r cells o)) ≤ rank r (markCells cells o) := by
  apply patch_last r (r - 1) (by omega) (markCells cells o)
  · intro i h1
    simp [markCells, setOne, flagsTerm, h1]
  · intro ob vb _ hv
    have := term_local_old r (r - 1) (by omega) (cells (r - 1)) { i := .e, c := .off } (o (r - 1)) ob vb hv
      (ho (r - 1) (by omega)) (hf (r - 1) (by omega))
    simpa [markCells, setOne, flagsTerm] using this

/-- The flags after a port step with the new border register `c'`.

Consumer: `rank_port_old`. -/
def flagsPort (cells : Nat → Cell) (o : Nat → Bool) (c' : Cell) : Nat → Bool :=
  fun j => if j = 0 then oldX (cells 0) c' (o 0) else o j

/-- The marked rank does not rise along a port step.

Consumer: `rank_step_old`. -/
theorem rank_port_old (r : Nat) (hr : 2 ≤ r) (cells : Nat → Cell) (o : Nat → Bool)
    (c' : Cell) (hc' : c' = portClean (cells 0) ∨ ∃ t, c' = portAccept t (cells 0))
    (ho : ∀ j, j < r → o j = true → (cells j).i.isP = true)
    (hf : ∀ j, j < r → (cells j).c = .fresh → (cells j).i = .e) :
    rank r (markCells (setOne cells 0 c') (flagsPort cells o c')) ≤
      rank r (markCells cells o) := by
  apply patch_one r 0 (by omega) (markCells cells o)
  · intro i h1
    simp [markCells, setOne, flagsPort, h1]
  · intro ob vb hfl _
    have hf' : scanFlags (markCells cells o) 0 0 false false = (false, false) := rfl
    rw [hf'] at hfl
    cases hfl
    have := port_local_old r (cells 0) c' (o 0) hc' (ho 0 (by omega)) (hf 0 (by omega))
    simpa [markCells, setOne, flagsPort] using this

/-! ### Clearing marks does not raise the rank -/

/-- The register weight is monotone in the mark.

Consumer: `rank_mark_mono`. -/
theorem wt_mk_mono (r j : Nat) (c : Cell) (o o' ob ob' vb vb' : Bool)
    (ho : o' = true → o = true) (h1 : ob = true → ob' = true) (h2 : vb = true → vb' = true) :
    wt r j ob vb (mk c o') ≤ wt r j ob' vb' (mk c o) := by
  rcases c with ⟨ci, cc⟩
  cases ci <;> cases cc <;> cases o <;> cases o' <;> cases ob <;> cases ob' <;>
    cases vb <;> cases vb' <;>
    simp (config := { decide := true }) [wt, gateW, violC, mk, Inp.isP, Inp.isS]
      at ho h1 h2 ⊢ <;> omega

/-- The obstacle flag is monotone in the mark.

Consumer: `rank_mark_mono`. -/
theorem nob_mk_mono (c : Cell) (o o' ob ob' : Bool) (ho : o' = true → o = true)
    (h1 : ob = true → ob' = true) : nob ob (mk c o') = true → nob ob' (mk c o) = true := by
  rcases c with ⟨ci, cc⟩
  cases ci <;> cases cc <;> cases o <;> cases o' <;> cases ob <;> cases ob' <;>
    simp (config := { decide := true }) [nob, obC, mk] at ho h1 ⊢

/-- The violator flag is monotone in the mark.

Consumer: `rank_mark_mono`. -/
theorem nvb_mk_mono (c : Cell) (o o' ob ob' vb vb' : Bool) (ho : o' = true → o = true)
    (h1 : ob = true → ob' = true) (h2 : vb = true → vb' = true) :
    nvb ob vb (mk c o') = true → nvb ob' vb' (mk c o) = true := by
  rcases c with ⟨ci, cc⟩
  cases ci <;> cases cc <;> cases o <;> cases o' <;> cases ob <;> cases ob' <;>
    cases vb <;> cases vb' <;>
    simp (config := { decide := true }) [nvb, violC, mk, Inp.isP] at ho h1 h2 ⊢

/-- Auxiliary fact `scan_mk_mono` of the old-pending repair.

Consumer: `rank_edgeStep_old_le`. -/
theorem scan_mk_mono (r : Nat) (cells : Nat → Cell) (o o' : Nat → Bool)
    (ho : ∀ j, o' j = true → o j = true) :
    ∀ k j ob ob' vb vb', (ob = true → ob' = true) → (vb = true → vb' = true) →
      scan r (markCells cells o') k j ob vb ≤ scan r (markCells cells o) k j ob' vb' := by
  intro k
  induction k with
  | zero => intros; exact Nat.le_refl _
  | succ k ih =>
      intro j ob ob' vb vb' h1 h2
      exact Nat.add_le_add (wt_mk_mono r j (cells j) (o j) (o' j) ob ob' vb vb' (ho j) h1 h2)
        (ih (j + 1) _ _ _ _ (nob_mk_mono (cells j) (o j) (o' j) ob ob' (ho j) h1)
          (nvb_mk_mono (cells j) (o j) (o' j) ob ob' vb vb' (ho j) h1 h2))

/-- Clearing marks does not raise the marked rank.

Consumer: `rank_step_old`. -/
theorem rank_mark_mono (r : Nat) (cells : Nat → Cell) (o o' : Nat → Bool)
    (ho : ∀ j, o' j = true → o j = true) :
    rank r (markCells cells o') ≤ rank r (markCells cells o) :=
  scan_mk_mono r cells o o' ho r 0 false false false false (fun h => h) (fun h => h)

end MarkedCells
end L3

#print axioms L3.MarkedCells.rank_edge_old
#print axioms L3.MarkedCells.rank_term_old
#print axioms L3.MarkedCells.rank_port_old
#print axioms L3.MarkedCells.rank_mark_mono

#print axioms L3.MarkedCells.pair_local_old
#print axioms L3.MarkedCells.rank_edge_old
#print axioms L3.MarkedCells.rank_term_old
#print axioms L3.MarkedCells.rank_port_old
#print axioms L3.MarkedCells.rank_mark_mono
