import Leader.L3.Top.MarkedGood
import Leader.L3.Top.MarkedProgress
import Leader.L3.Bank.RepairDigitPacketMomentWindow

/-!
# Stage M (R10c, Lemma e-max): flagged window registers and their local facts

The register-level part of `L3.StageMOldRank`: a Q7 window register with the old-pending flag
(`OCell`), the Q7 rows with the flag (`opair`, `oterm`, `oclean`, `oaccept`), the register weight
of the inherited-work rank (`owt`, with the wider violator test `oviol`), and the finite local
facts (nonincrease, strict decrease on a selected register, comparison with the Q7 weight, the
bound `4 r + 4`). The window-edge inequalities are read off one closed Boolean check over the
register values and flags, through linear forms in the position (section *Linear forms*); the
other facts are short case analyses or direct arguments.

Consumer: `L3.StageMOldRank`.
-/

namespace L3.StageMOldRank

set_option autoImplicit false

open L3.MarkedCells
open L3.PacketMomentWindow

/-- A window register with the old-pending flag. Consumer: every row and the rank. -/
structure OCell where
  i : Inp
  c : Car
  o : Bool
  deriving DecidableEq

/-- The Q7 register of a flagged register. Consumer: `ocellApply`, `rankLeOrank`. -/
def OCell.cell (x : OCell) : Cell := { i := x.i, c := x.c }

/-- A Q7 register with a flag. Consumer: the rows. -/
def mk (c : Cell) (o : Bool) : OCell := { i := c.i, c := c.c, o := o }

/-- The register holds an old pending packet. Consumer: the rows, `orankZeroNoOld`. -/
def oP (x : OCell) : Bool := x.o && x.i.isP

/-- **A window edge with flags.** The Q7 row `pair`; the flag of a moving packet moves with it,
and a flag survives only on a pending input. Consumer: `oedge`. -/
def opair (border : Bool) (x y : OCell) : OCell × OCell :=
  let q := pair border false x.cell y.cell
  let mv := x.i.isP && q.2.i.isP && !y.i.isP
  (mk q.1 (oP x && q.1.i.isP), mk q.2 ((if mv then oP x else oP y) && q.2.i.isP))

/-- The terminal edge with flags. Consumer: `oedge`. -/
def oterm (x : OCell) : OCell :=
  mk (pair false true x.cell { i := .e, c := .off }).1
    (oP x && (pair false true x.cell { i := .e, c := .off }).1.i.isP)

/-- The port cleanup with flags. Consumer: `oApply`. -/
def oclean (x : OCell) : OCell := mk (portClean x.cell) (oP x && (portClean x.cell).i.isP)

/-- The port acceptance with flags (an accepted packet is not old). Consumer: `oApply`. -/
def oaccept (t : Bool) (x : OCell) : OCell :=
  mk (portAccept t x.cell) (oP x && (portAccept t x.cell).i.isP)

/-- **A violator**: a pending input with an obstacle at or before it (Q7), or old, or after a
violator. Consumer: `owt`. -/
def oviol (ob vb : Bool) (c : OCell) : Bool :=
  c.i.isP && (ob || vb || decide (c.c ≠ .off) || c.o)

/-- Register weight: the Q7 weights with the wider violator test. Consumer: `orank`. -/
def owt (r j : Nat) (ob vb : Bool) (c : OCell) : Nat :=
  (if oviol ob vb c then 2 * r + 2 - j else 0) +
    (if vb then gateW r j c.cell else 0) +
    (if c.c = .inh then r - j + 1 else 0)

/-- Scan flag: an obstacle has been seen. Consumer: `oscan`. -/
def onob (ob : Bool) (c : OCell) : Bool := ob || obC c.cell

/-- Scan flag: a violator has been seen. Consumer: `oscan`. -/
def onvb (ob vb : Bool) (c : OCell) : Bool := vb || oviol ob vb c

/-! ### Linear forms in the position

The window-edge inequalities are finite in the register values and flags and linear in `r` and
the position `p` (with `p + 1 < r`). Writing `r = p + 2 + d`, the register weight at `p` or `p + 1`
is a linear form `a * p + b * d + c` with natural coefficients (`owtF`, `owt_eq`); an
inequality of two such forms holds for all `p, d` once it holds coefficient-wise (`LF.le_sound`).
The coefficient-wise check over every register pair and flag pattern is one closed Boolean
evaluation (`chkEdge_all`); the theorems read their case off it. The terminal
edge (`r = p + 1`) and the port moves (`p = 0`) use the same forms with `m = 1`. -/

/-- A linear form `a * p + b * d + c`. -/
private structure LF where
  a : Nat
  b : Nat
  c : Nat

private def LF.ev (A : LF) (p d : Nat) : Nat := A.a * p + A.b * d + A.c

private def LF.add (A B : LF) : LF := ⟨A.a + B.a, A.b + B.b, A.c + B.c⟩

private def LF.zero : LF := ⟨0, 0, 0⟩

/-- Coefficient-wise comparison. -/
private def LF.le (A B : LF) : Bool :=
  decide (A.a ≤ B.a) && decide (A.b ≤ B.b) && decide (A.c ≤ B.c)

private theorem LF.ev_add (A B : LF) (p d : Nat) : (A.add B).ev p d = A.ev p d + B.ev p d := by
  simp only [LF.add, LF.ev, Nat.add_mul]
  omega

private theorem LF.ev_ite {P : Prop} [Decidable P] (A : LF) (p d : Nat) :
    (if P then A else LF.zero).ev p d = if P then A.ev p d else 0 := by
  by_cases h : P
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]; simp [LF.ev, LF.zero]

private theorem LF.ev_ite0 {P : Prop} [Decidable P] (A : LF) (p d : Nat) :
    (if P then LF.zero else A).ev p d = if P then 0 else A.ev p d := by
  by_cases h : P
  · rw [if_pos h, if_pos h]; simp [LF.ev, LF.zero]
  · rw [if_neg h, if_neg h]

private theorem LF.le_sound {A B : LF} (h : A.le B = true) (p d : Nat) : A.ev p d ≤ B.ev p d := by
  simp only [LF.le, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  unfold LF.ev
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul h1 (Nat.le_refl p)) (Nat.mul_le_mul h2 (Nat.le_refl d))) h3

/-- `2 r + 2 - j` at `r = p + m + d`, `j = p + k`. -/
private def fV (m k : Nat) : LF := ⟨1, 2, 2 * m + 2 - k⟩

/-- `r - j + 1` at `r = p + m + d`, `j = p + k`. -/
private def fD (m k : Nat) : LF := ⟨0, 1, m + 1 - k⟩

/-- `r + 1` at `r = p + m + d`. -/
private def fS (m : Nat) : LF := ⟨1, 1, m + 1⟩

/-- `gateW` as a linear form. -/
private def gateF (m k : Nat) (c : Cell) : LF :=
  LF.add
    (match c.i with
      | .st => fS m
      | .sn => fS m
      | .x => fD m k
      | _ => LF.zero)
    (if c.c = .off then LF.zero else fD m k)

/-- `owt` as a linear form. -/
private def owtF (m k : Nat) (ob vb : Bool) (c : OCell) : LF :=
  LF.add
    (LF.add (if oviol ob vb c = true then fV m k else LF.zero)
      (if vb = true then gateF m k c.cell else LF.zero))
    (if c.c = .inh then fD m k else LF.zero)

private theorem gateW_eq (p d m k : Nat) (hk : k ≤ m) (c : Cell) :
    gateW (p + m + d) (p + k) c = (gateF m k c).ev p d := by
  rcases c with ⟨ci, cc⟩
  cases ci <;> cases cc <;> simp [gateW, gateF, LF.ev, LF.add, LF.zero, fS, fD] <;> omega

/-- The register weight at `r = p + m + d`, `j = p + k`, `k ≤ m`, is the form `owtF m k`. -/
private theorem owt_eq (r j p d m k : Nat) (hr : r = p + m + d) (hj : j = p + k) (hk : k ≤ m)
    (ob vb : Bool) (c : OCell) : owt r j ob vb c = (owtF m k ob vb c).ev p d := by
  subst hr hj
  unfold owt owtF
  rw [LF.ev_add, LF.ev_add, LF.ev_ite, LF.ev_ite, LF.ev_ite, gateW_eq p d m k hk]
  have h1 : 2 * (p + m + d) + 2 - (p + k) = (fV m k).ev p d := by simp only [fV, LF.ev]; omega
  have h3 : p + m + d - (p + k) + 1 = (fD m k).ev p d := by simp only [fD, LF.ev]; omega
  rw [h1, h3]

/-! ### Enumeration of the register values -/

private def allBool : List Bool := [false, true]

private def allOCell : List OCell :=
  allBool.flatMap fun o =>
    [Inp.e, .pt, .pn, .st, .sn, .x].flatMap fun i =>
      [Car.off, .fresh, .inh].map fun c => ({ i := i, c := c, o := o } : OCell)

private theorem memB (b : Bool) : b ∈ allBool := by cases b <;> decide

private theorem memO (x : OCell) : x ∈ allOCell := by
  rcases x with ⟨i, c, o⟩
  cases o <;> cases i <;> cases c <;> decide

private theorem allB {α : Type} {l : List α} {f : α → Bool} (h : l.all f = true) {a : α}
    (ha : a ∈ l) : f a = true :=
  List.all_eq_true.mp h a ha

private theorem impB {a b : Bool} (h : (!a || b) = true) : a = true → b = true := by
  cases a <;> cases b <;> simp_all

private theorem and3B {a b c : Bool} (h : (a && b && c) = true) :
    a = true ∧ b = true ∧ c = true := by
  cases a <;> cases b <;> cases c <;> simp_all

/-! ### The window-edge check

`pair` is evaluated once per edge input (`withCell` forces its result to constructors), and the
flag patterns are checked on the evaluated result. -/

private def allCell : List Cell :=
  [Inp.e, .pt, .pn, .st, .sn, .x].flatMap fun i =>
    [Car.off, .fresh, .inh].map fun c => ({ i := i, c := c } : Cell)

private theorem memC (x : Cell) : x ∈ allCell := by
  rcases x with ⟨i, c⟩
  cases i <;> cases c <;> decide

/-- Continue with an input class evaluated to a constructor. -/
private def withInp (i : Inp) (k : Inp → Bool) : Bool :=
  match i with
  | .e => k .e
  | .pt => k .pt
  | .pn => k .pn
  | .st => k .st
  | .sn => k .sn
  | .x => k .x

/-- Continue with a carry class evaluated to a constructor. -/
private def withCar (c : Car) (k : Car → Bool) : Bool :=
  match c with
  | .off => k .off
  | .fresh => k .fresh
  | .inh => k .inh

/-- Continue with a register evaluated to constructors. -/
private def withCell (c : Cell) (k : Cell → Bool) : Bool :=
  withInp c.i fun i => withCar c.c fun cc => k { i := i, c := cc }

private theorem withCell_eq (c : Cell) (k : Cell → Bool) : withCell c k = k c := by
  rcases c with ⟨i, cc⟩
  cases i <;> cases cc <;> rfl

/-- `opair` with the Q7 edge result given. -/
private def opairOf (x y : OCell) (q : Cell × Cell) : OCell × OCell :=
  (mk q.1 (oP x && q.1.i.isP),
    mk q.2 ((if x.i.isP && q.2.i.isP && !y.i.isP then oP x else oP y) && q.2.i.isP))

/-- `OSel` as a Boolean. -/
private def oselB (ob vb : Bool) (x y : OCell) : Bool :=
  decide ((x.c ≠ .off ∧ (oviol ob vb x = true ∨ vb = true)) ∨
    (x.i = .x ∧ x.c = .off ∧ vb = true) ∨
    (x.i.isP = true ∧ x.c = .off ∧ (ob = true ∨ vb = true ∨ x.o = true) ∧
      ((y.i = .e ∧ y.c = .off) ∨ (y.i.isS = true ∧ y.c = .off))) ∨
    x.c = .inh)

/-- The four facts of a window edge `x y ↦ q`, as forms: nonincrease, the two scan flags, and
strict decrease on a selected edge. -/
private def chkEdgeAt (x y : OCell) (q : OCell × OCell) (ob vb : Bool) : Bool :=
  LF.le
      ((owtF 2 0 ob vb q.1).add (owtF 2 1 (onob ob q.1) (onvb ob vb q.1) q.2))
      ((owtF 2 0 ob vb x).add (owtF 2 1 (onob ob x) (onvb ob vb x) y)) &&
    (!(onob (onob ob q.1) q.2) || onob (onob ob x) y) &&
    (!(onvb (onob ob q.1) (onvb ob vb q.1) q.2) || onvb (onob ob x) (onvb ob vb x) y) &&
    (!oselB ob vb x y ||
      LF.le
        (((owtF 2 0 ob vb q.1).add (owtF 2 1 (onob ob q.1) (onvb ob vb q.1) q.2)).add ⟨0, 0, 1⟩)
        ((owtF 2 0 ob vb x).add (owtF 2 1 (onob ob x) (onvb ob vb x) y)))

/-- All flag patterns of one Q7 edge input. -/
private def chkEdge (border : Bool) (xc yc : Cell) : Bool :=
  withCell (pair border false xc yc).1 fun c1 => withCell (pair border false xc yc).2 fun c2 =>
    allBool.all fun xo => allBool.all fun yo => allBool.all fun ob => allBool.all fun vb =>
      chkEdgeAt { i := xc.i, c := xc.c, o := xo } { i := yc.i, c := yc.c, o := yo }
        (opairOf { i := xc.i, c := xc.c, o := xo } { i := yc.i, c := yc.c, o := yo } (c1, c2))
        ob vb

/-- The check holds on every edge input (648 evaluations of `pair`, 10368 flag patterns). -/
private theorem chkEdge_all :
    allBool.all (fun border => allCell.all fun xc => allCell.all fun yc => chkEdge border xc yc) =
      true := by
  decide +kernel

private theorem chkEdge_ok (border : Bool) (x y : OCell) (ob vb : Bool) :
    chkEdgeAt x y (opair border x y) ob vb = true := by
  have h1 := allB (allB (allB chkEdge_all (memB border)) (memC x.cell)) (memC y.cell)
  simp only [chkEdge, withCell_eq] at h1
  have h2 := allB (allB (allB (allB h1 (memB x.o)) (memB y.o)) (memB ob)) (memB vb)
  rcases x with ⟨xi, xc, xo⟩
  rcases y with ⟨yi, yc, yo⟩
  exact h2

private theorem and4B {a b c e : Bool} (h : (a && b && c && e) = true) :
    a = true ∧ b = true ∧ c = true ∧ e = true := by
  cases a <;> cases b <;> cases c <;> cases e <;> simp_all

/-- Local inequality of a window edge (every flag pattern). Consumer: `orankMoveLe`. -/
theorem opairLocal (r p : Nat) (hp : p + 1 < r) (border : Bool) (x y : OCell) (ob vb : Bool) :
    owt r p ob vb (opair border x y).1 +
      owt r (p + 1) (onob ob (opair border x y).1) (onvb ob vb (opair border x y).1)
        (opair border x y).2 ≤
    owt r p ob vb x + owt r (p + 1) (onob ob x) (onvb ob vb x) y ∧
    (onob (onob ob (opair border x y).1) (opair border x y).2 = true →
      onob (onob ob x) y = true) ∧
    (onvb (onob ob (opair border x y).1) (onvb ob vb (opair border x y).1)
        (opair border x y).2 = true →
      onvb (onob ob x) (onvb ob vb x) y = true) := by
  obtain ⟨d, rfl⟩ : ∃ d, r = p + 2 + d := ⟨r - (p + 2), by omega⟩
  obtain ⟨hw, hn, hv, -⟩ := and4B (chkEdge_ok border x y ob vb)
  refine ⟨?_, impB hn, impB hv⟩
  have h := LF.le_sound hw p d
  rw [LF.ev_add, LF.ev_add] at h
  rw [owt_eq _ _ p d 2 0 rfl (Nat.add_zero p).symm (by omega),
    owt_eq _ _ p d 2 0 rfl (Nat.add_zero p).symm (by omega),
    owt_eq _ (p + 1) p d 2 1 rfl rfl (by omega), owt_eq _ (p + 1) p d 2 1 rfl rfl (by omega)]
  exact h

/-- The terminal-edge check, as forms (`r = p + 1`). -/
private def chkTerm (x : OCell) (ob vb : Bool) : Bool :=
  LF.le (owtF 1 0 ob vb (oterm x)) (owtF 1 0 ob vb x)

private theorem chkTerm_all :
    allOCell.all (fun x => allBool.all fun ob => allBool.all fun vb => chkTerm x ob vb) = true := by
  decide +kernel

/-- The port-move check, as forms (`p = 0`): weight and both scan flags. -/
private def chkPort (f : OCell → OCell) (x : OCell) : Bool :=
  LF.le (owtF 1 0 false false (f x)) (owtF 1 0 false false x) &&
    (!onob false (f x) || onob false x) && (!onvb false false (f x) || onvb false false x)

private theorem chkPort_all :
    allOCell.all (fun x => chkPort oclean x && chkPort (oaccept false) x &&
      chkPort (oaccept true) x) = true := by
  decide +kernel

private theorem chkPort_read (f : OCell → OCell) (r : Nat) (hr : 0 < r) (x : OCell)
    (hc : chkPort f x = true) :
    owt r 0 false false (f x) ≤ owt r 0 false false x ∧
    (onob false (f x) = true → onob false x = true) ∧
    (onvb false false (f x) = true → onvb false false x = true) := by
  obtain ⟨hw, hn, hv⟩ := and3B hc
  refine ⟨?_, impB hn, impB hv⟩
  rw [owt_eq r 0 0 (r - 1) 1 0 (by omega) rfl (by omega),
    owt_eq r 0 0 (r - 1) 1 0 (by omega) rfl (by omega)]
  exact LF.le_sound hw 0 (r - 1)

private theorem ite_le_self {P : Prop} [Decidable P] (X : Nat) : (if P then X else 0) ≤ X := by
  by_cases h : P
  · rw [if_pos h]; exact Nat.le_refl X
  · rw [if_neg h]; exact Nat.zero_le X

private theorem ite_mono {P Q : Prop} [Decidable P] [Decidable Q] (h : P → Q) (X : Nat) :
    (if P then X else 0) ≤ (if Q then X else 0) := by
  by_cases hp : P
  · rw [if_pos hp, if_pos (h hp)]; exact Nat.le_refl X
  · rw [if_neg hp]; exact Nat.zero_le _

private theorem andLeft {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a <;> simp_all

private theorem andMono {p a b : Bool} (hab : a = true → b = true) (h : (p && a) = true) :
    (p && b) = true := by
  cases p <;> cases a <;> cases b <;> simp_all

private theorem orMono4 {a v d o : Bool} (h : (a || d) = true) : (a || v || d || o) = true := by
  cases a <;> cases v <;> cases d <;> cases o <;> simp_all

private theorem gateW_le (r j : Nat) (c : Cell) :
    gateW r j c ≤ 2 * r + 2 ∧ (c.i.isP = true → gateW r j c ≤ r + 1) := by
  rcases c with ⟨ci, cc⟩
  constructor
  · cases ci <;> cases cc <;> simp [gateW] <;> omega
  · intro hp
    cases ci <;> simp [Inp.isP] at hp <;> cases cc <;> simp [gateW] <;> omega

private theorem oviolMono {ob ob' vb vb' : Bool} (c : OCell) (h1 : ob = true → ob' = true)
    (h2 : vb = true → vb' = true) (h : oviol ob vb c = true) : oviol ob' vb' c = true := by
  cases ob <;> cases ob' <;> cases vb <;> cases vb' <;> simp_all [oviol]

/-- Local inequality of the terminal edge. Consumer: `orankMoveLe`. -/
theorem otermLocal (r p : Nat) (hp : p + 1 = r) (x : OCell) (ob vb : Bool) :
    owt r p ob vb (oterm x) ≤ owt r p ob vb x := by
  have hc : chkTerm x ob vb = true :=
    allB (allB (allB chkTerm_all (memO x)) (memB ob)) (memB vb)
  rw [owt_eq r p p 0 1 0 (by omega) (by omega) (by omega),
    owt_eq r p p 0 1 0 (by omega) (by omega) (by omega)]
  exact LF.le_sound hc p 0

/-- Local inequality of the port cleanup. Consumer: `orankMoveLe`. -/
theorem ocleanLocal (r : Nat) (hr : 0 < r) (x : OCell) :
    owt r 0 false false (oclean x) ≤ owt r 0 false false x ∧
    (onob false (oclean x) = true → onob false x = true) ∧
    (onvb false false (oclean x) = true → onvb false false x = true) :=
  chkPort_read oclean r hr x (and3B (allB chkPort_all (memO x))).1

/-- Local inequality of the port acceptance. Consumer: `orankMoveLe`. -/
theorem oacceptLocal (r : Nat) (hr : 0 < r) (t : Bool) (x : OCell) :
    owt r 0 false false (oaccept t x) ≤ owt r 0 false false x ∧
    (onob false (oaccept t x) = true → onob false x = true) ∧
    (onvb false false (oaccept t x) = true → onvb false false x = true) := by
  obtain ⟨_, hf, ht⟩ := and3B (allB chkPort_all (memO x))
  cases t
  · exact chkPort_read (oaccept false) r hr x hf
  · exact chkPort_read (oaccept true) r hr x ht

/-- The register weight is monotone in the flags. Consumer: `oscanMono`. -/
theorem owtMono (r j : Nat) (ob ob' vb vb' : Bool) (c : OCell)
    (h1 : ob = true → ob' = true) (h2 : vb = true → vb' = true) :
    owt r j ob vb c ≤ owt r j ob' vb' c := by
  unfold owt
  exact Nat.add_le_add (Nat.add_le_add (ite_mono (oviolMono c h1 h2) _) (ite_mono h2 _))
    (Nat.le_refl _)

/-- The obstacle flag is monotone. Consumer: `oscanMono`. -/
theorem onobMono (ob ob' : Bool) (c : OCell) (h1 : ob = true → ob' = true) :
    onob ob c = true → onob ob' c = true := by
  cases ob <;> cases ob' <;> simp (config := { decide := true }) [onob] at h1 ⊢

/-- The violator flag is monotone. Consumer: `oscanMono`. -/
theorem onvbMono (ob ob' vb vb' : Bool) (c : OCell)
    (h1 : ob = true → ob' = true) (h2 : vb = true → vb' = true) :
    onvb ob vb c = true → onvb ob' vb' c = true := by
  intro h
  simp only [onvb, Bool.or_eq_true] at h ⊢
  rcases h with h | h
  · exact Or.inl (h2 h)
  · exact Or.inr (oviolMono c h1 h2 h)

/-- The selected registers of a window edge. Consumer: `opairStrict`. -/
def OSel (ob vb : Bool) (x y : OCell) : Prop :=
  (x.c ≠ .off ∧ (oviol ob vb x = true ∨ vb = true)) ∨
  (x.i = .x ∧ x.c = .off ∧ vb = true) ∨
  (x.i.isP = true ∧ x.c = .off ∧ (ob = true ∨ vb = true ∨ x.o = true) ∧
    ((y.i = .e ∧ y.c = .off) ∨ (y.i.isS = true ∧ y.c = .off))) ∨
  x.c = .inh

/-- The selected terminal register. Consumer: `otermStrict`. -/
def OSelT (ob vb : Bool) (x : OCell) : Prop :=
  (x.c ≠ .off ∧ (oviol ob vb x = true ∨ vb = true)) ∨
  (x.i = .x ∧ x.c = .off ∧ vb = true) ∨
  (x.i.isP = true ∧ x.c = .off ∧ (ob = true ∨ vb = true ∨ x.o = true)) ∨
  x.c = .inh

private theorem oselB_of {ob vb : Bool} {x y : OCell} (h : OSel ob vb x y) :
    oselB ob vb x y = true :=
  decide_eq_true h

/-- The selected window edge strictly lowers the local weight. Consumer: `oedgeLt`. -/
theorem opairStrict (r p : Nat) (hp : p + 1 < r) (border : Bool) (x y : OCell) (ob vb : Bool)
    (hsel : OSel ob vb x y) :
    owt r p ob vb (opair border x y).1 +
      owt r (p + 1) (onob ob (opair border x y).1) (onvb ob vb (opair border x y).1)
        (opair border x y).2 + 1 ≤
    owt r p ob vb x + owt r (p + 1) (onob ob x) (onvb ob vb x) y := by
  obtain ⟨d, rfl⟩ : ∃ d, r = p + 2 + d := ⟨r - (p + 2), by omega⟩
  obtain ⟨-, -, -, hc⟩ := and4B (chkEdge_ok border x y ob vb)
  have h := LF.le_sound (impB hc (oselB_of hsel)) p d
  rw [LF.ev_add, LF.ev_add, LF.ev_add] at h
  have h1 : (⟨0, 0, 1⟩ : LF).ev p d = 1 := by simp [LF.ev]
  rw [h1] at h
  rw [owt_eq _ _ p d 2 0 rfl (Nat.add_zero p).symm (by omega),
    owt_eq _ _ p d 2 0 rfl (Nat.add_zero p).symm (by omega),
    owt_eq _ (p + 1) p d 2 1 rfl rfl (by omega), owt_eq _ (p + 1) p d 2 1 rfl rfl (by omega)]
  exact h

/-- `OSelT` as a Boolean. -/
private def oselTB (ob vb : Bool) (x : OCell) : Bool :=
  decide ((x.c ≠ .off ∧ (oviol ob vb x = true ∨ vb = true)) ∨
    (x.i = .x ∧ x.c = .off ∧ vb = true) ∨
    (x.i.isP = true ∧ x.c = .off ∧ (ob = true ∨ vb = true ∨ x.o = true)) ∨
    x.c = .inh)

private theorem oselTB_of {ob vb : Bool} {x : OCell} (h : OSelT ob vb x) :
    oselTB ob vb x = true :=
  decide_eq_true h

/-- The strict terminal-edge check, as forms (`r = p + 1`). -/
private def chkTermS (x : OCell) (ob vb : Bool) : Bool :=
  !oselTB ob vb x || LF.le ((owtF 1 0 ob vb (oterm x)).add ⟨0, 0, 1⟩) (owtF 1 0 ob vb x)

private theorem chkTermS_all :
    allOCell.all (fun x => allBool.all fun ob => allBool.all fun vb => chkTermS x ob vb) =
      true := by
  decide +kernel

/-- The selected terminal edge strictly lowers the local weight. Consumer: `oedgeLt`. -/
theorem otermStrict (r p : Nat) (hp : p + 1 = r) (x : OCell) (ob vb : Bool)
    (hsel : OSelT ob vb x) : owt r p ob vb (oterm x) + 1 ≤ owt r p ob vb x := by
  have hc : chkTermS x ob vb = true :=
    allB (allB (allB chkTermS_all (memO x)) (memB ob)) (memB vb)
  have h := LF.le_sound (impB hc (oselTB_of hsel)) p 0
  rw [LF.ev_add] at h
  have h1 : (⟨0, 0, 1⟩ : LF).ev p 0 = 1 := by simp [LF.ev]
  rw [h1] at h
  rw [owt_eq r p p 0 1 0 (by omega) (by omega) (by omega),
    owt_eq r p p 0 1 0 (by omega) (by omega) (by omega)]
  exact h

/-- A clean register weighs nothing. Consumer: `oscanZeroClean`. -/
theorem owtZeroClean (r j : Nat) (ob : Bool) (c : OCell) (h1 : oviol ob false c = false)
    (h2 : c.c ≠ .inh) : owt r j ob false c = 0 := by
  rcases c with ⟨ci, cc, co⟩
  cases co <;> cases ci <;> cases cc <;> cases ob <;>
    simp (config := { decide := true }) [owt, gateW, oviol] at h1 h2 ⊢

/-- The Q7 weight is at most the inherited-work weight. Consumer: `rankLeOrank`. -/
theorem wtLeOwt (r j : Nat) (ob vb vb' : Bool) (c : OCell) (h : vb = true → vb' = true) :
    wt r j ob vb c.cell ≤ owt r j ob vb' c ∧ (nvb ob vb c.cell = true → onvb ob vb' c = true) := by
  have hv : violC ob c.cell = true → oviol ob vb' c = true :=
    fun hc => andMono (fun h => orMono4 h) hc
  refine ⟨?_, ?_⟩
  · unfold wt owt
    exact Nat.add_le_add (Nat.add_le_add (ite_mono hv _) (ite_mono h _)) (Nat.le_refl _)
  · intro hn
    simp only [nvb, onvb, Bool.or_eq_true] at hn ⊢
    rcases hn with hn | hn
    · exact Or.inl (h hn)
    · exact Or.inr (hv hn)

/-- A register weighs at most `4 r + 4`. Consumer: `orankLe`. -/
theorem owtLe (r j : Nat) (ob vb : Bool) (c : OCell) : owt r j ob vb c ≤ 4 * r + 4 := by
  have hG := gateW_le r j c.cell
  unfold owt
  by_cases hv : oviol ob vb c = true
  · have hp : c.i.isP = true := andLeft hv
    have h2 := Nat.le_trans (ite_le_self (P := vb = true) (gateW r j c.cell)) (hG.2 hp)
    have h1 := ite_le_self (P := oviol ob vb c = true) (2 * r + 2 - j)
    have h3 := ite_le_self (P := c.c = .inh) (r - j + 1)
    omega
  · rw [if_neg hv]
    have h2 := Nat.le_trans (ite_le_self (P := vb = true) (gateW r j c.cell)) hG.1
    have h3 := ite_le_self (P := c.c = .inh) (r - j + 1)
    omega

end L3.StageMOldRank

#print axioms L3.StageMOldRank.opairLocal
#print axioms L3.StageMOldRank.opairStrict
