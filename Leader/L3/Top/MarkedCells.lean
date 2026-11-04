/-!
# Q7: the abstract target window and the marked-debt rank (P.4--P.5)

The checker registers on the target window `certSite s (r + j)`, `j < r`, are
modelled by cells `Cell` (input class and carry class).  The first-match QI and
QC rows of `liveTopPair` act on a window edge as `pair`; the port edge acts on
cell `0` as `portClean` or `portAccept`.  This module is pure: no machine, no
audit.  It proves, for the abstract window:

* `rank_step_le`: no edge raises the rank (no invariant is used);
* `inv_step`: the two invariants of a fresh carry are inductive;
* `rank_zero_good`: rank zero plus the invariants gives barrier, gap, no reseed;
* `rank_progress`: off rank zero the rightmost-violator edge lowers the rank;
* `rank_le`: the rank is at most `4 r (r + 1) = topClockR r`.

Consumer: `Leader/L3/Top/MarkedDebtRows.lean` (the realisation lemma and the
assembly of `TopMarkedDebtRows`).
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false

/-- Input class of a target register (values are irrelevant to the dynamics).

Consumer: `rank_step_le`. -/
inductive Inp : Type
  | e | pt | pn | st | sn | x
  deriving DecidableEq

/-- Carry class: off, fresh (ledger `inherited = none`), inherited.

Consumer: `rank_step_le`. -/
inductive Car : Type
  | off | fresh | inh
  deriving DecidableEq

/-- One target register of the abstract window: input class and carry class.

Consumer: `rank_step_le`. -/
structure Cell where
  i : Inp
  c : Car
  deriving DecidableEq

/-- Pending-input test of an input class.

Consumer: `rank_step_le`. -/
def Inp.isP : Inp → Bool
  | .pt => true
  | .pn => true
  | _ => false

/-- Settled-input test of an input class.

Consumer: `rank_step_le`. -/
def Inp.isS : Inp → Bool
  | .st => true
  | .sn => true
  | _ => false

/-- The two input slots and their first-match flags of one edge.

Consumer: `rank_step_le`. -/
structure Slots where
  iX : Inp
  iY : Inp
  fx : Bool
  fy : Bool

/-- The QI first-match rows (`CertRows.liveTopPair`, `qi`), root-free.

Consumer: `rank_step_le`. -/
def inSlots (border terminal : Bool) (x y : Cell) : Slots :=
  let s : Slots := { iX := x.i, iY := y.i, fx := false, fy := false }
  let s := if !s.fx && decide (x.c ≠ .off) then
      { s with iX := .e, fx := true } else s
  let s := if !s.fy && decide (y.c ≠ .off) && !terminal then
      { s with iY := .e, fy := true } else s
  let s := if !s.fx && decide (x.i = .st) && !border then
      { s with iX := .x, fx := true } else s
  let s := if !s.fx && decide (x.i = .x) then
      let s := { s with iX := .e, fx := true }
      if !s.fy && !terminal && y.i.isS then { s with iY := .x, fy := true }
      else s
    else s
  let succ := decide (x.c ≠ .off) && !terminal && decide (y.c = .off) && y.i.isS
  let s := if succ && !s.fy then { s with iY := .e, fy := true } else s
  let qcThree := border && decide (x.c = .off) && x.i.isS
  let s := if qcThree && !s.fx then { s with iX := .e, fx := true } else s
  let s := if !s.fx && x.i.isP then
      if terminal then
        (if decide (x.i = .pn) then { s with iX := .sn, fx := true }
         else if !border then { s with iX := .e, fx := true } else s)
      else if decide (y.i = .e) && decide (y.c = .off) && !s.fy then
        { iX := .e, iY := x.i, fx := true, fy := true }
      else if y.i.isS && decide (y.c = .off) then
        { s with iX := (if decide (x.i = .pt) then .st else .sn), fx := true }
      else s
    else s
  s

/-- The QC rows: launch, advance, abort, retire.

Consumer: `rank_step_le`. -/
def carries (border terminal : Bool) (x y : Cell) : Car × Car :=
  if decide (x.c ≠ .off) then
    (if !terminal && decide (y.c = .off) && y.i.isS then (.off, x.c)
     else (.off, y.c))
  else if border && x.i.isS then (.fresh, y.c)
  else (x.c, y.c)

/-- One window edge `x -> y`; for the terminal edge `y` is returned unchanged.

Consumer: `rank_step_le`. -/
def pair (border terminal : Bool) (x y : Cell) : Cell × Cell :=
  let s := inSlots border terminal x y
  let k := carries border terminal x y
  ({ i := s.iX, c := k.1 }, { i := s.iY, c := k.2 })

/-- The port edge, carry-host cleanup of the border register.

Consumer: `rank_step_le`. -/
def portClean (c : Cell) : Cell :=
  if c.c = .off then c else { c with i := .e }

/-- The port edge accepting a packet into an empty carry-free border register.

Consumer: `rank_step_le`. -/
def portAccept (t : Bool) (c : Cell) : Cell :=
  if c = { i := .e, c := .off } then
    { i := (if t then .pt else .pn), c := .off }
  else c

/-- Replace one register of a window.

Consumer: `rank_step_le`. -/
def setOne (cells : Nat → Cell) (p : Nat) (a : Cell) : Nat → Cell :=
  fun j => if j = p then a else cells j

/-- Replace two adjacent registers of a window.

Consumer: `rank_step_le`. -/
def setTwo (cells : Nat → Cell) (p : Nat) (a b : Cell) : Nat → Cell :=
  fun j => if j = p then a else if j = p + 1 then b else cells j

/-- The abstract successor relation of the window (frame included).

Consumer: `rank_step_le`. -/
inductive Step (r : Nat) (cells : Nat → Cell) : (Nat → Cell) → Prop
  | frame : Step r cells cells
  | edge (p : Nat) (hp : p + 1 < r) :
      Step r cells
        (setTwo cells p (pair (decide (p = 0)) false (cells p) (cells (p + 1))).1
          (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2)
  | term :
      Step r cells
        (setOne cells (r - 1)
          (pair false true (cells (r - 1)) { i := .e, c := .off }).1)
  | clean : Step r cells (setOne cells 0 (portClean (cells 0)))
  | accept (t : Bool) : Step r cells (setOne cells 0 (portAccept t (cells 0)))

/-! ## The rank

Consumer: `rank_step_le`. -/

def obC (c : Cell) : Bool := c.i.isS || decide (c.i = .x) || decide (c.c ≠ .off)

/-- A pending input with an obstacle at or before it.

Consumer: `rank_step_le`. -/
def violC (ob : Bool) (c : Cell) : Bool :=
  c.i.isP && (ob || decide (c.c ≠ .off))

/-- Weight of an obstacle register right of the leftmost violator.

Consumer: `rank_step_le`. -/
def gateW (r j : Nat) (c : Cell) : Nat :=
  (match c.i with
    | .st => r + 1
    | .sn => r + 1
    | .x => r - j + 1
    | _ => 0) + (if c.c = .off then 0 else r - j + 1)

/-- Weight of one register given the scan flags.

Consumer: `rank_step_le`. -/
def wt (r j : Nat) (ob vb : Bool) (c : Cell) : Nat :=
  (if violC ob c then 2 * r + 2 - j else 0) +
    (if vb then gateW r j c else 0) +
    (if c.c = .inh then r - j + 1 else 0)

/-- Scan flag: an obstacle has been seen.

Consumer: `rank_step_le`. -/
def nob (ob : Bool) (c : Cell) : Bool := ob || obC c
/-- Scan flag: a violator has been seen.

Consumer: `rank_step_le`. -/
def nvb (ob vb : Bool) (c : Cell) : Bool := vb || violC ob c

/-- Left-to-right weighted scan of `k` registers from register `j`.

Consumer: `rank_step_le`. -/
def scan (r : Nat) (cells : Nat → Cell) : Nat → Nat → Bool → Bool → Nat
  | 0, _, _, _ => 0
  | k + 1, j, ob, vb =>
      wt r j ob vb (cells j) +
        scan r cells k (j + 1) (nob ob (cells j)) (nvb ob vb (cells j))

/-- The marked-debt rank of a window of `r` registers.

Consumer: `rank_step_le`. -/
def rank (r : Nat) (cells : Nat → Cell) : Nat := scan r cells r 0 false false

/-! ## Local inequality for one window edge -/

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 8192 in
theorem pair_local (r p : Nat) (hp : p + 1 < r) (border : Bool)
    (x y : Cell) (ob vb : Bool) (hv : vb = true → ob = true) :
    wt r p ob vb (pair border false x y).1 +
      wt r (p + 1) (nob ob (pair border false x y).1)
        (nvb ob vb (pair border false x y).1) (pair border false x y).2 ≤
    wt r p ob vb x +
      wt r (p + 1) (nob ob x) (nvb ob vb x) y ∧
    (nob (nob ob (pair border false x y).1) (pair border false x y).2 = true →
      nob (nob ob x) y = true) ∧
    (nvb (nob ob (pair border false x y).1) (nvb ob vb (pair border false x y).1)
        (pair border false x y).2 = true →
      nvb (nob ob x) (nvb ob vb x) y = true) := by
  rcases x with ⟨xi, xc⟩
  rcases y with ⟨yi, yc⟩
  cases xi <;> cases xc <;> cases yi <;> cases yc <;> cases ob <;> cases vb <;>
    cases border <;>
    simp (config := { decide := true })
      [pair, inSlots, carries, wt, gateW, violC, obC, nob, nvb,
        Inp.isP, Inp.isS] at hv ⊢ <;> omega

/-- A violator is an obstacle: the flags stay valid.

Consumer: `rank_step_le`. -/
theorem flags_valid (ob vb : Bool) (c : Cell) (hv : vb = true → ob = true) :
    nvb ob vb c = true → nob ob c = true := by
  rcases c with ⟨ci, cc⟩
  cases ci <;> cases cc <;> cases ob <;> cases vb <;>
    simp (config := { decide := true }) [nob, nvb, obC, violC, Inp.isP, Inp.isS] at hv ⊢

/-- Scan flags after `k` registers from register `j`.

Consumer: `rank_step_le`. -/
def scanFlags (cells : Nat → Cell) : Nat → Nat → Bool → Bool → Bool × Bool
  | 0, _, ob, vb => (ob, vb)
  | k + 1, j, ob, vb =>
      scanFlags cells k (j + 1) (nob ob (cells j)) (nvb ob vb (cells j))

/-- A violator flag implies the obstacle flag.

Consumer: `rank_step_le`. -/
theorem scanFlags_valid (cells : Nat → Cell) :
    ∀ k j ob vb, (vb = true → ob = true) →
      ((scanFlags cells k j ob vb).2 = true →
        (scanFlags cells k j ob vb).1 = true) := by
  intro k
  induction k with
  | zero => intro j ob vb hv; exact hv
  | succ k ih =>
      intro j ob vb hv
      exact ih (j + 1) (nob ob (cells j)) (nvb ob vb (cells j))
        (flags_valid ob vb (cells j) hv)

/-- The register weight is monotone in the scan flags.

Consumer: `rank_step_le`. -/
theorem wt_mono (r j : Nat) (ob ob' vb vb' : Bool) (c : Cell)
    (h1 : ob = true → ob' = true) (h2 : vb = true → vb' = true) :
    wt r j ob vb c ≤ wt r j ob' vb' c := by
  rcases c with ⟨ci, cc⟩
  cases ci <;> cases cc <;> cases ob <;> cases ob' <;> cases vb <;> cases vb' <;>
    simp (config := { decide := true }) [wt, gateW, violC] at h1 h2 ⊢ <;> omega

/-- The obstacle flag is monotone in its input flag.

Consumer: `rank_step_le`. -/
theorem nob_mono (ob ob' : Bool) (c : Cell) (h1 : ob = true → ob' = true) :
    nob ob c = true → nob ob' c = true := by
  cases ob <;> cases ob' <;> simp (config := { decide := true }) [nob] at h1 ⊢

/-- The violator flag is monotone in its input flags.

Consumer: `rank_step_le`. -/
theorem nvb_mono (ob ob' vb vb' : Bool) (c : Cell)
    (h1 : ob = true → ob' = true) (h2 : vb = true → vb' = true) :
    nvb ob vb c = true → nvb ob' vb' c = true := by
  rcases c with ⟨ci, cc⟩
  cases ci <;> cases cc <;> cases ob <;> cases ob' <;> cases vb <;> cases vb' <;>
    simp (config := { decide := true }) [nvb, violC, Inp.isP] at h1 h2 ⊢

/-- The scan is monotone in the entering flags.

Consumer: `rank_step_le`. -/
theorem scan_mono (r : Nat) (cells : Nat → Cell) :
    ∀ k j ob ob' vb vb', (ob = true → ob' = true) → (vb = true → vb' = true) →
      scan r cells k j ob vb ≤ scan r cells k j ob' vb' := by
  intro k
  induction k with
  | zero => intros; exact Nat.le_refl _
  | succ k ih =>
      intro j ob ob' vb vb' h1 h2
      exact Nat.add_le_add (wt_mono r j ob ob' vb vb' (cells j) h1 h2)
        (ih (j + 1) _ _ _ _ (nob_mono ob ob' (cells j) h1)
          (nvb_mono ob ob' vb vb' (cells j) h1 h2))

/-- The outgoing scan flags are monotone in the entering flags.

Consumer: `rank_step_le`. -/
theorem scanFlags_mono (cells : Nat → Cell) :
    ∀ k j ob ob' vb vb', (ob = true → ob' = true) → (vb = true → vb' = true) →
      ((scanFlags cells k j ob vb).1 = true →
        (scanFlags cells k j ob' vb').1 = true) ∧
      ((scanFlags cells k j ob vb).2 = true →
        (scanFlags cells k j ob' vb').2 = true) := by
  intro k
  induction k with
  | zero => intro j ob ob' vb vb' h1 h2; exact ⟨h1, h2⟩
  | succ k ih =>
      intro j ob ob' vb vb' h1 h2
      exact ih (j + 1) _ _ _ _ (nob_mono ob ob' (cells j) h1)
        (nvb_mono ob ob' vb vb' (cells j) h1 h2)

/-- Splitting a scan at a register.

Consumer: `rank_step_le`. -/
theorem scan_add (r : Nat) (cells : Nat → Cell) :
    ∀ k1 k2 j ob vb, scan r cells (k1 + k2) j ob vb =
      scan r cells k1 j ob vb +
        scan r cells k2 (j + k1) (scanFlags cells k1 j ob vb).1
          (scanFlags cells k1 j ob vb).2 := by
  intro k1
  induction k1 with
  | zero => intro k2 j ob vb; simp [scan, scanFlags]
  | succ k1 ih =>
      intro k2 j ob vb
      have h : k1 + 1 + k2 = (k1 + k2) + 1 := by omega
      rw [h]
      simp only [scan, scanFlags]
      rw [ih k2 (j + 1) _ _]
      have h2 : j + 1 + k1 = j + (k1 + 1) := by omega
      rw [h2, Nat.add_assoc]

/-- A scan depends only on the registers it reads.

Consumer: `rank_step_le`. -/
theorem scan_congr (r : Nat) (cells cells' : Nat → Cell) :
    ∀ k j ob vb, (∀ i, j ≤ i → i < j + k → cells' i = cells i) →
      scan r cells' k j ob vb = scan r cells k j ob vb ∧
      scanFlags cells' k j ob vb = scanFlags cells k j ob vb := by
  intro k
  induction k with
  | zero => intros; exact ⟨rfl, rfl⟩
  | succ k ih =>
      intro j ob vb h
      have h0 : cells' j = cells j := h j (Nat.le_refl _) (by omega)
      have hr := ih (j + 1) (nob ob (cells j)) (nvb ob vb (cells j))
        (fun i hi hi' => h i (by omega) (by omega))
      simp only [scan, scanFlags, h0]
      exact ⟨by rw [hr.1], hr.2⟩

/-- Patch of two adjacent cells: the rank does not rise when the local weight and
the outgoing flags do not rise.

Consumer: `rank_step_le`. -/
theorem patch_two (r p : Nat) (hp : p + 1 < r) (cells cells' : Nat → Cell)
    (hout : ∀ i, i ≠ p → i ≠ p + 1 → cells' i = cells i)
    (hloc : ∀ ob vb, scanFlags cells p 0 false false = (ob, vb) →
      (vb = true → ob = true) →
      wt r p ob vb (cells' p) +
        wt r (p + 1) (nob ob (cells' p)) (nvb ob vb (cells' p)) (cells' (p + 1)) ≤
      wt r p ob vb (cells p) +
        wt r (p + 1) (nob ob (cells p)) (nvb ob vb (cells p)) (cells (p + 1)) ∧
      (nob (nob ob (cells' p)) (cells' (p + 1)) = true →
        nob (nob ob (cells p)) (cells (p + 1)) = true) ∧
      (nvb (nob ob (cells' p)) (nvb ob vb (cells' p)) (cells' (p + 1)) = true →
        nvb (nob ob (cells p)) (nvb ob vb (cells p)) (cells (p + 1)) = true)) :
    rank r cells' ≤ rank r cells := by
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

end MarkedCells
end L3

#print axioms L3.MarkedCells.pair_local
#print axioms L3.MarkedCells.patch_two
