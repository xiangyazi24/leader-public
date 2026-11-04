import Leader.L3.Top.PinnedPhaseFillShape

/-!
# Q7 (P.12 preparation, lemma 3, abstract layer): the fill potential

The potential of a window `c` (registers `0..r-1`), a source block `src` and the residue `a` of the
index of the oldest outstanding serial modulo `r`:

* `fcnt` is the number `p` of pending-or-settled registers;
* `ftail r a` is the number of accepted packets, counted from the oldest outstanding one, that
  precede the next tail (`r - 1 - a`, or `r` when the oldest outstanding packet is itself a tail,
  which is deleted at the terminal);
* while the tail is still to be accepted (`p ≤ ftail`) the potential is the pending weight, the
  source distance, the accepting service `r + 1` and `2r + 2` for each further packet;
* once the tail is accepted the potential is the pending weight of the registers from the pending
  tail on (the packets that are older than the tail or the tail itself).

Consumer: `Leader/L3/Top/PinnedPhaseFillStep.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- One for a pending-or-settled register.

Consumer: `fcnt`. -/
def fl (c : Nat → Cell) (j : Nat) : Nat := if puNonE (c j).i = true then 1 else 0

/-- The number of pending-or-settled registers.

Consumer: `fillPhi`. -/
def fcnt (r : Nat) (c : Nat → Cell) : Nat := wsum (fl c) r

/-- The weight `r - j` of a pending register.

Consumer: `fwAll`. -/
def fwt (r : Nat) (c : Nat → Cell) (j : Nat) : Nat :=
  if (c j).i.isP = true then r - j else 0

/-- The pending weight of the window.

Consumer: `fillPhi`. -/
def fwAll (r : Nat) (c : Nat → Cell) : Nat := wsum (fwt r c) r

/-- The first pending tail (`r` when none).

Consumer: `fwPt`. -/
def fpos (r : Nat) (c : Nat → Cell) : Nat := firstS (fun j => decide ((c j).i = .pt)) r

/-- The pending weight from the first pending tail on.

Consumer: `fillPhi`. -/
def fwPt (r : Nat) (c : Nat → Cell) : Nat :=
  wsum (fun j => if fpos r c ≤ j then fwt r c j else 0) r

/-- The number of accepted packets, from the oldest outstanding one, up to the next tail.

Consumer: `fillPhi`. -/
def ftail (r a : Nat) : Nat := if a + 1 < r then r - 1 - a else r

/-- **The fill potential.**

Consumer: `Leader/L3/Top/PinnedPhaseFillStep.lean`. -/
def fillPhi (r : Nat) (c : Nat → Cell) (src : Nat → Tok) (a : Nat) : Nat :=
  if fcnt r c ≤ ftail r a then
    fwAll r c + dist r src + (r + 1) + (ftail r a - fcnt r c) * (2 * r + 2)
  else fwPt r c

/-- The tail bit of a register: a pending or settled tail.

Consumer: `tl`. -/
def tailBit (x : Cell) : Bool := decide (x.i = .pt ∨ x.i = .st)

/-- The tail bits of the pending-or-settled registers, right to left.

Consumer: `FillInv`. -/
def tl (r : Nat) (c : Nat → Cell) : List Bool :=
  ordLab (fun j => puNonE (c j).i) (fun j => tailBit (c j)) r

/-- The tail pattern of `p` consecutive serials from residue `a`.

Consumer: `FillInv`. -/
def pat (r a p : Nat) : List Bool := (List.range p).map (fun i => decide ((a + i) % r = r - 1))

/-- **The fill invariant**: the fill shape, and the tail bits of the packets in the window are the
tail pattern of consecutive serials from the residue `a`.

Consumer: `Leader/L3/Top/PinnedPhaseFillStep.lean`. -/
def FillInv (r : Nat) (c : Nat → Cell) (a : Nat) : Prop :=
  FillShape r c ∧ tl r c = pat r a (fcnt r c)

/-- The length of the reading is the number of flagged registers.

Consumer: `fillInv_length`. -/
theorem ordLab_length {α : Type} (o : Nat → Bool) (ℓ : Nat → α) :
    ∀ k, (ordLab o ℓ k).length = wsum (fun j => if o j = true then 1 else 0) k
  | 0 => rfl
  | k + 1 => by
      simp only [ordLab, wsum, List.length_append]
      rw [ordLab_length o ℓ k]
      by_cases h : o k = true <;> simp [h] <;> omega

/-- The number of tails in the reading is the number of flagged tail registers.

Consumer: `fill_pt_exists`. -/
theorem ordLab_true_mem {o : Nat → Bool} {ℓ : Nat → Bool} :
    ∀ k, true ∈ ordLab o ℓ k → ∃ j, j < k ∧ o j = true ∧ ℓ j = true
  | 0, h => by simp [ordLab] at h
  | k + 1, h => by
      simp only [ordLab, List.mem_append] at h
      rcases h with h | h
      · by_cases ho : o k = true
        · simp only [ho, if_true, List.mem_singleton] at h
          exact ⟨k, by omega, ho, h.symm⟩
        · simp only [ho, if_false] at h
          exact absurd h (by simp)
      · obtain ⟨j, hj, h1, h2⟩ := ordLab_true_mem k h
        exact ⟨j, by omega, h1, h2⟩

/-- The head of a reading is the highest flagged register.

Consumer: `fill_pt_term`. -/
theorem ordLab_succ_flag {α : Type} (o : Nat → Bool) (ℓ : Nat → α) (k : Nat) (h : o k = true) :
    ordLab o ℓ (k + 1) = ℓ k :: ordLab o ℓ k := by
  simp [ordLab, h]

/-- The reading skips an unflagged register.

Consumer: `tl_term_pt`. -/
theorem ordLab_succ_noflag {α : Type} (o : Nat → Bool) (ℓ : Nat → α) (k : Nat)
    (h : o k = false) : ordLab o ℓ (k + 1) = ordLab o ℓ k := by
  simp [ordLab, h]

/-- The pattern of one more serial.

Consumer: `tl_accept`. -/
theorem pat_succ (r a p : Nat) :
    pat r a (p + 1) = pat r a p ++ [decide ((a + p) % r = r - 1)] := by
  unfold pat
  rw [List.range_succ, List.map_append]
  rfl

/-- The pattern shifted by the head.

Consumer: `tl_term_pt`. -/
theorem pat_cons (r a p : Nat) :
    pat r a (p + 1) = decide (a % r = r - 1) :: pat r (a + 1) p := by
  unfold pat
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map]
  have hmap : List.map ((fun i => decide ((a + i) % r = r - 1)) ∘ Nat.succ) (List.range p) =
      List.map (fun i => decide ((a + 1 + i) % r = r - 1)) (List.range p) := by
    apply List.map_congr_left
    intro i _
    simp only [Function.comp]
    rw [show a + Nat.succ i = a + 1 + i by omega]
  rw [hmap]
  simp

/-- The pattern is periodic in the residue.

Consumer: `tl_term_pt`. -/
theorem pat_mod (r a p : Nat) : pat r (a % r) p = pat r a p := by
  unfold pat
  apply List.map_congr_left
  intro i _
  congr 1
  apply propext
  rw [Nat.add_mod (a % r), Nat.mod_mod, ← Nat.add_mod]

/-- The window after a move of the pending packet of register `p` into the empty register `p+1`.

Consumer: `move_counts`. -/
def mvC (c : Nat → Cell) (p : Nat) : Nat → Cell :=
  setTwo c p { i := .e, c := .off } { i := (c p).i, c := .off }

/-- The flag count does not change under a move, the pending weight falls by one.

Consumer: `fill_step_window`. -/
theorem move_counts (r p : Nat) (hp : p + 1 < r) (c : Nat → Cell) (hP : (c p).i.isP = true)
    (hy : c (p + 1) = { i := .e, c := .off }) :
    fcnt r (mvC c p) = fcnt r c ∧ fwAll r (mvC c p) + 1 = fwAll r c := by
  have hyi : (c (p + 1)).i = .e := by rw [hy]
  constructor
  · unfold fcnt
    have key := wsum_edit (fl c) (fl (mvC c p)) p
      (by
        intro k hk1 hk2
        simp [fl, mvC, setTwo, hk1, hk2]) r (by omega)
    have e1 : fl c p = 1 := by simp [fl, puNonE, hP]
    have e2 : fl c (p + 1) = 0 := by simp [fl, puNonE, hyi, Inp.isP, Inp.isS]
    have e3 : fl (mvC c p) p = 0 := by simp [fl, mvC, setTwo, puNonE, Inp.isP, Inp.isS]
    have e4 : fl (mvC c p) (p + 1) = 1 := by simp [fl, mvC, setTwo, puNonE, hP]
    omega
  · unfold fwAll
    have key := wsum_edit (fwt r c) (fwt r (mvC c p)) p
      (by
        intro k hk1 hk2
        simp [fwt, mvC, setTwo, hk1, hk2]) r (by omega)
    have e1 : fwt r c p = r - p := by simp [fwt, hP]
    have e2 : fwt r c (p + 1) = 0 := by simp [fwt, hyi, Inp.isP]
    have e3 : fwt r (mvC c p) p = 0 := by simp [fwt, mvC, setTwo, Inp.isP]
    have e4 : fwt r (mvC c p) (p + 1) = r - (p + 1) := by simp [fwt, mvC, setTwo, hP]
    omega

/-- The window after a settlement in place of the pending packet of register `p`.

Consumer: `settle_counts`. -/
def stC (c : Nat → Cell) (p : Nat) (x : Cell) : Nat → Cell := setOne c p x

/-- A settlement in place of a pending packet (to a settled input) keeps the flag count and takes
its weight off.

Consumer: `fill_step_window`. -/
theorem settle_counts (r p : Nat) (hp : p < r) (c : Nat → Cell) (hP : (c p).i.isP = true)
    (x : Cell) (hxs : x.i.isS = true) (hxp : x.i.isP = false) :
    fcnt r (stC c p x) = fcnt r c ∧ fwAll r (stC c p x) + (r - p) = fwAll r c := by
  constructor
  · unfold fcnt
    have key := wsum_edit_one (fl c) (fl (stC c p x)) p
      (by
        intro k hk
        simp [fl, stC, setOne, hk]) r (by omega)
    have e1 : fl c p = 1 := by simp [fl, puNonE, hP]
    have e2 : fl (stC c p x) p = 1 := by simp [fl, stC, setOne, puNonE, hxs]
    omega
  · unfold fwAll
    have key := wsum_edit_one (fwt r c) (fwt r (stC c p x)) p
      (by
        intro k hk
        simp [fwt, stC, setOne, hk]) r (by omega)
    have e1 : fwt r c p = r - p := by simp [fwt, hP]
    have e2 : fwt r (stC c p x) p = 0 := by simp [fwt, stC, setOne, hxp]
    omega

/-- The terminal deletion of a pending tail takes one off the flag count and the weight.

Consumer: `fill_step_window`. -/
theorem delete_counts (r : Nat) (hr : 1 ≤ r) (c : Nat → Cell) (hP : (c (r - 1)).i.isP = true) :
    fcnt r (stC c (r - 1) { i := .e, c := .off }) + 1 = fcnt r c ∧
    fwAll r (stC c (r - 1) { i := .e, c := .off }) + 1 = fwAll r c := by
  constructor
  · unfold fcnt
    have key := wsum_edit_one (fl c) (fl (stC c (r - 1) { i := .e, c := .off })) (r - 1)
      (by
        intro k hk
        simp [fl, stC, setOne, hk]) r (by omega)
    have e1 : fl c (r - 1) = 1 := by simp [fl, puNonE, hP]
    have e2 : fl (stC c (r - 1) { i := .e, c := .off }) (r - 1) = 0 := by
      simp [fl, stC, setOne, puNonE, Inp.isP, Inp.isS]
    omega
  · unfold fwAll
    have key := wsum_edit_one (fwt r c) (fwt r (stC c (r - 1) { i := .e, c := .off })) (r - 1)
      (by
        intro k hk
        simp [fwt, stC, setOne, hk]) r (by omega)
    have e1 : fwt r c (r - 1) = 1 := by simp [fwt, hP]; omega
    have e2 : fwt r (stC c (r - 1) { i := .e, c := .off }) (r - 1) = 0 := by
      simp [fwt, stC, setOne, Inp.isP]
    omega

/-- Accepting a packet into the empty border register adds one to the flag count and `r` to the
weight.

Consumer: `fill_step_window`. -/
theorem accept_counts (r : Nat) (hr : 1 ≤ r) (c : Nat → Cell) (t : Bool)
    (h0 : c 0 = { i := .e, c := .off }) :
    fcnt r (stC c 0 { i := (if t then .pt else .pn), c := .off }) = fcnt r c + 1 ∧
    fwAll r (stC c 0 { i := (if t then .pt else .pn), c := .off }) = fwAll r c + r := by
  have h0i : (c 0).i = .e := by rw [h0]
  constructor
  · unfold fcnt
    have key := wsum_edit_one (fl c) (fl (stC c 0 { i := (if t then .pt else .pn), c := .off })) 0
      (by
        intro k hk
        simp [fl, stC, setOne, hk]) r (by omega)
    have e1 : fl c 0 = 0 := by simp [fl, h0i, puNonE, Inp.isP, Inp.isS]
    have e2 : fl (stC c 0 { i := (if t then .pt else .pn), c := .off }) 0 = 1 := by
      cases t <;> simp [fl, stC, setOne, puNonE, Inp.isP]
    omega
  · unfold fwAll
    have key := wsum_edit_one (fwt r c)
      (fwt r (stC c 0 { i := (if t then .pt else .pn), c := .off })) 0
      (by
        intro k hk
        simp [fwt, stC, setOne, hk]) r (by omega)
    have e1 : fwt r c 0 = 0 := by simp [fwt, h0i, Inp.isP]
    have e2 : fwt r (stC c 0 { i := (if t then .pt else .pn), c := .off }) 0 = r := by
      cases t <;> simp [fwt, stC, setOne, Inp.isP]
    omega

end MarkedCells
end L3

#print axioms L3.MarkedCells.move_counts
#print axioms L3.MarkedCells.accept_counts
#print axioms L3.MarkedCells.settle_counts
#print axioms L3.MarkedCells.delete_counts
