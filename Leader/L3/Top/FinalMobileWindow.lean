import Leader.L3.Top.MarkedGood
import Leader.L3.Top.MarkedProgress

/-!
# Q7 (P.11): the clearing of fronts and carries in the abstract window

At a settled-empty cut with the moving barrier, no edge creates a settled input while a
front or a live carry stands: new fronts and carries need a settled input, and a pending
input cannot reach the terminal because the front or carry stands to its right.  The
number `Phi` of registers holding a front or a live carry never rises, and the edge of any
such register lowers it.

Consumer: `Leader/L3/Top/FinalMobileLink.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false

/-- A register holding a front or a live carry.

Consumer: `Phi`. -/
def isObs (c : Cell) : Bool := decide (c.i = .x) || decide (c.c ≠ .off)

/-- No settled input in the first `r` registers.

Consumer: `regime_step`. -/
def NoS (r : Nat) (cells : Nat → Cell) : Prop := ∀ j, j < r → (cells j).i.isS = false

/-- Count of fronts and live carries in `k` registers from `j`.

Consumer: `Phi`. -/
def phiCnt (cells : Nat → Cell) : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, j => (if isObs (cells j) then 1 else 0) + phiCnt cells k (j + 1)

/-- The number of fronts and live carries of the window.

Consumer: `regime_step`. -/
def Phi (r : Nat) (cells : Nat → Cell) : Nat := phiCnt cells r 0

/-- Auxiliary fact `phiCnt_add` of the final mobile phase.

Consumer: `regime_step`. -/
theorem phiCnt_add (cells : Nat → Cell) :
    ∀ k1 k2 j, phiCnt cells (k1 + k2) j = phiCnt cells k1 j + phiCnt cells k2 (j + k1) := by
  intro k1
  induction k1 with
  | zero => intro k2 j; simp [phiCnt]
  | succ k1 ih =>
      intro k2 j
      have h : k1 + 1 + k2 = (k1 + k2) + 1 := by omega
      rw [h]
      simp only [phiCnt]
      rw [ih k2 (j + 1)]
      have h2 : j + 1 + k1 = j + (k1 + 1) := by omega
      rw [h2]
      omega

/-- Auxiliary fact `phiCnt_congr` of the final mobile phase.

Consumer: `regime_step`. -/
theorem phiCnt_congr (cells cells' : Nat → Cell) :
    ∀ k j, (∀ i, j ≤ i → i < j + k → cells' i = cells i) →
      phiCnt cells' k j = phiCnt cells k j := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
      intro j h
      have h0 : cells' j = cells j := h j (Nat.le_refl _) (by omega)
      simp only [phiCnt, h0]
      rw [ih (j + 1) (fun i hi hi' => h i (by omega) (by omega))]

/-- A two-register patch of the window changes the count by the local change.

Consumer: `regime_step`. -/
theorem phi_patch_two (r p : Nat) (hp : p + 1 < r) (cells cells' : Nat → Cell)
    (hout : ∀ i, i ≠ p → i ≠ p + 1 → cells' i = cells i) :
    Phi r cells' + ((if isObs (cells p) then 1 else 0) + (if isObs (cells (p + 1)) then 1 else 0)) =
      Phi r cells + ((if isObs (cells' p) then 1 else 0) +
        (if isObs (cells' (p + 1)) then 1 else 0)) := by
  obtain ⟨m, hm⟩ : ∃ m, r = p + (m + 2) := ⟨r - p - 2, by omega⟩
  have hsplit : ∀ cs : Nat → Cell, Phi r cs = phiCnt cs p 0 +
      ((if isObs (cs p) then 1 else 0) + ((if isObs (cs (p + 1)) then 1 else 0) +
        phiCnt cs m (p + 2))) := by
    intro cs
    unfold Phi
    have h := phiCnt_add cs p (m + 2) 0
    rw [← hm, Nat.zero_add] at h
    rw [h]
    try simp only [Nat.zero_add]
    have e : phiCnt cs (m + 2) p = (if isObs (cs p) then 1 else 0) +
        ((if isObs (cs (p + 1)) then 1 else 0) + phiCnt cs m (p + 2)) := rfl
    rw [e]
  rw [hsplit cells', hsplit cells]
  have h1 := phiCnt_congr cells cells' p 0 (fun i _ hi => hout i (by omega) (by omega))
  have h2 := phiCnt_congr cells cells' m (p + 2) (fun i h1 h2 => hout i (by omega) (by omega))
  rw [h1, h2]
  omega

/-- A one-register patch.

Consumer: `regime_step`. -/
theorem phi_patch_one (r p : Nat) (hp : p < r) (cells cells' : Nat → Cell)
    (hout : ∀ i, i ≠ p → cells' i = cells i) :
    Phi r cells' + (if isObs (cells p) then 1 else 0) =
      Phi r cells + (if isObs (cells' p) then 1 else 0) := by
  obtain ⟨m, hm⟩ : ∃ m, r = p + (m + 1) := ⟨r - p - 1, by omega⟩
  have hsplit : ∀ cs : Nat → Cell, Phi r cs = phiCnt cs p 0 +
      ((if isObs (cs p) then 1 else 0) + phiCnt cs m (p + 1)) := by
    intro cs
    unfold Phi
    have h := phiCnt_add cs p (m + 1) 0
    rw [← hm, Nat.zero_add] at h
    rw [h]
    try simp only [Nat.zero_add]
    have e : phiCnt cs (m + 1) p = (if isObs (cs p) then 1 else 0) + phiCnt cs m (p + 1) := rfl
    rw [e]
  rw [hsplit cells', hsplit cells]
  have h1 := phiCnt_congr cells cells' p 0 (fun i _ hi => hout i (by omega))
  have h2 := phiCnt_congr cells cells' m (p + 1) (fun i h1 h2 => hout i (by omega))
  rw [h1, h2]
  omega

/-- Auxiliary fact `phi_pos_exists` of the final mobile phase.

Consumer: `regime_step`. -/
theorem phi_pos_exists (cells : Nat → Cell) :
    ∀ k j, 0 < phiCnt cells k j → ∃ i, j ≤ i ∧ i < j + k ∧ isObs (cells i) = true := by
  intro k
  induction k with
  | zero => intro j h; simp [phiCnt] at h
  | succ k ih =>
      intro j h
      simp only [phiCnt] at h
      by_cases hc : isObs (cells j) = true
      · exact ⟨j, Nat.le_refl _, by omega, hc⟩
      · have hc' : isObs (cells j) = false := by simpa using hc
        rw [hc'] at h
        simp at h
        obtain ⟨i, h1, h2, h3⟩ := ih (j + 1) h
        exact ⟨i, by omega, by omega, h3⟩

/-! ### Local facts of one window edge without settled inputs -/

/-- Without settled inputs an edge makes none.

Consumer: `regime_step`. -/
theorem pair_nos (b : Bool) (x y : Cell) (hx : x.i.isS = false) (hy : y.i.isS = false) :
    (pair b false x y).1.i.isS = false ∧ (pair b false x y).2.i.isS = false := by
  rcases x with ⟨xi, xk⟩
  rcases y with ⟨yi, yk⟩
  cases xi <;> cases xk <;> cases yi <;> cases yk <;> cases b <;>
    simp (config := { decide := true }) [pair, inSlots, carries, Inp.isS, Inp.isP] at hx hy ⊢

/-- A front or carry after an edge was already there (same register).

Consumer: `regime_step`. -/
theorem pair_obs (b : Bool) (x y : Cell) (hx : x.i.isS = false) (hy : y.i.isS = false) :
    (isObs (pair b false x y).1 = true → isObs x = true) ∧
    (isObs (pair b false x y).2 = true → isObs y = true) := by
  rcases x with ⟨xi, xk⟩
  rcases y with ⟨yi, yk⟩
  cases xi <;> cases xk <;> cases yi <;> cases yk <;> cases b <;>
    simp (config := { decide := true }) [pair, inSlots, carries, isObs, Inp.isS, Inp.isP]
      at hx hy ⊢

/-- The local count does not rise, and falls when the source holds a front or a carry.

Consumer: `regime_step`. -/
theorem pair_phi (b : Bool) (x y : Cell) (hx : x.i.isS = false) (hy : y.i.isS = false) :
    (if isObs (pair b false x y).1 then 1 else 0) + (if isObs (pair b false x y).2 then 1 else 0) +
      (if isObs x then 1 else 0) ≤
    (if isObs x then 1 else 0) + (if isObs y then 1 else 0) + (if isObs x then 1 else 0) ∧
    (isObs x = true →
      (if isObs (pair b false x y).1 then 1 else 0) +
        (if isObs (pair b false x y).2 then 1 else 0) + 1 ≤
      (if isObs x then 1 else 0) + (if isObs y then 1 else 0)) := by
  rcases x with ⟨xi, xk⟩
  rcases y with ⟨yi, yk⟩
  cases xi <;> cases xk <;> cases yi <;> cases yk <;> cases b <;>
    simp (config := { decide := true }) [pair, inSlots, carries, isObs, Inp.isS, Inp.isP]
      at hx hy ⊢

/-- Pending outputs of an edge come from pending inputs, or from a pending source moving
into an empty carry-free responder.

Consumer: `regime_step`. -/
theorem pair_pending (b : Bool) (x y : Cell) :
    ((pair b false x y).1.i.isP = true → x.i.isP = true) ∧
    ((pair b false x y).2.i.isP = true →
      y.i.isP = true ∨ (x.i.isP = true ∧ y = { i := .e, c := .off })) := by
  rcases x with ⟨xi, xk⟩
  rcases y with ⟨yi, yk⟩
  cases xi <;> cases xk <;> cases yi <;> cases yk <;> cases b <;>
    simp (config := { decide := true }) [pair, inSlots, carries, Inp.isS, Inp.isP]

/-- The terminal edge of a source that is not a non-tail pending input makes no settled input.

Consumer: `regime_step`. -/
theorem term_nos (x y : Cell) (hx : x.i.isS = false) (hp : x.i.isP = false) :
    (pair false true x y).1.i.isS = false := by
  rcases x with ⟨xi, xk⟩
  cases xi <;> cases xk <;>
    simp (config := { decide := true }) [pair, inSlots, carries, Inp.isS, Inp.isP] at hx hp ⊢

/-- The terminal edge: obstacles stay, the count does not rise and falls on an obstacle.

Consumer: `regime_step`. -/
theorem term_obs (x y : Cell) (hx : x.i.isS = false) :
    (isObs (pair false true x y).1 = true → isObs x = true) ∧
    (if isObs (pair false true x y).1 then 1 else 0) ≤ (if isObs x then 1 else 0) ∧
    (isObs x = true → (if isObs (pair false true x y).1 then 1 else 0) + 1 ≤
      (if isObs x then 1 else 0)) ∧
    ((pair false true x y).1.i.isP = true → x.i.isP = true) := by
  rcases x with ⟨xi, xk⟩
  cases xi <;> cases xk <;>
    simp (config := { decide := true }) [pair, inSlots, carries, isObs, Inp.isS, Inp.isP] at hx ⊢

/-- The port edge keeps obstacles and settled-freeness; pending output comes from pending
or from an empty register.

Consumer: `regime_step`. -/
theorem port_facts (c c' : Cell) (hc : c' = portClean c ∨ ∃ t, c' = portAccept t c)
    (hx : c.i.isS = false) :
    c'.i.isS = false ∧ (isObs c' = isObs c) ∧
      (c'.i.isP = true → c.i.isP = true ∨ c = { i := .e, c := .off }) := by
  rcases c with ⟨ci, ck⟩
  rcases hc with rfl | ⟨t, rfl⟩ <;>
  cases ci <;> cases ck <;>
    simp (config := { decide := true }) [portClean, portAccept, isObs, Inp.isS, Inp.isP] at hx ⊢ <;>
    (try cases t) <;>
    simp (config := { decide := true }) [portClean, portAccept, isObs, Inp.isS, Inp.isP] at hx ⊢

end MarkedCells
end L3

#print axioms L3.MarkedCells.pair_nos
#print axioms L3.MarkedCells.pair_obs
#print axioms L3.MarkedCells.pair_phi
#print axioms L3.MarkedCells.pair_pending
#print axioms L3.MarkedCells.term_nos
#print axioms L3.MarkedCells.term_obs
#print axioms L3.MarkedCells.port_facts
