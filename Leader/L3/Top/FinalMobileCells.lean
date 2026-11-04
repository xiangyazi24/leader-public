import Leader.L3.Top.MarkedProgress

/-!
# Q7: the clearing step of the final mobile phase (P.11), abstract window

From a settled-empty window whose pending inputs stand left of every front and every live
carry, no abstract step creates a settled input, a front or a carry; no step moves a pending
input right of an obstacle; the number of obstacles (fronts and live carries) never rises;
and the edge of an obstacle register lowers it.

* `obx` : a front or a live carry;
* `NoS`, `Bar` : no settled input; pending inputs strictly left of every obstacle;
* `step_noS`, `step_bar`, `step_count` : closure of both and the count;
* `edge_count_drop` : the edge of an obstacle register lowers the count.

Consumer: `Leader/L3/Top/FinalMobileLink.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false

/-- An obstacle register: a front or a live carry.

Consumer: `Bar`. -/
def obx (c : Cell) : Bool := decide (c.i = .x) || decide (c.c ≠ .off)

/-- No register holds a settled input.

Consumer: `step_noS`. -/
def NoS (r : Nat) (cells : Nat → Cell) : Prop := ∀ j, j < r → (cells j).i.isS = false

/-- Every pending input is strictly left of every obstacle.

Consumer: `step_bar`. -/
def Bar (r : Nat) (cells : Nat → Cell) : Prop :=
  ∀ i j, i < r → j < r → (cells i).i.isP = true → obx (cells j) = true → i < j

/-- A window edge on settled-free registers: the source is cleared, no settled input or
obstacle is created, a pending output comes from a pending register (staying, or moving
into an empty carry-free responder).

Consumer: `step_frame`. -/
theorem pair_clear (b : Bool) (x y : Cell) (hx : x.i.isS = false) (hy : y.i.isS = false) :
    (pair b false x y).1.i.isS = false ∧ (pair b false x y).2.i.isS = false ∧
    obx (pair b false x y).1 = false ∧
    (obx (pair b false x y).2 = true → obx y = true) ∧
    ((pair b false x y).1.i.isP = true → x.i.isP = true) ∧
    ((pair b false x y).2.i.isP = true →
      y.i.isP = true ∨ (x.i.isP = true ∧ y = { i := .e, c := .off })) := by
  rcases x with ⟨xi, xk⟩
  rcases y with ⟨yi, yk⟩
  cases xi <;> cases xk <;> cases yi <;> cases yk <;> cases b <;>
    simp (config := { decide := true }) [pair, inSlots, carries, Inp.isP, Inp.isS, obx]
      at hx hy ⊢

/-- The terminal edge on a settled-free source.

Consumer: `step_frame`. -/
theorem pair_term_clear (b : Bool) (x y : Cell) (hx : x.i.isS = false) (hp : x.i.isP = false) :
    (pair b true x y).1.i.isS = false ∧ obx (pair b true x y).1 = false ∧
    (pair b true x y).1.i.isP = false := by
  rcases x with ⟨xi, xk⟩
  cases xi <;> cases xk <;> cases b <;>
    simp (config := { decide := true }) [pair, inSlots, carries, Inp.isP, Inp.isS, obx]
      at hx hp ⊢

/-- The port cleanup on a settled-free register.

Consumer: `step_good`. -/
theorem port_clean_clear (c : Cell) (hc : c.i.isS = false) :
    (portClean c).i.isS = false ∧ (obx (portClean c) = true → obx c = true) ∧
    ((portClean c).i.isP = true → c.i.isP = true) := by
  rcases c with ⟨ci, ck⟩
  cases ci <;> cases ck <;>
    simp (config := { decide := true }) [portClean, Inp.isP, Inp.isS, obx] at hc ⊢

/-- The port acceptance on a settled-free register.

Consumer: `step_good`. -/
theorem port_accept_clear (t : Bool) (c : Cell) (hc : c.i.isS = false) :
    (portAccept t c).i.isS = false ∧ (obx (portAccept t c) = true → obx c = true) ∧
    ((portAccept t c).i.isP = true → c.i.isP = true ∨ c = { i := .e, c := .off }) := by
  rcases c with ⟨ci, ck⟩
  cases ci <;> cases ck <;> cases t <;>
    simp (config := { decide := true }) [portAccept, Inp.isP, Inp.isS, obx] at hc ⊢

/-- Pending inputs stay strictly left of the obstacles when obstacles only disappear and a
pending input arises only where it stood, by a move into an empty carry-free register, or by
an acceptance at the border.

Consumer: `step_good`. -/
theorem bar_of_frame (r : Nat) (cells cells' : Nat → Cell) (hB : Bar r cells)
    (hmono : ∀ j, j < r → obx (cells' j) = true → obx (cells j) = true)
    (horig : ∀ i, i < r → (cells' i).i.isP = true →
      (cells i).i.isP = true ∨
      (0 < i ∧ (cells (i - 1)).i.isP = true ∧ cells i = { i := .e, c := .off }) ∨
      (i = 0 ∧ cells 0 = { i := .e, c := .off })) :
    Bar r cells' := by
  intro i j hi hj hPi hobs
  have hj' := hmono j hj hobs
  rcases horig i hi hPi with h | ⟨h0, hp, hc⟩ | ⟨rfl, hc⟩
  · exact hB i j hi hj h hj'
  · have h1 := hB (i - 1) j (by omega) hj hp hj'
    have h2 : j ≠ i := by
      intro hji
      subst hji
      rw [hc] at hj'
      simp [obx] at hj'
    omega
  · have h2 : j ≠ 0 := by
      intro hji
      subst hji
      rw [hc] at hj'
      simp [obx] at hj'
    omega

/-- **Closure.**  On a settled-free window with the pending inputs left of the obstacles and
at least one obstacle, every abstract step keeps both properties and creates no obstacle.

Consumer: `Leader/L3/Top/FinalMobileLink.lean`. -/
theorem step_good (r : Nat) (hr : 2 ≤ r) (cells cells' : Nat → Cell)
    (hS : NoS r cells) (hB : Bar r cells) (hobs : ∃ j, j < r ∧ obx (cells j) = true)
    (hst : Step r cells cells') :
    NoS r cells' ∧ Bar r cells' ∧
      ∀ j, j < r → obx (cells' j) = true → obx (cells j) = true := by
  cases hst with
  | frame => exact ⟨hS, hB, fun _ _ h => h⟩
  | edge p hp =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := pair_clear (decide (p = 0)) (cells p) (cells (p + 1))
      (hS p (by omega)) (hS (p + 1) hp)
    have hmono : ∀ j, j < r → obx (setTwo cells p (pair (decide (p = 0)) false (cells p)
        (cells (p + 1))).1 (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2 j) = true →
        obx (cells j) = true := by
      intro j hj
      unfold setTwo
      by_cases hjp : j = p
      · subst hjp; simp [h3]
      · by_cases hjq : j = p + 1
        · subst hjq; simp only [if_neg hjp, if_true]; exact h4
        · simp only [if_neg hjp, if_neg hjq]; exact id
    refine ⟨?_, bar_of_frame r cells _ hB hmono ?_, hmono⟩
    · intro j hj
      unfold setTwo
      by_cases hjp : j = p
      · subst hjp; simpa using h1
      · by_cases hjq : j = p + 1
        · subst hjq; simpa using h2
        · simp only [if_neg hjp, if_neg hjq]; exact hS j hj
    · intro i hi hPi
      unfold setTwo at hPi
      by_cases hjp : i = p
      · subst hjp
        simp only [if_true] at hPi
        exact Or.inl (h5 hPi)
      · by_cases hjq : i = p + 1
        · subst hjq
          simp only [if_neg hjp, if_true] at hPi
          rcases h6 hPi with h | ⟨h, hc⟩
          · exact Or.inl h
          · exact Or.inr (Or.inl ⟨by omega, by simpa using h, hc⟩)
        · simp only [if_neg hjp, if_neg hjq] at hPi
          exact Or.inl hPi
  | term =>
    have hP : (cells (r - 1)).i.isP = false := by
      cases hq : (cells (r - 1)).i.isP
      · rfl
      · obtain ⟨j, hj, hoj⟩ := hobs
        have := hB (r - 1) j (by omega) hj hq hoj
        omega
    obtain ⟨h1, h2, h3⟩ := pair_term_clear false (cells (r - 1)) { i := .e, c := .off }
      (hS (r - 1) (by omega)) hP
    have hmono : ∀ j, j < r → obx (setOne cells (r - 1) (pair false true (cells (r - 1))
        { i := .e, c := .off }).1 j) = true → obx (cells j) = true := by
      intro j hj
      unfold setOne
      by_cases hjp : j = r - 1
      · subst hjp; simp [h2]
      · simp only [if_neg hjp]; exact id
    refine ⟨?_, bar_of_frame r cells _ hB hmono ?_, hmono⟩
    · intro j hj
      unfold setOne
      by_cases hjp : j = r - 1
      · subst hjp; simpa using h1
      · simp only [if_neg hjp]; exact hS j hj
    · intro i hi hPi
      unfold setOne at hPi
      by_cases hjp : i = r - 1
      · subst hjp
        simp only [if_true] at hPi
        rw [h3] at hPi
        exact absurd hPi (by decide)
      · simp only [if_neg hjp] at hPi
        exact Or.inl hPi
  | clean =>
    obtain ⟨h1, h2, h3⟩ := port_clean_clear (cells 0) (hS 0 (by omega))
    have hmono : ∀ j, j < r → obx (setOne cells 0 (portClean (cells 0)) j) = true →
        obx (cells j) = true := by
      intro j hj
      unfold setOne
      by_cases hjp : j = 0
      · subst hjp; simpa using h2
      · simp only [if_neg hjp]; exact id
    refine ⟨?_, bar_of_frame r cells _ hB hmono ?_, hmono⟩
    · intro j hj
      unfold setOne
      by_cases hjp : j = 0
      · subst hjp; simpa using h1
      · simp only [if_neg hjp]; exact hS j hj
    · intro i hi hPi
      unfold setOne at hPi
      by_cases hjp : i = 0
      · subst hjp
        simp only [if_true] at hPi
        exact Or.inl (h3 hPi)
      · simp only [if_neg hjp] at hPi
        exact Or.inl hPi
  | accept t =>
    obtain ⟨h1, h2, h3⟩ := port_accept_clear t (cells 0) (hS 0 (by omega))
    have hmono : ∀ j, j < r → obx (setOne cells 0 (portAccept t (cells 0)) j) = true →
        obx (cells j) = true := by
      intro j hj
      unfold setOne
      by_cases hjp : j = 0
      · subst hjp; simpa using h2
      · simp only [if_neg hjp]; exact id
    refine ⟨?_, bar_of_frame r cells _ hB hmono ?_, hmono⟩
    · intro j hj
      unfold setOne
      by_cases hjp : j = 0
      · subst hjp; simpa using h1
      · simp only [if_neg hjp]; exact hS j hj
    · intro i hi hPi
      unfold setOne at hPi
      by_cases hjp : i = 0
      · subst hjp
        simp only [if_true] at hPi
        rcases h3 hPi with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr ⟨rfl, h⟩)
      · simp only [if_neg hjp] at hPi
        exact Or.inl hPi

/-- The number of obstacle registers among the first `k`.

Consumer: `obCount_le`, `clearPotential`. -/
def obCount (cells : Nat → Cell) : Nat → Nat
  | 0 => 0
  | k + 1 => obCount cells k + (if obx (cells k) = true then 1 else 0)

/-- The count is at most the number of registers.

Consumer: `clearPotential_le`. -/
theorem obCount_le_self (cells : Nat → Cell) : ∀ k, obCount cells k ≤ k := by
  intro k
  induction k with
  | zero => exact Nat.le_refl 0
  | succ k ih =>
    simp only [obCount]
    split <;> omega

/-- Obstacles that only disappear lower the count.

Consumer: `step_count`. -/
theorem obCount_le (c c' : Nat → Cell) :
    ∀ k, (∀ j, j < k → obx (c' j) = true → obx (c j) = true) → obCount c' k ≤ obCount c k := by
  intro k
  induction k with
  | zero => intro _; exact Nat.le_refl 0
  | succ k ih =>
    intro h
    have h1 := ih (fun j hj => h j (by omega))
    have h2 := h k (by omega)
    simp only [obCount]
    by_cases h3 : obx (c' k) = true
    · rw [if_pos h3, if_pos (h2 h3)]; omega
    · rw [if_neg h3]
      split <;> omega

/-- If moreover one obstacle disappears the count drops.

Consumer: `edge_count_drop`. -/
theorem obCount_lt (c c' : Nat → Cell) :
    ∀ k, (∀ j, j < k → obx (c' j) = true → obx (c j) = true) →
      (∃ j, j < k ∧ obx (c j) = true ∧ obx (c' j) = false) → obCount c' k < obCount c k := by
  intro k
  induction k with
  | zero => intro _ ⟨j, hj, _⟩; omega
  | succ k ih =>
    intro h ⟨j, hj, hc, hc'⟩
    have h2 := h k (by omega)
    simp only [obCount]
    by_cases hjk : j = k
    · subst hjk
      have h1 := obCount_le c c' j (fun i hi => h i (by omega))
      rw [if_pos hc, if_neg (by simp [hc'])]
      omega
    · have h1 := ih (fun i hi => h i (by omega)) ⟨j, by omega, hc, hc'⟩
      by_cases h3 : obx (c' k) = true
      · rw [if_pos h3, if_pos (h2 h3)]; omega
      · rw [if_neg h3]
        split <;> omega

/-- No step raises the count.

Consumer: `Leader/L3/Top/FinalMobileLink.lean`. -/
theorem step_count (r : Nat) (hr : 2 ≤ r) (cells cells' : Nat → Cell)
    (hS : NoS r cells) (hB : Bar r cells) (hobs : ∃ j, j < r ∧ obx (cells j) = true)
    (hst : Step r cells cells') : obCount cells' r ≤ obCount cells r :=
  obCount_le cells cells' r (step_good r hr cells cells' hS hB hobs hst).2.2

/-- **The edge of an obstacle register lowers the count.**

Consumer: `Leader/L3/Top/FinalMobileLink.lean`. -/
theorem edge_count_drop (r : Nat) (hr : 2 ≤ r) (cells : Nat → Cell) (p : Nat) (hp : p < r)
    (hS : NoS r cells) (hB : Bar r cells) (hob : obx (cells p) = true) :
    obCount (edgeStep r cells p) r < obCount cells r := by
  have hobs : ∃ j, j < r ∧ obx (cells j) = true := ⟨p, hp, hob⟩
  have hm := (step_good r hr cells _ hS hB hobs (edgeStep_step r cells p hp)).2.2
  apply obCount_lt cells _ r hm
  refine ⟨p, hp, hob, ?_⟩
  unfold edgeStep
  by_cases hp1 : p + 1 < r
  · rw [if_pos hp1]
    have := (pair_clear (decide (p = 0)) (cells p) (cells (p + 1)) (hS p hp)
      (hS (p + 1) hp1)).2.2.1
    simpa [setTwo] using this
  · rw [if_neg hp1]
    have hpe : p = r - 1 := by omega
    have hP : (cells (r - 1)).i.isP = false := by
      cases hq : (cells (r - 1)).i.isP
      · rfl
      · have := hB (r - 1) p (by omega) hp hq hob
        omega
    have := (pair_term_clear false (cells (r - 1)) { i := .e, c := .off }
      (hS (r - 1) (by omega)) hP).2.1
    subst hpe
    simpa [setOne] using this

/-- A zero count means no obstacle.

Consumer: `Leader/L3/Top/FinalMobileLink.lean`. -/
theorem obCount_zero (cells : Nat → Cell) :
    ∀ k, obCount cells k = 0 → ∀ j, j < k → obx (cells j) = false := by
  intro k
  induction k with
  | zero => intro _ j hj; omega
  | succ k ih =>
    intro h j hj
    simp only [obCount] at h
    by_cases hjk : j = k
    · subst hjk
      by_cases h3 : obx (cells j) = true
      · rw [if_pos h3] at h; omega
      · simpa using h3
    · apply ih _ j (by omega)
      split at h <;> omega

/-- A positive count means an obstacle.

Consumer: `Leader/L3/Top/FinalMobileLink.lean`. -/
theorem obCount_pos (cells : Nat → Cell) :
    ∀ k, 0 < obCount cells k → ∃ j, j < k ∧ obx (cells j) = true := by
  intro k
  induction k with
  | zero => intro h; simp [obCount] at h
  | succ k ih =>
    intro h
    simp only [obCount] at h
    by_cases h3 : obx (cells k) = true
    · exact ⟨k, by omega, h3⟩
    · rw [if_neg h3] at h
      obtain ⟨j, hj, hj'⟩ := ih (by omega)
      exact ⟨j, by omega, hj'⟩

end MarkedCells
end L3
