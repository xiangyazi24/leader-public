import Leader.L3.Top.OldMark

/-!
# Q7: flagged pending packets in the abstract window (P.11, serial-suffix genealogy)

A flagged register is a pending input that was accepted after the anchor.  The flags ride on
the pending inputs: a flagged input stays, or moves right into an empty carry-free register.
This module proves, for the abstract window with labels:

* `pair_flag` : the local facts of one window edge on a flagged source and responder;
* `LInv` : the flagged registers are strictly left of every obstacle (`FBar`) and the labels of
  the flagged registers, read right to left, are a suffix of the accepted queue `Q`.

Consumer: `Leader/L3/Top/FinalMobileLabels.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false

/-- Local facts of one window edge on a flagged source and responder.

Consumer: `lstep_edge`. -/
theorem pair_flag (b : Bool) (x y : Cell) (ox oy : Bool)
    (hox : ox = true → x.i.isP = true ∧ x.c = .off)
    (hoy : oy = true → y.i.isP = true ∧ y.c = .off) :
    (oldX x (pair b false x y).1 ox = true →
      (pair b false x y).1.i.isP = true ∧ (pair b false x y).1.c = .off) ∧
    (oldY x y (pair b false x y).2 ox oy = true →
      (pair b false x y).2.i.isP = true ∧ (pair b false x y).2.c = .off) ∧
    (oy = true → (pair b false x y).2 = y) ∧
    (ox = true → oldX x (pair b false x y).1 ox = true ∨
      (y = { i := .e, c := .off } ∧ (pair b false x y).2.i.isP = true ∧
        (pair b false x y).1.i.isP = false) ∨
      (y.i.isS = true ∧ y.c = .off)) ∧
    (obC (pair b false x y).1 = true → obC x = true ∨ (x.i.isP = true ∧ y.i.isS = true)) ∧
    (obC (pair b false x y).2 = true → obC y = true) ∧
    (oldY x y (pair b false x y).2 ox oy = true → oy = true ∨
      (ox = true ∧ y = { i := .e, c := .off } ∧ (pair b false x y).1.i.isP = false)) ∧
    (y.i.isS = true → (pair b false x y).2.i.isP = false) := by
  rcases x with ⟨xi, xk⟩
  rcases y with ⟨yi, yk⟩
  cases xi <;> cases xk <;> cases yi <;> cases yk <;> cases ox <;> cases oy <;> cases b <;>
    simp (config := { decide := true }) [pair, inSlots, carries, oldX, oldY, obC, Inp.isP, Inp.isS]
      at hox hoy ⊢

/-- The flag bookkeeping of one window edge: either the flags stay where they are, or the
flagged source moves into an empty carry-free responder, or the flagged source is consumed
beside a settled responder.

Consumer: `lstep_edge`. -/
theorem edge_flags (b : Bool) (x y : Cell) (ox oy : Bool)
    (hox : ox = true → x.i.isP = true ∧ x.c = .off)
    (hoy : oy = true → y.i.isP = true ∧ y.c = .off) :
    (oldX x (pair b false x y).1 ox = ox ∧
      oldY x y (pair b false x y).2 ox oy = oy ∧
      (oy = true → (oy && (pair b false x y).2.i.isP && y.i.isP) = true)) ∨
    (ox = true ∧ oy = false ∧ y = { i := .e, c := .off } ∧
      oldX x (pair b false x y).1 ox = false ∧
      oldY x y (pair b false x y).2 ox oy = true ∧
      (oy && (pair b false x y).2.i.isP && y.i.isP) = false) ∨
    (ox = true ∧ oy = false ∧ y.i.isS = true ∧
      oldX x (pair b false x y).1 ox = false ∧
      oldY x y (pair b false x y).2 ox oy = false) := by
  rcases x with ⟨xi, xk⟩
  rcases y with ⟨yi, yk⟩
  cases xi <;> cases xk <;> cases yi <;> cases yk <;> cases ox <;> cases oy <;> cases b <;>
    simp (config := { decide := true }) [pair, inSlots, carries, oldX, oldY, obC, Inp.isP, Inp.isS]
      at hox hoy ⊢

/-- The flagged registers of a window, read right to left.

Consumer: `LInv`. -/
def ordLab {α : Type} (o : Nat → Bool) (ℓ : Nat → α) : Nat → List α
  | 0 => []
  | k + 1 => (if o k = true then [ℓ k] else []) ++ ordLab o ℓ k

/-- The reading depends only on the registers read.

Consumer: `lstep_edge`. -/
theorem ordLab_congr {α : Type} (o o' : Nat → Bool) (ℓ ℓ' : Nat → α) :
    ∀ k, (∀ j, j < k → o j = o' j) → (∀ j, j < k → o j = true → ℓ j = ℓ' j) →
      ordLab o ℓ k = ordLab o' ℓ' k := by
  intro k
  induction k with
  | zero => intro _ _; rfl
  | succ k ih =>
    intro h1 h2
    simp only [ordLab]
    rw [ih (fun j hj => h1 j (by omega)) (fun j hj => h2 j (by omega)), h1 k (by omega)]
    by_cases hk : o' k = true
    · rw [if_pos hk, if_pos hk, h2 k (by omega) (by rw [h1 k (by omega)]; exact hk)]
    · rw [if_neg hk, if_neg hk]

/-- Without flags above `k` the reading stops at `k`.

Consumer: `lstep_edge`. -/
theorem ordLab_above {α : Type} (o : Nat → Bool) (ℓ : Nat → α) (k : Nat) :
    ∀ m, (∀ j, k ≤ j → j < m → o j = false) → k ≤ m → ordLab o ℓ m = ordLab o ℓ k := by
  intro m
  induction m with
  | zero => intro _ hk; have : k = 0 := by omega
            subst this; rfl
  | succ m ih =>
    intro h hk
    by_cases hkm : k = m + 1
    · subst hkm; rfl
    · simp only [ordLab]
      rw [h m (by omega) (by omega)]
      simp only [Bool.false_eq_true, if_false, List.nil_append]
      exact ih (fun j hj1 hj2 => h j hj1 (by omega)) (by omega)

/-- Registers above `a` that read alike keep the reading equal.

Consumer: `lstep_edge`. -/
theorem ordLab_ext {α : Type} (o o' : Nat → Bool) (ℓ ℓ' : Nat → α) (a : Nat)
    (h : ordLab o' ℓ' a = ordLab o ℓ a) :
    ∀ m, a ≤ m → (∀ j, a ≤ j → j < m → o' j = o j) →
      (∀ j, a ≤ j → j < m → o j = true → ℓ' j = ℓ j) →
      ordLab o' ℓ' m = ordLab o ℓ m := by
  intro m
  induction m with
  | zero =>
    intro ha _ _
    have : a = 0 := by omega
    subst this; exact h
  | succ m ih =>
    intro ha h1 h2
    by_cases ham : a = m + 1
    · subst ham; exact h
    · simp only [ordLab]
      rw [ih (by omega) (fun j hj1 hj2 => h1 j hj1 (by omega))
        (fun j hj1 hj2 => h2 j hj1 (by omega)), h1 m (by omega) (by omega)]
      by_cases hm : o m = true
      · rw [if_pos hm, if_pos hm, h2 m (by omega) (by omega) hm]
      · rw [if_neg hm, if_neg hm]

/-- Flagged registers are strictly left of every obstacle.

Consumer: `LInv`. -/
def FBar (r : Nat) (c : Nat → Cell) (o : Nat → Bool) : Prop :=
  ∀ j i, j < r → i < r → o j = true → obC (c i) = true → j < i

/-- Flagged registers hold pending inputs.

Consumer: `LInv`. -/
def FPend (r : Nat) (c : Nat → Cell) (o : Nat → Bool) : Prop :=
  ∀ j, j < r → o j = true → (c j).i.isP = true

/-- **The window invariant**: flagged registers are pending and left of every obstacle, and
their labels, right to left, are the tail `Q.drop k` of the accepted queue `Q`.

Consumer: `lstep_inv`. -/
def LInv {α : Type} (r : Nat) (Q : List α) (c : Nat → Cell) (o : Nat → Bool) (ℓ : Nat → α) :
    Prop :=
  FPend r c o ∧ FBar r c o ∧ ∃ k, k ≤ Q.length ∧ ordLab o ℓ r = Q.drop k

/-- A flagged register has no obstacle on it.

Consumer: `lstep_edge`. -/
theorem fbar_diag {r : Nat} {c : Nat → Cell} {o : Nat → Bool} (hb : FBar r c o) (j : Nat)
    (hj : j < r) (hoj : o j = true) : obC (c j) = false := by
  cases h : obC (c j)
  · rfl
  · have := hb j j hj hj hoj h
    omega

/-- A pending register without obstacle has a pending input and no carry.

Consumer: `lstep_edge`. -/
theorem flag_cell {r : Nat} {c : Nat → Cell} {o : Nat → Bool} (hp : FPend r c o)
    (hb : FBar r c o) (j : Nat) (hj : j < r) (hoj : o j = true) :
    (c j).i.isP = true ∧ (c j).c = .off := by
  refine ⟨hp j hj hoj, ?_⟩
  have h := fbar_diag hb j hj hoj
  unfold obC at h
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
  exact Decidable.of_not_not h.2

/-- A pending input without carry is not an obstacle.

Consumer: `lstep_edge`. -/
theorem obC_false_of_P (c : Cell) (h1 : c.i.isP = true) (h2 : c.c = .off) : obC c = false := by
  rcases c with ⟨ci, ck⟩
  cases ci <;> cases ck <;>
    simp (config := { decide := true }) [obC, Inp.isP, Inp.isS] at h1 h2 ⊢

/-- A settled input is an obstacle.

Consumer: `lstep_edge`. -/
theorem obC_of_S (c : Cell) (h : c.i.isS = true) : obC c = true := by
  unfold obC
  simp [h]

/-- A pending input is not a settled input.

Consumer: `lstep_edge`. -/
theorem P_not_S (i : Inp) (h : i.isP = true) : i.isS = false := by
  cases i <;> simp [Inp.isP, Inp.isS] at h ⊢

/-- The labels after a window edge: a flagged input that moved carries its label.

Consumer: `lstep_edge`. -/
def labEdge {α : Type} (c : Nat → Cell) (o : Nat → Bool) (ℓ : Nat → α) (p : Nat) :
    Nat → α :=
  fun j => if j = p + 1 then
      (if (o (p + 1) && (pair (decide (p = 0)) false (c p) (c (p + 1))).2.i.isP &&
          (c (p + 1)).i.isP) = true then ℓ (p + 1) else ℓ p)
    else ℓ j

/-- **A window edge keeps the invariant**: flagged inputs stay or move right, the oldest
flagged input may be consumed beside a settled input, and nothing else changes.

Consumer: `lstep_inv`. -/
theorem lstep_edge {α : Type} (r p : Nat) (hp : p + 1 < r) (Q : List α) (c : Nat → Cell)
    (o : Nat → Bool) (ℓ : Nat → α) (h : LInv r Q c o ℓ) :
    LInv r Q
      (setTwo c p (pair (decide (p = 0)) false (c p) (c (p + 1))).1
        (pair (decide (p = 0)) false (c p) (c (p + 1))).2)
      (flagsEdge r c o p) (labEdge c o ℓ p) := by
  obtain ⟨hF, hB, k, hk, hlist⟩ := h
  have hoxp : o p = true → (c p).i.isP = true ∧ (c p).c = .off :=
    fun ho => flag_cell hF hB p (by omega) ho
  have hoyq : o (p + 1) = true → (c (p + 1)).i.isP = true ∧ (c (p + 1)).c = .off :=
    fun ho => flag_cell hF hB (p + 1) hp ho
  have hpf := pair_flag (decide (p = 0)) (c p) (c (p + 1)) (o p) (o (p + 1)) hoxp hoyq
  have hef := edge_flags (decide (p = 0)) (c p) (c (p + 1)) (o p) (o (p + 1)) hoxp hoyq
  generalize hP : pair (decide (p = 0)) false (c p) (c (p + 1)) = P at hpf hef ⊢
  have s1 : setTwo c p P.1 P.2 p = P.1 := by simp [setTwo]
  have s2 : setTwo c p P.1 P.2 (p + 1) = P.2 := by simp [setTwo]
  have s3 : ∀ j, j ≠ p → j ≠ p + 1 → setTwo c p P.1 P.2 j = c j := by
    intro j h1 h2; simp [setTwo, h1, h2]
  have e1 : flagsEdge r c o p p = oldX (c p) P.1 (o p) := by simp [flagsEdge, hP]
  have e2 : flagsEdge r c o p (p + 1) = oldY (c p) (c (p + 1)) P.2 (o p) (o (p + 1)) := by
    simp [flagsEdge, hP]
  have e3 : ∀ j, j ≠ p → j ≠ p + 1 → flagsEdge r c o p j = o j := by
    intro j h1 h2; simp [flagsEdge, h1, h2]
  have l1 : labEdge c o ℓ p p = ℓ p := by simp [labEdge]
  have l2 : labEdge c o ℓ p (p + 1) =
      (if (o (p + 1) && P.2.i.isP && (c (p + 1)).i.isP) = true then ℓ (p + 1) else ℓ p) := by
    simp [labEdge, hP]
  have l3 : ∀ j, j ≠ p + 1 → labEdge c o ℓ p j = ℓ j := by
    intro j h1; simp [labEdge, h1]
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := hpf
  -- origins of the new flags
  have orig_p : flagsEdge r c o p p = true → o p = true ∧ P.1.i.isP = true ∧ P.1.c = .off := by
    intro h
    rw [e1] at h
    have h' := h
    unfold oldX at h'
    simp only [Bool.and_eq_true] at h'
    exact ⟨h'.1, f1 h⟩
  have orig_q : flagsEdge r c o p (p + 1) = true →
      (o (p + 1) = true ∨ (o p = true ∧ (c (p + 1)) = { i := .e, c := .off })) ∧
        P.2.i.isP = true ∧ P.2.c = .off := by
    intro h
    rw [e2] at h
    refine ⟨?_, f2 h⟩
    rcases f7 h with h1 | ⟨h1, h2, _⟩
    · exact Or.inl h1
    · exact Or.inr ⟨h1, h2⟩
  refine ⟨?_, ?_, ?_⟩
  · -- flagged registers are pending
    intro j hj hoj
    by_cases hjp : j = p
    · subst hjp; rw [s1]; exact (orig_p hoj).2.1
    · by_cases hjq : j = p + 1
      · subst hjq; rw [s2]; exact (orig_q hoj).2.1
      · rw [s3 j hjp hjq]; rw [e3 j hjp hjq] at hoj; exact hF j hj hoj
  · -- the flagged registers stay left of every obstacle
    intro j i hj hi hoj hobs
    by_cases hjp : j = p
    · subst hjp
      obtain ⟨hop, hx1, hx2⟩ := orig_p hoj
      by_cases hip : i = j
      · subst hip; rw [s1] at hobs; rw [obC_false_of_P _ hx1 hx2] at hobs; exact absurd hobs (by decide)
      · by_cases hiq : i = j + 1
        · omega
        · rw [s3 i hip hiq] at hobs; have := hB j i (by omega) hi hop hobs; exact this
    · by_cases hjq : j = p + 1
      · subst hjq
        obtain ⟨hor, hy1, hy2⟩ := orig_q hoj
        by_cases hip : i = p
        · subst hip
          rw [s1] at hobs
          rcases f5 hobs with h1 | ⟨h1, h2⟩
          · rcases hor with hor | ⟨hor, _⟩
            · have := hB (i + 1) i hj (by omega) hor h1; omega
            · have := hB i i (by omega) (by omega) hor h1; omega
          · rcases hor with hor | ⟨_, hor⟩
            · have := (hoyq hor).1; rw [P_not_S _ this] at h2; exact absurd h2 (by decide)
            · rw [hor] at h2; exact absurd h2 (by decide)
        · by_cases hiq : i = p + 1
          · subst hiq; rw [s2] at hobs; rw [obC_false_of_P _ hy1 hy2] at hobs
            exact absurd hobs (by decide)
          · rw [s3 i hip hiq] at hobs
            rcases hor with hor | ⟨hor, _⟩
            · have := hB (p + 1) i hj hi hor hobs; exact this
            · have := hB p i (by omega) hi hor hobs; omega
      · rw [e3 j hjp hjq] at hoj
        by_cases hip : i = p
        · subst hip
          rw [s1] at hobs
          rcases f5 hobs with h1 | ⟨_, h2⟩
          · have := hB j i hj (by omega) hoj h1; exact this
          · have := hB j (i + 1) hj hp hoj (obC_of_S _ h2); omega
        · by_cases hiq : i = p + 1
          · subst hiq; rw [s2] at hobs
            have := hB j (p + 1) hj hi hoj (f6 hobs); exact this
          · rw [s3 i hip hiq] at hobs; exact hB j i hj hi hoj hobs
  · -- the labels, read right to left
    have hcongr_below : ∀ j, j < p → flagsEdge r c o p j = o j := fun j hj =>
      e3 j (by omega) (by omega)
    have hord_below : ordLab (flagsEdge r c o p) (labEdge c o ℓ p) p = ordLab o ℓ p :=
      ordLab_congr _ _ _ _ p (fun j hj => hcongr_below j hj)
        (fun j hj _ => l3 j (by omega))
    have hA : ordLab o ℓ (p + 2) = (if o (p + 1) = true then [ℓ (p + 1)] else []) ++
        ((if o p = true then [ℓ p] else []) ++ ordLab o ℓ p) := rfl
    have hA' : ordLab (flagsEdge r c o p) (labEdge c o ℓ p) (p + 2) =
        (if flagsEdge r c o p (p + 1) = true then [labEdge c o ℓ p (p + 1)] else []) ++
        ((if flagsEdge r c o p p = true then [labEdge c o ℓ p p] else []) ++
          ordLab (flagsEdge r c o p) (labEdge c o ℓ p) p) := rfl
    rw [hord_below, l1] at hA'
    have habove : ∀ j, p + 2 ≤ j → j < r → flagsEdge r c o p j = o j := fun j h1 _ =>
      e3 j (by omega) (by omega)
    have habove' : ∀ j, p + 2 ≤ j → j < r → o j = true →
        labEdge c o ℓ p j = ℓ j := fun j h1 _ _ => l3 j (by omega)
    rcases hef with ⟨g1, g2, g3⟩ | ⟨g0, g1, g2, g3, g4, g5⟩ | ⟨g0, g1, g2, g3, g4⟩
    · -- the flags stay
      refine ⟨k, hk, ?_⟩
      rw [← hlist]
      apply ordLab_congr
      · intro j hj
        by_cases hjp : j = p
        · subst hjp; rw [e1, g1]
        · by_cases hjq : j = p + 1
          · subst hjq; rw [e2, g2]
          · exact e3 j hjp hjq
      · intro j hj hoj
        by_cases hjq : j = p + 1
        · subst hjq
          have hoq : o (p + 1) = true := by rw [e2, g2] at hoj; exact hoj
          rw [l2, if_pos (g3 hoq)]
        · exact l3 j hjq
    · -- the flagged source moves into the empty responder
      refine ⟨k, hk, ?_⟩
      rw [← hlist]
      apply ordLab_ext o _ ℓ _ (p + 2) _ r (by omega) habove habove'
      rw [hA, hA', e1, e2, g3, g4, l2, g5, g1, g0]
      simp
    · -- the oldest flagged input is consumed beside a settled responder
      have hno : ∀ j, p + 2 ≤ j → j < r → o j = false := by
        intro j h1 h2
        cases hoj : o j
        · rfl
        · have := hB j (p + 1) h2 hp hoj (obC_of_S _ g2)
          omega
      have hno' : ∀ j, p + 2 ≤ j → j < r → flagsEdge r c o p j = false := by
        intro j h1 h2
        rw [habove j h1 h2]; exact hno j h1 h2
      have hr1 := ordLab_above o ℓ (p + 2) r hno (by omega)
      have hr2 := ordLab_above (flagsEdge r c o p) (labEdge c o ℓ p) (p + 2) r hno' (by omega)
      rw [hA, g0, g1] at hr1
      rw [hA', e1, e2, g3, g4] at hr2
      simp only [Bool.false_eq_true, if_false, if_true, List.nil_append] at hr1 hr2
      rw [hr1] at hlist
      have hne : Q.drop k ≠ [] := by rw [← hlist]; simp
      have hlen : k < Q.length := by
        by_cases h : Q.length ≤ k
        · exact absurd (List.drop_eq_nil_of_le h) hne
        · omega
      refine ⟨k + 1, by omega, ?_⟩
      rw [hr2, ← List.tail_drop, ← hlist]
      simp

/-- The terminal edge consumes a flagged source and creates an obstacle only from a pending
source.

Consumer: `lstep_term`. -/
theorem term_flag (x y : Cell) (ox : Bool) (hox : ox = true → x.i.isP = true ∧ x.c = .off) :
    (ox = true → oldX x (pair false true x y).1 ox = false) ∧
    (obC (pair false true x y).1 = true → obC x = true ∨ x.i.isP = true) := by
  rcases x with ⟨xi, xk⟩
  cases xi <;> cases xk <;> cases ox <;>
    simp (config := { decide := true }) [pair, inSlots, carries, oldX, obC, Inp.isP, Inp.isS]
      at hox ⊢

/-- **The terminal edge keeps the invariant.**

Consumer: `lstep_inv`. -/
theorem lstep_term {α : Type} (r : Nat) (hr : 2 ≤ r) (Q : List α) (c : Nat → Cell)
    (o : Nat → Bool) (ℓ : Nat → α) (h : LInv r Q c o ℓ) :
    LInv r Q
      (setOne c (r - 1) (pair false true (c (r - 1)) { i := .e, c := .off }).1)
      (flagsTerm r c o) ℓ := by
  obtain ⟨hF, hB, k, hk, hlist⟩ := h
  have hoxp : o (r - 1) = true → (c (r - 1)).i.isP = true ∧ (c (r - 1)).c = .off :=
    fun ho => flag_cell hF hB (r - 1) (by omega) ho
  have ht := term_flag (c (r - 1)) { i := .e, c := .off } (o (r - 1)) hoxp
  have s1 : setOne c (r - 1) (pair false true (c (r - 1)) { i := .e, c := .off }).1 (r - 1) =
      (pair false true (c (r - 1)) { i := .e, c := .off }).1 := by simp [setOne]
  have s3 : ∀ j, j ≠ r - 1 →
      setOne c (r - 1) (pair false true (c (r - 1)) { i := .e, c := .off }).1 j = c j := by
    intro j h1; simp [setOne, h1]
  have e1 : flagsTerm r c o (r - 1) =
      oldX (c (r - 1)) (pair false true (c (r - 1)) { i := .e, c := .off }).1 (o (r - 1)) := by
    simp [flagsTerm]
  have e3 : ∀ j, j ≠ r - 1 → flagsTerm r c o j = o j := by
    intro j h1; simp [flagsTerm, h1]
  refine ⟨?_, ?_, ?_⟩
  · intro j hj hoj
    by_cases hjp : j = r - 1
    · subst hjp
      rw [s1]
      rw [e1] at hoj
      unfold oldX at hoj
      simp only [Bool.and_eq_true] at hoj
      exact hoj.2
    · rw [s3 j hjp]; rw [e3 j hjp] at hoj; exact hF j hj hoj
  · intro j i hj hi hoj hobs
    by_cases hjp : j = r - 1
    · subst hjp
      rw [e1] at hoj
      have hox' : o (r - 1) = true := by
        unfold oldX at hoj
        simp only [Bool.and_eq_true] at hoj
        exact hoj.1
      rw [ht.1 hox'] at hoj
      exact absurd hoj (by decide)
    · rw [e3 j hjp] at hoj
      have hjlt : j < r - 1 := by omega
      by_cases hip : i = r - 1
      · omega
      · rw [s3 i hip] at hobs
        exact hB j i hj hi hoj hobs
  · by_cases hox : o (r - 1) = true
    · have hfalse : flagsTerm r c o (r - 1) = false := by rw [e1]; exact ht.1 hox
      obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
      have h1 : ordLab (flagsTerm (m + 1) c o) ℓ (m + 1) = ordLab o ℓ m := by
        simp only [ordLab]
        have : flagsTerm (m + 1) c o m = false := by simpa using hfalse
        rw [this]
        simp only [Bool.false_eq_true, if_false, List.nil_append]
        apply ordLab_congr
        · intro j hj; exact e3 j (by omega)
        · intro j hj hoj; rfl
      have h2 : ordLab o ℓ (m + 1) = ℓ m :: ordLab o ℓ m := by
        simp only [ordLab]
        have : o m = true := by simpa using hox
        rw [if_pos this]; rfl
      have hne : Q.drop k ≠ [] := by rw [← hlist, h2]; simp
      have hlen : k < Q.length := by
        by_cases h : Q.length ≤ k
        · exact absurd (List.drop_eq_nil_of_le h) hne
        · omega
      refine ⟨k + 1, by omega, ?_⟩
      rw [h1, ← List.tail_drop, ← hlist, h2]
      simp
    · have hfalse : o (r - 1) = false := by simpa using hox
      refine ⟨k, hk, ?_⟩
      rw [← hlist]
      apply ordLab_congr
      · intro j hj
        by_cases hjp : j = r - 1
        · subst hjp; rw [e1, hfalse]; simp [oldX]
        · exact e3 j hjp
      · intro j hj hoj; rfl

/-- The port cleanup leaves a pending register without carry alone.

Consumer: `lstep_clean`. -/
theorem port_clean_pend (c : Cell) (h1 : c.i.isP = true) (h2 : c.c = .off) :
    portClean c = c := by
  rcases c with ⟨ci, ck⟩
  cases ci <;> cases ck <;> simp (config := { decide := true }) [portClean, Inp.isP] at h1 h2 ⊢

/-- The port cleanup creates no obstacle.

Consumer: `lstep_clean`. -/
theorem port_clean_obC (c : Cell) : obC (portClean c) = true → obC c = true := by
  rcases c with ⟨ci, ck⟩
  cases ci <;> cases ck <;> simp (config := { decide := true }) [portClean, obC]

/-- A packet accepted into an empty carry-free register is pending and carries nothing.

Consumer: `lstep_accept`. -/
theorem port_accept_new (t : Bool) :
    (portAccept t { i := .e, c := .off }).i.isP = true ∧
    (portAccept t { i := .e, c := .off }).c = .off := by
  cases t <;> simp (config := { decide := true }) [portAccept, Inp.isP]

/-- **The port cleanup keeps the invariant.**

Consumer: `lstep_inv`. -/
theorem lstep_clean {α : Type} (r : Nat) (hr : 2 ≤ r) (Q : List α) (c : Nat → Cell)
    (o : Nat → Bool) (ℓ : Nat → α) (h : LInv r Q c o ℓ) :
    LInv r Q (setOne c 0 (portClean (c 0)))
      (fun j => if j = 0 then o 0 && (portClean (c 0)).i.isP else o j) ℓ := by
  obtain ⟨hF, hB, k, hk, hlist⟩ := h
  have hflag : ∀ j, j < r → (if j = 0 then o 0 && (portClean (c 0)).i.isP else o j) = o j := by
    intro j hj
    by_cases hj0 : j = 0
    · subst hj0
      simp only [if_true]
      cases ho : o 0
      · rfl
      · have := flag_cell hF hB 0 (by omega) ho
        rw [port_clean_pend _ this.1 this.2]
        simp [this.1]
    · simp [hj0]
  have hcell : ∀ j, j < r → o j = true → setOne c 0 (portClean (c 0)) j = c j := by
    intro j hj hoj
    by_cases hj0 : j = 0
    · subst hj0
      have := flag_cell hF hB 0 (by omega) hoj
      simp [setOne, port_clean_pend _ this.1 this.2]
    · simp [setOne, hj0]
  refine ⟨?_, ?_, k, hk, ?_⟩
  · intro j hj hoj
    dsimp only at hoj
    rw [hflag j hj] at hoj
    rw [hcell j hj hoj]
    exact hF j hj hoj
  · intro j i hj hi hoj hobs
    dsimp only at hoj
    rw [hflag j hj] at hoj
    apply hB j i hj hi hoj
    by_cases hi0 : i = 0
    · subst hi0
      simp only [setOne, if_true] at hobs
      exact port_clean_obC _ hobs
    · simpa [setOne, hi0] using hobs
  · rw [← hlist]
    apply ordLab_congr
    · intro j hj; exact hflag j hj
    · intro j hj hoj; rfl

/-- Appending a flagged register at the bottom appends its label.

Consumer: `lstep_accept`. -/
theorem ordLab_bottom {α : Type} (o : Nat → Bool) (ℓ : Nat → α) (a : α) (h0 : o 0 = false) :
    ∀ k, ordLab (fun j => if j = 0 then true else o j) (fun j => if j = 0 then a else ℓ j) (k + 1) =
      ordLab o ℓ (k + 1) ++ [a] := by
  intro k
  induction k with
  | zero => simp [ordLab, h0]
  | succ k ih =>
    show (if (if k + 1 = 0 then true else o (k + 1)) = true then
        [if k + 1 = 0 then a else ℓ (k + 1)] else []) ++
      ordLab (fun j => if j = 0 then true else o j) (fun j => if j = 0 then a else ℓ j) (k + 1) =
      ((if o (k + 1) = true then [ℓ (k + 1)] else []) ++ ordLab o ℓ (k + 1)) ++ [a]
    rw [ih]
    simp

/-- **A packet accepted at the border keeps the invariant**: the accepted label is appended
to the queue and flagged at the bottom of the reading.

Consumer: `lstep_inv`. -/
theorem lstep_accept {α : Type} (r : Nat) (hr : 2 ≤ r) (Q : List α) (c : Nat → Cell)
    (o : Nat → Bool) (ℓ : Nat → α) (t : Bool) (a : α) (h0 : c 0 = { i := .e, c := .off })
    (h : LInv r Q c o ℓ) :
    LInv r (Q ++ [a]) (setOne c 0 (portAccept t (c 0)))
      (fun j => if j = 0 then true else o j) (fun j => if j = 0 then a else ℓ j) := by
  obtain ⟨hF, hB, k, hk, hlist⟩ := h
  have hnew := port_accept_new t
  rw [← h0] at hnew
  have ho0 : o 0 = false := by
    cases ho : o 0
    · rfl
    · have := hF 0 (by omega) ho
      rw [h0] at this
      exact absurd this (by decide)
  refine ⟨?_, ?_, k, by simp; omega, ?_⟩
  · intro j hj hoj
    by_cases hj0 : j = 0
    · subst hj0; simpa [setOne] using hnew.1
    · simp only [hj0, if_false] at hoj
      simpa [setOne, hj0] using hF j hj hoj
  · intro j i hj hi hoj hobs
    by_cases hj0 : j = 0
    · subst hj0
      by_cases hi0 : i = 0
      · subst hi0
        simp only [setOne, if_true] at hobs
        rw [obC_false_of_P _ hnew.1 hnew.2] at hobs
        exact absurd hobs (by decide)
      · omega
    · simp only [hj0, if_false] at hoj
      by_cases hi0 : i = 0
      · subst hi0
        simp only [setOne, if_true] at hobs
        rw [obC_false_of_P _ hnew.1 hnew.2] at hobs
        exact absurd hobs (by decide)
      · simp only [setOne, hi0, if_false] at hobs
        exact hB j i hj hi hoj hobs
  · obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    rw [ordLab_bottom o ℓ a ho0 m, hlist]
    exact (List.drop_append_of_le_length hk).symm

/-- The abstract successor of a labelled window: a frame, a window edge, the terminal edge,
the port cleanup, or the acceptance of the labelled packet `a`.

Consumer: `lstep_inv`. -/
inductive LStep {α : Type} (r : Nat) (c : Nat → Cell) (o : Nat → Bool) (ℓ : Nat → α)
    (Q : List α) : (Nat → Cell) → (Nat → Bool) → (Nat → α) → List α → Prop
  | frame : LStep r c o ℓ Q c o ℓ Q
  | edge (p : Nat) (hp : p + 1 < r) :
      LStep r c o ℓ Q
        (setTwo c p (pair (decide (p = 0)) false (c p) (c (p + 1))).1
          (pair (decide (p = 0)) false (c p) (c (p + 1))).2)
        (flagsEdge r c o p) (labEdge c o ℓ p) Q
  | term :
      LStep r c o ℓ Q
        (setOne c (r - 1) (pair false true (c (r - 1)) { i := .e, c := .off }).1)
        (flagsTerm r c o) ℓ Q
  | clean :
      LStep r c o ℓ Q (setOne c 0 (portClean (c 0)))
        (fun j => if j = 0 then o 0 && (portClean (c 0)).i.isP else o j) ℓ Q
  | accept (t : Bool) (a : α) (h : c 0 = { i := .e, c := .off }) :
      LStep r c o ℓ Q (setOne c 0 (portAccept t (c 0)))
        (fun j => if j = 0 then true else o j) (fun j => if j = 0 then a else ℓ j) (Q ++ [a])

/-- **The labelled window invariant is inductive.**

Consumer: `Leader/L3/Top/FinalMobileLabels.lean`. -/
theorem lstep_inv {α : Type} (r : Nat) (hr : 2 ≤ r) (Q Q' : List α) (c c' : Nat → Cell)
    (o o' : Nat → Bool) (ℓ ℓ' : Nat → α) (h : LInv r Q c o ℓ)
    (hst : LStep r c o ℓ Q c' o' ℓ' Q') : LInv r Q' c' o' ℓ' := by
  cases hst with
  | frame => exact h
  | edge p hp => exact lstep_edge r p hp Q c o ℓ h
  | term => exact lstep_term r hr Q c o ℓ h
  | clean => exact lstep_clean r hr Q c o ℓ h
  | accept t a h0 => exact lstep_accept r hr Q c o ℓ t a h0 h

end MarkedCells
end L3

#print axioms L3.MarkedCells.lstep_inv
