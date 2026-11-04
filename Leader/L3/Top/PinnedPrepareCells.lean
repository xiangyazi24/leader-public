import Leader.L3.Top.FinalMobileFlags

/-!
# Q7 (preparation, lemma 1, abstract layer): flagged pending-or-settled registers

The labelled window of `TopFinalMobileFlags` flags only PENDING registers, so a pending input
that settles leaves the reading.  This module flags every register that holds a pending or a
settled input (`puNonE`) and shows that, while the window holds no erasure front and no live
carry (`puFree`), the labels of the flagged registers read right to left stay a suffix of the
queue `Q`:

* an edge moves a flagged pending input right into an empty register, or settles it in place;
  nothing is consumed (`pu_edge`);
* the terminal edge settles a flagged non-tail input in place and deletes a flagged tail, which
  is the first element of the reading (`pu_term`);
* the port cleans (the identity on a carry-free register) or appends the accepted label
  (`pu_clean`, `pu_accept`).

The only letters that leave the regime are the ones that create a front or a carry: the edge of a
settled tail away from the border (front) and the edge of a settled register at the border
(carry launch).  `pu_born_edge`, `pu_born_term` show that these letters do create an obstacle.

Consumer: `Leader/L3/Top/PinnedPrepareSettled.lean`.
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The input class holds a pending or a settled input.

Consumer: `PuInv`. -/
def puNonE (i : Inp) : Bool := i.isP || i.isS

/-- No register of the window holds an erasure front or a live carry.

Consumer: `PuInv`. -/
def puFree (r : Nat) (c : Nat → Cell) : Prop :=
  ∀ j, j < r → (c j).c = .off ∧ (c j).i ≠ .x

/-- The edge of this register creates an erasure front (a settled tail away from the border)
or launches a carry (a settled register at the border).

Consumer: `pu_edge`, `pu_born_edge`. -/
def PuBorn (p : Nat) (cell : Cell) : Prop :=
  cell.i = .st ∨ (p = 0 ∧ cell.i.isS = true)

/-- **The pending-or-settled window invariant**: no front and no live carry, the flagged
registers hold a pending or a settled input, and their labels, right to left, are the tail
`Q.drop k` of the accepted queue.

Consumer: `pu_step_inv`. -/
def PuInv {α : Type} (r : Nat) (Q : List α) (c : Nat → Cell) (o : Nat → Bool) (ℓ : Nat → α) :
    Prop :=
  puFree r c ∧ (∀ j, j < r → o j = true → puNonE (c j).i = true) ∧
    ∃ k, k ≤ Q.length ∧ ordLab o ℓ r = Q.drop k

/-- The flags after the edge of register `p`: a flagged input stays, settles in place, or moves
into the empty responder.

Consumer: `PuStep`. -/
def puFlagsEdge (c : Nat → Cell) (o : Nat → Bool) (p : Nat) : Nat → Bool :=
  fun j =>
    if j = p then o p && puNonE (pair (decide (p = 0)) false (c p) (c (p + 1))).1.i
    else if j = p + 1 then
      (o (p + 1) && puNonE (pair (decide (p = 0)) false (c p) (c (p + 1))).2.i) ||
        (o p && !puNonE (c (p + 1)).i &&
          puNonE (pair (decide (p = 0)) false (c p) (c (p + 1))).2.i)
    else o j

/-- The labels after the edge of register `p`: the moved input carries its label.

Consumer: `PuStep`. -/
def puLabEdge {α : Type} (c : Nat → Cell) (ℓ : Nat → α) (p : Nat) : Nat → α :=
  fun j => if j = p + 1 then (if puNonE (c (p + 1)).i = true then ℓ (p + 1) else ℓ p) else ℓ j

/-- The flags after the terminal edge.

Consumer: `PuStep`. -/
def puFlagsTerm (r : Nat) (c : Nat → Cell) (o : Nat → Bool) : Nat → Bool :=
  fun j =>
    if j = r - 1 then
      o (r - 1) && puNonE (pair false true (c (r - 1)) { i := .e, c := .off }).1.i
    else o j

/-- The abstract successor of a pending-or-settled labelled window.

Consumer: `pu_step_inv`. -/
inductive PuStep {α : Type} (r : Nat) (c : Nat → Cell) (o : Nat → Bool) (ℓ : Nat → α)
    (Q : List α) : (Nat → Cell) → (Nat → Bool) → (Nat → α) → List α → Prop
  | frame : PuStep r c o ℓ Q c o ℓ Q
  | edge (p : Nat) (hp : p + 1 < r) :
      PuStep r c o ℓ Q
        (setTwo c p (pair (decide (p = 0)) false (c p) (c (p + 1))).1
          (pair (decide (p = 0)) false (c p) (c (p + 1))).2)
        (puFlagsEdge c o p) (puLabEdge c ℓ p) Q
  | term :
      PuStep r c o ℓ Q
        (setOne c (r - 1) (pair false true (c (r - 1)) { i := .e, c := .off }).1)
        (puFlagsTerm r c o) ℓ Q
  | clean :
      PuStep r c o ℓ Q (setOne c 0 (portClean (c 0)))
        (fun j => if j = 0 then o 0 && puNonE (portClean (c 0)).i else o j) ℓ Q
  | accept (t : Bool) (a : α) (h : c 0 = { i := .e, c := .off }) :
      PuStep r c o ℓ Q (setOne c 0 (portAccept t (c 0)))
        (fun j => if j = 0 then true else o j) (fun j => if j = 0 then a else ℓ j) (Q ++ [a])

/-- **Local facts of one window edge** on a front-free, carry-free pair that does not create an
obstacle: the outputs are front-free and carry-free, and either the flags stay, or the flagged
source moves into an empty responder.

Consumer: `pu_edge`. -/
theorem pu_pair (b : Bool) (x y : Cell) (a q : Bool)
    (hx : x.c = .off ∧ x.i ≠ .x) (hy : y.c = .off ∧ y.i ≠ .x)
    (hnb : ¬ (x.i = .st ∨ (b = true ∧ x.i.isS = true)))
    (ha : a = true → puNonE x.i = true) (hq : q = true → puNonE y.i = true) :
    ((pair b false x y).1.c = .off ∧ (pair b false x y).1.i ≠ .x) ∧
    ((pair b false x y).2.c = .off ∧ (pair b false x y).2.i ≠ .x) ∧
    (((a && puNonE (pair b false x y).1.i) = a ∧
        (((q && puNonE (pair b false x y).2.i) ||
          (a && !puNonE y.i && puNonE (pair b false x y).2.i)) = q)) ∨
      (a = true ∧ (a && puNonE (pair b false x y).1.i) = false ∧ q = false ∧
        ((q && puNonE (pair b false x y).2.i) ||
          (a && !puNonE y.i && puNonE (pair b false x y).2.i)) = true ∧
        puNonE y.i = false)) := by
  rcases x with ⟨xi, xk⟩
  rcases y with ⟨yi, yk⟩
  obtain ⟨hxk, hxx⟩ := hx
  obtain ⟨hyk, hyx⟩ := hy
  simp only at hxk hxx hyk hyx hnb ha hq
  subst hxk hyk
  cases xi <;> cases yi <;> cases b <;> cases a <;> cases q <;>
    simp (config := { decide := true })
      [pair, inSlots, carries, puNonE, Inp.isP, Inp.isS] at hxx hyx hnb ha hq ⊢

/-- The terminal edge on a front-free, carry-free source that is not a settled tail: the output
is front-free and carry-free, and the flag stays or a flagged source is deleted.

Consumer: `pu_term`. -/
theorem pu_pair_term (x : Cell) (a : Bool) (hx : x.c = .off ∧ x.i ≠ .x) (hnb : x.i ≠ .st)
    (ha : a = true → puNonE x.i = true) :
    ((pair false true x { i := .e, c := .off }).1.c = .off ∧
      (pair false true x { i := .e, c := .off }).1.i ≠ .x) ∧
    ((a && puNonE (pair false true x { i := .e, c := .off }).1.i) = a ∨
      (a = true ∧ (a && puNonE (pair false true x { i := .e, c := .off }).1.i) = false)) := by
  rcases x with ⟨xi, xk⟩
  obtain ⟨hxk, hxx⟩ := hx
  simp only at hxk hxx hnb ha
  subst hxk
  cases xi <;> cases a <;>
    simp (config := { decide := true })
      [pair, inSlots, carries, puNonE, Inp.isP, Inp.isS] at hxx hnb ha ⊢

/-- A settled tail away from the border, or a settled register at the border, creates an
obstacle on its edge.

Consumer: `pu_born_edge`. -/
theorem pu_pair_born (b : Bool) (x y : Cell) (hx : x.c = .off ∧ x.i ≠ .x)
    (hb : x.i = .st ∨ (b = true ∧ x.i.isS = true)) :
    (pair b false x y).1.c ≠ .off ∨ (pair b false x y).1.i = .x := by
  rcases x with ⟨xi, xk⟩
  rcases y with ⟨yi, yk⟩
  obtain ⟨hxk, hxx⟩ := hx
  simp only at hxk hxx hb
  subst hxk
  cases xi <;> cases yi <;> cases yk <;> cases b <;>
    simp (config := { decide := true })
      [pair, inSlots, carries, Inp.isP, Inp.isS] at hxx hb ⊢

/-- The terminal edge on a settled tail creates a front.

Consumer: `pu_born_term`. -/
theorem pu_pair_born_term (x : Cell) (hx : x.c = .off) (hb : x.i = .st) :
    (pair false true x { i := .e, c := .off }).1.i = .x := by
  rcases x with ⟨xi, xk⟩
  simp only at hx hb
  subst hx hb
  simp (config := { decide := true }) [pair, inSlots, carries, Inp.isP, Inp.isS]

/-- A window edge that creates no obstacle keeps the invariant: nothing is consumed.

Consumer: `pu_step_inv`. -/
theorem pu_edge {α : Type} (r p : Nat) (hp : p + 1 < r) (Q : List α) (c : Nat → Cell)
    (o : Nat → Bool) (ℓ : Nat → α) (h : PuInv r Q c o ℓ) (hnb : ¬ PuBorn p (c p)) :
    PuInv r Q
      (setTwo c p (pair (decide (p = 0)) false (c p) (c (p + 1))).1
        (pair (decide (p = 0)) false (c p) (c (p + 1))).2)
      (puFlagsEdge c o p) (puLabEdge c ℓ p) := by
  obtain ⟨hfree, hI, k, hk, hlist⟩ := h
  have hnb' : ¬ ((c p).i = .st ∨ (decide (p = 0) = true ∧ (c p).i.isS = true)) := by
    intro h'
    apply hnb
    unfold PuBorn
    rcases h' with h' | ⟨h1, h2⟩
    · exact Or.inl h'
    · exact Or.inr ⟨by simpa using h1, h2⟩
  have hpl := pu_pair (decide (p = 0)) (c p) (c (p + 1)) (o p) (o (p + 1))
    (hfree p (by omega)) (hfree (p + 1) hp) hnb'
    (fun ho => hI p (by omega) ho) (fun ho => hI (p + 1) hp ho)
  generalize hP : pair (decide (p = 0)) false (c p) (c (p + 1)) = P at hpl
  obtain ⟨f1, f2, f3⟩ := hpl
  have s1 : setTwo c p P.1 P.2 p = P.1 := by simp [setTwo]
  have s2 : setTwo c p P.1 P.2 (p + 1) = P.2 := by simp [setTwo]
  have s3 : ∀ j, j ≠ p → j ≠ p + 1 → setTwo c p P.1 P.2 j = c j := by
    intro j h1 h2; simp [setTwo, h1, h2]
  have e1 : puFlagsEdge c o p p = (o p && puNonE P.1.i) := by simp [puFlagsEdge, hP]
  have e2 : puFlagsEdge c o p (p + 1) =
      ((o (p + 1) && puNonE P.2.i) || (o p && !puNonE (c (p + 1)).i && puNonE P.2.i)) := by
    simp [puFlagsEdge, hP]
  have e3 : ∀ j, j ≠ p → j ≠ p + 1 → puFlagsEdge c o p j = o j := by
    intro j h1 h2; simp [puFlagsEdge, h1, h2]
  have l2 : puLabEdge c ℓ p (p + 1) =
      (if puNonE (c (p + 1)).i = true then ℓ (p + 1) else ℓ p) := by simp [puLabEdge]
  have l1 : puLabEdge c ℓ p p = ℓ p := by simp [puLabEdge]
  have l3 : ∀ j, j ≠ p + 1 → puLabEdge c ℓ p j = ℓ j := by
    intro j h1; simp [puLabEdge, h1]
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    by_cases hjp : j = p
    · subst hjp; rw [s1]; exact f1
    · by_cases hjq : j = p + 1
      · subst hjq; rw [s2]; exact f2
      · rw [s3 j hjp hjq]; exact hfree j hj
  · intro j hj hoj
    by_cases hjp : j = p
    · subst hjp
      rw [s1]
      rw [e1] at hoj
      simp only [Bool.and_eq_true] at hoj
      exact hoj.2
    · by_cases hjq : j = p + 1
      · subst hjq
        rw [s2]
        rw [e2] at hoj
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hoj
        rcases hoj with h' | h'
        · exact h'.2
        · exact h'.2
      · rw [s3 j hjp hjq]; rw [e3 j hjp hjq] at hoj; exact hI j hj hoj
  · have hcongr_below : ordLab (puFlagsEdge c o p) (puLabEdge c ℓ p) p = ordLab o ℓ p :=
      ordLab_congr _ _ _ _ p (fun j hj => e3 j (by omega) (by omega))
        (fun j hj _ => l3 j (by omega))
    have hA : ordLab o ℓ (p + 2) = (if o (p + 1) = true then [ℓ (p + 1)] else []) ++
        ((if o p = true then [ℓ p] else []) ++ ordLab o ℓ p) := rfl
    have hA' : ordLab (puFlagsEdge c o p) (puLabEdge c ℓ p) (p + 2) =
        (if puFlagsEdge c o p (p + 1) = true then [puLabEdge c ℓ p (p + 1)] else []) ++
        ((if puFlagsEdge c o p p = true then [puLabEdge c ℓ p p] else []) ++
          ordLab (puFlagsEdge c o p) (puLabEdge c ℓ p) p) := rfl
    rw [hcongr_below, l1] at hA'
    have habove : ∀ j, p + 2 ≤ j → j < r → puFlagsEdge c o p j = o j := fun j h1 _ =>
      e3 j (by omega) (by omega)
    have habove' : ∀ j, p + 2 ≤ j → j < r → o j = true →
        puLabEdge c ℓ p j = ℓ j := fun j h1 _ _ => l3 j (by omega)
    refine ⟨k, hk, ?_⟩
    rw [← hlist]
    apply ordLab_ext o _ ℓ _ (p + 2) _ r (by omega) habove habove'
    rw [hA, hA', e1, e2, l2]
    rcases f3 with ⟨g1, g2⟩ | ⟨g0, g1, g2, g3, g4⟩
    · rw [g1, g2]
      cases hq : o (p + 1)
      · simp
      · have := hI (p + 1) hp hq
        simp [this]
    · rw [g3, g1, g4, g2]
      simp [g0]

/-- The terminal edge on a source that is not a settled tail keeps the invariant: a flagged
settled or non-tail input stays, a flagged tail is deleted and leaves the reading.

Consumer: `pu_step_inv`. -/
theorem pu_term {α : Type} (r : Nat) (hr : 2 ≤ r) (Q : List α) (c : Nat → Cell)
    (o : Nat → Bool) (ℓ : Nat → α) (h : PuInv r Q c o ℓ) (hnb : (c (r - 1)).i ≠ .st) :
    PuInv r Q
      (setOne c (r - 1) (pair false true (c (r - 1)) { i := .e, c := .off }).1)
      (puFlagsTerm r c o) ℓ := by
  obtain ⟨hfree, hI, k, hk, hlist⟩ := h
  have hpl := pu_pair_term (c (r - 1)) (o (r - 1)) (hfree (r - 1) (by omega)) hnb
    (fun ho => hI (r - 1) (by omega) ho)
  generalize hP : (pair false true (c (r - 1)) { i := .e, c := .off }).1 = P at hpl
  obtain ⟨f1, f2⟩ := hpl
  have s1 : setOne c (r - 1) P (r - 1) = P := by simp [setOne]
  have s3 : ∀ j, j ≠ r - 1 → setOne c (r - 1) P j = c j := by
    intro j h1; simp [setOne, h1]
  have e1 : puFlagsTerm r c o (r - 1) = (o (r - 1) && puNonE P.i) := by simp [puFlagsTerm, hP]
  have e3 : ∀ j, j ≠ r - 1 → puFlagsTerm r c o j = o j := by
    intro j h1; simp [puFlagsTerm, h1]
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    by_cases hjp : j = r - 1
    · subst hjp; rw [s1]; exact f1
    · rw [s3 j hjp]; exact hfree j hj
  · intro j hj hoj
    by_cases hjp : j = r - 1
    · subst hjp
      rw [s1]
      rw [e1] at hoj
      simp only [Bool.and_eq_true] at hoj
      exact hoj.2
    · rw [s3 j hjp]; rw [e3 j hjp] at hoj; exact hI j hj hoj
  · rcases f2 with g1 | ⟨g0, g1⟩
    · refine ⟨k, hk, ?_⟩
      rw [← hlist]
      apply ordLab_congr
      · intro j hj
        by_cases hjp : j = r - 1
        · subst hjp; rw [e1, g1]
        · exact e3 j hjp
      · intro j hj hoj; rfl
    · obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
      have h1 : ordLab (puFlagsTerm (m + 1) c o) ℓ (m + 1) = ordLab o ℓ m := by
        simp only [ordLab]
        have : puFlagsTerm (m + 1) c o m = false := by
          have h1' := e1
          have g1' : (o m && puNonE P.i) = false := by simpa using g1
          simp only [Nat.add_sub_cancel] at h1'
          rw [h1', g1']
        rw [this]
        simp only [Bool.false_eq_true, if_false, List.nil_append]
        apply ordLab_congr
        · intro j hj; exact e3 j (by omega)
        · intro j hj hoj; rfl
      have h2 : ordLab o ℓ (m + 1) = ℓ m :: ordLab o ℓ m := by
        simp only [ordLab]
        have : o m = true := by simpa using g0
        rw [if_pos this]; rfl
      have hne : Q.drop k ≠ [] := by rw [← hlist, h2]; simp
      have hlen : k < Q.length := by
        by_cases h : Q.length ≤ k
        · exact absurd (List.drop_eq_nil_of_le h) hne
        · omega
      refine ⟨k + 1, by omega, ?_⟩
      rw [h1, ← List.tail_drop, ← hlist, h2]
      simp

/-- The port cleanup of a front-free, carry-free register is the identity.

Consumer: `pu_clean`. -/
theorem pu_port_clean (c : Cell) (h : c.c = .off) : portClean c = c := by
  unfold portClean
  rw [if_pos h]

/-- The port cleanup keeps the invariant.

Consumer: `pu_step_inv`. -/
theorem pu_clean {α : Type} (r : Nat) (hr : 2 ≤ r) (Q : List α) (c : Nat → Cell)
    (o : Nat → Bool) (ℓ : Nat → α) (h : PuInv r Q c o ℓ) :
    PuInv r Q (setOne c 0 (portClean (c 0)))
      (fun j => if j = 0 then o 0 && puNonE (portClean (c 0)).i else o j) ℓ := by
  obtain ⟨hfree, hI, k, hk, hlist⟩ := h
  have hc : portClean (c 0) = c 0 := pu_port_clean _ (hfree 0 (by omega)).1
  have hset : setOne c 0 (portClean (c 0)) = c := by
    funext j
    by_cases hj : j = 0
    · subst hj; simp [setOne, hc]
    · simp [setOne, hj]
  have hflag : ∀ j, (if j = 0 then o 0 && puNonE (portClean (c 0)).i else o j) = o j := by
    intro j
    by_cases hj : j = 0
    · subst hj
      simp only [if_true]
      cases ho : o 0
      · rfl
      · have := hI 0 (by omega) ho
        rw [hc]
        simp [this]
    · simp [hj]
  rw [hset]
  refine ⟨hfree, ?_, k, hk, ?_⟩
  · intro j hj hoj
    dsimp only at hoj
    rw [hflag j] at hoj
    exact hI j hj hoj
  · rw [← hlist]
    apply ordLab_congr
    · intro j hj; exact hflag j
    · intro j hj hoj; rfl

/-- A packet accepted into an empty register is appended to the reading.

Consumer: `pu_step_inv`. -/
theorem pu_accept {α : Type} (r : Nat) (hr : 2 ≤ r) (Q : List α) (c : Nat → Cell)
    (o : Nat → Bool) (ℓ : Nat → α) (t : Bool) (a : α) (h0 : c 0 = { i := .e, c := .off })
    (h : PuInv r Q c o ℓ) :
    PuInv r (Q ++ [a]) (setOne c 0 (portAccept t (c 0)))
      (fun j => if j = 0 then true else o j) (fun j => if j = 0 then a else ℓ j) := by
  obtain ⟨hfree, hI, k, hk, hlist⟩ := h
  have hnew := port_accept_new t
  rw [← h0] at hnew
  have ho0 : o 0 = false := by
    cases ho : o 0
    · rfl
    · have := hI 0 (by omega) ho
      rw [h0] at this
      exact absurd this (by decide)
  refine ⟨?_, ?_, k, by simp; omega, ?_⟩
  · intro j hj
    by_cases hj0 : j = 0
    · subst hj0
      simp only [setOne, if_true]
      refine ⟨hnew.2, ?_⟩
      have := hnew.1
      intro hx
      rw [hx] at this
      exact absurd this (by decide)
    · simpa [setOne, hj0] using hfree j hj
  · intro j hj hoj
    by_cases hj0 : j = 0
    · subst hj0
      simp only [setOne, if_true]
      have := hnew.1
      simp [puNonE, this]
    · simp only [hj0, if_false] at hoj
      simpa [setOne, hj0] using hI j hj hoj
  · obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    rw [ordLab_bottom o ℓ a ho0 m, hlist]
    exact (List.drop_append_of_le_length hk).symm

/-- A born obstacle on a window edge leaves the obstacle-free regime.

Consumer: `pu_step_inv`. -/
theorem pu_born_edge (r p : Nat) (hp : p + 1 < r) (c : Nat → Cell) (hfree : puFree r c)
    (hb : PuBorn p (c p)) :
    ¬ puFree r (setTwo c p (pair (decide (p = 0)) false (c p) (c (p + 1))).1
      (pair (decide (p = 0)) false (c p) (c (p + 1))).2) := by
  intro hf
  have h1 := hf p (by omega)
  simp only [setTwo, if_true] at h1
  have hb' : (c p).i = .st ∨ (decide (p = 0) = true ∧ (c p).i.isS = true) := by
    rcases hb with hb | ⟨hb1, hb2⟩
    · exact Or.inl hb
    · exact Or.inr ⟨by simpa using hb1, hb2⟩
  rcases pu_pair_born (decide (p = 0)) (c p) (c (p + 1)) (hfree p (by omega)) hb' with h2 | h2
  · exact h2 h1.1
  · exact h1.2 h2

/-- A settled tail on the terminal edge leaves the obstacle-free regime.

Consumer: `pu_step_inv`. -/
theorem pu_born_term (r : Nat) (hr : 2 ≤ r) (c : Nat → Cell) (hfree : puFree r c)
    (hb : (c (r - 1)).i = .st) :
    ¬ puFree r (setOne c (r - 1) (pair false true (c (r - 1)) { i := .e, c := .off }).1) := by
  intro hf
  have h1 := hf (r - 1) (by omega)
  simp only [setOne, if_true] at h1
  exact h1.2 (pu_pair_born_term _ (hfree (r - 1) (by omega)).1 hb)

/-- **A step that leaves an obstacle-free window into an obstacle-free window keeps the
invariant**: every letter of the abstract window either keeps `PuInv` or creates a front or a
live carry.

Consumer: `Leader/L3/Top/PinnedPrepareSettled.lean`. -/
theorem pu_step_inv {α : Type} (r : Nat) (hr : 2 ≤ r) (Q Q' : List α) (c c' : Nat → Cell)
    (o o' : Nat → Bool) (ℓ ℓ' : Nat → α) (h : PuInv r Q c o ℓ)
    (hst : PuStep r c o ℓ Q c' o' ℓ' Q') (hfree : puFree r c') : PuInv r Q' c' o' ℓ' := by
  cases hst with
  | frame => exact h
  | edge p hp =>
    by_cases hb : PuBorn p (c p)
    · exact absurd hfree (pu_born_edge r p hp c h.1 hb)
    · exact pu_edge r p hp Q c o ℓ h hb
  | term =>
    by_cases hb : (c (r - 1)).i = .st
    · exact absurd hfree (pu_born_term r hr c h.1 hb)
    · exact pu_term r hr Q c o ℓ h hb
  | clean => exact pu_clean r hr Q c o ℓ h
  | accept t a h0 => exact pu_accept r hr Q c o ℓ t a h0 h

end MarkedCells
end L3

#print axioms L3.MarkedCells.pu_step_inv
