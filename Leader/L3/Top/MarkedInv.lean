import Leader.L3.Top.MarkedCells

/-!
# Q7: the fresh-carry invariants of the abstract window

A fresh carry (ledger `inherited = none`) has an input-empty host, only `E`/`P`
inputs on its left, and is the only fresh carry.  Both clauses are inductive
over every window edge, with no hypothesis on the other cells.

Consumer: `Leader/L3/Top/MarkedDebtRows.lean` (invariant of reached states,
`generatedCarryGap` at rank zero).
-/

namespace L3
namespace MarkedCells

set_option autoImplicit false

/-- An empty or pending input.

Consumer: `inv_step`. -/
def EP (c : Cell) : Prop := c.i = .e ∨ c.i.isP = true

/-- A fresh carry has an empty host and only empty or pending inputs on its left.

Consumer: `inv_step`. -/
def InvA (r : Nat) (cells : Nat → Cell) : Prop :=
  ∀ j, j < r → (cells j).c = .fresh →
    (cells j).i = .e ∧ ∀ i, i < j → EP (cells i)

/-- There is at most one fresh carry.

Consumer: `inv_step`. -/
def InvU (r : Nat) (cells : Nat → Cell) : Prop :=
  ∀ j k, j < r → k < r → (cells j).c = .fresh → (cells k).c = .fresh → j = k

/-- Both fresh-carry invariants.

Consumer: `inv_step`. -/
def Inv (r : Nat) (cells : Nat → Cell) : Prop := InvA r cells ∧ InvU r cells

/-! ### Local facts of one window edge -/

theorem pair_launch (b : Bool) (x y : Cell)
    (h : (pair b false x y).1.c = .fresh) :
    b = true ∧ x.c = .off ∧ x.i.isS = true ∧ (pair b false x y).1.i = .e := by
  rcases x with ⟨xi, xc⟩
  rcases y with ⟨yi, yc⟩
  cases xi <;> cases xc <;> cases yi <;> cases yc <;> cases b <;>
    simp (config := { decide := true })
      [pair, inSlots, carries, Inp.isP, Inp.isS] at h ⊢

/-- A fresh responder carry comes from a fresh source or a fresh responder.

Consumer: `inv_step`. -/
theorem pair_moved (b : Bool) (x y : Cell)
    (h : (pair b false x y).2.c = .fresh) :
    x.c = .fresh ∨ y.c = .fresh := by
  rcases x with ⟨xi, xc⟩
  rcases y with ⟨yi, yc⟩
  cases xi <;> cases xc <;> cases yi <;> cases yc <;> cases b <;>
    simp (config := { decide := true })
      [pair, inSlots, carries, Inp.isP, Inp.isS] at h ⊢

/-- An advanced fresh carry leaves empty hosts.

Consumer: `inv_step`. -/
theorem pair_moved_host (b : Bool) (x y : Cell) (hx : x.c = .fresh)
    (hxi : x.i = .e) (h : (pair b false x y).2.c = .fresh) :
    (pair b false x y).2.i = .e ∧ (pair b false x y).1.i = .e := by
  rcases x with ⟨xi, xc⟩
  rcases y with ⟨yi, yc⟩
  simp only at hx hxi
  subst hx hxi
  cases yi <;> cases yc <;> cases b <;>
    simp (config := { decide := true })
      [pair, inSlots, carries, Inp.isP, Inp.isS] at h ⊢

/-- A fresh responder carry keeps an empty host.

Consumer: `inv_step`. -/
theorem pair_stay_host (b : Bool) (x y : Cell) (hy : y.c = .fresh)
    (h : (pair b false x y).2.c = .fresh) :
    (pair b false x y).2.i = .e := by
  rcases x with ⟨xi, xc⟩
  rcases y with ⟨yi, yc⟩
  simp only at hy
  subst hy
  cases xi <;> cases xc <;> cases yi <;> cases b <;>
    simp (config := { decide := true })
      [pair, inSlots, carries, Inp.isP, Inp.isS] at h ⊢

/-- Empty or pending registers stay empty or pending.

Consumer: `inv_step`. -/
theorem pair_ep (b : Bool) (x y : Cell) (hx : EP x) (hy : EP y) :
    EP (pair b false x y).1 ∧ EP (pair b false x y).2 := by
  rcases x with ⟨xi, xc⟩
  rcases y with ⟨yi, yc⟩
  unfold EP at hx hy ⊢
  cases xi <;> cases xc <;> cases yi <;> cases yc <;> cases b <;>
    simp (config := { decide := true })
      [pair, inSlots, carries, Inp.isP, Inp.isS] at hx hy ⊢

/-! ### Preservation -/

theorem inv_edge (r p : Nat) (hp : p + 1 < r) (cells : Nat → Cell)
    (hinv : Inv r cells) :
    Inv r (setTwo cells p (pair (decide (p = 0)) false (cells p) (cells (p + 1))).1
      (pair (decide (p = 0)) false (cells p) (cells (p + 1))).2) := by
  obtain ⟨hA, hU⟩ := hinv
  generalize hb : decide (p = 0) = b
  generalize hx : cells p = x
  generalize hy : cells (p + 1) = y
  have hAx : x.c = .fresh → x.i = .e ∧ ∀ i, i < p → EP (cells i) := by
    intro h
    have := hA p (by omega) (by rw [hx]; exact h)
    rw [hx] at this
    exact this
  have hAy : y.c = .fresh → y.i = .e ∧ ∀ i, i < p + 1 → EP (cells i) := by
    intro h
    have := hA (p + 1) hp (by rw [hy]; exact h)
    rw [hy] at this
    exact this
  -- sources of a fresh carry in the new state
  have src : ∀ q, q < r →
      (setTwo cells p (pair b false x y).1 (pair b false x y).2 q).c = .fresh →
      (q = p ∧ b = true ∧ x.c = .off ∧ x.i.isS = true ∧
          (pair b false x y).1.i = .e) ∨
      (q = p + 1 ∧ (x.c = .fresh ∨ y.c = .fresh) ∧ (pair b false x y).2.c = .fresh) ∨
      (q ≠ p ∧ q ≠ p + 1 ∧ (cells q).c = .fresh) := by
    intro q hq h
    by_cases h1 : q = p
    · subst h1
      simp only [setTwo, if_true] at h
      exact Or.inl ⟨rfl, pair_launch b x y h⟩
    · by_cases h2 : q = p + 1
      · subst h2
        simp only [setTwo, if_neg h1, if_true] at h
        exact Or.inr (Or.inl ⟨rfl, pair_moved b x y h, h⟩)
      · simp only [setTwo, if_neg h1, if_neg h2] at h
        exact Or.inr (Or.inr ⟨h1, h2, h⟩)
  have hlaunch : ∀ q, q < r → b = true → x.c = .off → x.i.isS = true →
      p = 0 → (cells q).c ≠ .fresh := by
    intro q hq hb hxc hxs hp0 hcq
    have := hA q hq hcq
    by_cases hq0 : q = 0
    · subst hq0
      rw [← hp0, hx] at hcq
      rw [hxc] at hcq
      exact absurd hcq (by decide)
    · have h0 := this.2 0 (by omega)
      rw [← hp0, hx] at h0
      unfold EP at h0
      rcases h0 with h0 | h0
      · rw [h0] at hxs; exact absurd hxs (by decide)
      · cases hxi : x.i <;> simp [hxi, Inp.isP, Inp.isS] at h0 hxs
  have hbp : b = true → p = 0 := by
    intro h; rw [← hb] at h; simpa using h
  constructor
  · intro j hj hfresh
    rcases src j hj hfresh with ⟨rfl, hb1, hxc, hxs, hai⟩ | ⟨rfl, hsrc, hf2⟩ | ⟨h1, h2, hfj⟩
    · refine ⟨?_, ?_⟩
      · simpa [setTwo] using hai
      · intro i hi
        have := hbp hb1
        omega
    · rcases hsrc with hxf | hyf
      · obtain ⟨hxe, hleft⟩ := hAx hxf
        obtain ⟨h2e, h1e⟩ := pair_moved_host b x y hxf hxe hf2
        refine ⟨by simpa [setTwo] using h2e, ?_⟩
        intro i hi
        by_cases hip : i = p
        · subst hip
          simp only [setTwo, if_true]
          exact Or.inl h1e
        · have hip' : i < p := by omega
          have := hleft i hip'
          simpa [setTwo, hip, show i ≠ p + 1 by omega] using this
      · obtain ⟨hye, hleft⟩ := hAy hyf
        have h2e := pair_stay_host b x y hyf hf2
        refine ⟨by simpa [setTwo] using h2e, ?_⟩
        intro i hi
        by_cases hip : i = p
        · subst hip
          simp only [setTwo, if_true]
          have hex := hleft i (by omega)
          rw [hx] at hex
          have hey : EP y := Or.inl hye
          exact (pair_ep b x y hex hey).1
        · have hip' : i < p := by omega
          have := hleft i (by omega)
          simpa [setTwo, hip, show i ≠ p + 1 by omega] using this
    · obtain ⟨hje, hleft⟩ := hA j hj hfj
      refine ⟨by simpa [setTwo, h1, h2] using hje, ?_⟩
      intro i hi
      by_cases hip : i = p
      · subst hip
        simp only [setTwo, if_true]
        have hex := hleft i hi
        have hey := hleft (i + 1) (by omega)
        rw [hx] at hex
        rw [hy] at hey
        exact (pair_ep b x y hex hey).1
      · by_cases hip1 : i = p + 1
        · subst hip1
          simp only [setTwo, if_neg hip, if_true]
          have hex := hleft p (by omega)
          have hey := hleft (p + 1) hi
          rw [hx] at hex
          rw [hy] at hey
          exact (pair_ep b x y hex hey).2
        · simpa [setTwo, hip, hip1] using hleft i hi
  · intro j k hj hk hfj hfk
    have hxold : x.c = .fresh → (cells p).c = .fresh := by
      intro h; rw [hx]; exact h
    have hyold : y.c = .fresh → (cells (p + 1)).c = .fresh := by
      intro h; rw [hy]; exact h
    have hpr : p < r := by omega
    have hp1r : p + 1 < r := hp
    rcases src j hj hfj with ⟨hjp, hb1, hxc, hxs, _⟩ | ⟨hjp, hsrc, _⟩ | ⟨h1, h2, hfj'⟩
    · rcases src k hk hfk with ⟨hkp, _⟩ | ⟨hkp, hsrc', _⟩ | ⟨h1', h2', hfk'⟩
      · omega
      · exfalso
        rcases hsrc' with h | h
        · rw [hxc] at h; exact absurd h (by decide)
        · exact hlaunch (p + 1) hp1r hb1 hxc hxs (hbp hb1) (hyold h)
      · exact absurd hfk' (hlaunch k hk hb1 hxc hxs (hbp hb1))
    · rcases src k hk hfk with ⟨hkp, hb1', hxc', hxs', _⟩ | ⟨hkp, hsrc', _⟩ | ⟨h1', h2', hfk'⟩
      · exfalso
        rcases hsrc with h | h
        · rw [hxc'] at h; exact absurd h (by decide)
        · exact hlaunch (p + 1) hp1r hb1' hxc' hxs' (hbp hb1') (hyold h)
      · omega
      · exfalso
        rcases hsrc with h | h
        · have := hU p k hpr hk (hxold h) hfk'
          omega
        · have := hU (p + 1) k hp1r hk (hyold h) hfk'
          omega
    · rcases src k hk hfk with ⟨hkp, hb1', hxc', hxs', _⟩ | ⟨hkp, hsrc', _⟩ | ⟨h1', h2', hfk'⟩
      · exact absurd hfj' (hlaunch j hj hb1' hxc' hxs' (hbp hb1'))
      · exfalso
        rcases hsrc' with h | h
        · have := hU j p hj hpr hfj' (hxold h)
          omega
        · have := hU j (p + 1) hj hp1r hfj' (hyold h)
          omega
      · exact hU j k hj hk hfj' hfk'

/-- The terminal edge preserves both invariants.

Consumer: `inv_step`. -/
theorem inv_term (r : Nat) (hr : 2 ≤ r) (cells : Nat → Cell) (hinv : Inv r cells) :
    Inv r (setOne cells (r - 1) (pair false true (cells (r - 1)) { i := .e, c := .off }).1) := by
  obtain ⟨hA, hU⟩ := hinv
  have hnf : ((pair false true (cells (r - 1)) { i := .e, c := .off }).1).c ≠ .fresh := by
    rcases hc : cells (r - 1) with ⟨xi, xc⟩
    cases xi <;> cases xc <;>
      simp (config := { decide := true }) [pair, inSlots, carries, Inp.isP, Inp.isS]
  constructor
  · intro j hj hf
    by_cases hjr : j = r - 1
    · subst hjr
      simp only [setOne, if_true] at hf
      exact absurd hf hnf
    · have hf' : (cells j).c = .fresh := by simpa [setOne, hjr] using hf
      obtain ⟨hje, hleft⟩ := hA j hj hf'
      refine ⟨by simpa [setOne, hjr] using hje, ?_⟩
      intro i hi
      have hir : i ≠ r - 1 := by omega
      simpa [setOne, hir] using hleft i hi
  · intro j k hj hk hfj hfk
    have hjr : j ≠ r - 1 := by
      intro h; subst h; simp only [setOne, if_true] at hfj; exact hnf hfj
    have hkr : k ≠ r - 1 := by
      intro h; subst h; simp only [setOne, if_true] at hfk; exact hnf hfk
    exact hU j k hj hk (by simpa [setOne, hjr] using hfj) (by simpa [setOne, hkr] using hfk)

/-- The port edge preserves both invariants.

Consumer: `inv_step`. -/
theorem inv_port (r : Nat) (hr : 2 ≤ r) (cells : Nat → Cell) (hinv : Inv r cells)
    (a : Cell) (ha : a.c = (cells 0).c ∨ a.c = .off)
    (hae : EP (cells 0) → EP a) (hfr : a.c = .fresh → a = cells 0) :
    Inv r (setOne cells 0 a) := by
  obtain ⟨hA, hU⟩ := hinv
  have hnf : a.c = .fresh → (cells 0).c = .fresh := by
    intro h; rw [hfr h] at h; exact h
  constructor
  · intro j hj hf
    by_cases hj0 : j = 0
    · subst hj0
      simp only [setOne, if_true] at hf
      have hc := hnf hf
      obtain ⟨hje, _⟩ := hA 0 hj hc
      refine ⟨?_, fun i hi => absurd hi (by omega)⟩
      simp only [setOne, if_true]
      rw [hfr hf]; exact hje
    · have hf' : (cells j).c = .fresh := by simpa [setOne, hj0] using hf
      obtain ⟨hje, hleft⟩ := hA j hj hf'
      refine ⟨by simpa [setOne, hj0] using hje, ?_⟩
      intro i hi
      by_cases hi0 : i = 0
      · subst hi0
        simpa [setOne] using hae (hleft 0 hi)
      · simpa [setOne, hi0] using hleft i hi
  · intro j k hj hk hfj hfk
    have hlift : ∀ q, q < r → (setOne cells 0 a q).c = .fresh → (cells q).c = .fresh := by
      intro q hq h
      by_cases hq0 : q = 0
      · subst hq0
        simp only [setOne, if_true] at h
        exact hnf h
      · simpa [setOne, hq0] using h
    exact hU j k hj hk (hlift j hj hfj) (hlift k hk hfk)

/-- Every abstract window edge preserves both invariants.

Consumer: `inv_reached`. -/
theorem inv_step (r : Nat) (hr : 2 ≤ r) (cells cells' : Nat → Cell)
    (hinv : Inv r cells) (h : Step r cells cells') : Inv r cells' := by
  cases h with
  | frame => exact hinv
  | edge p hp => exact inv_edge r p hp cells hinv
  | term => exact inv_term r hr cells hinv
  | clean =>
      apply inv_port r hr cells hinv
      · rcases hc : cells 0 with ⟨ci, cc⟩
        cases ci <;> cases cc <;> simp [portClean, hc]
      · intro hep
        rcases hc : cells 0 with ⟨ci, cc⟩
        rw [hc] at hep
        cases ci <;> cases cc <;> simp [portClean, EP, Inp.isP] at hep ⊢
      · intro hfr
        have hA0 := hinv.1 0 (by omega)
        rcases hc : cells 0 with ⟨ci, cc⟩
        cases ci <;> cases cc <;> simp [portClean, hc] at hfr ⊢
        all_goals
          have := hA0 (by rw [hc]) 
          simp [hc] at this
  | accept t =>
      apply inv_port r hr cells hinv
      · rcases hc : cells 0 with ⟨ci, cc⟩
        cases ci <;> cases cc <;> cases t <;> simp [portAccept, hc]
      · intro hep
        rcases hc : cells 0 with ⟨ci, cc⟩
        rw [hc] at hep
        cases ci <;> cases cc <;> cases t <;> simp [portAccept, EP, Inp.isP] at hep ⊢
      · intro hfr
        rcases hc : cells 0 with ⟨ci, cc⟩
        cases ci <;> cases cc <;> cases t <;> simp [portAccept, hc] at hfr ⊢

end MarkedCells
end L3

#print axioms L3.MarkedCells.inv_step
