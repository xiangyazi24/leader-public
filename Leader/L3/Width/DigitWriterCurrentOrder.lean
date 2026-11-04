import Leader.L3.Width.DigitWriterCurrentShape

/-!
# Writer currentness: inherited carries lie to the right of new ones in the target window

The carries of the target window `[R, 2R)` of one lane, read as `Nat → Option (DigitCarryGhost)`.
`WinShape R k cw cw'` says how one edge `(k, k + 1)` changes them: the other cells are untouched,
the entry edge `(R - 1, R)` drops or keeps the carry of `R`, an inner edge drops or keeps both
carries, moves the left carry onto an empty right cell, or (at `k = R`) launches a new carry
without inheritance, and the exit edge drops or keeps the carry of `2R - 1`.

* `OrdWin R cw`: an inherited carry has no non-inherited carry to its right (new carries are born
  at the left end and nothing overtakes);
* `NoInhWin R cw`: no carry of the window is inherited;
* `ordWin_step`, `noInhWin_step`: both are carried by every edge;
* `noInhWin_exit`: if the edge `(2R - 1, 2R)` is taken while the carry of `2R - 1` is not
  inherited, then no carry of the window is inherited afterwards.

Consumer: `WidthDigitWriterCurrentOrderStep` (the audit fold).
-/

namespace L3

set_option autoImplicit false

section Pure

variable {c : Compiled} {n : Nat}

/-- Consumer: `ordWin_step`, `noInhWin_exit`. -/
def OrdWin (R : Nat) (cw : Nat → Option (DigitCarryGhost c n)) : Prop :=
  ∀ (q q' : Nat) (L L' : DigitCarryGhost c n), R ≤ q → q < q' → q' < 2 * R →
    cw q = some L → cw q' = some L' → L'.inherited = none → L.inherited = none

/-- Consumer: `noInhWin_step`, `noInhWin_exit`. -/
def NoInhWin (R : Nat) (cw : Nat → Option (DigitCarryGhost c n)) : Prop :=
  ∀ (q : Nat) (L : DigitCarryGhost c n), R ≤ q → q < 2 * R → cw q = some L →
    L.inherited = none

/-- **How one edge `(k, k + 1)` changes the carries of the window.**

Consumer: `ordWin_step`, `noInhWin_step`, `noInhWin_exit`. -/
def WinShape (R k : Nat) (cw cw' : Nat → Option (DigitCarryGhost c n)) : Prop :=
  (∀ q, R ≤ q → q < 2 * R → q ≠ k → q ≠ k + 1 → cw' q = cw q) ∧
  (k + 1 = R → cw' R = none ∨ cw' R = cw R) ∧
  (R ≤ k → k + 1 < 2 * R →
    (((cw' k = none ∨ cw' k = cw k) ∧ (cw' (k + 1) = none ∨ cw' (k + 1) = cw (k + 1))) ∨
      (cw' k = none ∧ cw (k + 1) = none ∧ ∃ (L : DigitCarryGhost c n) (u : DigitUse c n),
        cw k = some L ∧ cw' (k + 1) = some { inherited := L.inherited, uses := L.uses ++ [u] }) ∨
      (k = R ∧ cw k = none ∧ (∃ u : DigitUse c n, cw' k = some { inherited := none, uses := [u] }) ∧
        cw' (k + 1) = cw (k + 1)))) ∧
  (k + 1 = 2 * R → cw' k = none ∨ cw' k = cw k)

/-- **Where a carry of the window comes from.**  A new carry is a launch at the left end, an old
carry that stayed, or an old carry that moved one cell right onto an emptied-behind cell.

Consumer: `ordWin_step`, `noInhWin_step`, `noInhWin_exit`. -/
theorem winOrigin {R k : Nat} {cw cw' : Nat → Option (DigitCarryGhost c n)}
    (_hR : 2 ≤ R) (hs : WinShape R k cw cw') (p : Nat) (hp1 : R ≤ p) (hp2 : p < 2 * R)
    (M : DigitCarryGhost c n) (hM : cw' p = some M) :
    (k = R ∧ p = R ∧ M.inherited = none) ∨
    (cw p = some M ∨ ∃ M0 : DigitCarryGhost c n, cw p = some M0 ∧ M0.inherited = M.inherited) ∨
    (p = k + 1 ∧ R ≤ k ∧ cw' k = none ∧ ∃ M0 : DigitCarryGhost c n, cw k = some M0 ∧
      M0.inherited = M.inherited) := by
  obtain ⟨h0, hent, hin, hex⟩ := hs
  by_cases hk : p = k
  · subst hk
    by_cases hexit : p + 1 = 2 * R
    · rcases hex hexit with h | h
      · rw [h] at hM; cases hM
      · rw [h] at hM
        exact Or.inr (Or.inl (Or.inl hM))
    · rcases hin hp1 (by omega) with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨hkR, -, ⟨u, hu⟩, -⟩
      · rcases h1 with h | h
        · rw [h] at hM; cases hM
        · rw [h] at hM
          exact Or.inr (Or.inl (Or.inl hM))
      · rw [h1] at hM; cases hM
      · rw [hu] at hM
        cases hM
        exact Or.inl ⟨hkR, hkR, rfl⟩
  · by_cases hk1 : p = k + 1
    · subst hk1
      by_cases hent' : k + 1 = R
      · rcases hent hent' with h | h
        · rw [hent'] at hM; rw [h] at hM; cases hM
        · rw [hent'] at hM; rw [h] at hM
          rw [hent']
          exact Or.inr (Or.inl (Or.inl hM))
      · have hkR : R ≤ k := by omega
        rcases hin hkR (by omega) with ⟨-, h2⟩ | ⟨h1, -, L, u, hL, h2⟩ | ⟨-, -, -, h2⟩
        · rcases h2 with h | h
          · rw [h] at hM; cases hM
          · rw [h] at hM
            exact Or.inr (Or.inl (Or.inl hM))
        · rw [h2] at hM
          cases hM
          exact Or.inr (Or.inr ⟨rfl, hkR, h1, L, hL, rfl⟩)
        · rw [h2] at hM
          exact Or.inr (Or.inl (Or.inl hM))
    · rw [h0 p hp1 hp2 hk hk1] at hM
      exact Or.inr (Or.inl (Or.inl hM))

/-- **One edge preserves the order.**  Consumer: `orderRun`. -/
theorem ordWin_step {R k : Nat} {cw cw' : Nat → Option (DigitCarryGhost c n)}
    (hR : 2 ≤ R) (hs : WinShape R k cw cw') (ho : OrdWin R cw) : OrdWin R cw' := by
  intro q q' L L' h1 h2 h3 hq hq' hinh
  have hq2 : q < 2 * R := by omega
  rcases winOrigin hR hs q' (by omega) h3 L' hq' with ⟨-, hq'R, -⟩ | hst' | ⟨hq'k, hRk, hk0, M0', hM0', hi'⟩
  · omega
  · -- the right carry stayed
    obtain ⟨M0', hM0', hi'⟩ : ∃ M0' : DigitCarryGhost c n, cw q' = some M0' ∧
        M0'.inherited = L'.inherited := by
      rcases hst' with h | ⟨M0', h, hi⟩
      · exact ⟨L', h, rfl⟩
      · exact ⟨M0', h, hi⟩
    rcases winOrigin hR hs q h1 hq2 L hq with ⟨-, -, hi⟩ | hst | ⟨hqk, hRk', hk0, M0, hM0, hi⟩
    · exact hi
    · obtain ⟨M0, hM0, hi⟩ : ∃ M0 : DigitCarryGhost c n, cw q = some M0 ∧
          M0.inherited = L.inherited := by
        rcases hst with h | ⟨M0, h, hi⟩
        · exact ⟨L, h, rfl⟩
        · exact ⟨M0, h, hi⟩
      rw [← hi]
      exact ho q q' M0 M0' h1 h2 h3 hM0 hM0' (by rw [hi']; exact hinh)
    · -- the left carry moved from `q - 1`, the right one stayed at `q' > q = k + 1`
      rw [← hi]
      exact ho k q' M0 M0' hRk' (by omega) h3 hM0 hM0' (by rw [hi']; exact hinh)
  · -- the right carry moved from `k = q' - 1`
    rcases winOrigin hR hs q h1 hq2 L hq with ⟨-, -, hi⟩ | hst | ⟨hqk, hRk', hk0', M1, hM1, hi⟩
    · exact hi
    · obtain ⟨M0, hM0, hi⟩ : ∃ M0 : DigitCarryGhost c n, cw q = some M0 ∧
          M0.inherited = L.inherited := by
        rcases hst with h | ⟨M0, h, hi⟩
        · exact ⟨L, h, rfl⟩
        · exact ⟨M0, h, hi⟩
      have hqk : q ≠ k := by
        intro h
        rw [h, hk0] at hq
        cases hq
      rw [← hi]
      exact ho q k M0 M0' h1 (by omega) (by omega) hM0 hM0' (by rw [hi']; exact hinh)
    · omega

/-- **One edge keeps the window free of inherited carries.**  Consumer: `orderRun`. -/
theorem noInhWin_step {R k : Nat} {cw cw' : Nat → Option (DigitCarryGhost c n)}
    (hR : 2 ≤ R) (hs : WinShape R k cw cw') (hn : NoInhWin R cw) : NoInhWin R cw' := by
  intro p M hp1 hp2 hM
  rcases winOrigin hR hs p hp1 hp2 M hM with ⟨-, -, hi⟩ | h | ⟨hpk, hRk, -, M0, hM0, hi⟩
  · exact hi
  · rcases h with h | ⟨M0, h, hi⟩
    · exact hn p M hp1 hp2 h
    · rw [← hi]; exact hn p M0 hp1 hp2 h
  · rw [← hi]; exact hn k M0 hRk (by omega) hM0

/-- **The exit edge with a non-inherited carry on `2R - 1` clears the window of inherited
carries.**  Consumer: `orderRun`. -/
theorem noInhWin_exit {R k : Nat} {cw cw' : Nat → Option (DigitCarryGhost c n)}
    (hR : 2 ≤ R) (hs : WinShape R k cw cw') (hk : k + 1 = 2 * R) (ho : OrdWin R cw)
    (L : DigitCarryGhost c n) (hL : cw k = some L) (hLi : L.inherited = none) :
    NoInhWin R cw' := by
  intro p M hp1 hp2 hM
  rcases winOrigin hR hs p hp1 hp2 M hM with ⟨-, -, hi⟩ | h | ⟨hpk, -⟩
  · exact hi
  · obtain ⟨M0, h0, hi⟩ : ∃ M0 : DigitCarryGhost c n, cw p = some M0 ∧
        M0.inherited = M.inherited := by
      rcases h with h | ⟨M0, h, hi⟩
      · exact ⟨M, h, rfl⟩
      · exact ⟨M0, h, hi⟩
    rw [← hi]
    by_cases hpk : p = k
    · subst hpk
      rw [hL] at h0
      cases h0
      exact hLi
    · exact ho p k M0 L hp1 (by omega) (by omega) h0 hL hLi
  · omega

end Pure

end L3

#print axioms L3.ordWin_step
#print axioms L3.noInhWin_step
#print axioms L3.noInhWin_exit
