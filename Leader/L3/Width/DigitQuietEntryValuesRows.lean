import Leader.L3.Width.DigitQuietSafe
import Leader.L3.Width.DigitComparisonValuesRow

/-!
# Digit-change rows of `liveTopPair`

A digit changes only by the base write of a `ZERO` site, a writer launch or a writer advance; the
last two leave the written site with an empty writer input.

* `liveTop_y_change`, `liveTop_x_change`: the row of a digit change on each side;
* `phiChange`: the same through `phiD`, at a site with no `ZERO` label;
* `dirtyInvStep`: at a site with no `ZERO` label, "dirty implies no settled writer input" is carried
  by every letter.

Consumer: `L3.QuietEntryValues` (WidthDigitQuietEntryValuesStep): the digits of a target cell are
quiet after its use, and a use is clean.

Paper: research/lean-l3/ledgers/R10c-qdigit-notes.md section 9.
-/

namespace L3

open L3.DigitQuiet

set_option autoImplicit false

section Rows

variable (c : Compiled) (ox oy : Agent c) (bX bY : Bool)

/-- A change of the right digit is a writer advance.  Consumer: `phiChange`. -/
theorem liveTop_y_change (h : (liveTopPair c ox oy bX bY).y.d ≠ oy.d) :
    ∃ (cc : Bool) (v : Fin c.topA) (T : Bool), ox.l = false ∧ oy.l = false ∧ bY = false ∧
      ox.wCarry = .W cc ∧ oy.wCarry = .OFF ∧ oy.wIn = .S v T ∧ oy.topDirty = false ∧
      (liveTopPair c ox oy bX bY).y.d = c.digitMod (v.val + (if cc then 1 else 0)) := by
  cases hxl : ox.l
  · cases hyl : oy.l
    · cases hbY : bY
      · cases hw : ox.wCarry with
        | OFF =>
          exfalso
          apply h
          cases hd : oy.topDirty <;> simp [liveTopPair, hxl, hyl, hbY, hw, hd, WCarry.isW]
        | W cc =>
          cases hoff : oy.wCarry with
          | W c' =>
            exfalso
            apply h
            cases hd : oy.topDirty <;>
              simp [liveTopPair, hxl, hyl, hbY, hw, hoff, hd, WCarry.isW, WCarry.isOff, topTerminal]
          | OFF =>
            cases hs : oy.wIn with
            | S v T =>
              cases hd : oy.topDirty
              · refine ⟨cc, v, T, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
                have := liveTop_advance_d c ox oy bX false cc v T hxl hyl rfl hw hoff hs
                rw [hd] at this
                simpa using this
              · exfalso
                apply h
                have := liveTop_advance_d c ox oy bX bY cc v T hxl hyl hbY hw hoff hs
                rw [hd] at this
                simpa using this
            | E =>
              exfalso
              apply h
              cases hd : oy.topDirty <;>
                simp [liveTopPair, hxl, hyl, hbY, hw, hoff, hs, hd, WCarry.isW, WCarry.isOff,
                  InTok.isS, topTerminal]
            | X =>
              exfalso
              apply h
              cases hd : oy.topDirty <;>
                simp [liveTopPair, hxl, hyl, hbY, hw, hoff, hs, hd, WCarry.isW, WCarry.isOff,
                  InTok.isS, topTerminal]
            | P v T =>
              exfalso
              apply h
              cases hd : oy.topDirty <;>
                simp [liveTopPair, hxl, hyl, hbY, hw, hoff, hs, hd, WCarry.isW, WCarry.isOff,
                  InTok.isS, topTerminal]
      · exfalso
        apply h
        cases hd : oy.topDirty <;> cases hw : ox.wCarry <;>
          simp [liveTopPair, hxl, hyl, hbY, hd, hw, WCarry.isW, topTerminal]
    · exfalso
      apply h
      cases hd : oy.topDirty <;> simp [liveTopPair, hxl, hyl, hd]
  · exfalso
    apply h
    cases hd : oy.topDirty <;> simp [liveTopPair, hxl, hd]

/-- A change of the left digit at a site with no `ZERO` label is a writer launch.  Consumer:
`phiChange`. -/
theorem liveTop_x_change (hb : ox.wBase ≠ .ZERO) (h : (liveTopPair c ox oy bX bY).x.d ≠ ox.d) :
    ∃ (v : Fin c.topA) (T : Bool), ox.l = false ∧ oy.l = false ∧ bX = true ∧
      ox.wCarry = .OFF ∧ ox.wIn = .S v T ∧ ox.topDirty = false ∧
      (liveTopPair c ox oy bX bY).x.d = c.digitMod (v.val + 1) := by
  cases hxl : ox.l
  · cases hyl : oy.l
    · cases hbX : bX
      · exfalso
        apply h
        cases hd : ox.topDirty <;> cases hB : ox.wBase <;> first
          | exact absurd hB hb
          | simp [liveTopPair, hxl, hyl, hbX, hd, hB, topBorder]
      · cases hw : ox.wCarry with
        | W cc =>
          exfalso
          apply h
          cases hd : ox.topDirty <;> cases hB : ox.wBase <;> first
            | exact absurd hB hb
            | simp [liveTopPair, hxl, hyl, hbX, hw, hd, hB, WCarry.isW, topBorder]
        | OFF =>
          cases hs : ox.wIn with
          | S v T =>
            cases hd : ox.topDirty
            · refine ⟨v, T, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
              have := liveTop_launch_d c ox oy true bY v T hxl hyl rfl hb hw hs
              rw [hd] at this
              simpa using this
            · exfalso
              apply h
              have := liveTop_launch_d c ox oy bX bY v T hxl hyl hbX hb hw hs
              rw [hd] at this
              simpa using this
          | E =>
            exfalso
            apply h
            cases hd : ox.topDirty <;> cases hB : ox.wBase <;> first
              | exact absurd hB hb
              | simp [liveTopPair, hxl, hyl, hbX, hw, hs, hd, hB, WCarry.isW, WCarry.isOff,
                  InTok.isS, topBorder]
          | X =>
            exfalso
            apply h
            cases hd : ox.topDirty <;> cases hB : ox.wBase <;> first
              | exact absurd hB hb
              | simp [liveTopPair, hxl, hyl, hbX, hw, hs, hd, hB, WCarry.isW, WCarry.isOff,
                  InTok.isS, topBorder]
          | P v T =>
            exfalso
            apply h
            cases hd : ox.topDirty <;> cases hB : ox.wBase <;> first
              | exact absurd hB hb
              | simp [liveTopPair, hxl, hyl, hbX, hw, hs, hd, hB, WCarry.isW, WCarry.isOff,
                  InTok.isS, topBorder]
    · exfalso
      apply h
      cases hd : ox.topDirty <;> simp [liveTopPair, hxl, hyl, hd]
  · exfalso
    apply h
    cases hd : ox.topDirty <;> simp [liveTopPair, hxl, hd]

/-- The advance empties the right writer input.  Consumer: `phiChange`. -/
theorem liveTop_advance_in (cc : Bool) (v : Fin c.topA) (T : Bool)
    (hxl : ox.l = false) (hyl : oy.l = false) (hbY : bY = false)
    (hw : ox.wCarry = .W cc) (hoff : oy.wCarry = .OFF) (hs : oy.wIn = .S v T) :
    (liveTopPair c ox oy bX bY).y.wIn = .E := by
  simp [liveTopPair, hxl, hyl, hbY, hw, hoff, hs, WCarry.isW, WCarry.isOff, InTok.isS, topTerminal]

/-- The launch empties the left writer input.  Consumer: `phiChange`. -/
theorem liveTop_launch_in (v : Fin c.topA) (T : Bool)
    (hxl : ox.l = false) (hyl : oy.l = false) (hbX : bX = true)
    (hw : ox.wCarry = .OFF) (hs : ox.wIn = .S v T) :
    (liveTopPair c ox oy bX bY).x.wIn = .E := by
  cases hoc : oy.wCarry <;> cases T <;>
    simp [liveTopPair, hxl, hyl, hbX, hw, hs, hoc, WCarry.isW, WCarry.isOff, InTok.isS, InTok.isX,
      InTok.isP, topBorder] <;> split <;> rfl

end Rows

section Phi

variable {c : Compiled} {n : Nat}

/-- **A digit change on a site with no `ZERO` label** is an advance into it or a launch at it, and
the changed site is left with an empty writer input.  Consumer: `dirtyInvStep` and
`L3.QuietEntryValues.targetWriteOfBundle`. -/
theorem phiChange (ring : DirectedRing n) (S : Fin n → ProjD c) (e i : Fin n)
    (hne : ring.rightNeighbor e ≠ e) (hb : (S i).top.wBase ≠ .ZERO)
    (h : ((phiD ring S e) i).top.d ≠ (S i).top.d) :
    (i = ring.rightNeighbor e ∧ ∃ (cc : Bool) (v : Fin c.topA) (T : Bool),
      (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta = false ∧
      (S e).top.wCarry = .W cc ∧ (S i).top.wCarry = .OFF ∧ (S i).top.wIn = .S v T ∧
      (S i).top.topDirty = false ∧
      ((phiD ring S e) i).top.d = c.digitMod (v.val + (if cc then 1 else 0)) ∧
      ((phiD ring S e) i).top.wIn = .E) ∨
    (i = e ∧ ∃ (v : Fin c.topA) (T : Bool),
      (S i).word.native.l = false ∧ (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta = true ∧
      (S i).top.wCarry = .OFF ∧ (S i).top.wIn = .S v T ∧ (S i).top.topDirty = false ∧
      ((phiD ring S e) i).top.d = c.digitMod (v.val + 1) ∧ ((phiD ring S e) i).top.wIn = .E) := by
  by_cases hie : i = e
  · subst hie
    right
    rw [phiD_at_left] at h ⊢
    obtain ⟨v, T, h1, h2, h3, h4, h5, h6, h7⟩ := liveTop_x_change c (S i).lift
      (S (ring.rightNeighbor i)).lift (pairW (S i).word (S (ring.rightNeighbor i)).word).1.beta
      (pairW (S i).word (S (ring.rightNeighbor i)).word).2.beta hb h
    exact ⟨rfl, v, T, h1, h3, h4, h5, h6, h7,
      liveTop_launch_in c _ _ _ _ v T h1 h2 h3 h4 h5⟩
  · by_cases hij : i = ring.rightNeighbor e
    · subst hij
      left
      rw [phiD_at_right ring S e hne] at h ⊢
      obtain ⟨cc, v, T, h1, h2, h3, h4, h5, h6, h7, h8⟩ := liveTop_y_change c (S e).lift
        (S (ring.rightNeighbor e)).lift (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta
        (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta h
      exact ⟨rfl, cc, v, T, h3, h4, h5, h6, h7, h8, liveTop_advance_in c _ _ _ _ cc v T h1 h2 h3 h4 h5 h6⟩
    · exact absurd (by rw [phiD_at_other ring S e i hie hij]) h

/-- The dirty invariant of a site: a dirty site holds no settled writer input.  Consumer:
`dirtyInvStep`, `L3.QuietEntryValues`. -/
def DirtyInv (x : ProjD c) : Prop :=
  x.top.topDirty = true → ∀ (v : Fin c.topA) (T : Bool), x.top.wIn ≠ .S v T

/-- **The dirty invariant is carried by every letter** at a site with no `ZERO` label: a letter
touching the site either clears OLD dirty or sets dirty by a change of its digit, and a change
empties the input.  Consumer: `L3.QuietEntryValues.useClean`. -/
theorem dirtyInvStep (ring : DirectedRing n) (S : Fin n → ProjD c) (e i : Fin n)
    (hne : ring.rightNeighbor e ≠ e) (hb : (S i).top.wBase ≠ .ZERO) (hI : DirtyInv (S i)) :
    DirtyInv ((phiD ring S e) i) := by
  intro hd v T
  by_cases hoff : i ≠ e ∧ i ≠ ring.rightNeighbor e
  · rw [phiD_at_other ring S e i hoff.1 hoff.2] at hd ⊢
    exact hI hd v T
  by_cases hch : ((phiD ring S e) i).top.d = (S i).top.d
  · exfalso
    by_cases hie : i = e
    · subst hie
      rw [phiD_at_left] at hd hch
      have := liveTop_dirty_x c (S i).lift (S (ring.rightNeighbor i)).lift
        (pairW (S i).word (S (ring.rightNeighbor i)).word).1.beta
        (pairW (S i).word (S (ring.rightNeighbor i)).word).2.beta
      have h2 : (liveTopPair c (S i).lift (S (ring.rightNeighbor i)).lift
        (pairW (S i).word (S (ring.rightNeighbor i)).word).1.beta
        (pairW (S i).word (S (ring.rightNeighbor i)).word).2.beta).x.topDirty = true := hd
      have hch' : (liveTopPair c (S i).lift (S (ring.rightNeighbor i)).lift
        (pairW (S i).word (S (ring.rightNeighbor i)).word).1.beta
        (pairW (S i).word (S (ring.rightNeighbor i)).word).2.beta).x.d = (S i).lift.d := hch
      rw [h2, hch'] at this
      cases hdo : (S i).lift.topDirty <;> simp [hdo] at this
    · have hij : i = ring.rightNeighbor e := by
        refine Classical.byContradiction fun hj => hoff ⟨hie, hj⟩
      subst hij
      rw [phiD_at_right ring S e hne] at hd hch
      have := liveTop_dirty_y c (S e).lift (S (ring.rightNeighbor e)).lift
        (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta
        (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta
      have h2 : (liveTopPair c (S e).lift (S (ring.rightNeighbor e)).lift
        (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta
        (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta).y.topDirty = true := hd
      have hch' : (liveTopPair c (S e).lift (S (ring.rightNeighbor e)).lift
        (pairW (S e).word (S (ring.rightNeighbor e)).word).1.beta
        (pairW (S e).word (S (ring.rightNeighbor e)).word).2.beta).y.d =
          (S (ring.rightNeighbor e)).lift.d := hch
      rw [h2, hch'] at this
      cases hdo : (S (ring.rightNeighbor e)).lift.topDirty <;> simp [hdo] at this
  · rcases phiChange ring S e i hne hb hch with ⟨-, cc, v', T', -, -, -, -, -, -, hE⟩ | ⟨-, v', T', -, -, -, -, -, -, hE⟩ <;>
      rw [hE] <;> simp

end Phi

end L3

#print axioms L3.liveTop_y_change
#print axioms L3.liveTop_x_change
#print axioms L3.liveTop_advance_in
#print axioms L3.liveTop_launch_in
#print axioms L3.phiChange
#print axioms L3.dirtyInvStep
