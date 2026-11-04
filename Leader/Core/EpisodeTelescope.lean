-- core only: no Std.Tactic import needed


set_option autoImplicit false


/-!
# Episode-level amortized telescope


This file contains only natural-number accounting.


Interface to the real stopping-tree layer:


* `next x y` means that one completed successful elimination episode can
  renew from state `x` at state `y`.
* `episodeBound x y` is a natural-number upper bound already supplied by the
  episode-level Bellman argument.  It may be constant in `y`.
* `w x` is the remaining unpaid mass.
* `phase x` is a rank that strictly decreases at every successful episode.


Internal scheduler steps and retries are deliberately absent here.  They are
part of the per-episode bound that is fed into this accounting lemma.
-/


namespace EpisodeTelescope


/-- Global amortized credit.  In the intended application `scale = C * n`. -/
def amortizedPotential {S : Type} (scale : Nat)
    (w phase : S → Nat) (x : S) : Nat :=
  scale * (w x + phase x)


/-- One successful episode consumes some `w` credit and at least one unit of
phase credit.  The explicit monotonicity hypothesis makes the natural-number
subtraction an exact drop rather than an untracked positive part. -/
theorem one_episode_amortized
    {S : Type} {scale : Nat} {w phase : S → Nat}
    {x y : S} {c : Nat}
    (hw : w y ≤ w x)
    (hphase : phase y < phase x)
    (hcost : c ≤ scale * ((w x - w y) + 1)) :
    c + amortizedPotential scale w phase y ≤
      amortizedPotential scale w phase x := by
  have hraw :
      ((w x - w y) + 1) + (w y + phase y) ≤
        w x + phase x := by
    omega
  have hscaled :
      scale * (((w x - w y) + 1) + (w y + phase y)) ≤
        scale * (w x + phase x) :=
    Nat.mul_le_mul_left scale hraw
  simp only [amortizedPotential]
  calc
    c + scale * (w y + phase y) ≤
        scale * ((w x - w y) + 1) +
          scale * (w y + phase y) :=
      Nat.add_le_add hcost (Nat.le_refl _)
    _ = scale * (((w x - w y) + 1) + (w y + phase y)) := by
      simp only [Nat.mul_add]
    _ ≤ scale * (w x + phase x) := hscaled


/-- A finite sequence of completed successful episodes.  The middle `Nat`
index is the sum of the per-episode certified bounds. -/
inductive EpisodeTrace {S : Type}
    (next : S → S → Prop) (episodeBound : S → S → Nat) :
    S → Nat → S → Prop where
  | refl (x : S) : EpisodeTrace next episodeBound x 0 x
  | cons {x y z : S} {tailCost : Nat}
      (head : next x y)
      (tail : EpisodeTrace next episodeBound y tailCost z) :
      EpisodeTrace next episodeBound x
        (episodeBound x y + tailCost) z


/-- Strong telescope retaining the final unused amortized credit. -/
theorem telescoping_with_residual
    {S : Type}
    {next : S → S → Prop}
    {episodeBound : S → S → Nat}
    (scale : Nat) (w phase : S → Nat)
    (hstep : ∀ {x y : S}, next x y →
      w y ≤ w x ∧
      phase y < phase x ∧
      episodeBound x y ≤ scale * ((w x - w y) + 1))
    {start finish : S} {total : Nat}
    (trace : EpisodeTrace next episodeBound start total finish) :
    total + amortizedPotential scale w phase finish ≤
      amortizedPotential scale w phase start := by
  induction trace with
  | refl x =>
      simp
  | @cons x y z tailCost head tail ih =>
      rcases hstep head with ⟨hw, hphase, hcost⟩
      have hlocal :
          episodeBound x y + amortizedPotential scale w phase y ≤
            amortizedPotential scale w phase x :=
        one_episode_amortized
          (scale := scale) (w := w) (phase := phase)
          (x := x) (y := y) (c := episodeBound x y)
          hw hphase hcost
      calc
        (episodeBound x y + tailCost) +
              amortizedPotential scale w phase z =
            episodeBound x y +
              (tailCost + amortizedPotential scale w phase z) := by
          omega
        _ ≤ episodeBound x y + amortizedPotential scale w phase y :=
          Nat.add_le_add (Nat.le_refl _) ih
        _ ≤ amortizedPotential scale w phase x := hlocal


/-- The terminal residual is nonnegative, so the accumulated episode budgets
are bounded by the initial amortized potential. -/
theorem telescoping
    {S : Type}
    {next : S → S → Prop}
    {episodeBound : S → S → Nat}
    (scale : Nat) (w phase : S → Nat)
    (hstep : ∀ {x y : S}, next x y →
      w y ≤ w x ∧
      phase y < phase x ∧
      episodeBound x y ≤ scale * ((w x - w y) + 1))
    {start finish : S} {total : Nat}
    (trace : EpisodeTrace next episodeBound start total finish) :
    total ≤ amortizedPotential scale w phase start := by
  have hres :=
    telescoping_with_residual scale w phase hstep trace
  omega


/-- Protocol-friendly R-c interface.  `fresh x y` is work that has never been
paid before.  The inequality `fresh + w_after ≤ w_before` is stronger and
cleaner than writing a truncated subtraction in the protocol theorem. -/
theorem telescoping_fresh
    {S : Type}
    {next : S → S → Prop}
    {episodeBound fresh : S → S → Nat}
    (scale : Nat) (w phase : S → Nat)
    (hstep : ∀ {x y : S}, next x y →
      fresh x y + w y ≤ w x ∧
      phase y < phase x ∧
      episodeBound x y ≤ scale * (fresh x y + 1))
    {start finish : S} {total : Nat}
    (trace : EpisodeTrace next episodeBound start total finish) :
    total ≤ amortizedPotential scale w phase start := by
  have hstep_sub : ∀ {x y : S}, next x y →
      w y ≤ w x ∧
      phase y < phase x ∧
      episodeBound x y ≤ scale * ((w x - w y) + 1) := by
    intro x y hxy
    rcases hstep hxy with ⟨hfresh, hphase, hcost⟩
    have hw : w y ≤ w x := by
      omega
    have hplus :
        fresh x y + 1 ≤ (w x - w y) + 1 := by
      omega
    have hscaled :
        scale * (fresh x y + 1) ≤
          scale * ((w x - w y) + 1) :=
      Nat.mul_le_mul_left scale hplus
    exact ⟨hw, hphase, Nat.le_trans hcost hscaled⟩
  exact telescoping scale w phase hstep_sub trace


/-- Ring-size specialization.  With `scale = C*n`, initial unpaid mass at most
`n`, and at most `n` successful phases, the total is at most
`(C*n)*(2*n)`, hence quadratic in `n` for fixed `C`. -/
theorem telescoping_quadratic
    {S : Type}
    {next : S → S → Prop}
    {episodeBound : S → S → Nat}
    (C n : Nat) (w phase : S → Nat)
    (hstep : ∀ {x y : S}, next x y →
      w y ≤ w x ∧
      phase y < phase x ∧
      episodeBound x y ≤
        (C * n) * ((w x - w y) + 1))
    {start finish : S} {total : Nat}
    (trace : EpisodeTrace next episodeBound start total finish)
    (hw_start : w start ≤ n)
    (hphase_start : phase start ≤ n) :
    total ≤ (C * n) * (2 * n) := by
  have htotal :
      total ≤ (C * n) * (w start + phase start) := by
    simpa [amortizedPotential] using
      (telescoping (C * n) w phase hstep trace)
  have hsum : w start + phase start ≤ 2 * n := by
    omega
  have hscaled :
      (C * n) * (w start + phase start) ≤
        (C * n) * (2 * n) :=
    Nat.mul_le_mul_left (C * n) hsum
  exact Nat.le_trans htotal hscaled


/-- Four unit gaps can be merged successively into lengths 2, 3, and 4.
Charging each whole merged gap gives total charge 9, already larger than the
ring mass 4. -/
theorem naive_gap_mass_counterexample :
    (4 : Nat) < 2 + 3 + 4 := by
  omega


/-- Truncated positive drops alone do not telescope if the weight may rise:
`5 -> 0 -> 5 -> 0` has positive drops `5, 0, 5`. -/
theorem truncated_drop_needs_monotonicity :
    (5 : Nat) < (5 - 0) + (0 - 5) + (5 - 0) := by
  omega


end EpisodeTelescope

#print axioms EpisodeTelescope.amortizedPotential
#print axioms EpisodeTelescope.one_episode_amortized
#print axioms EpisodeTelescope.telescoping_with_residual
#print axioms EpisodeTelescope.telescoping
#print axioms EpisodeTelescope.telescoping_fresh
#print axioms EpisodeTelescope.telescoping_quadratic
#print axioms EpisodeTelescope.naive_gap_mass_counterexample
#print axioms EpisodeTelescope.truncated_drop_needs_monotonicity
