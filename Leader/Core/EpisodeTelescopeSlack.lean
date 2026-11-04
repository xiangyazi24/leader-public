import Lean.Elab.Tactic.Omega

set_option autoImplicit false

universe u

variable {S : Type u}

inductive EpisodeTrace (next : S → S → Prop)
    (episodeBound : S → S → Nat) : S → Nat → S → Prop where
  | nil (x : S) :
      EpisodeTrace next episodeBound x 0 x
  | cons {x y finish : S} {tailTotal : Nat}
      (hxy : next x y)
      (tail : EpisodeTrace next episodeBound y tailTotal finish) :
      EpisodeTrace next episodeBound x
        (episodeBound x y + tailTotal) finish

inductive EpisodeTransitTrace (next : S → S → Prop)
    (episodeBound transit : S → S → Nat) :
    S → Nat → Nat → S → Prop where
  | nil (x : S) :
      EpisodeTransitTrace next episodeBound transit x 0 0 x
  | cons {x y finish : S} {tailTotal tailTransit : Nat}
      (hxy : next x y)
      (tail : EpisodeTransitTrace next episodeBound transit
        y tailTotal tailTransit finish) :
      EpisodeTransitTrace next episodeBound transit x
        (episodeBound x y + tailTotal)
        (transit x y + tailTransit) finish

theorem slack_drop_potential
    (K wx wy px py : Nat)
    (hw : wy ≤ wx + K)
    (hp : py < px) :
    (wx - wy + 1) + (wy + (K + 1) * py) ≤
      wx + (K + 1) * px := by
  have hdrop : (wx - wy) + wy ≤ wx + K := by
    omega
  have hphase : py + 1 ≤ px := by
    omega
  have hphaseMul :
      (K + 1) * (py + 1) ≤ (K + 1) * px :=
    Nat.mul_le_mul_left (K + 1) hphase
  have hphaseBudget :
      (K + 1) * py + (K + 1) ≤ (K + 1) * px := by
    calc
      (K + 1) * py + (K + 1) =
          (K + 1) * (py + 1) := by
        simp [Nat.mul_add]
      _ ≤ (K + 1) * px := hphaseMul
  omega

theorem trace_amortized_slack
    (C n K : Nat) (w phase : S → Nat)
    {next : S → S → Prop}
    {episodeBound : S → S → Nat}
    (hstep : ∀ {x y : S}, next x y →
      w y ≤ w x + K ∧
      phase y < phase x ∧
      episodeBound x y ≤
        (C * n) * ((w x - w y) + 1))
    {start finish : S} {total : Nat}
    (trace : EpisodeTrace next episodeBound start total finish) :
    total ≤ (C * n) *
      (w start + (K + 1) * phase start) := by
  induction trace with
  | nil x =>
      simp
  | @cons x y finish tailTotal hxy tail ih =>
      have hs := hstep hxy
      have hw : w y ≤ w x + K := hs.1
      have hp : phase y < phase x := hs.2.1
      have hcost :
          episodeBound x y ≤
            (C * n) * ((w x - w y) + 1) := hs.2.2
      have hpot := slack_drop_potential K
        (w x) (w y) (phase x) (phase y) hw hp
      calc
        episodeBound x y + tailTotal ≤
            (C * n) * ((w x - w y) + 1) +
              (C * n) *
                (w y + (K + 1) * phase y) :=
          Nat.add_le_add hcost ih
        _ = (C * n) *
            (((w x - w y) + 1) +
              (w y + (K + 1) * phase y)) := by
          rw [← Nat.mul_add]
        _ ≤ (C * n) *
            (w x + (K + 1) * phase x) :=
          Nat.mul_le_mul_left (C * n) hpot

theorem telescoping_quadratic_slack
    (C n K : Nat) (w phase : S → Nat)
    {next : S → S → Prop}
    {episodeBound : S → S → Nat}
    (hstep : ∀ {x y : S}, next x y →
      w y ≤ w x + K ∧
      phase y < phase x ∧
      episodeBound x y ≤
        (C * n) * ((w x - w y) + 1))
    {start finish : S} {total : Nat}
    (trace : EpisodeTrace next episodeBound start total finish)
    (hw_start : w start ≤ n)
    (hphase_start : phase start ≤ n) :
    total ≤ (C * n) * (2 * n + K * n) := by
  have htrace :=
    trace_amortized_slack C n K w phase hstep trace
  have hphaseMul :
      (K + 1) * phase start ≤ (K + 1) * n :=
    Nat.mul_le_mul_left (K + 1) hphase_start
  have hstart :
      w start + (K + 1) * phase start ≤
        n + (K + 1) * n :=
    Nat.add_le_add hw_start hphaseMul
  have hnorm :
      n + (K + 1) * n = 2 * n + K * n := by
    calc
      n + (K + 1) * n = n + (K * n + n) := by
        rw [Nat.add_mul]
        simp
      _ = 2 * n + K * n := by
        omega
  have hinside :
      w start + (K + 1) * phase start ≤
        2 * n + K * n := by
    rw [← hnorm]
    exact hstart
  exact Nat.le_trans htrace
    (Nat.mul_le_mul_left (C * n) hinside)

theorem trace_amortized_slack_transit
    (C n K : Nat) (w phase : S → Nat)
    (transit : S → S → Nat)
    {next : S → S → Prop}
    {episodeBound : S → S → Nat}
    (hstep : ∀ {x y : S}, next x y →
      w y ≤ w x + K ∧
      phase y < phase x ∧
      episodeBound x y ≤
        (C * n) * ((w x - w y) + 1) +
          (C * n) * transit x y)
    {start finish : S} {total transitTotal : Nat}
    (trace : EpisodeTransitTrace next episodeBound transit
      start total transitTotal finish) :
    total ≤ (C * n) *
      (w start + (K + 1) * phase start + transitTotal) := by
  induction trace with
  | nil x =>
      simp
  | @cons x y finish tailTotal tailTransit hxy tail ih =>
      have hs := hstep hxy
      have hw : w y ≤ w x + K := hs.1
      have hp : phase y < phase x := hs.2.1
      have hcost :
          episodeBound x y ≤
            (C * n) * ((w x - w y) + 1) +
              (C * n) * transit x y := hs.2.2
      have hpot := slack_drop_potential K
        (w x) (w y) (phase x) (phase y) hw hp
      have hplus :
          (((w x - w y) + 1) +
              (w y + (K + 1) * phase y)) +
                (transit x y + tailTransit) ≤
            (w x + (K + 1) * phase x) +
              (transit x y + tailTransit) :=
        Nat.add_le_add_right hpot
          (transit x y + tailTransit)
      have hinside :
          (((w x - w y) + 1) + transit x y) +
              (w y + (K + 1) * phase y + tailTransit) ≤
            (w x + (K + 1) * phase x) +
              (transit x y + tailTransit) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using hplus
      calc
        episodeBound x y + tailTotal ≤
            ((C * n) * ((w x - w y) + 1) +
              (C * n) * transit x y) +
              (C * n) *
                (w y + (K + 1) * phase y + tailTransit) :=
          Nat.add_le_add hcost ih
        _ = (C * n) *
              (((w x - w y) + 1) + transit x y) +
              (C * n) *
                (w y + (K + 1) * phase y + tailTransit) := by
          rw [← Nat.mul_add]
        _ = (C * n) *
            ((((w x - w y) + 1) + transit x y) +
              (w y + (K + 1) * phase y + tailTransit)) := by
          rw [← Nat.mul_add]
        _ ≤ (C * n) *
            ((w x + (K + 1) * phase x) +
              (transit x y + tailTransit)) :=
          Nat.mul_le_mul_left (C * n) hinside

theorem telescoping_quadratic_slack_transit
    (C n K Tmax : Nat) (w phase : S → Nat)
    (transit : S → S → Nat)
    {next : S → S → Prop}
    {episodeBound : S → S → Nat}
    (hstep : ∀ {x y : S}, next x y →
      w y ≤ w x + K ∧
      phase y < phase x ∧
      episodeBound x y ≤
        (C * n) * ((w x - w y) + 1) +
          (C * n) * transit x y)
    {start finish : S} {total transitTotal : Nat}
    (trace : EpisodeTransitTrace next episodeBound transit
      start total transitTotal finish)
    (htransit : transitTotal ≤ Tmax)
    (hw_start : w start ≤ n)
    (hphase_start : phase start ≤ n) :
    total ≤ (C * n) * (2 * n + K * n + Tmax) := by
  have htrace :=
    trace_amortized_slack_transit
      C n K w phase transit hstep trace
  have hphaseMul :
      (K + 1) * phase start ≤ (K + 1) * n :=
    Nat.mul_le_mul_left (K + 1) hphase_start
  have hstart :
      w start + (K + 1) * phase start ≤
        n + (K + 1) * n :=
    Nat.add_le_add hw_start hphaseMul
  have hall :
      w start + (K + 1) * phase start + transitTotal ≤
        n + (K + 1) * n + Tmax :=
    Nat.add_le_add hstart htransit
  have hnorm :
      n + (K + 1) * n = 2 * n + K * n := by
    calc
      n + (K + 1) * n = n + (K * n + n) := by
        rw [Nat.add_mul]
        simp
      _ = 2 * n + K * n := by
        omega
  have hinside :
      w start + (K + 1) * phase start + transitTotal ≤
        2 * n + K * n + Tmax := by
    rw [← hnorm]
    exact hall
  exact Nat.le_trans htrace
    (Nat.mul_le_mul_left (C * n) hinside)

#print axioms EpisodeTrace
#print axioms EpisodeTransitTrace
#print axioms slack_drop_potential
#print axioms trace_amortized_slack
#print axioms telescoping_quadratic_slack
#print axioms trace_amortized_slack_transit
#print axioms telescoping_quadratic_slack_transit
