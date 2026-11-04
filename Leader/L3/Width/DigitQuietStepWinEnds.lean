import Leader.L3.Width.DigitQuietStepGlue
import Leader.L3.Width.DigitQuietStepReplace

/-!
# The quiet class: the window lemmas at the two ends of a pair

Two of the window lemmas of the pair closure of `QuietStepLaw` (package C of
`research/lean-l3/ledgers/R10c-quiet-law-agent-brief.md`):

* `win_term`: the terminal letter at the last target cell (cell `R - 1`, the next delimiter `y`);
* `win_del`: the junction letter, source cell `R - 1` onto the target delimiter (cell `0`).

Consumer: the pair closure of `QuietStepLaw` (`WidthDigitQuietStep*`).
-/

namespace L3.DigitQuiet

open L3

set_option autoImplicit false

variable {c : Compiled}

/-- A continuation of the target scan that is antitone in the flags: fewer set flags only make it easier to satisfy (the lower scan of a pair, whose flags only add conditions).  Consumer: `win_term`, `scanTargetW_flagAnti`. -/
def WinEndsFlagAnti (K : Nat → Bool → Bool → Prop) : Prop :=
  ∀ a b d b' d', K a b d → (b' = true → b = true) → (d' = true → d = true) → K a b' d'

/-- Entering a flag as `false` is never harder: if the flags are antitone for the continuation they are for the scan of any window.  Consumer: `win_term` (its hypothesis holds for the lower scan of a pair). -/
theorem scanTargetW_flagAnti (R : Nat) (v : Nat → DigitLaneView c) (Dp : Nat → Fin c.topA)
    (lo : Nat) (K : Nat → Bool → Bool → Prop) (hK : WinEndsFlagAnti K) :
    ∀ (k nxt : Nat) (sawP seen sawP' seen' : Bool),
      ScanTargetW R v Dp lo K k nxt sawP seen → (sawP' = true → sawP = true) →
        (seen' = true → seen = true) → ScanTargetW R v Dp lo K k nxt sawP' seen' := by
  have hf : ∀ b b' : Bool, (b' = true → b = true) → b = false → b' = false := by
    intro b b' h hb
    cases b' with
    | false => rfl
    | true => have := h rfl; rw [hb] at this; cases this
  intro k
  induction k with
  | zero => intro nxt sawP seen sawP' seen' h h1 h2; exact hK _ _ _ _ _ h h1 h2
  | succ k ih =>
    intro nxt sawP seen sawP' seen' hs h1 h2
    simp only [ScanTargetW] at hs ⊢
    by_cases hl : (v (k + lo)).carryLive = true
    · rw [if_pos hl] at hs ⊢
      obtain ⟨a, b, c, d, e, f⟩ := hs
      exact ⟨a, hf _ _ h1 b, c, d, e, ih _ _ _ _ _ f h1 (fun h => h)⟩
    · rw [if_neg hl] at hs ⊢
      revert hs
      cases (v (k + lo)).input with
      | E => intro hs; exact ih _ _ _ _ _ hs h1 h2
      | X => intro hs; exact hs
      | S val tail =>
        intro hs
        obtain ⟨a, b, c, d, e⟩ := hs
        exact ⟨hf _ _ h1 a, b, c, d, ih _ _ _ _ _ e h1 (fun h => h)⟩
      | P val tail =>
        intro hs
        rcases hs with ⟨a, b, c, d, e⟩ | ⟨a, b, c, e⟩
        · exact Or.inl ⟨a, b, hf _ _ h2 c, d, ih _ _ _ _ _ e (fun h => h) (fun h => h)⟩
        · exact Or.inr ⟨a, b, c, ih _ _ _ _ _ e (fun h => h) (fun h => h)⟩

set_option hygiene false in
/-- Split the remaining view fields of the two endpoints (carries, inputs, left output) into
constructors (and the packet tag `t` when one is named), so that `simp` decides every guard of `rowIn` / `rowOut` instead of splitting on
them symbolically. -/
local macro "view_cases" : tactic =>
  `(tactic| ((try cases cx) <;> (try cases cy) <;>
    (try rcases ix with _ | _ | ⟨_, _ | _⟩ | ⟨_, _ | _⟩) <;>
    (try rcases iy with _ | _ | ⟨_, _ | _⟩ | ⟨_, _ | _⟩) <;>
    (try rcases ox with _ | _ | ⟨_, _ | _⟩) <;> (try cases t)))

/-- At a terminal step (left cell a non-leader non-marker, right cell the marker `X`'s delimiter) the left carry is dropped: the new left cell has no live carry.  Consumer: `win_term`. -/
theorem winEnds_term_carry (lane : DigitLane) (vx vy : DigitLaneView c) (hlx : vx.leader = false)
    (hly : vy.leader = false) (hmx : vx.marker = false) (hmy : vy.marker = true) :
    (laneRow lane vx vy).1.carryLive = false := by
  rcases vx with ⟨lx, mx, dx, ox, ix, cx, bx, ex⟩
  rcases vy with ⟨ly, my, dy, oy, iy, cy, by_, ey⟩
  simp only at hlx hly hmx hmy
  subst hlx hly hmx hmy
  cases cx <;> simp [laneRow, rowCarry, rowSucc, rowLaunch]

/-- The new left input of a terminal step: a live carry or a tail `P` erases it, a non-tail `P` settles as `S v false`, an `S v false` or an empty input stays.  Consumer: `win_term`. -/
theorem winEnds_term_input (lane : DigitLane) (vx vy : DigitLaneView c) (hlx : vx.leader = false)
    (hly : vy.leader = false) (hmx : vx.marker = false) (hmy : vy.marker = true) :
    (vx.carryLive = true → (laneRow lane vx vy).1.input = .E) ∧
    (vx.carryLive = false → vx.input = .E → (laneRow lane vx vy).1.input = .E) ∧
    (vx.carryLive = false → ∀ v, vx.input = .S v false → (laneRow lane vx vy).1.input = .S v false) ∧
    (vx.carryLive = false → ∀ v, vx.input = .P v false → (laneRow lane vx vy).1.input = .S v false) ∧
    (vx.carryLive = false → ∀ v, vx.input = .P v true → (laneRow lane vx vy).1.input = .E) := by
  rcases vx with ⟨lx, mx, dx, ox, ix, cx, bx, ex⟩
  rcases vy with ⟨ly, my, dy, oy, iy, cy, by_, ey⟩
  simp only at hlx hly hmx hmy
  subst hlx hly hmx hmy
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    simp only at h
    subst h
    view_cases <;> simp_all [laneRow, rowIn, rowSucc, rowLaunch, InTok.isS, InTok.isX, InTok.isP, InTok.isE, inT, inV, OutTok.isD, OutTok.isU, OutTok.isE, outV, outT]
  · intro h hi
    simp only at h hi
    subst h hi
    view_cases <;> simp_all [laneRow, rowIn, rowSucc, rowLaunch, InTok.isS, InTok.isX, InTok.isP, InTok.isE, inT, inV, OutTok.isD, OutTok.isU, OutTok.isE, outV, outT]
  · intro h v hi
    simp only at h hi
    subst h hi
    view_cases <;> simp_all [laneRow, rowIn, rowSucc, rowLaunch, InTok.isS, InTok.isX, InTok.isP, InTok.isE, inT, inV, OutTok.isD, OutTok.isU, OutTok.isE, outV, outT]
  · intro h v hi
    simp only at h hi
    subst h hi
    view_cases <;> simp_all [laneRow, rowIn, rowSucc, rowLaunch, InTok.isS, InTok.isX, InTok.isP, InTok.isE, inT, inV, OutTok.isD, OutTok.isU, OutTok.isE, outV, outT]
  · intro h v hi
    simp only at h hi
    subst h hi
    view_cases <;> simp_all [laneRow, rowIn, rowSucc, rowLaunch, InTok.isS, InTok.isX, InTok.isP, InTok.isE, inT, inV, OutTok.isD, OutTok.isU, OutTok.isE, outV, outT]

/-- A step onto a delimiter leaves the right carry alone.  Consumer: `win_del`. -/
theorem winEnds_del_carry (lane : DigitLane) (vx vy : DigitLaneView c) (hlx : vx.leader = false)
    (hly : vy.leader = false) (hmx : vx.marker = false) (hmy : vy.marker = true) :
    (laneRow lane vx vy).2.carryLive = vy.carryLive ∧
    (laneRow lane vx vy).2.carryBit = vy.carryBit ∧
    (laneRow lane vx vy).2.carryError = vy.carryError := by
  rcases vx with ⟨lx, mx, dx, ox, ix, cx, bx, ex⟩
  rcases vy with ⟨ly, my, dy, oy, iy, cy, by_, ey⟩
  simp only at hlx hly hmx hmy
  subst hlx hly hmx hmy
  cases cx <;> simp [laneRow, rowCarry, rowSucc, rowLaunch]

/-- The new right input of a step onto a delimiter: a live carry erases it, an empty delimiter without carry accepts a packet `D v t` as `P v t`, otherwise it is kept.  Consumer: `win_del`. -/
theorem winEnds_del_input (lane : DigitLane) (vx vy : DigitLaneView c) (hlx : vx.leader = false)
    (hly : vy.leader = false) (hmx : vx.marker = false) (hmy : vy.marker = true) :
    (vy.carryLive = true → (laneRow lane vx vy).2.input = .E) ∧
    (vy.carryLive = false → vy.input = .E → ∀ v t, vx.out = .D v t →
      (laneRow lane vx vy).2.input = .P v t) ∧
    (vy.carryLive = false → vy.input = .E → (vx.out = .E ∨ vx.out = .U) →
      (laneRow lane vx vy).2.input = .E) ∧
    (vy.carryLive = false → vy.input ≠ .E → (laneRow lane vx vy).2.input = vy.input) := by
  rcases vx with ⟨lx, mx, dx, ox, ix, cx, bx, ex⟩
  rcases vy with ⟨ly, my, dy, oy, iy, cy, by_, ey⟩
  simp only at hlx hly hmx hmy
  subst hlx hly hmx hmy
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    simp only at h
    subst h
    view_cases <;> simp_all [laneRow, rowIn, rowSucc, rowLaunch, InTok.isS, InTok.isX, InTok.isP, InTok.isE, inT, OutTok.isD, OutTok.isU, OutTok.isE, inV, outV, outT]
  · intro h hi v t ho
    simp only at h hi ho
    subst h hi ho
    view_cases <;> simp_all [laneRow, rowIn, rowSucc, rowLaunch, InTok.isS, InTok.isX, InTok.isP, InTok.isE, OutTok.isD, outV, outT, OutTok.isU, OutTok.isE, inT, inV]
  · intro h hi ho
    simp only at h hi ho
    subst h hi
    rcases ho with ho | ho <;> subst ho <;>
    view_cases <;> simp_all [laneRow, rowIn, rowSucc, rowLaunch, InTok.isS, InTok.isX, InTok.isP, InTok.isE, OutTok.isD, outV, outT, OutTok.isU, OutTok.isE, inT, inV]
  · intro h hi
    simp only at h hi ⊢
    subst h
    view_cases <;> simp_all [laneRow, rowIn, rowSucc, rowLaunch, InTok.isS, InTok.isX, InTok.isP, InTok.isE, OutTok.isD, outV, outT, OutTok.isU, OutTok.isE, inT, inV]

/-- The new left output of a step onto a delimiter: `E` stays, `U` is sampled to `D digit false`, a `D v t` is accepted (leaving `U`/`E` by its tail bit) exactly when the right delimiter has no carry and an empty input.  Consumer: `win_del`. -/
theorem winEnds_del_out (lane : DigitLane) (vx vy : DigitLaneView c) (hlx : vx.leader = false)
    (hly : vy.leader = false) (hmx : vx.marker = false) (hmy : vy.marker = true) :
    (vx.out = .E → (laneRow lane vx vy).1.out = .E) ∧
    (vx.out = .U → (laneRow lane vx vy).1.out = .D vx.digit false) ∧
    (∀ v t, vx.out = .D v t → vy.carryLive = false → vy.input = .E →
      (laneRow lane vx vy).1.out = if t then .U else .E) ∧
    (∀ v t, vx.out = .D v t → (vy.carryLive = true ∨ vy.input ≠ .E) →
      (laneRow lane vx vy).1.out = .D v t) := by
  rcases vx with ⟨lx, mx, dx, ox, ix, cx, bx, ex⟩
  rcases vy with ⟨ly, my, dy, oy, iy, cy, by_, ey⟩
  simp only at hlx hly hmx hmy
  subst hlx hly hmx hmy
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ho
    simp only at ho
    subst ho
    view_cases <;> simp_all [laneRow, rowIn, rowOut, rowSucc, rowLaunch, InTok.isS, InTok.isX, InTok.isP, InTok.isE, OutTok.isD, OutTok.isU, OutTok.isE, outV, outT, inT, inV]
  · intro ho
    simp only at ho ⊢
    subst ho
    view_cases <;> simp_all [laneRow, rowIn, rowOut, rowSucc, rowLaunch, InTok.isS, InTok.isX, InTok.isP, InTok.isE, OutTok.isD, OutTok.isU, OutTok.isE, outV, outT, inT, inV]
  · intro v t ho h1 h2
    simp only at ho h1 h2
    subst ho h1 h2
    view_cases <;> simp_all [laneRow, rowIn, rowOut, rowSucc, rowLaunch, InTok.isS, InTok.isX, InTok.isP, InTok.isE, OutTok.isD, OutTok.isU, OutTok.isE, outV, outT, inT, inV]
  · intro v t ho h1
    simp only at ho h1
    subst ho
    view_cases <;> simp_all [laneRow, rowIn, rowOut, rowSucc, rowLaunch, InTok.isS, InTok.isX, InTok.isP, InTok.isE, OutTok.isD, OutTok.isU, OutTok.isE, outV, outT, inT, inV]

/-- The source scan over the top cell `m` and the cells below, when the top output is unchanged and the lower cells are unchanged.  Consumer: `win_del`. -/
theorem winEnds_srcTop_same (m : Nat) (vs ws : Nat → DigitLaneView c) (Dp : Nat → Fin c.topA)
    (K : Nat → Prop) (hlow : ∀ q, q < m → ws q = vs q) (hout : (ws m).out = (vs m).out)
    (nxt : Nat) :
    ScanSourceW vs Dp 0 K (m + 1) nxt → ScanSourceW ws Dp 0 K (m + 1) nxt := by
  intro h
  have hl : ∀ a, ScanSourceW vs Dp 0 K m a → ScanSourceW ws Dp 0 K m a :=
    fun a => scanSourceW_mono vs ws Dp 0 K K (fun _ h => h) m
      (fun i _ h2 => (hlow i (by omega)).symm) a
  simp only [ScanSourceW, Nat.add_zero] at h ⊢
  rw [hout]
  revert h
  cases (vs m).out <;> simp only [] <;> intro h
  · exact ⟨h.1, hl _ h.2⟩
  · exact ⟨h.1, hl _ h.2⟩
  · exact ⟨h.1, h.2.1, h.2.2.1, hl _ h.2.2.2⟩

/-- The same when the top output `U` is sampled into `D (Dp m) false` (`1 ≤ m`).  Consumer: `win_del`. -/
theorem winEnds_srcTop_sample (m : Nat) (hm : 1 ≤ m) (vs ws : Nat → DigitLaneView c)
    (Dp : Nat → Fin c.topA) (K : Nat → Prop) (hlow : ∀ q, q < m → ws q = vs q)
    (hu : (vs m).out = .U) (hd : (ws m).out = .D (Dp m) false) (nxt : Nat) :
    ScanSourceW vs Dp 0 K (m + 1) nxt → ScanSourceW ws Dp 0 K (m + 1) nxt := by
  intro h
  have hl : ∀ a, ScanSourceW vs Dp 0 K m a → ScanSourceW ws Dp 0 K m a :=
    fun a => scanSourceW_mono vs ws Dp 0 K K (fun _ h => h) m
      (fun i _ h2 => (hlow i (by omega)).symm) a
  simp only [ScanSourceW, Nat.add_zero] at h ⊢
  rw [hu] at h
  rw [hd]
  simp only [] at h ⊢
  obtain ⟨h1, h2⟩ := h
  rw [h1]
  have hm0 : m ≠ 0 := by omega
  simp only [hm0, if_false, decide_false, Nat.le_refl, true_and]
  exact hl _ h2

/-- **The terminal letter at the last target cell** (cell `R-1`, the next delimiter `y`): the scan over the single top position `R-1`, entering in the initial state, is kept, for every continuation `K` antitone in the flags `sawP`/`seen` (`WinEndsFlagAnti`; the lower scan of a pair is, `scanTargetW_flagAnti`).  Without this hypothesis the claim is false: a live carry at `R-1` is dropped by the letter, so the flag `seen` passed to `K` changes from `true` to `false` (`K := fun _ _ d => d = true`).  Consumer: the pair closure. -/
theorem win_term (lane : DigitLane) (R : Nat) (hR : 2 ≤ R) (vt wt : Nat → DigitLaneView c)
    (Dp : Nat → Fin c.topA) (y : DigitLaneView c) (hlx : (vt (R-1)).leader = false)
    (hly : y.leader = false) (hmx : (vt (R-1)).marker = false) (hmy : y.marker = true)
    (hw : wt (R-1) = (laneRow lane (vt (R-1)) y).1) (K : Nat → Bool → Bool → Prop)
    (hK : WinEndsFlagAnti K) :
    ScanTargetW R vt Dp (R-1) K 1 (R-1) false false → ScanTargetW R wt Dp (R-1) K 1 (R-1) false false := by
  intro h
  have hc := winEnds_term_carry lane (vt (R-1)) y hlx hly hmx hmy
  obtain ⟨hE1, hE2, hS, hP0, hP1⟩ := winEnds_term_input lane (vt (R-1)) y hlx hly hmx hmy
  have hne : R - 1 ≠ 0 := by omega
  simp only [ScanTargetW, Nat.zero_add] at h ⊢
  rw [hw, hc]
  simp only [Bool.false_eq_true, if_false]
  by_cases hl : (vt (R-1)).carryLive = true
  · rw [if_pos hl] at h
    obtain ⟨-, -, -, -, -, hk⟩ := h
    rw [hE1 hl]
    exact hK _ _ _ _ _ hk (fun h => by cases h) (fun h => by cases h)
  · rw [if_neg hl] at h
    have hl' : (vt (R-1)).carryLive = false := by simpa using hl
    revert h
    cases hin : (vt (R-1)).input with
    | E => intro h; rw [hE2 hl' hin]; exact h
    | X => intro h; exact h.elim
    | S val tail =>
      intro h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      have ht : tail = false := by rw [h4]; simp [hne]
      subst ht
      rw [hS hl' val hin]
      exact ⟨h1, h2, h3, h4, h5⟩
    | P val tail =>
      intro h
      rcases h with ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h5⟩
      · subst h1
        rw [hP1 hl' val hin]
        exact hK _ _ _ _ _ h5 (fun h => by cases h) (fun h => by cases h)
      · have ht : tail = false := by rw [h3]; simp [hne]
        subst ht
        rw [hP0 hl' val hin]
        refine ⟨trivial, trivial, h2, by simp [hne], ?_⟩
        exact hK _ _ _ _ _ h5 (fun h => by cases h) (fun h => h)


/-- **The junction letter**: source cell `R-1` (the last source cell) onto the target delimiter (cell `0`): the target scan over position `0`, continued by the whole source out-scan, is kept, wherever the letter samples `U` into `D`, accepts a `D` into the empty carry-free delimiter, or does nothing.  Consumer: the pair closure (junction letter). -/
theorem win_del (lane : DigitLane) (R : Nat) (hR : 2 ≤ R) (vs ws vt wt : Nat → DigitLaneView c)
    (Dp : Nat → Fin c.topA) (hlx : (vs (R-1)).leader = false) (hly : (vt 0).leader = false)
    (hmx : (vs (R-1)).marker = false) (hmy : (vt 0).marker = true)
    (hDx : (vs (R-1)).digit = Dp (R-1))
    (hw0 : ws (R-1) = (laneRow lane (vs (R-1)) (vt 0)).1)
    (hw1 : wt 0 = (laneRow lane (vs (R-1)) (vt 0)).2)
    (hsb : ∀ q, q < R - 1 → ws q = vs q) (_htb : ∀ q, 0 < q → q < R → wt q = vt q)
    (nxt : Nat) (sawP seen : Bool) :
    ScanTargetW R vt Dp 0 (fun a _ _ => ScanSource vs Dp R a) 1 nxt sawP seen →
      ScanTargetW R wt Dp 0 (fun a _ _ => ScanSource ws Dp R a) 1 nxt sawP seen := by
  obtain ⟨m, rfl⟩ : ∃ m, R = m + 1 := ⟨R - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  have e : m + 1 - 1 = m := rfl
  rw [e] at hlx hmx hDx hw0 hsb hw1
  have hm0 : m ≠ 0 := by omega
  obtain ⟨hcl, hcb, hce⟩ := winEnds_del_carry lane (vs m) (vt 0) hlx hly hmx hmy
  obtain ⟨hi1, hi2, hi3, hi4⟩ := winEnds_del_input lane (vs m) (vt 0) hlx hly hmx hmy
  obtain ⟨ho1, ho2, ho3, ho4⟩ := winEnds_del_out lane (vs m) (vt 0) hlx hly hmx hmy
  rw [← hw0] at ho1 ho2 ho3 ho4
  rw [← hw1] at hcl hcb hce hi1 hi2 hi3 hi4
  rw [hDx] at ho2
  have hS : ∀ K : Nat → Prop, ∀ n, ((ws m).out = (vs m).out ∨
      ((vs m).out = .U ∧ (ws m).out = .D (Dp m) false)) →
      ScanSourceW vs Dp 0 K (m + 1) n → ScanSourceW ws Dp 0 K (m + 1) n := by
    intro K n hout
    rcases hout with hout | ⟨hu, hd⟩
    · exact winEnds_srcTop_same m vs ws Dp K hsb hout n
    · exact winEnds_srcTop_sample m hm vs ws Dp K hsb hu hd n
  have hgen : ¬ ((vt 0).carryLive = false ∧ (vt 0).input = .E ∧ (vs m).out.isD = true) →
      ((ws m).out = (vs m).out ∨ ((vs m).out = .U ∧ (ws m).out = .D (Dp m) false)) := by
    intro hn
    cases ho : (vs m).out with
    | E => exact Or.inl (ho1 ho)
    | U => exact Or.inr ⟨rfl, ho2 ho⟩
    | D v t =>
      have hd : (vt 0).carryLive = true ∨ (vt 0).input ≠ .E := by
        by_cases hc : (vt 0).carryLive = true
        · exact Or.inl hc
        · by_cases hi : (vt 0).input = .E
          · exact absurd ⟨by simpa using hc, hi, by rw [ho]; rfl⟩ hn
          · exact Or.inr hi
      exact Or.inl (ho4 v t ho hd)
  intro h
  simp only [ScanTargetW, Nat.add_zero, Nat.zero_add, Nat.add_sub_cancel] at h ⊢
  rw [hcl, hcb, hce]
  have hconv := scanSource_eq_W vs Dp (m + 1)
  have hconv' := scanSource_eq_W ws Dp (m + 1)
  have hgS : ∀ n, ¬ ((vt 0).carryLive = false ∧ (vt 0).input = .E ∧ (vs m).out.isD = true) →
      ScanSource vs Dp (m + 1) n → ScanSource ws Dp (m + 1) n :=
    fun n hn hh => (hconv' n).mpr (hS _ n (hgen hn) ((hconv n).mp hh))
  by_cases hl : (vt 0).carryLive = true
  · rw [if_pos hl] at h
    rw [if_pos hl, hi1 hl]
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨h1, h2, rfl, h4, h5, hgS _ (fun hn => by rw [hl] at hn; cases hn.1) h6⟩
  · rw [if_neg hl] at h
    rw [if_neg hl]
    have hl' : (vt 0).carryLive = false := by simpa using hl
    revert h
    cases hin : (vt 0).input with
    | E =>
      intro h
      cases ho : (vs m).out with
      | E =>
        rw [hi3 hl' hin (Or.inl ho)]
        exact hgS nxt (fun hn => by have := hn.2.2; rw [ho] at this; cases this) h
      | U =>
        rw [hi3 hl' hin (Or.inr ho)]
        exact hgS nxt (fun hn => by have := hn.2.2; rw [ho] at this; cases this) h
      | D v t =>
        rw [hi2 hl' hin v t ho]
        have hW := (hconv nxt).mp h
        simp only [ScanSourceW, Nat.add_zero, ho] at hW
        obtain ⟨g1, g2, g3, g4⟩ := hW
        refine Or.inr ⟨Nat.zero_le _, g2, g3, (hconv' _).mpr ?_⟩
        have hmono : ∀ a, ScanSourceW vs Dp 0 (fun _ => True) m a →
            ScanSourceW ws Dp 0 (fun _ => True) m a :=
          fun a => scanSourceW_mono vs ws Dp 0 _ _ (fun _ h => h) m
            (fun i _ h2 => (hsb i (by omega)).symm) a
        by_cases hn0 : nxt = 0
        · have ht : t = true := by rw [g3]; simp [hn0]
          have hwo : (ws m).out = .U := by rw [ho3 v t ho hl' hin, ht]; rfl
          rw [if_pos hn0]
          rw [if_pos hn0] at g4
          simp only [ScanSourceW, Nat.add_zero, hwo]
          exact ⟨trivial, hmono _ g4⟩
        · have ht : t = false := by rw [g3]; simp [hn0]
          have hwo : (ws m).out = .E := by rw [ho3 v t ho hl' hin, ht]; rfl
          rw [if_neg hn0]
          rw [if_neg hn0] at g4
          simp only [ScanSourceW, Nat.add_zero, hwo]
          refine ⟨?_, hmono _ g4⟩
          rw [if_neg hm0]
          omega
    | X => intro h; exact h.elim
    | S val tail =>
      intro h
      have hi := hi4 hl' (by rw [hin]; intro h; cases h)
      rw [hi, hin]
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      exact ⟨h1, h2, h3, h4, hgS _ (fun hn => by rw [hin] at hn; cases hn.2.1) h5⟩
    | P val tail =>
      intro h
      have hi := hi4 hl' (by rw [hin]; intro h; cases h)
      rw [hi, hin]
      have hn : ¬ ((vt 0).carryLive = false ∧ (vt 0).input = .E ∧ (vs m).out.isD = true) :=
        fun hn => by rw [hin] at hn; cases hn.2.1
      rcases h with ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h5⟩
      · exact Or.inl ⟨h1, h2, h3, h4, hgS _ hn h5⟩
      · exact Or.inr ⟨h1, h2, h3, hgS _ hn h5⟩

end L3.DigitQuiet

#print axioms L3.DigitQuiet.win_term
#print axioms L3.DigitQuiet.win_del
#print axioms L3.DigitQuiet.scanTargetW_flagAnti
