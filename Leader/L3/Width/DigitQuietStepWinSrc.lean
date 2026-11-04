import Leader.L3.Width.DigitQuietStepGlue
import Leader.L3.Width.DigitQuietStepReplace

/-!
# The quiet class: the source out-lane window of one pipe letter

* `win_pipe`: a letter on two adjacent cells `h → h + 1` inside a block (neither a leader, the right
  one not a delimiter) preserves the source out-lane scan over the two cells;
* `laneRow_entry_out`: a letter whose right cell is a delimiter never changes that cell's out slot;
* `scanSourceW_congr_out`, `scanTargetW_congr_in`: the scans read only the out slots (source), resp.
  the input and carry fields (target) of their window.

Consumer: the pair closure of `QuietStepLaw` (`WidthDigitQuietStep*`).
-/

namespace L3.DigitQuiet

open L3
open L3.AcceptedReceipts

set_option autoImplicit false

variable {c : Compiled}

/-- **A pipe letter keeps the source out-lane scan over its two cells.**  Consumer: the pair closure
of `QuietStepLaw`. -/
theorem win_pipe (lane : DigitLane) (v w : Nat → DigitLaneView c) (Dp : Nat → Fin c.topA) (h : Nat)
    (hlx : (v h).leader = false) (hly : (v (h+1)).leader = false)
    (hmx : (v h).marker = decide (h = 0)) (hmy : (v (h+1)).marker = false)
    (hdx : (v h).digit = Dp h)
    (hw0 : w h = (laneRow lane (v h) (v (h+1))).1)
    (hw1 : w (h+1) = (laneRow lane (v h) (v (h+1))).2)
    (K : Nat → Prop) (nxt : Nat) :
    ScanSourceW v Dp h K 2 nxt → ScanSourceW w Dp h K 2 nxt := by
  intro hs
  have e1 : 1 + h = h + 1 := by omega
  have h0 : (w h).out = (rowOut (v h) (v (h+1)) (rowIn (v h) (v (h+1))).2).1 := by rw [hw0]; rfl
  have h1 : (w (h+1)).out = (rowOut (v h) (v (h+1)) (rowIn (v h) (v (h+1))).2).2 := by rw [hw1]; rfl
  generalize (rowIn (v h) (v (h+1))).2 = acc at h0 h1
  simp only [rowOut, hlx, hly, hmy, Bool.or_self, Bool.and_false, Bool.false_eq_true, if_false,
    Bool.not_false, Bool.and_true] at h0 h1
  simp only [ScanSourceW, Nat.zero_add, e1] at hs ⊢
  rw [h0, h1]
  rw [hmx, hdx]
  revert hs
  generalize (v h).out = ox
  generalize (v (h+1)).out = oy
  by_cases hh : h = 0
  · subst hh
    cases ox <;> cases oy <;> simp [OutTok.isD, OutTok.isU, OutTok.isE, outT, outV] <;> (intros; subst_vars; simp_all) <;> (by_cases hn : nxt = 0 <;> simp_all <;> omega)
  · cases ox <;> cases oy <;> simp [OutTok.isD, OutTok.isU, OutTok.isE, outT, outV, hh] <;> (intros; subst_vars; simp_all) <;> (by_cases hn : nxt = 0 <;> simp_all <;> omega)

/-- **A letter whose right cell is a delimiter never changes that cell's out slot.**  Consumer: the
pair closure of `QuietStepLaw` (the block-entry letter). -/
theorem laneRow_entry_out (lane : DigitLane) (vx vy : DigitLaneView c) (hlx : vx.leader = false)
    (hly : vy.leader = false) (hmy : vy.marker = true) :
    (laneRow lane vx vy).2.out = vy.out := by
  show (rowOut vx vy (rowIn vx vy).2).2 = vy.out
  generalize (rowIn vx vy).2 = acc
  simp only [rowOut, hlx, hly, hmy, Bool.or_self, Bool.false_eq_true, if_false, Bool.not_true,
    Bool.and_false, Bool.and_true, Bool.false_and]
  repeat' split
  all_goals first | rfl | (simp_all; done)

/-- **The source scan reads only the out slots of its window.**  Consumer: the pair closure of
`QuietStepLaw`. -/
theorem scanSourceW_congr_out (v w : Nat → DigitLaneView c) (Dp : Nat → Fin c.topA) (lo : Nat)
    (K : Nat → Prop) : ∀ (k : Nat), (∀ i, lo ≤ i → i < k + lo → (v i).out = (w i).out) →
      ∀ (nxt : Nat), ScanSourceW v Dp lo K k nxt ↔ ScanSourceW w Dp lo K k nxt := by
  intro k
  induction k with
  | zero => intro _ nxt; exact Iff.rfl
  | succ k ih =>
    intro hvw nxt
    have hk : (v (k + lo)).out = (w (k + lo)).out := hvw (k + lo) (by omega) (by omega)
    have ih' := ih (fun i h1 h2 => hvw i h1 (by omega))
    simp only [ScanSourceW, hk]
    cases (w (k + lo)).out <;> simp only [ih']

/-- **The target scan reads only the input and carry fields of its window.**  Consumer: the pair
closure of `QuietStepLaw`. -/
theorem scanTargetW_congr_in (R : Nat) (v w : Nat → DigitLaneView c) (Dp : Nat → Fin c.topA)
    (lo : Nat) (K : Nat → Bool → Bool → Prop) : ∀ (k : Nat),
      (∀ i, lo ≤ i → i < k + lo → (v i).input = (w i).input ∧ (v i).carryLive = (w i).carryLive ∧
        (v i).carryBit = (w i).carryBit ∧ (v i).carryError = (w i).carryError) →
      ∀ (nxt : Nat) (sawP seen : Bool),
        ScanTargetW R v Dp lo K k nxt sawP seen ↔ ScanTargetW R w Dp lo K k nxt sawP seen := by
  intro k
  induction k with
  | zero => intro _ nxt sawP seen; exact Iff.rfl
  | succ k ih =>
    intro hvw nxt sawP seen
    obtain ⟨h1, h2, h3, h4⟩ := hvw (k + lo) (by omega) (by omega)
    have ih' := ih (fun i hi1 hi2 => hvw i hi1 (by omega))
    simp only [ScanTargetW, h1, h2, h3, h4]
    by_cases hl : (w (k + lo)).carryLive = true
    · simp only [if_pos hl, ih']
    · simp only [if_neg hl]
      cases (w (k + lo)).input <;> simp only [ih']

end L3.DigitQuiet

#print axioms L3.DigitQuiet.win_pipe
#print axioms L3.DigitQuiet.laneRow_entry_out
#print axioms L3.DigitQuiet.scanSourceW_congr_out
#print axioms L3.DigitQuiet.scanTargetW_congr_in
