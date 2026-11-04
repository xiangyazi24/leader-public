import Leader.L3.Width.DigitQuietStepGlue
import Leader.L3.Width.DigitQuietStepReplace

/-!
# The quiet class: the FIN letter on the target in-lane scan

`win_fin`: the closure of the two-position target window `h + 1, h` under a FIN letter inside a target
block (a `P` moving up, a `P` settling next to an `S`, the launch at the border, the advance of a live
carry).  The continuation must be monotone in `sawP` (`hK`): the letter that settles a `P` next to an
`S` turns the flag `sawP` from `true` to `false`; `winFin_sawP_mono` shows that every lower target
window scan has this monotonicity.

Consumer: the pair closure of `QuietStepLaw` (`research/lean-l3/ledgers/R10c-quiet-law-notes.md`).
-/

namespace L3.DigitQuiet

open L3

set_option autoImplicit false

variable {c : Compiled}

/-- Boolean equality of naturals is the decision.  Consumer: `win_fin`. -/
theorem winFin_beq (a b : Nat) : (a == b) = decide (a = b) := Bool.eq_iff_iff.2 (by simp)

/-- **The target window scan is monotone in `sawP`**: a scan entered with `sawP = true` is also a scan
entered with `sawP = false`, provided the continuation is.  Consumer: `win_fin` (its hypothesis `hK`
for a continuation that is a lower window scan). -/
theorem winFin_sawP_mono (R : Nat) (v : Nat → DigitLaneView c) (Dp : Nat → Fin c.topA) (lo : Nat)
    (K : Nat → Bool → Bool → Prop) (hK : ∀ a d, K a true d → K a false d) :
    ∀ (k nxt : Nat) (seen : Bool),
      ScanTargetW R v Dp lo K k nxt true seen → ScanTargetW R v Dp lo K k nxt false seen := by
  intro k
  induction k with
  | zero => intro nxt seen hs; exact hK nxt seen hs
  | succ k ih =>
    intro nxt seen hs
    simp only [ScanTargetW] at hs ⊢
    by_cases hl : (v (k + lo)).carryLive = true
    · rw [if_pos hl] at hs
      exact absurd hs.2.1 (by decide)
    · rw [if_neg hl] at hs ⊢
      revert hs
      cases (v (k + lo)).input with
      | E => intro hs; exact ih _ _ hs
      | X => intro hs; exact hs
      | S val tail => intro hs; exact absurd hs.1 (by decide)
      | P val tail => intro hs; exact hs

/-- **The FIN letter on the target window `h + 1, h`**: the in-lane scan of the two cells `h`, `h + 1`
of a target block (leaders false, marker at `h` iff `h = 0`, digits those of the block successor) is
kept by one letter `x = cell h → y = cell h + 1`, provided the entering counter has room above
(`h + 1 ≤ nxt`) and the continuation is monotone in `sawP`.  The statement without `hK` is false: for
`h = 0`, `R = 2`, `nxt = 1`, `sawP = false`, cell 1 holding `S (Dp 1) false`, cell 0 the marker with
input `P (Dp 0) true`, the `P` settles to `S (Dp 0) true` and the continuation receives `sawP = false`
instead of `true` (take `K a b d := b = true`).  Consumer: the pair closure of `QuietStepLaw`. -/
theorem win_fin (lane : DigitLane) (R : Nat) (vt wt : Nat → DigitLaneView c) (Dp : Nat → Fin c.topA) (h : Nat) (hh : h + 1 < R) (hlx : (vt h).leader = false) (hly : (vt (h+1)).leader = false) (hmx : (vt h).marker = decide (h = 0)) (hmy : (vt (h+1)).marker = false) (hdx : ((vt h).digit).val = ((Dp h).val + (if carryInto Dp h then 1 else 0)) % c.topA) (hdy : ((vt (h+1)).digit).val = ((Dp (h+1)).val + (if carryInto Dp (h+1) then 1 else 0)) % c.topA) (hw0 : wt h = (laneRow lane (vt h) (vt (h+1))).1) (hw1 : wt (h+1) = (laneRow lane (vt h) (vt (h+1))).2) (K : Nat → Bool → Bool → Prop) (nxt : Nat) (sawP seen : Bool) (hg : h + 1 ≤ nxt) (hK : ∀ a d, K a true d → K a false d) : ScanTargetW R vt Dp h K 2 nxt sawP seen → ScanTargetW R wt Dp h K 2 nxt sawP seen := by
  intro hs
  simp only [ScanTargetW, Nat.zero_add, Nat.add_comm 1 h] at hs ⊢
  rw [hw0, hw1]
  clear hw0 hw1
  generalize vt h = X at *
  generalize vt (h+1) = Y at *
  rcases X with ⟨lx, mx, dx, ox, ix, clx, cbx, cex⟩
  rcases Y with ⟨ly, my, dy, oy, iy, cly, cby, cey⟩
  dsimp only at hlx hly hmx hmy hdx hdy
  subst hlx hly hmx hmy
  have hA := c.topA_pos
  by_cases h0 : h = 0
  · subst h0
    cases clx <;> cases cly <;> rcases ix with _|_|⟨vx,tx⟩|⟨vx,tx⟩ <;> rcases iy with _|_|⟨vy,ty⟩|⟨vy,ty⟩ <;>
    simp [laneRow, rowIn, rowCarry, rowSucc, rowLaunch, InTok.isS, InTok.isE, InTok.isP, InTok.isX, inT, inV] at hs ⊢
    all_goals try simp_all
    all_goals (revert hs; try simp (config := {contextual := true}))
    all_goals (intros; first | (exfalso; omega) | (apply hK; assumption) | (cases lane <;> simp_all [carryInto, winFin_beq] <;> done))
  · cases clx <;> cases cly <;> rcases ix with _|_|⟨vx,tx⟩|⟨vx,tx⟩ <;> rcases iy with _|_|⟨vy,ty⟩|⟨vy,ty⟩ <;>
    simp [laneRow, rowIn, rowCarry, rowSucc, rowLaunch, InTok.isS, InTok.isE, InTok.isP, InTok.isX, inT, inV, h0] at hs ⊢
    all_goals try simp_all
    all_goals (revert hs; try simp (config := {contextual := true}))
    all_goals (intros; first | (exfalso; omega) | (apply hK; assumption) | (rename_i hq; rcases hq with hq | hq; exact Or.inl hq; exact Or.inr hq.2) | (cases lane <;> simp_all [carryInto, winFin_beq] <;> done))

end L3.DigitQuiet

#print axioms L3.DigitQuiet.winFin_sawP_mono
#print axioms L3.DigitQuiet.win_fin
