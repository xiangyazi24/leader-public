import Leader.L3.Width.DigitQuietStepReplace
import Leader.L3.Width.DigitQuietStepWinFin

/-!
# The quiet class: the guard of the target scan and the replace lemmas that use it

Along a valid target scan the counter `nxt` is at least the next position to read, up to one
(`nxt + 1 ≥ p` before reading position `p - 1`): a token at position `p` settles at a position `≤ p`
or at `nxt ≥ p`, a carry resets the counter to `R - 1`, a wrap resets it to `R - 1`.  A `P` moving up
one cell needs exactly this room.

* `scanTargetW_exit_guard`: the scan of a window that enters with the guard leaves with the guard for
  the positions below it;
* `scanTargetW_replace_guard`: the replace lemma whose window implication may assume the guard at the
  entry of the window;
* `scanTargetW_replace_zero`: replacing a window at the bottom of the scan when the continuation also
  changes (the junction letter).

Consumer: `WidthDigitQuietStepPairs` (closure of `PQ` under a letter).
-/

namespace L3.DigitQuiet

open L3

set_option autoImplicit false

variable {c : Compiled}

/-- **The guard is kept by the scan**: if the window `lo .. k + lo - 1` is entered with
`k + lo ≤ nxt + 1` (and `k + lo ≤ R`) then the continuation is entered with `lo ≤ nxt + 1`.
Consumer: `scanTargetW_replace_guard`. -/
theorem scanTargetW_exit_guard (R : Nat) (v : Nat → DigitLaneView c) (Dp : Nat → Fin c.topA)
    (lo : Nat) (K : Nat → Bool → Bool → Prop) :
    ∀ (k nxt : Nat) (sawP seen : Bool), ScanTargetW R v Dp lo K k nxt sawP seen →
      k + lo ≤ nxt + 1 → k + lo ≤ R →
        ScanTargetW R v Dp lo (fun a b d => K a b d ∧ lo ≤ a + 1) k nxt sawP seen := by
  intro k
  induction k with
  | zero =>
    intro nxt sawP seen hs hg _
    exact ⟨hs, by omega⟩
  | succ k ih =>
    intro nxt sawP seen hs hg hR
    simp only [ScanTargetW] at hs ⊢
    by_cases hl : (v (k + lo)).carryLive = true
    · rw [if_pos hl] at hs ⊢
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hs
      exact ⟨h1, h2, h3, h4, h5, ih _ _ _ h6 (by omega) (by omega)⟩
    · rw [if_neg hl] at hs ⊢
      revert hs
      cases hin : (v (k + lo)).input with
      | E => intro hs; exact ih _ _ _ hs (by omega) (by omega)
      | X => intro hs; exact hs
      | S val tail =>
        intro hs
        obtain ⟨h1, h2, h3, h4, h5⟩ := hs
        refine ⟨h1, h2, h3, h4, ih _ _ _ h5 ?_ (by omega)⟩
        by_cases hz : k + lo = 0
        · rw [if_pos hz]; omega
        · rw [if_neg hz]; omega
      | P val tail =>
        intro hs
        rcases hs with hs | hs
        · obtain ⟨h1, h2, h3, h4, h5⟩ := hs
          exact Or.inl ⟨h1, h2, h3, h4, ih _ _ _ h5 (by omega) (by omega)⟩
        · obtain ⟨h1, h2, h3, h4⟩ := hs
          refine Or.inr ⟨h1, h2, h3, ih _ _ _ h4 ?_ (by omega)⟩
          by_cases hz : nxt = 0
          · rw [if_pos hz]; omega
          · rw [if_neg hz]; omega

/-- **Replacing a window of the target scan, with the guard.**  As `scanTargetW_replace`, but the
window implication may assume `lo + cnt ≤ nxt + 1` at the entry of the window (and that the
continuation is monotone in `sawP`, as `winFin_sawP_mono` shows for a lower window scan), which holds along any
scan that enters with `lo + cnt + t ≤ nxt + 1` and `lo + cnt + t ≤ R`.  Consumer: the fin letter of
the pair closure. -/
theorem scanTargetW_replace_guard (R : Nat) (v w : Nat → DigitLaneView c) (Dp : Nat → Fin c.topA)
    (lo cnt t : Nat) (hbot : ∀ q, q < lo → v q = w q)
    (htop : ∀ q, lo + cnt ≤ q → q < lo + cnt + t → v q = w q) (hRle : lo + cnt + t ≤ R)
    (hwin : ∀ (K : Nat → Bool → Bool → Prop) (nxt : Nat) (sawP seen : Bool),
      (∀ a d, K a true d → K a false d) → lo + cnt ≤ nxt + 1 →
      ScanTargetW R v Dp lo K cnt nxt sawP seen → ScanTargetW R w Dp lo K cnt nxt sawP seen)
    (K0 : Nat → Bool → Bool → Prop) (hK0 : ∀ a d, K0 a true d → K0 a false d)
    (nxt : Nat) (sawP seen : Bool)
    (hg : lo + cnt + t ≤ nxt + 1) :
    ScanTargetW R v Dp 0 K0 (lo + cnt + t) nxt sawP seen →
      ScanTargetW R w Dp 0 K0 (lo + cnt + t) nxt sawP seen := by
  intro h
  rw [scanTargetW_append R v Dp 0 K0 (lo + cnt) t nxt sawP seen] at h
  rw [scanTargetW_append R w Dp 0 K0 (lo + cnt) t nxt sawP seen]
  have hgd := scanTargetW_exit_guard R v Dp (lo + cnt + 0)
    (fun a b d => ScanTargetW R v Dp 0 K0 (lo + cnt) a b d) t nxt sawP seen h
    (by omega) (by omega)
  refine scanTargetW_mono R v w Dp (lo + cnt + 0) _ _ ?_ t
    (fun i h1 h2 => htop i (by omega) (by omega)) nxt sawP seen hgd
  intro a b d ha
  obtain ⟨ha, hga⟩ := ha
  rw [scanTargetW_append R v Dp 0 K0 lo cnt a b d] at ha
  rw [scanTargetW_append R w Dp 0 K0 lo cnt a b d]
  refine scanTargetW_mono R w w Dp (lo + 0) _ _ ?_ cnt (fun _ _ _ => rfl) a b d
    (hwin _ a b d (fun a' d' h' => winFin_sawP_mono R v Dp 0 K0 hK0 lo a' d' h') (by omega) ha)
  intro a' b' d' ha'
  exact scanTargetW_mono R v w Dp 0 K0 K0 (fun _ _ _ h => h) lo (fun i _ h2 => hbot i (by omega))
    a' b' d' ha'

/-- **Replacing a window at the bottom of the target scan when the continuation changes.**  Consumer:
the junction letter of the pair closure. -/
theorem scanTargetW_replace_zero (R : Nat) (v w : Nat → DigitLaneView c) (Dp : Nat → Fin c.topA)
    (cnt t : Nat) (htop : ∀ q, cnt ≤ q → q < cnt + t → v q = w q)
    (K0 K0' : Nat → Bool → Bool → Prop)
    (hwin : ∀ (nxt : Nat) (sawP seen : Bool),
      ScanTargetW R v Dp 0 K0 cnt nxt sawP seen → ScanTargetW R w Dp 0 K0' cnt nxt sawP seen)
    (nxt : Nat) (sawP seen : Bool) :
    ScanTargetW R v Dp 0 K0 (cnt + t) nxt sawP seen →
      ScanTargetW R w Dp 0 K0' (cnt + t) nxt sawP seen := by
  intro h
  rw [scanTargetW_append R v Dp 0 K0 cnt t nxt sawP seen] at h
  rw [scanTargetW_append R w Dp 0 K0' cnt t nxt sawP seen]
  exact scanTargetW_mono R v w Dp (cnt + 0) _ _ (fun a b d ha => hwin a b d ha) t
    (fun i h1 h2 => htop i (by omega) (by omega)) nxt sawP seen h

end L3.DigitQuiet

#print axioms L3.DigitQuiet.scanTargetW_exit_guard
#print axioms L3.DigitQuiet.scanTargetW_replace_guard
#print axioms L3.DigitQuiet.scanTargetW_replace_zero
