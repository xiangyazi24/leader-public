import Leader.L3.Width.DigitQuietStepPairsPipeFin
import Leader.L3.Width.DigitQuietStepWinEnds

/-!
# The pair predicate under the junction and the terminal letter, block-relative

* `pq_del`: the letter from the last source cell onto the target delimiter (a `D` is accepted into the
  empty delimiter, or the last source cell is sampled): `win_del` on the bottom window of the target
  scan, whose continuation is the source scan;
* `pq_term`: the letter from the last target cell onto the next delimiter: `win_term` on the top
  window, whose continuation is the lower target scan (antitone in the flags, by
  `scanTargetW_flagAnti`).

Consumer: `WidthDigitQuietStepPairsC` (`pq_after_letter`).
-/

namespace L3.DigitQuiet

open L3

set_option autoImplicit false

variable {c : Compiled}

/-- **The junction letter keeps the pair predicate.**  Consumer: `pq_after_letter`. -/
theorem pq_del (lane : DigitLane) (R : Nat) (hR : 2 ≤ R) (vs vs' vt vt' : Nat → DigitLaneView c)
    (Dp : Nat → Fin c.topA)
    (hlx : (vs (R-1)).leader = false) (hly : (vt 0).leader = false)
    (hmx : (vs (R-1)).marker = false) (hmy : (vt 0).marker = true)
    (hDx : (vs (R-1)).digit = Dp (R-1))
    (hw0 : vs' (R-1) = (laneRow lane (vs (R-1)) (vt 0)).1)
    (hw1 : vt' 0 = (laneRow lane (vs (R-1)) (vt 0)).2)
    (hsb : ∀ q, q < R - 1 → vs' q = vs q) (htb : ∀ q, 0 < q → q < R → vt' q = vt q) :
    PQ R vs vt Dp → PQ R vs' vt' Dp := by
  unfold PQ
  intro hp
  rw [scanTarget_eq_W] at hp ⊢
  obtain ⟨t, ht⟩ : ∃ t, R = 1 + t := ⟨R - 1, by omega⟩
  have hR1 : R - 1 = t := by omega
  have hwd := fun nxt sawP seen => win_del lane R hR vs vs' vt vt' Dp hlx hly hmx hmy hDx hw0 hw1
    hsb htb nxt sawP seen
  clear hlx hly hmx hmy hDx hw0 hw1
  subst ht
  exact scanTargetW_replace_zero (1 + t) vt vt' Dp 1 t
    (fun q h1 h2 => (htb q (by omega) h2).symm) _ _ (fun nxt sawP seen hs => hwd nxt sawP seen hs)
    (1 + t - 1) false false hp

/-- **The terminal letter keeps the pair predicate.**  Consumer: `pq_after_letter`. -/
theorem pq_term (lane : DigitLane) (R : Nat) (hR : 2 ≤ R) (vs vt vt' : Nat → DigitLaneView c)
    (Dp : Nat → Fin c.topA) (y : DigitLaneView c)
    (hlx : (vt (R-1)).leader = false) (hly : y.leader = false)
    (hmx : (vt (R-1)).marker = false) (hmy : y.marker = true)
    (hw : vt' (R-1) = (laneRow lane (vt (R-1)) y).1)
    (htb : ∀ q, q < R - 1 → vt' q = vt q) :
    PQ R vs vt Dp → PQ R vs vt' Dp := by
  unfold PQ
  intro hp
  rw [scanTarget_eq_W] at hp ⊢
  obtain ⟨m, rfl⟩ : ∃ m, R = m + 1 := ⟨R - 1, by omega⟩
  have e : m + 1 - 1 = m := rfl
  rw [e] at hp ⊢ hlx hmx hw htb
  rw [scanTargetW_append (m + 1) vt Dp 0 _ m 1 m false false] at hp
  rw [scanTargetW_append (m + 1) vt' Dp 0 _ m 1 m false false]
  have hK : WinEndsFlagAnti
      (fun a b d => ScanTargetW (m + 1) vt Dp 0 (fun a _ _ => ScanSource vs Dp (m + 1) a) m a b d) :=
    fun a b d b' d' h h1 h2 =>
      scanTargetW_flagAnti (m + 1) vt Dp 0 (fun a _ _ => ScanSource vs Dp (m + 1) a)
        (fun a b d b' d' h _ _ => h) m a b d b' d' h h1 h2
  have hwt := win_term lane (m + 1) hR vt vt' Dp y hlx hly hmx hmy
    (by rw [e]; exact hw) _ hK
  rw [e] at hwt
  refine scanTargetW_mono (m + 1) vt' vt' Dp (m + 0) _ _ ?_ 1 (fun _ _ _ => rfl) m false false
    (hwt hp)
  intro a b d ha
  exact scanTargetW_mono (m + 1) vt vt' Dp 0 _ _ (fun _ _ _ h => h) m
    (fun i _ hi => (htb i hi).symm) a b d ha

end L3.DigitQuiet

#print axioms L3.DigitQuiet.pq_del
#print axioms L3.DigitQuiet.pq_term
