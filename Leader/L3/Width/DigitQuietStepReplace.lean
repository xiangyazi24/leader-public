import Leader.L3.Width.DigitQuietStepScan

/-!
# The quiet class: replacing a window of a scan

A letter changes two adjacent slots.  These lemmas turn a LOCAL statement about the window of the
changed slots into a statement about the whole scan:

* `scanSourceW_replace`, `scanTargetW_replace`: if two view functions agree below and above a
  window, and the scan over the window (read with an arbitrary continuation) of the first implies the
  scan over the window of the second for every continuation and entering counter state, then the
  whole scan of the first implies the whole scan of the second.

Consumer: `WidthDigitQuietStepPipe` / `Fin` / `Junction` (the window lemmas of the pair closure).
-/

namespace L3.DigitQuiet

open L3

set_option autoImplicit false

variable {c : Compiled}

/-- Monotone form of `scanSourceW_congr`.  Consumer: `scanSourceW_replace`. -/
theorem scanSourceW_mono (v w : Nat → DigitLaneView c) (Dp : Nat → Fin c.topA) (lo : Nat)
    (K K' : Nat → Prop) (hK : ∀ a, K a → K' a) :
    ∀ (k : Nat), (∀ i, lo ≤ i → i < k + lo → v i = w i) → ∀ (nxt : Nat),
      ScanSourceW v Dp lo K k nxt → ScanSourceW w Dp lo K' k nxt := by
  intro k
  induction k with
  | zero => intro _ nxt h; exact hK nxt h
  | succ k ih =>
    intro hvw nxt hs
    have hk : v (k + lo) = w (k + lo) := hvw (k + lo) (by omega) (by omega)
    have ih' := ih (fun i h1 h2 => hvw i h1 (by omega))
    simp only [ScanSourceW, hk] at hs ⊢
    revert hs
    cases (w (k + lo)).out <;> simp only [] <;> intro hs
    · exact ⟨hs.1, ih' _ hs.2⟩
    · exact ⟨hs.1, ih' _ hs.2⟩
    · exact ⟨hs.1, hs.2.1, hs.2.2.1, ih' _ hs.2.2.2⟩

/-- Monotone form of `scanTargetW_congr`.  Consumer: `scanTargetW_replace`. -/
theorem scanTargetW_mono (R : Nat) (v w : Nat → DigitLaneView c) (Dp : Nat → Fin c.topA)
    (lo : Nat) (K K' : Nat → Bool → Bool → Prop) (hK : ∀ a b d, K a b d → K' a b d) :
    ∀ (k : Nat), (∀ i, lo ≤ i → i < k + lo → v i = w i) →
      ∀ (nxt : Nat) (sawP seen : Bool),
        ScanTargetW R v Dp lo K k nxt sawP seen → ScanTargetW R w Dp lo K' k nxt sawP seen := by
  intro k
  induction k with
  | zero => intro _ nxt sawP seen h; exact hK nxt sawP seen h
  | succ k ih =>
    intro hvw nxt sawP seen hs
    have hk : v (k + lo) = w (k + lo) := hvw (k + lo) (by omega) (by omega)
    have ih' := ih (fun i h1 h2 => hvw i h1 (by omega))
    simp only [ScanTargetW, hk] at hs ⊢
    by_cases hl : (w (k + lo)).carryLive = true
    · rw [if_pos hl] at hs ⊢
      exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, ih' _ _ _ hs.2.2.2.2.2⟩
    · rw [if_neg hl] at hs ⊢
      revert hs
      cases (w (k + lo)).input with
      | E => intro hs; exact ih' _ _ _ hs
      | X => intro hs; exact hs
      | S val tail => intro hs; exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, ih' _ _ _ hs.2.2.2.2⟩
      | P val tail =>
        intro hs
        rcases hs with hs | hs
        · exact Or.inl ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, ih' _ _ _ hs.2.2.2.2⟩
        · exact Or.inr ⟨hs.1, hs.2.1, hs.2.2.1, ih' _ _ _ hs.2.2.2⟩

/-- **Replacing a window of the source scan.**  If `v` and `w` agree below the window
`lo, …, lo + cnt - 1` and above it up to `lo + cnt + t`, and the window scan of `v` implies that of `w`
for every continuation and entering `nxt`, the whole scans satisfy the same implication.  Consumer:
the window lemmas of the pair closure. -/
theorem scanSourceW_replace (v w : Nat → DigitLaneView c) (Dp : Nat → Fin c.topA)
    (lo cnt t : Nat) (hbot : ∀ q, q < lo → v q = w q)
    (htop : ∀ q, lo + cnt ≤ q → q < lo + cnt + t → v q = w q)
    (hwin : ∀ (K : Nat → Prop) (nxt : Nat),
      ScanSourceW v Dp lo K cnt nxt → ScanSourceW w Dp lo K cnt nxt)
    (K0 : Nat → Prop) (nxt : Nat) :
    ScanSourceW v Dp 0 K0 (lo + cnt + t) nxt → ScanSourceW w Dp 0 K0 (lo + cnt + t) nxt := by
  intro h
  rw [scanSourceW_append v Dp 0 K0 (lo + cnt) t nxt] at h
  rw [scanSourceW_append w Dp 0 K0 (lo + cnt) t nxt]
  refine scanSourceW_mono v w Dp (lo + cnt + 0) _ _ ?_ t
    (fun i h1 h2 => htop i (by omega) (by omega)) nxt h
  intro a ha
  rw [scanSourceW_append v Dp 0 K0 lo cnt a] at ha
  rw [scanSourceW_append w Dp 0 K0 lo cnt a]
  refine scanSourceW_mono w w Dp (lo + 0) _ _ ?_ cnt (fun _ _ _ => rfl) a (hwin _ a ha)
  intro a' ha'
  exact scanSourceW_mono v w Dp 0 K0 K0 (fun _ h => h) lo (fun i _ h2 => hbot i (by omega)) a' ha'

/-- **Replacing a window of the target scan.**  The same for the target in-lane scan, whose counter
state is `(nxt, sawP, seen)`.  Consumer: the window lemmas of the pair closure. -/
theorem scanTargetW_replace (R : Nat) (v w : Nat → DigitLaneView c) (Dp : Nat → Fin c.topA)
    (lo cnt t : Nat) (hbot : ∀ q, q < lo → v q = w q)
    (htop : ∀ q, lo + cnt ≤ q → q < lo + cnt + t → v q = w q)
    (hwin : ∀ (K : Nat → Bool → Bool → Prop) (nxt : Nat) (sawP seen : Bool),
      ScanTargetW R v Dp lo K cnt nxt sawP seen → ScanTargetW R w Dp lo K cnt nxt sawP seen)
    (K0 : Nat → Bool → Bool → Prop) (nxt : Nat) (sawP seen : Bool) :
    ScanTargetW R v Dp 0 K0 (lo + cnt + t) nxt sawP seen →
      ScanTargetW R w Dp 0 K0 (lo + cnt + t) nxt sawP seen := by
  intro h
  rw [scanTargetW_append R v Dp 0 K0 (lo + cnt) t nxt sawP seen] at h
  rw [scanTargetW_append R w Dp 0 K0 (lo + cnt) t nxt sawP seen]
  refine scanTargetW_mono R v w Dp (lo + cnt + 0) _ _ ?_ t
    (fun i h1 h2 => htop i (by omega) (by omega)) nxt sawP seen h
  intro a b d ha
  rw [scanTargetW_append R v Dp 0 K0 lo cnt a b d] at ha
  rw [scanTargetW_append R w Dp 0 K0 lo cnt a b d]
  refine scanTargetW_mono R w w Dp (lo + 0) _ _ ?_ cnt (fun _ _ _ => rfl) a b d (hwin _ a b d ha)
  intro a' b' d' ha'
  exact scanTargetW_mono R v w Dp 0 K0 K0 (fun _ _ _ h => h) lo (fun i _ h2 => hbot i (by omega))
    a' b' d' ha'

end L3.DigitQuiet

#print axioms L3.DigitQuiet.scanSourceW_replace
#print axioms L3.DigitQuiet.scanTargetW_replace
