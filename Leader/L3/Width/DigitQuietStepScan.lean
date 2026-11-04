import Leader.L3.Width.DigitQuiet

/-!
# The quiet class: the pipeline scan is local

`PairQuiet` is a whole-block scan (`ScanTarget` over `R - 1, …, 0` continuing into `ScanSource` over
`R - 1, …, 0`), while a letter changes two adjacent slots.  This module makes the scan local:

* `ScanTargetK`, `ScanSourceK`: the same scans with the continuation at position `0` an arbitrary
  predicate of the counter state `(nxt, sawP, seen)` (resp. `nxt`); `scanTarget_eq_K`,
  `scanSource_eq_K` show the originals are the case of the constant continuation;
* `scanTargetK_append`, `scanSourceK_append`: **the scan over `h + k - 1, …, 0` equals the scan over
  `h + k - 1, …, h` followed by the scan over `h - 1, …, 0` with the counter state passed along**;
* `scanTargetW_congr`, `scanSourceW_congr`: the scan over a window reads only the slots of the window
  and the continuation, so a letter that leaves a window alone leaves its scan alone;
* `scanTargetW_carryError`, `scanTargetW_noX`: a live carry met by the scan has error bit `false`,
  and no input met by the scan is the marker `X`.

Consumer: `Leader/L3/Width/DigitQuietStepReport.lean` (the report clause) and the pair closure of
`QuietStepLaw` (open, `research/lean-l3/ledgers/R10c-quiet-law-notes.md`).
-/

namespace L3.DigitQuiet

open L3

set_option autoImplicit false

variable {c : Compiled}

/-- The target in-lane scan over the window of absolute positions `lo, …, k + lo - 1`, with an
arbitrary continuation at the bottom.  Consumer: `scanTarget_eq_W`, `scanTargetW_append`. -/
def ScanTargetW (R : Nat) (v : Nat → DigitLaneView c) (Dp : Nat → Fin c.topA) (lo : Nat)
    (K : Nat → Bool → Bool → Prop) : Nat → Nat → Bool → Bool → Prop
  | 0, nxt, sawP, seen => K nxt sawP seen
  | k + 1, nxt, sawP, seen =>
      if (v (k + lo)).carryLive = true then
        nxt = k + lo ∧ sawP = false ∧ (v (k + lo)).input = .E ∧
          (v (k + lo)).carryBit = carryInto Dp (k + lo + 1) ∧ (v (k + lo)).carryError = false ∧
          ScanTargetW R v Dp lo K k (R - 1) sawP true
      else
        match (v (k + lo)).input with
        | .E => ScanTargetW R v Dp lo K k nxt sawP seen
        | .X => False
        | .S val tail =>
            sawP = false ∧ nxt = k + lo ∧ val = Dp (k + lo) ∧ tail = decide (k + lo = 0) ∧
              ScanTargetW R v Dp lo K k (if k + lo = 0 then R - 1 else k + lo - 1) sawP true
        | .P val tail =>
            (tail = true ∧ nxt ≠ 0 ∧ seen = false ∧ val = Dp 0 ∧
              ScanTargetW R v Dp lo K k nxt true true) ∨
            (k + lo ≤ nxt ∧ val = Dp nxt ∧ tail = decide (nxt = 0) ∧
              ScanTargetW R v Dp lo K k (if nxt = 0 then R - 1 else nxt - 1) true true)

/-- The source out-lane scan over the window of absolute positions `lo, …, k + lo - 1`, with an
arbitrary continuation at the bottom.  Consumer: `scanSource_eq_W`, `scanSourceW_append`. -/
def ScanSourceW (v : Nat → DigitLaneView c) (Dp : Nat → Fin c.topA) (lo : Nat)
    (K : Nat → Prop) : Nat → Nat → Prop
  | 0, nxt => K nxt
  | k + 1, nxt =>
      match (v (k + lo)).out with
      | .E => (if k + lo = 0 then nxt = 0 else nxt < k + lo) ∧ ScanSourceW v Dp lo K k nxt
      | .U => nxt = k + lo ∧ ScanSourceW v Dp lo K k (k + lo - 1)
      | .D val tail =>
          nxt ≤ k + lo ∧ val = Dp nxt ∧ tail = decide (nxt = 0) ∧
            ScanSourceW v Dp lo K k (if nxt = 0 then k + lo - 1 else nxt - 1)

/-- `ScanTarget` is the window scan from `0` with the continuation `src` on the counter.  Consumer:
`pairQuiet_iff_W`. -/
theorem scanTarget_eq_W (R : Nat) (v : Nat → DigitLaneView c) (Dp : Nat → Fin c.topA)
    (src : Nat → Prop) :
    ∀ (k nxt : Nat) (sawP seen : Bool),
      ScanTarget R v Dp src k nxt sawP seen ↔
        ScanTargetW R v Dp 0 (fun a _ _ => src a) k nxt sawP seen := by
  intro k
  induction k with
  | zero => intro nxt sawP seen; exact Iff.rfl
  | succ k ih =>
    intro nxt sawP seen
    simp only [ScanTarget, ScanTargetW, Nat.add_zero]
    by_cases hl : (v k).carryLive = true
    · simp only [if_pos hl, ih]
    · simp only [if_neg hl]
      cases (v k).input <;> simp only [ih]

/-- `ScanSource` is the window scan from `0` with the trivial continuation.  Consumer:
`pairQuiet_iff_W`. -/
theorem scanSource_eq_W (v : Nat → DigitLaneView c) (Dp : Nat → Fin c.topA) :
    ∀ (k nxt : Nat), ScanSource v Dp k nxt ↔ ScanSourceW v Dp 0 (fun _ => True) k nxt := by
  intro k
  induction k with
  | zero => intro nxt; exact Iff.rfl
  | succ k ih =>
    intro nxt
    simp only [ScanSource, ScanSourceW, Nat.add_zero]
    cases (v k).out <;> simp only [ih]

/-- **The scan over `m + k` positions from `lo` is the scan over the top `k` positions (from
`m + lo`) followed by the scan over the bottom `m` positions (from `lo`)**, the counter state
passed along: target in-lane.  Consumer: the closure of `PairQuiet` under the in-lane rules. -/
theorem scanTargetW_append (R : Nat) (v : Nat → DigitLaneView c) (Dp : Nat → Fin c.topA)
    (lo : Nat) (K : Nat → Bool → Bool → Prop) (m : Nat) :
    ∀ (k nxt : Nat) (sawP seen : Bool),
      ScanTargetW R v Dp lo K (m + k) nxt sawP seen ↔
        ScanTargetW R v Dp (m + lo) (fun a b d => ScanTargetW R v Dp lo K m a b d)
          k nxt sawP seen := by
  intro k
  induction k with
  | zero => intro nxt sawP seen; exact Iff.rfl
  | succ k ih =>
    intro nxt sawP seen
    show ScanTargetW R v Dp lo K ((m + k) + 1) nxt sawP seen ↔ _
    have e : m + k + lo = k + (m + lo) := by omega
    simp only [ScanTargetW, e]
    by_cases hl : (v (k + (m + lo))).carryLive = true
    · simp only [if_pos hl, ih]
    · simp only [if_neg hl]
      cases (v (k + (m + lo))).input <;> simp only [ih]

/-- The same for the source out-lane.  Consumer: the closure of `PairQuiet` under the out-lane
rules. -/
theorem scanSourceW_append (v : Nat → DigitLaneView c) (Dp : Nat → Fin c.topA)
    (lo : Nat) (K : Nat → Prop) (m : Nat) :
    ∀ (k nxt : Nat),
      ScanSourceW v Dp lo K (m + k) nxt ↔
        ScanSourceW v Dp (m + lo) (fun a => ScanSourceW v Dp lo K m a) k nxt := by
  intro k
  induction k with
  | zero => intro nxt; exact Iff.rfl
  | succ k ih =>
    intro nxt
    show ScanSourceW v Dp lo K ((m + k) + 1) nxt ↔ _
    have e : m + k + lo = k + (m + lo) := by omega
    simp only [ScanSourceW, e]
    cases (v (k + (m + lo))).out <;> simp only [ih]

/-- The target scan over a window reads only the slots of the window and the continuation.
Consumer: the closure of `PairQuiet` under a letter that leaves the window alone. -/
theorem scanTargetW_congr (R : Nat) (v w : Nat → DigitLaneView c) (Dp : Nat → Fin c.topA)
    (lo : Nat) (K K' : Nat → Bool → Bool → Prop) (hK : ∀ a b d, K a b d ↔ K' a b d) :
    ∀ (k : Nat), (∀ i, lo ≤ i → i < k + lo → v i = w i) →
      ∀ (nxt : Nat) (sawP seen : Bool),
        ScanTargetW R v Dp lo K k nxt sawP seen ↔ ScanTargetW R w Dp lo K' k nxt sawP seen := by
  intro k
  induction k with
  | zero => intro _ nxt sawP seen; exact hK nxt sawP seen
  | succ k ih =>
    intro hvw nxt sawP seen
    have hk : v (k + lo) = w (k + lo) := hvw (k + lo) (by omega) (by omega)
    have ih' := ih (fun i h1 h2 => hvw i h1 (by omega))
    simp only [ScanTargetW, hk]
    by_cases hl : (w (k + lo)).carryLive = true
    · simp only [if_pos hl, ih']
    · simp only [if_neg hl]
      cases (w (k + lo)).input <;> simp only [ih']

/-- The source scan over a window reads only the slots of the window and the continuation.
Consumer: the closure of `PairQuiet` under a letter that leaves the window alone. -/
theorem scanSourceW_congr (v w : Nat → DigitLaneView c) (Dp : Nat → Fin c.topA) (lo : Nat)
    (K K' : Nat → Prop) (hK : ∀ a, K a ↔ K' a) :
    ∀ (k : Nat), (∀ i, lo ≤ i → i < k + lo → v i = w i) → ∀ (nxt : Nat),
      ScanSourceW v Dp lo K k nxt ↔ ScanSourceW w Dp lo K' k nxt := by
  intro k
  induction k with
  | zero => intro _ nxt; exact hK nxt
  | succ k ih =>
    intro hvw nxt
    have hk : v (k + lo) = w (k + lo) := hvw (k + lo) (by omega) (by omega)
    have ih' := ih (fun i h1 h2 => hvw i h1 (by omega))
    simp only [ScanSourceW, hk]
    cases (w (k + lo)).out <;> simp only [ih']

/-- **A live carry met by the target scan has error bit `false`.**  Consumer:
`pairQuiet_target_carryError`. -/
theorem scanTargetW_carryError (R : Nat) (v : Nat → DigitLaneView c) (Dp : Nat → Fin c.topA)
    (lo : Nat) (K : Nat → Bool → Bool → Prop) :
    ∀ (k nxt : Nat) (sawP seen : Bool), ScanTargetW R v Dp lo K k nxt sawP seen →
      ∀ i, lo ≤ i → i < k + lo → (v i).carryLive = true → (v i).carryError = false := by
  intro k
  induction k with
  | zero => intro nxt sawP seen _ i h1 hi; omega
  | succ k ih =>
    intro nxt sawP seen hs i h1 hi hlive
    simp only [ScanTargetW] at hs
    by_cases hl : (v (k + lo)).carryLive = true
    · rw [if_pos hl] at hs
      obtain ⟨-, -, -, -, herr, hrest⟩ := hs
      by_cases hik : i = k + lo
      · subst hik; exact herr
      · exact ih _ _ _ hrest i h1 (by omega) hlive
    · rw [if_neg hl] at hs
      have hik : i ≠ k + lo := fun h => hl (h ▸ hlive)
      have hlt : i < k + lo := by omega
      revert hs
      cases hin : (v (k + lo)).input with
      | E => intro hs; exact ih _ _ _ hs i h1 hlt hlive
      | X => intro hs; exact hs.elim
      | S val tail => intro hs; exact ih _ _ _ hs.2.2.2.2 i h1 hlt hlive
      | P val tail =>
        intro hs
        rcases hs with hs | hs
        · exact ih _ _ _ hs.2.2.2.2 i h1 hlt hlive
        · exact ih _ _ _ hs.2.2.2 i h1 hlt hlive

/-- **No input met by the target scan is the marker `X`.**  Consumer: the closure of `PairQuiet`
under the marker rules. -/
theorem scanTargetW_noX (R : Nat) (v : Nat → DigitLaneView c) (Dp : Nat → Fin c.topA)
    (lo : Nat) (K : Nat → Bool → Bool → Prop) :
    ∀ (k nxt : Nat) (sawP seen : Bool), ScanTargetW R v Dp lo K k nxt sawP seen →
      ∀ i, lo ≤ i → i < k + lo → (v i).input ≠ .X := by
  intro k
  induction k with
  | zero => intro nxt sawP seen _ i h1 hi; omega
  | succ k ih =>
    intro nxt sawP seen hs i h1 hi
    simp only [ScanTargetW] at hs
    by_cases hl : (v (k + lo)).carryLive = true
    · rw [if_pos hl] at hs
      obtain ⟨-, -, hE, -, -, hrest⟩ := hs
      by_cases hik : i = k + lo
      · subst hik; rw [hE]; intro h; cases h
      · exact ih _ _ _ hrest i h1 (by omega)
    · rw [if_neg hl] at hs
      by_cases hik : i = k + lo
      · subst hik
        revert hs
        cases hin : (v (k + lo)).input with
        | E => intro _; intro h; cases h
        | X => intro hs; exact hs.elim
        | S val tail => intro _; intro h; cases h
        | P val tail => intro _; intro h; cases h
      · have hlt : i < k + lo := by omega
        revert hs
        cases hin : (v (k + lo)).input with
        | E => intro hs; exact ih _ _ _ hs i h1 hlt
        | X => intro hs; exact hs.elim
        | S val tail => intro hs; exact ih _ _ _ hs.2.2.2.2 i h1 hlt
        | P val tail =>
          intro hs
          rcases hs with hs | hs
          · exact ih _ _ _ hs.2.2.2.2 i h1 hlt
          · exact ih _ _ _ hs.2.2.2 i h1 hlt

/-- `PairQuiet` in the window form.  Consumer: `pairQuiet_target_carryError`, the pair closure. -/
theorem pairQuiet_iff_W {n : Nat} (ring : DirectedRing n) (root : Fin n) (S : Fin n → ProjD c)
    (lane : DigitLane) (source target : Nat) :
    PairQuiet ring root S lane source target ↔
      ScanTargetW (digitSpan c) (fun h => view ring root S lane (target + h))
        (fun h => (S (digitSite ring root (source + h))).top.d) 0
        (fun a _ _ => ScanSourceW (fun h => view ring root S lane (source + h))
          (fun h => (S (digitSite ring root (source + h))).top.d) 0 (fun _ => True)
          (digitSpan c) a)
        (digitSpan c) (digitSpan c - 1) false false := by
  unfold PairQuiet
  rw [scanTarget_eq_W]
  refine scanTargetW_congr _ _ _ _ _ _ _ ?_ _ (fun _ _ _ => rfl) _ _ _
  intro a b d
  exact scanSource_eq_W _ _ _ _

/-- **In a quiet pair a live target carry has error bit `false`.**  Consumer:
`quiet_no_error_terminal` (WidthDigitQuietStepReport). -/
theorem pairQuiet_target_carryError {n : Nat} (ring : DirectedRing n) (root : Fin n)
    (S : Fin n → ProjD c) (lane : DigitLane) (source target : Nat)
    (h : PairQuiet ring root S lane source target) (i : Nat) (hi : i < digitSpan c)
    (hlive : (view ring root S lane (target + i)).carryLive = true) :
    (view ring root S lane (target + i)).carryError = false :=
  scanTargetW_carryError _ _ _ _ _ _ _ _ _ ((pairQuiet_iff_W ring root S lane source target).mp h) i
    (Nat.zero_le _) (by omega) hlive

end L3.DigitQuiet

#print axioms L3.DigitQuiet.scanTarget_eq_W
#print axioms L3.DigitQuiet.scanTargetW_append
#print axioms L3.DigitQuiet.scanSourceW_append
#print axioms L3.DigitQuiet.scanTargetW_congr
#print axioms L3.DigitQuiet.pairQuiet_target_carryError
